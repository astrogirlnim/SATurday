import Theory.ProofComplexity.CuttingPlanes

/-!
# Monotone feasible interpolation for cutting planes (Ladder Rung R3)

Pudlák's construction. Fix a CP refutation `L` of `A ∪ B` where `A` uses variables in
`P ∪ Q` (with `P` only positive) and `B` uses variables in `P ∪ R`. For an assignment `a`
each line `k` gets two integer bounds `(DA k, DB k)` that depend only on `a` restricted
to `P`:

* the `Q` part of line `k` is at least `DA k` whenever `a` satisfies `A`;
* the part outside `P ∪ Q` is at least `DB k` whenever `a` satisfies `B`;
* `DA k + DB k ≥ rhs k - (P part of line k)`.

On the final line `0 ≥ b` (`b > 0`) this forces `DA ≤ 0` under `A` and `DA ≥ 1` under
`B`. A monotone real circuit tracks `- DA k` line by line.

LOG: R3 CuttingPlanesInterp module (Pudlák interpolation)
-/

namespace SATurday.ProofComplexity

noncomputable section

open Classical

/-! ## Indexed rules -/

/-- The empty line, used as a default. -/
def zeroIneq : Ineq := ⟨0, 0⟩

/-- Line `k` of a proof (default `0 ≥ 0`). -/
def lineAt (L : List Ineq) (k : ℕ) : Ineq := L.getD k zeroIneq

/-- A CP inference with premises given by line indices. -/
inductive Rule where
  | hyp (C : Clause)
  | low (i : ℕ)
  | up (i : ℕ)
  | add (i j : ℕ)
  | scale (i c : ℕ)
  | div (i c : ℕ)

/-- Validity of an indexed rule at line `k`. -/
def Rule.Valid (F : CNF) (L : List Ineq) (k : ℕ) : Rule → Prop
  | .hyp C => C ∈ F ∧ lineAt L k = clauseIneq C
  | .low i => lineAt L k = lowerAx i
  | .up i => lineAt L k = upperAx i
  | .add i j => i < k ∧ j < k ∧ lineAt L k = lineAt L i + lineAt L j
  | .scale i c => i < k ∧ lineAt L k = (lineAt L i).scale c
  | .div i c => i < k ∧ 0 < c ∧ (lineAt L i).coef = (c : ℤ) • (lineAt L k).coef ∧
      (c : ℤ) * ((lineAt L k).rhs - 1) < (lineAt L i).rhs

theorem lineAt_of_lt {L : List Ineq} {k : ℕ} (hk : k < L.length) :
    lineAt L k = L.get ⟨k, hk⟩ := by
  simp [lineAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem mem_take_index {L : List Ineq} {k : ℕ} {J : Ineq} (h : J ∈ L.take k) :
    ∃ i < k, lineAt L i = J := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
  have hik : i < k := by simp at hi; omega
  have hiL : i < L.length := by simp at hi; omega
  refine ⟨i, hik, ?_⟩
  rw [lineAt_of_lt hiL]
  simp

theorem exists_rule {F : CNF} {L : List Ineq} (hL : CPProof F L) {k : ℕ} (hk : k < L.length) :
    ∃ r : Rule, r.Valid F L k := by
  have h := hL k hk
  rw [← lineAt_of_lt hk] at h
  rcases h with ⟨C, hC, h⟩ | ⟨i, h⟩ | ⟨i, h⟩ | ⟨J, hJ, K, hK, h⟩ | ⟨J, hJ, c, h⟩ |
      ⟨J, hJ, c, hc, hcoef, hrhs⟩
  · exact ⟨.hyp C, hC, h⟩
  · exact ⟨.low i, h⟩
  · exact ⟨.up i, h⟩
  · obtain ⟨i, hi, rfl⟩ := mem_take_index hJ
    obtain ⟨j, hj, rfl⟩ := mem_take_index hK
    exact ⟨.add i j, hi, hj, h⟩
  · obtain ⟨i, hi, rfl⟩ := mem_take_index hJ
    exact ⟨.scale i c, hi, h⟩
  · obtain ⟨i, hi, rfl⟩ := mem_take_index hJ
    exact ⟨.div i c, hi, hc, hcoef, hrhs⟩

/-- The chosen rule of line `k`. -/
def ruleAt (F : CNF) (L : List Ineq) (k : ℕ) : Rule :=
  if h : ∃ r : Rule, r.Valid F L k then Classical.choose h else .hyp ∅

theorem ruleAt_valid {F : CNF} {L : List Ineq} (hL : CPProof F L) {k : ℕ} (hk : k < L.length) :
    (ruleAt F L k).Valid F L k := by
  have h := exists_rule hL hk
  unfold ruleAt
  rw [dif_pos h]
  exact Classical.choose_spec h

/-! ## Partial sums of a line -/

/-- Part of the left hand side on the variables in `S`. -/
def partOn (S : Finset ℕ) (I : Ineq) (a : Assignment) : ℤ := ∑ i ∈ S, I.coef i * bitZ a i

theorem partOn_add (S : Finset ℕ) (I J : Ineq) (a : Assignment) :
    partOn S (I + J) a = partOn S I a + partOn S J a := by
  unfold partOn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (I.coef + J.coef) i * _ = _
  rw [Finsupp.add_apply]; ring

theorem partOn_smul (S : Finset ℕ) (c : ℤ) (f : ℕ →₀ ℤ) (r : ℤ) (a : Assignment) :
    partOn S ⟨c • f, r⟩ a = c * partOn S ⟨f, 0⟩ a := by
  unfold partOn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finsupp.smul_apply, smul_eq_mul]; ring

theorem partOn_scale (S : Finset ℕ) (c : ℕ) (I : Ineq) (a : Assignment) :
    partOn S (I.scale c) a = c * partOn S I a := by
  rw [Ineq.scale, partOn_smul]; rfl

/-- The left hand side as a sum over any superset of the support. -/
theorem lhs_eq_sum_of_support {I : Ineq} {S : Finset ℕ} (h : I.coef.support ⊆ S)
    (a : Assignment) : I.lhs a = partOn S I a := by
  unfold Ineq.lhs partOn
  exact Finsupp.sum_of_support_subset _ h _ (fun _ _ => by simp)

theorem partOn_union {S T : Finset ℕ} (h : Disjoint S T) (I : Ineq) (a : Assignment) :
    partOn (S ∪ T) I a = partOn S I a + partOn T I a := by
  unfold partOn; exact Finset.sum_union h

theorem partOn_eq_zero {S : Finset ℕ} {I : Ineq} (h : ∀ i ∈ S, I.coef i = 0) (a : Assignment) :
    partOn S I a = 0 := by
  unfold partOn; exact Finset.sum_eq_zero fun i hi => by rw [h i hi]; ring

theorem clauseIneq_coef_eq_zero {C : Clause} {i : ℕ} (h : ∀ l ∈ C, l.var ≠ i) :
    (clauseIneq C).coef i = 0 := by
  show (∑ l ∈ C, litCoef l) i = 0
  rw [Finsupp.finset_sum_apply]
  exact Finset.sum_eq_zero fun l hl => by
    unfold litCoef; rw [Finsupp.single_apply, if_neg (h l hl)]

theorem clauseIneq_coef_nonneg {C : Clause} {i : ℕ} (h : ∀ l ∈ C, l.var = i → l.pos = true) :
    0 ≤ (clauseIneq C).coef i := by
  show 0 ≤ (∑ l ∈ C, litCoef l) i
  rw [Finsupp.finset_sum_apply]
  exact Finset.sum_nonneg fun l hl => by
    unfold litCoef; rw [Finsupp.single_apply]
    split_ifs with h1 h2
    · norm_num
    · exact absurd (h l hl h1) h2
    · exact le_refl 0

theorem clauseIneq_support {C : Clause} {S : Finset ℕ} (h : ∀ l ∈ C, l.var ∈ S) :
    (clauseIneq C).coef.support ⊆ S := by
  intro i hi
  by_contra hS
  exact (Finsupp.mem_support_iff.1 hi) (clauseIneq_coef_eq_zero fun l hl he => hS (he ▸ h l hl))

theorem axiom_support_low (i : ℕ) : (lowerAx i).coef.support ⊆ {i} :=
  Finsupp.support_single_subset
theorem axiom_support_up (i : ℕ) : (upperAx i).coef.support ⊆ {i} :=
  Finsupp.support_single_subset

/-! ## Integer ceiling division -/

/-- `⌈x / c⌉` for `c > 0`. -/
def ceilDiv (x : ℤ) (c : ℕ) : ℤ := -((-x) / (c : ℤ))

theorem ceilDiv_le {x y : ℤ} {c : ℕ} (hc : 0 < c) (h : x ≤ c * y) : ceilDiv x c ≤ y := by
  unfold ceilDiv
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  have : -y ≤ (-x) / (c : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hc']; linarith
  linarith

theorem le_ceilDiv {s t : ℤ} {c : ℕ} (hc : 0 < c) (h : (c : ℤ) * (t - 1) < s) :
    t ≤ ceilDiv s c := by
  unfold ceilDiv
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  have : (-s) / (c : ℤ) < -t + 1 := by
    rw [Int.ediv_lt_iff_lt_mul hc']; linarith
  linarith

theorem ceilDiv_add_le {x y : ℤ} {c : ℕ} (hc : 0 < c) :
    ceilDiv (x + y) c ≤ ceilDiv x c + ceilDiv y c := by
  unfold ceilDiv
  have hc' : (0 : ℤ) < c := by exact_mod_cast hc
  have h1 := Int.ediv_mul_le (-x) hc'.ne'
  have h2 := Int.ediv_mul_le (-y) hc'.ne'
  have : (-x) / (c : ℤ) + (-y) / (c : ℤ) ≤ (-(x + y)) / (c : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hc']; linarith
  linarith

/-! ## The bounds `DA`, `DB` -/

section Bounds

variable (A B : CNF) (P Q : Finset ℕ) (L : List Ineq) (a : Assignment)

/-- One step of the bound recursion, reading earlier bounds from `vals`. -/
def stepD (k : ℕ) (vals : ℕ → ℤ × ℤ) : ℤ × ℤ :=
  match ruleAt (A ∪ B) L k with
  | .hyp C => if C ∈ A then ((lineAt L k).rhs - partOn P (lineAt L k) a, 0)
      else (0, (lineAt L k).rhs - partOn P (lineAt L k) a)
  | .low i => if i ∈ Q then ((lineAt L k).rhs, 0)
      else (0, (lineAt L k).rhs - partOn P (lineAt L k) a)
  | .up i => if i ∈ Q then ((lineAt L k).rhs, 0)
      else (0, (lineAt L k).rhs - partOn P (lineAt L k) a)
  | .add i j => vals i + vals j
  | .scale i c => ((c : ℤ) * (vals i).1, (c : ℤ) * (vals i).2)
  | .div i c => (ceilDiv (vals i).1 c, ceilDiv (vals i).2 c)

/-- The bounds `(DA k, DB k)` of line `k` under the assignment `a`. -/
def DD : ℕ → ℤ × ℤ
  | k => stepD A B P Q L a k (fun i => if h : i < k then DD i else 0)
decreasing_by all_goals exact h

theorem DD_eq (k : ℕ) :
    DD A B P Q L a k = stepD A B P Q L a k (fun i => if i < k then DD A B P Q L a i else 0) := by
  rw [DD]
  congr 1

theorem partOn_of_coef {S : Finset ℕ} {I J : Ineq} {c : ℤ} (h : I.coef = c • J.coef) :
    partOn S I a = c * partOn S J a := by
  unfold partOn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h, Finsupp.smul_apply, smul_eq_mul]; ring

theorem lhs_of_coef {I J : Ineq} {c : ℤ} (h : I.coef = c • J.coef) :
    I.lhs a = c * J.lhs a := by
  unfold Ineq.lhs; rw [h]; exact Ineq.lhs_smul a c J.coef

theorem ax_sat_low (i : ℕ) : (lowerAx i).rhs ≤ (lowerAx i).lhs a := by
  unfold Ineq.lhs lowerAx; simp only; rw [lhs_single]
  have := bitZ_nonneg a i; linarith

theorem ax_sat_up (i : ℕ) : (upperAx i).rhs ≤ (upperAx i).lhs a := by
  unfold Ineq.lhs upperAx; simp only; rw [lhs_single]
  have := bitZ_le_one a i; linarith

variable {A B P Q L} in
/-- Axiom lines: either all on the `Q` side (variable in `Q`) or all on the rest. -/
theorem ax_inv {I : Ineq} {i : ℕ} (hsupp : I.coef.support ⊆ {i}) (hsat : I.rhs ≤ I.lhs a)
    (hPQ : Disjoint P Q) :
    let D : ℤ × ℤ := if i ∈ Q then (I.rhs, 0) else (0, I.rhs - partOn P I a)
    I.rhs - partOn P I a ≤ D.1 + D.2 ∧ (D.1 ≤ partOn Q I a) ∧
      (D.2 ≤ I.lhs a - partOn P I a - partOn Q I a) := by
  intro D
  by_cases hi : i ∈ Q
  · have hiP : i ∉ P := Finset.disjoint_right.1 hPQ hi
    have hzP : partOn P I a = 0 := partOn_eq_zero (fun j hj => by
      by_contra hne
      have := hsupp (Finsupp.mem_support_iff.2 hne)
      rw [Finset.mem_singleton] at this; subst this; exact hiP hj) a
    have hQ : I.lhs a = partOn Q I a :=
      lhs_eq_sum_of_support (hsupp.trans (Finset.singleton_subset_iff.2 hi)) a
    simp only [D, if_pos hi]
    refine ⟨by omega, by omega, by omega⟩
  · have hzQ : partOn Q I a = 0 := partOn_eq_zero (fun j hj => by
      by_contra hne
      have := hsupp (Finsupp.mem_support_iff.2 hne)
      rw [Finset.mem_singleton] at this; subst this; exact hi hj) a
    simp only [D, if_neg hi]
    refine ⟨by omega, by omega, by omega⟩

variable {A B P Q L} in
/-- The three invariants of the bounds. -/
theorem DD_inv {R : Finset ℕ} (hL : CPProof (A ∪ B) L)
    (hA : ∀ C ∈ A, ∀ l ∈ C, l.var ∈ P ∪ Q ∧ (l.var ∈ P → l.pos = true))
    (hB : ∀ C ∈ B, ∀ l ∈ C, l.var ∈ P ∪ R)
    (hPQ : Disjoint P Q) (hQR : Disjoint Q R) :
    ∀ k < L.length,
      (lineAt L k).rhs - partOn P (lineAt L k) a ≤ (DD A B P Q L a k).1 + (DD A B P Q L a k).2 ∧
      (cnfSat a A → (DD A B P Q L a k).1 ≤ partOn Q (lineAt L k) a) ∧
      (cnfSat a B → (DD A B P Q L a k).2 ≤
        (lineAt L k).lhs a - partOn P (lineAt L k) a - partOn Q (lineAt L k) a) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  have hv := ruleAt_valid hL hk
  rw [DD_eq]
  unfold stepD
  generalize ruleAt (A ∪ B) L k = r at hv ⊢
  cases r with
  | hyp C =>
      obtain ⟨hC, hI⟩ := hv
      rw [hI]
      by_cases hCA : C ∈ A
      · simp only [if_pos hCA]
        have hsupp : (clauseIneq C).coef.support ⊆ P ∪ Q :=
          clauseIneq_support fun l hl => (hA C hCA l hl).1
        have hsplit : (clauseIneq C).lhs a = partOn P (clauseIneq C) a + partOn Q (clauseIneq C) a := by
          rw [lhs_eq_sum_of_support hsupp, partOn_union hPQ]
        refine ⟨by omega, fun ha => ?_, fun _ => by omega⟩
        have := clauseIneq_sat (ha C hCA)
        unfold Ineq.Sat at this
        omega
      · simp only [if_neg hCA]
        have hCB : C ∈ B := by
          rcases Finset.mem_union.1 hC with h | h
          · exact absurd h hCA
          · exact h
        have hzQ : partOn Q (clauseIneq C) a = 0 := partOn_eq_zero (fun j hj =>
          clauseIneq_coef_eq_zero fun l hl he => by
            have hv := hB C hCB l hl
            rw [he] at hv
            rcases Finset.mem_union.1 hv with h | h
            · exact Finset.disjoint_left.1 hPQ h hj
            · exact Finset.disjoint_left.1 hQR hj h) a
        refine ⟨by omega, fun _ => by omega, fun ha => ?_⟩
        have := clauseIneq_sat (ha C hCB)
        unfold Ineq.Sat at this
        omega
  | low i =>
      rw [hv]
      have := ax_inv a (axiom_support_low i) (ax_sat_low a i) hPQ
      exact ⟨this.1, fun _ => this.2.1, fun _ => this.2.2⟩
  | up i =>
      rw [hv]
      have := ax_inv a (axiom_support_up i) (ax_sat_up a i) hPQ
      exact ⟨this.1, fun _ => this.2.1, fun _ => this.2.2⟩
  | add i j =>
      obtain ⟨hi, hj, hI⟩ := hv
      simp only [if_pos hi, if_pos hj, Prod.fst_add, Prod.snd_add]
      obtain ⟨a1, a2, a3⟩ := ih i hi (by omega)
      obtain ⟨b1, b2, b3⟩ := ih j hj (by omega)
      rw [hI, partOn_add, partOn_add, Ineq.lhs_add]
      have hr : (lineAt L i + lineAt L j).rhs = (lineAt L i).rhs + (lineAt L j).rhs := rfl
      rw [hr]
      refine ⟨by omega, fun ha => ?_, fun hb => ?_⟩
      · have := a2 ha; have := b2 ha; omega
      · have := a3 hb; have := b3 hb; omega
  | scale i c =>
      obtain ⟨hi, hI⟩ := hv
      simp only [if_pos hi]
      obtain ⟨a1, a2, a3⟩ := ih i hi (by omega)
      rw [hI, partOn_scale, partOn_scale, Ineq.lhs_scale]
      have hr : ((lineAt L i).scale c).rhs = (c : ℤ) * (lineAt L i).rhs := rfl
      rw [hr]
      have hc : (0 : ℤ) ≤ c := by positivity
      refine ⟨?_, fun ha => ?_, fun hb => ?_⟩
      · have := mul_le_mul_of_nonneg_left a1 hc; linarith
      · exact mul_le_mul_of_nonneg_left (a2 ha) hc
      · have := mul_le_mul_of_nonneg_left (a3 hb) hc; linarith
  | div i c =>
      obtain ⟨hi, hc, hcoef, hrhs⟩ := hv
      simp only [if_pos hi]
      obtain ⟨a1, a2, a3⟩ := ih i hi (by omega)
      have eP := partOn_of_coef a (S := P) hcoef
      have eQ := partOn_of_coef a (S := Q) hcoef
      have eL := lhs_of_coef a hcoef
      rw [eP] at a1 a3
      rw [eQ] at a2 a3
      rw [eL] at a3
      refine ⟨?_, fun ha => ceilDiv_le hc (a2 ha), fun hb => ceilDiv_le hc ?_⟩
      · refine le_trans (le_ceilDiv hc ?_) (ceilDiv_add_le hc)
        have : (c : ℤ) * ((lineAt L k).rhs - partOn P (lineAt L k) a - 1) =
            (c : ℤ) * ((lineAt L k).rhs - 1) - c * partOn P (lineAt L k) a := by ring
        rw [this]; linarith
      · have := a3 hb
        have e : (c : ℤ) * (lineAt L k).lhs a - c * partOn P (lineAt L k) a -
            c * partOn Q (lineAt L k) a =
            (c : ℤ) * ((lineAt L k).lhs a - partOn P (lineAt L k) a - partOn Q (lineAt L k) a) := by
          ring
        linarith

end Bounds

/-! ## Straight line program values -/

theorem mcVals_append (a : Assignment) (C : List MGate) (g : MGate) :
    mcVals a (C ++ [g]) = mcVals a C ++ [g.val a (mcVals a C)] := by
  unfold mcVals; rw [List.foldl_append]; rfl

theorem mcVals_length (a : Assignment) (C : List MGate) : (mcVals a C).length = C.length := by
  induction C using List.reverseRecOn with
  | nil => rfl
  | append_singleton C g ih => rw [mcVals_append]; simp [ih]

/-- Value of gate `m` of the program `g 0, g 1, ...`. -/
def gateValue (a : Assignment) (g : ℕ → MGate) (m : ℕ) : ℝ :=
  (g m).val a (mcVals a ((List.range m).map g))

theorem mcVals_range_getD (a : Assignment) (g : ℕ → MGate) :
    ∀ n m, m < n → (mcVals a ((List.range n).map g)).getD m 0 = gateValue a g m := by
  intro n
  induction n with
  | zero => intro m hm; omega
  | succ n ih =>
      intro m hm
      rw [List.range_succ, List.map_append, List.map_singleton, mcVals_append]
      have hl : (mcVals a ((List.range n).map g)).length = n := by
        rw [mcVals_length]; simp
      by_cases h : m < n
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD, ih m h]
      · have : m = n := by omega
        subst this
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        simp [hl, gateValue]

/-- Reading an earlier gate from inside gate `m`. -/
theorem read_earlier (a : Assignment) (g : ℕ → MGate) {i m : ℕ} (h : i < m) :
    (mcVals a ((List.range m).map g)).getD i 0 = gateValue a g i :=
  mcVals_range_getD a g m i h

theorem mcEval_range (a : Assignment) (g : ℕ → MGate) (n : ℕ) :
    mcEval a ((List.range (n + 1)).map g) = gateValue a g n := by
  unfold mcEval
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
  rw [mcVals_length]
  simp only [List.length_map, List.length_range, Nat.add_sub_cancel]
  rw [← List.getD_eq_getElem?_getD, mcVals_range_getD a g (n + 1) n (by omega)]

/-! ## The interpolating circuit -/

section Circuit

variable (A B : CNF) (P Q : Finset ℕ) (L : List Ineq)

/-- The `P` variables in increasing order (circuit inputs). -/
def Pl : List ℕ := P.sort (· ≤ ·)

theorem Pl_length : (Pl P).length = P.card := Finset.length_sort _

/-- First gate of the block of line `k`. -/
def bstart (k : ℕ) : ℕ := P.card + k * (P.card + 1)

/-- Gate holding `- DA k`: the last gate of the block of line `k`. -/
def posN (k : ℕ) : ℕ := bstart P k + P.card

/-- Is line `k` an `A` hypothesis? -/
def IsHypA (k : ℕ) : Prop := ∃ C, ruleAt (A ∪ B) L k = .hyp C ∧ C ∈ A

/-- Monotone weight of variable `v` on line `k`. -/
def wt (k v : ℕ) : ℝ := max ((lineAt L k).coef v : ℝ) 0

def firstGate (k : ℕ) : MGate :=
  match ruleAt (A ∪ B) L k with
  | .hyp C => if C ∈ A then .cst (-((lineAt L k).rhs : ℝ)) else .cst 0
  | .low i => if i ∈ Q then .cst (-((lineAt L k).rhs : ℝ)) else .cst 0
  | .up i => if i ∈ Q then .cst (-((lineAt L k).rhs : ℝ)) else .cst 0
  | .add i j => .op (fun x y => x + y) (posN P i) (posN P j)
  | .scale i c => .op (fun x _ => (c : ℝ) * x) (posN P i) (posN P i)
  | .div i c => .op (fun x _ => ((⌊x / (c : ℝ)⌋ : ℤ) : ℝ)) (posN P i) (posN P i)

def chainGate (k t : ℕ) : MGate :=
  if IsHypA A B L k then
    .op (fun x y => x + wt L k ((Pl P).getD t 0) * y) (bstart P k + t) t
  else .op (fun x _ => x) (bstart P k + t) (bstart P k + t)

def finalGate (f : ℕ) : MGate := .op (fun x _ => if 0 ≤ x then 1 else 0) (posN P f) (posN P f)

/-- Gate number `m` of the interpolating circuit. -/
def circGate (f m : ℕ) : MGate :=
  if m < P.card then .inp ((Pl P).getD m 0)
  else if (m - P.card) / (P.card + 1) < L.length then
    (if (m - P.card) % (P.card + 1) = 0 then firstGate A B P Q L ((m - P.card) / (P.card + 1))
     else chainGate A B P L ((m - P.card) / (P.card + 1)) ((m - P.card) % (P.card + 1) - 1))
  else finalGate P f

/-- Number of gates before the output gate. -/
def circLen : ℕ := P.card + L.length * (P.card + 1)

/-- The interpolating circuit for the refutation line `f`. -/
def interpCircuit (f : ℕ) : List MGate :=
  (List.range (circLen P L + 1)).map (circGate A B P Q L f)

theorem circGate_block {f k r : ℕ} (hk : k < L.length) (hr : r ≤ P.card) :
    circGate A B P Q L f (bstart P k + r) =
      if r = 0 then firstGate A B P Q L k else chainGate A B P L k (r - 1) := by
  unfold circGate bstart
  have h1 : ¬ (P.card + k * (P.card + 1) + r < P.card) := by omega
  have e : P.card + k * (P.card + 1) + r - P.card = r + k * (P.card + 1) := by omega
  have hd : (r + k * (P.card + 1)) / (P.card + 1) = k := by
    rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]; simp
  have hm : (r + k * (P.card + 1)) % (P.card + 1) = r := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [if_neg h1, e, hd, hm, if_pos hk]

theorem circGate_final {f : ℕ} : circGate A B P Q L f (circLen P L) = finalGate P f := by
  unfold circGate circLen
  have h1 : ¬ (P.card + L.length * (P.card + 1) < P.card) := by omega
  have e : P.card + L.length * (P.card + 1) - P.card = 0 + L.length * (P.card + 1) := by omega
  have hd : (0 + L.length * (P.card + 1)) / (P.card + 1) = L.length := by
    rw [Nat.add_mul_div_right _ _ (by omega)]; simp
  rw [if_neg h1, e, hd, if_neg (lt_irrefl _)]

theorem circGate_input {f t : ℕ} (ht : t < P.card) :
    circGate A B P Q L f t = .inp ((Pl P).getD t 0) := by
  unfold circGate; rw [if_pos ht]

theorem posN_lt_bstart {i k : ℕ} (h : i < k) : posN P i < bstart P k := by
  unfold posN bstart
  have : i * (P.card + 1) + (P.card + 1) ≤ k * (P.card + 1) := by
    have := Nat.mul_le_mul_right (P.card + 1) (show i + 1 ≤ k by omega)
    simpa [Nat.succ_mul] using this
  omega

end Circuit

/-! ## Values of the interpolating circuit -/

section Values

variable (A B : CNF) (P Q : Finset ℕ) (L : List Ineq) (a : Assignment) (f : ℕ)

/-- 0/1 value of a variable as a real. -/
def bitR (v : ℕ) : ℝ := if a v then 1 else 0

theorem bitR_eq (v : ℕ) : bitR a v = ((bitZ a v : ℤ) : ℝ) := by
  unfold bitR bitZ; split <;> simp

theorem val_input {t : ℕ} (ht : t < P.card) :
    gateValue a (circGate A B P Q L f) t = bitR a ((Pl P).getD t 0) := by
  unfold gateValue; rw [circGate_input A B P Q L ht]; rfl

/-- Along a block the value accumulates the weighted `P` inputs (for `A` hypotheses). -/
theorem val_chain {k : ℕ} (hk : k < L.length) :
    ∀ t ≤ P.card, gateValue a (circGate A B P Q L f) (bstart P k + t) =
      gateValue a (circGate A B P Q L f) (bstart P k) +
        (if IsHypA A B L k then
          (((Pl P).take t).map fun v => wt L k v * bitR a v).sum else 0) := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      have hg := circGate_block A B P Q L (f := f) hk (r := t + 1) ht
      simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at hg
      have hm : bstart P k + (t + 1) = bstart P k + t + 1 := by omega
      have htl : t < (Pl P).length := by rw [Pl_length]; omega
      have htake : (Pl P).take (t + 1) = (Pl P).take t ++ [(Pl P).getD t 0] := by
        rw [List.take_add_one, List.getElem?_eq_getElem htl,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl]
        rfl
      have hbs : t < bstart P k + t + 1 := by unfold bstart; omega
      have hval : gateValue a (circGate A B P Q L f) (bstart P k + (t + 1)) =
          (chainGate A B P L k t).val a
            (mcVals a ((List.range (bstart P k + t + 1)).map (circGate A B P Q L f))) := by
        unfold gateValue; rw [hg, hm]
      have r1 : (mcVals a ((List.range (bstart P k + t + 1)).map (circGate A B P Q L f))).getD
          (bstart P k + t) 0 = gateValue a (circGate A B P Q L f) (bstart P k + t) :=
        read_earlier a _ (by omega)
      rw [hval]
      unfold chainGate
      by_cases hH : IsHypA A B L k
      · have r2 : (mcVals a ((List.range (bstart P k + t + 1)).map (circGate A B P Q L f))).getD
            t 0 = gateValue a (circGate A B P Q L f) t := read_earlier a _ hbs
        rw [if_pos hH]
        simp only [MGate.val]
        rw [r1, r2, hprev, if_pos hH, if_pos hH, val_input A B P Q L a f (t := t) (by omega), htake,
          List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
        ring
      · rw [if_neg hH]
        simp only [MGate.val]
        rw [r1, hprev, if_neg hH, if_neg hH]

/-- `∑` over the sorted `P` list equals the `Finset` sum. -/
theorem sum_Pl (g : ℕ → ℝ) : ((Pl P).map g).sum = ∑ v ∈ P, g v := by
  unfold Pl
  rw [← List.sum_toFinset g (Finset.sort_nodup _ _), Finset.sort_toFinset]

variable {A B P Q L} in
/-- Every block computes `- DA` of its line. -/
theorem val_posN {R : Finset ℕ} (hL : CPProof (A ∪ B) L)
    (hA : ∀ C ∈ A, ∀ l ∈ C, l.var ∈ P ∪ Q ∧ (l.var ∈ P → l.pos = true)) :
    ∀ k < L.length, gateValue a (circGate A B P Q L f) (posN P k) =
      ((-(DD A B P Q L a k).1 : ℤ) : ℝ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  have hchain := val_chain A B P Q L a f hk P.card le_rfl
  have hfirst := circGate_block A B P Q L (f := f) hk (r := 0) (Nat.zero_le _)
  simp only [if_true, Nat.add_zero] at hfirst
  have hv := ruleAt_valid hL hk
  unfold posN
  rw [hchain]
  have hfv : gateValue a (circGate A B P Q L f) (bstart P k) =
      (firstGate A B P Q L k).val a (mcVals a ((List.range (bstart P k)).map
        (circGate A B P Q L f))) := by
    unfold gateValue; rw [hfirst]
  rw [hfv, DD_eq]
  have hlt : ∀ i < k, posN P i < bstart P k := fun i hi => posN_lt_bstart P hi
  unfold firstGate stepD
  unfold IsHypA
  generalize ruleAt (A ∪ B) L k = r at hv ⊢
  cases r with
  | hyp C =>
      obtain ⟨hC, hI⟩ := hv
      by_cases hCA : C ∈ A
      · simp only [if_pos hCA, MGate.val]
        have hH : ∃ C', Rule.hyp C = Rule.hyp C' ∧ C' ∈ A := ⟨C, rfl, hCA⟩
        rw [if_pos hH, List.take_of_length_le (by rw [Pl_length]), sum_Pl]
        have hw : ∀ v ∈ P, wt L k v * bitR a v = ((lineAt L k).coef v * bitZ a v : ℤ) := by
          intro v hv'
          have hnn : 0 ≤ (lineAt L k).coef v := by
            rw [hI]
            exact clauseIneq_coef_nonneg (fun l hl he => (hA C hCA l hl).2 (he ▸ hv'))
          unfold wt
          rw [max_eq_left (by exact_mod_cast hnn), bitR_eq]
          push_cast; ring
        rw [Finset.sum_congr rfl hw]
        unfold partOn
        push_cast; ring
      · simp only [if_neg hCA, MGate.val]
        have hH : ¬ ∃ C', Rule.hyp C = Rule.hyp C' ∧ C' ∈ A := by
          rintro ⟨C', h1, h2⟩; cases h1; exact hCA h2
        rw [if_neg hH]; simp
  | low i =>
      have hH : ¬ ∃ C', Rule.low i = Rule.hyp C' ∧ C' ∈ A := by rintro ⟨C', h1, _⟩; cases h1
      rw [if_neg hH]
      by_cases hi : i ∈ Q
      · simp [if_pos hi, MGate.val]
      · simp [if_neg hi, MGate.val]
  | up i =>
      have hH : ¬ ∃ C', Rule.up i = Rule.hyp C' ∧ C' ∈ A := by rintro ⟨C', h1, _⟩; cases h1
      rw [if_neg hH]
      by_cases hi : i ∈ Q
      · simp [if_pos hi, MGate.val]
      · simp [if_neg hi, MGate.val]
  | add i j =>
      obtain ⟨hi, hj, _⟩ := hv
      have hH : ¬ ∃ C', Rule.add i j = Rule.hyp C' ∧ C' ∈ A := by rintro ⟨C', h1, _⟩; cases h1
      rw [if_neg hH]
      simp only [MGate.val, if_pos hi, if_pos hj, add_zero]
      rw [read_earlier _ _ (hlt i hi), read_earlier _ _ (hlt j hj)]
      have e1 := ih i hi (by omega); have e2 := ih j hj (by omega)
      rw [e1, e2]; simp; ring
  | scale i c =>
      obtain ⟨hi, _⟩ := hv
      have hH : ¬ ∃ C', Rule.scale i c = Rule.hyp C' ∧ C' ∈ A := by rintro ⟨C', h1, _⟩; cases h1
      rw [if_neg hH]
      simp only [MGate.val, if_pos hi, add_zero]
      rw [read_earlier _ _ (hlt i hi)]
      have e1 := ih i hi (by omega)
      rw [e1]; push_cast; ring
  | div i c =>
      obtain ⟨hi, hc, _⟩ := hv
      have hH : ¬ ∃ C', Rule.div i c = Rule.hyp C' ∧ C' ∈ A := by rintro ⟨C', h1, _⟩; cases h1
      rw [if_neg hH]
      simp only [MGate.val, if_pos hi, add_zero]
      rw [read_earlier _ _ (hlt i hi)]
      have e1 := ih i hi (by omega)
      rw [e1, Int.floor_div_natCast, Int.floor_intCast]
      unfold ceilDiv
      push_cast; ring_nf

end Values

/-! ## Monotonicity, inputs, size, and the interpolation theorem -/

section Assemble

variable (A B : CNF) (P Q : Finset ℕ) (L : List Ineq) (f : ℕ)

theorem firstGate_mono (k : ℕ) : (firstGate A B P Q L k).Mono := by
  unfold firstGate
  cases ruleAt (A ∪ B) L k with
  | hyp C => dsimp only; split_ifs <;> trivial
  | low i => dsimp only; split_ifs <;> trivial
  | up i => dsimp only; split_ifs <;> trivial
  | add i j => intro x x' y y' hx hy; linarith
  | scale i c =>
      intro x x' y y' hx _
      exact mul_le_mul_of_nonneg_left hx (by positivity)
  | div i c =>
      intro x x' y y' hx _
      exact Int.cast_le.mpr (Int.floor_le_floor (div_le_div_of_nonneg_right hx (by positivity)))

theorem firstGate_ne_inp (k v : ℕ) : firstGate A B P Q L k ≠ MGate.inp v := by
  unfold firstGate
  cases ruleAt (A ∪ B) L k <;> dsimp only <;> (try split_ifs) <;> simp

theorem chainGate_mono (k t : ℕ) : (chainGate A B P L k t).Mono := by
  unfold chainGate
  split_ifs
  · intro x x' y y' hx hy
    have hw : 0 ≤ wt L k ((Pl P).getD t 0) := le_max_right _ _
    have := mul_le_mul_of_nonneg_left hy hw
    linarith
  · intro x x' y y' hx _; exact hx

theorem interp_mono : MCMono (interpCircuit A B P Q L f) := by
  intro g hg
  obtain ⟨m, _, rfl⟩ := List.mem_map.1 hg
  unfold circGate
  split_ifs
  · trivial
  · exact firstGate_mono A B P Q L _
  · exact chainGate_mono A B P L _ _
  · intro x x' y y' hx _
    simp only
    split_ifs with h1 h2 h2
    · exact le_refl _
    · exact absurd (h1.trans hx) h2
    · norm_num
    · exact le_refl _

theorem interp_inputs : MCInputsIn P (interpCircuit A B P Q L f) := by
  intro v hv
  obtain ⟨m, _, hm⟩ := List.mem_map.1 hv
  unfold circGate at hm
  split_ifs at hm with h1 h2 h3
  · cases hm
    have hl : m < (Pl P).length := by rw [Pl_length]; exact h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
    simp only [Option.getD_some]
    exact (Finset.mem_sort _).1 (List.getElem_mem hl)
  · exact absurd hm (firstGate_ne_inp A B P Q L _ v)
  · unfold chainGate at hm; split_ifs at hm <;> cases hm
  · unfold finalGate at hm; cases hm

theorem interp_length : (interpCircuit A B P Q L f).length = circLen P L + 1 := by
  unfold interpCircuit; simp

variable {A B P Q L f} in
theorem interp_eval {R : Finset ℕ} (hL : CPProof (A ∪ B) L)
    (hA : ∀ C ∈ A, ∀ l ∈ C, l.var ∈ P ∪ Q ∧ (l.var ∈ P → l.pos = true))
    (hf : f < L.length) (a : Assignment) :
    mcEval a (interpCircuit A B P Q L f) =
      if (0 : ℝ) ≤ ((-(DD A B P Q L a f).1 : ℤ) : ℝ) then 1 else 0 := by
  unfold interpCircuit
  rw [mcEval_range]
  unfold gateValue
  rw [circGate_final]
  unfold finalGate
  simp only [MGate.val]
  have hlt : posN P f < circLen P L := by
    have h1 := posN_lt_bstart P (Nat.lt_succ_self f)
    have h2 : (f + 1) * (P.card + 1) ≤ L.length * (P.card + 1) :=
      Nat.mul_le_mul_right _ hf
    unfold bstart at h1; unfold circLen
    simp only [Nat.succ_eq_add_one] at h1
    omega
  rw [read_earlier a _ hlt, val_posN a f (R := R) hL hA f hf]

end Assemble

/-- Monotone feasible interpolation for cutting planes (Pudlák 1997). -/
theorem cp_monotone_interpolation_proof : CPMonotoneInterpolation := by
  refine ⟨(Polynomial.X + 1) ^ 2, ?_⟩
  intro A B P Q R L hA hB hPQ hPR hQR hLr
  obtain ⟨hL, I, hI, h0, hpos⟩ := hLr
  obtain ⟨f, hf, hfI⟩ := List.mem_iff_getElem.1 hI
  have hline : lineAt L f = I := by rw [lineAt_of_lt hf]; simpa using hfI
  refine ⟨interpCircuit A B P Q L f, interp_mono A B P Q L f, interp_inputs A B P Q L f, ?_, ?_⟩
  · rw [interp_length]
    simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    have hP : P.card ≤ (P ∪ Q ∪ R).card :=
      Finset.card_le_card (Finset.subset_union_left.trans Finset.subset_union_left)
    unfold circLen
    set s := L.length
    set v := (P ∪ Q ∪ R).card
    have h1 : s * (P.card + 1) ≤ s * (v + 1) := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  · intro a
    have inv := DD_inv a (R := R) hL hA hB hPQ hQR f hf
    rw [hline] at inv
    have hzP : partOn P I a = 0 := partOn_eq_zero (fun i _ => by rw [h0]; rfl) a
    have hzQ : partOn Q I a = 0 := partOn_eq_zero (fun i _ => by rw [h0]; rfl) a
    have hzL : I.lhs a = 0 := by unfold Ineq.lhs; rw [h0]; simp
    rw [hzP, hzQ, hzL] at inv
    obtain ⟨i1, i2, i3⟩ := inv
    rw [interp_eval (R := R) hL hA hf a]
    constructor
    · intro ha
      have := i2 ha
      rw [if_pos (by exact_mod_cast (show (0 : ℤ) ≤ -(DD A B P Q L a f).1 by omega))]
    · intro hb
      have := i3 hb
      rw [if_neg (by exact_mod_cast (show ¬ (0 : ℤ) ≤ -(DD A B P Q L a f).1 by omega))]

/-- The R3 target from the circuit lower bound alone. -/
theorem cp_superpoly_of_lb (h : MonoRealCliqueLB) : CPCliqueColoringSuperpoly :=
  cp_superpoly_of_interp_lb cp_monotone_interpolation_proof h

end

end SATurday.ProofComplexity
