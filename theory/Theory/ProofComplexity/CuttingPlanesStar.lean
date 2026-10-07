import Theory.ProofComplexity.CuttingPlanesInterp
import Theory.ProofComplexity.RealToBool

/-!
# Interpolation for cutting planes with bounded coefficients (CP*) (Ladder Rung R3)

For CP* refutations (all coefficients and right hand sides at most `M` in absolute
value) the `A` side bounds can be clamped to `[-S_k, S_k + 1]`, `S_k` the absolute
coefficient sum of line `k` over `Q`, with `S_k + 1` meaning "`A` is unsatisfiable".
The resulting monotone real circuit has polynomially many integer values, so
`real_to_bool` turns it into a monotone Boolean circuit (Bonet, Pitassi and Raz 1997).

LOG: R3 CuttingPlanesStar module (clamped interpolation)
-/

namespace SATurday.ProofComplexity

noncomputable section

open Classical

/-- CP* refutation: every line has coefficients and right hand side at most `M`. -/
def CPStarRefutes (M : ℕ) (F : CNF) (L : List Ineq) : Prop :=
  CPRefutes F L ∧ ∀ I ∈ L, (∀ i, |I.coef i| ≤ M) ∧ |I.rhs| ≤ M

/-! ## Clamping -/

/-- Absolute coefficient sum on `Q`. -/
def absQ (Q : Finset ℕ) (I : Ineq) : ℤ := ∑ i ∈ Q, |I.coef i|

theorem absQ_nonneg (Q : Finset ℕ) (I : Ineq) : 0 ≤ absQ Q I :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem partOn_le_absQ (Q : Finset ℕ) (I : Ineq) (a : Assignment) : partOn Q I a ≤ absQ Q I := by
  unfold partOn absQ
  refine Finset.sum_le_sum fun i _ => ?_
  have h0 := bitZ_nonneg a i
  have h1 := bitZ_le_one a i
  rcases le_total 0 (I.coef i) with h | h
  · rw [abs_of_nonneg h]; nlinarith
  · rw [abs_of_nonpos h]; nlinarith

theorem neg_absQ_le_partOn (Q : Finset ℕ) (I : Ineq) (a : Assignment) :
    -absQ Q I ≤ partOn Q I a := by
  unfold partOn absQ
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h0 := bitZ_nonneg a i
  have h1 := bitZ_le_one a i
  rcases le_total 0 (I.coef i) with h | h
  · rw [abs_of_nonneg h]; nlinarith
  · rw [abs_of_nonpos h]; nlinarith

/-- Clamp an `A` bound into `[-S, S + 1]`; `S + 1` means saturated. -/
def clampA (S x : ℤ) : ℤ := if S + 1 ≤ x then S + 1 else max x (-S)

theorem clampA_range {S x : ℤ} (hS : 0 ≤ S) : -S ≤ clampA S x ∧ clampA S x ≤ S + 1 := by
  unfold clampA; split_ifs with h
  · omega
  · constructor <;> [exact le_max_right _ _; exact max_le (by omega) (by omega)]

theorem absQ_add (Q : Finset ℕ) (I J : Ineq) : absQ Q (I + J) ≤ absQ Q I + absQ Q J := by
  unfold absQ
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  show |(I.coef + J.coef) i| ≤ _
  rw [Finsupp.add_apply]; exact abs_add_le _ _

section Bounds

variable (A B : CNF) (P Q : Finset ℕ) (L : List Ineq) (a : Assignment)

/-- Saturation level of line `k`. -/
def SL (k : ℕ) : ℤ := absQ Q (lineAt L k)

/-- One clamped step; `vals` holds earlier `(DA', DB)`. -/
def stepC (k : ℕ) (vals : ℕ → ℤ × ℤ) : ℤ × ℤ :=
  match ruleAt (A ∪ B) L k with
  | .hyp C => if C ∈ A then (clampA (SL Q L k) ((lineAt L k).rhs - partOn P (lineAt L k) a), 0)
      else (0, (lineAt L k).rhs - partOn P (lineAt L k) a)
  | .low i => if i ∈ Q then (clampA (SL Q L k) (lineAt L k).rhs, 0)
      else (0, (lineAt L k).rhs - partOn P (lineAt L k) a)
  | .up i => if i ∈ Q then (clampA (SL Q L k) (lineAt L k).rhs, 0)
      else (0, (lineAt L k).rhs - partOn P (lineAt L k) a)
  | .add i j =>
      if (vals i).1 = SL Q L i + 1 ∨ (vals j).1 = SL Q L j + 1 then
        (SL Q L k + 1, (vals i).2 + (vals j).2)
      else (clampA (SL Q L k) ((vals i).1 + (vals j).1), (vals i).2 + (vals j).2)
  | .scale i c =>
      if (vals i).1 = SL Q L i + 1 then (SL Q L k + 1, (c : ℤ) * (vals i).2)
      else (clampA (SL Q L k) ((c : ℤ) * (vals i).1), (c : ℤ) * (vals i).2)
  | .div i c =>
      if (vals i).1 = SL Q L i + 1 then (SL Q L k + 1, ceilDiv (vals i).2 c)
      else (clampA (SL Q L k) (ceilDiv (vals i).1 c), ceilDiv (vals i).2 c)

/-- Clamped bounds of line `k`. -/
def DC : ℕ → ℤ × ℤ
  | k => stepC A B P Q L a k (fun i => if h : i < k then DC i else 0)
decreasing_by all_goals exact h

theorem DC_eq (k : ℕ) :
    DC A B P Q L a k = stepC A B P Q L a k (fun i => if i < k then DC A B P Q L a i else 0) := by
  rw [DC]
  congr 1

/-- Clamping keeps the invariants of a raw bound. -/
theorem clamp_ok {S x y r pp qp : ℤ} {hA : Prop} (hS : 0 ≤ S) (hqp : qp ≤ S) (hqn : -S ≤ qp)
    (h1 : r - pp ≤ x + y) (h2 : hA → x ≤ qp) :
    (-S ≤ clampA S x ∧ clampA S x ≤ S + 1) ∧
      (clampA S x = S + 1 ∨ r - pp ≤ clampA S x + y) ∧ (hA → clampA S x ≤ qp) := by
  refine ⟨clampA_range hS, ?_, ?_⟩
  · unfold clampA; split_ifs with h
    · left; rfl
    · right; have := le_max_left x (-S); linarith
  · intro ha
    have := h2 ha
    unfold clampA; split_ifs with h
    · omega
    · exact max_le this hqn

variable {A B P Q L} in
/-- Invariants of the clamped bounds. -/
theorem DC_inv {R : Finset ℕ} (hL : CPProof (A ∪ B) L)
    (hA : ∀ C ∈ A, ∀ l ∈ C, l.var ∈ P ∪ Q ∧ (l.var ∈ P → l.pos = true))
    (hB : ∀ C ∈ B, ∀ l ∈ C, l.var ∈ P ∪ R)
    (hPQ : Disjoint P Q) (hQR : Disjoint Q R) :
    ∀ k < L.length,
      (-SL Q L k ≤ (DC A B P Q L a k).1 ∧ (DC A B P Q L a k).1 ≤ SL Q L k + 1) ∧
      ((DC A B P Q L a k).1 = SL Q L k + 1 ∨
        (lineAt L k).rhs - partOn P (lineAt L k) a ≤ (DC A B P Q L a k).1 + (DC A B P Q L a k).2) ∧
      (cnfSat a A → (DC A B P Q L a k).1 ≤ partOn Q (lineAt L k) a) ∧
      (cnfSat a B → (DC A B P Q L a k).2 ≤
        (lineAt L k).lhs a - partOn P (lineAt L k) a - partOn Q (lineAt L k) a) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  have hv := ruleAt_valid hL hk
  have hS : 0 ≤ SL Q L k := absQ_nonneg _ _
  have hqp : partOn Q (lineAt L k) a ≤ SL Q L k := partOn_le_absQ _ _ _
  have hqn : -SL Q L k ≤ partOn Q (lineAt L k) a := neg_absQ_le_partOn _ _ _
  -- a saturated earlier line rules out `A`
  have hsat : ∀ i < k, (DC A B P Q L a i).1 = SL Q L i + 1 → ¬ cnfSat a A := by
    intro i hi he ha
    have := (ih i hi (by omega)).2.2.1 ha
    have := partOn_le_absQ Q (lineAt L i) a
    unfold SL at he; omega
  rw [DC_eq]
  unfold stepC
  generalize ruleAt (A ∪ B) L k = r at hv ⊢
  cases r with
  | hyp C =>
      obtain ⟨hC, hI⟩ := hv
      by_cases hCA : C ∈ A
      · simp only [if_pos hCA]
        have hsupp : (clauseIneq C).coef.support ⊆ P ∪ Q :=
          clauseIneq_support fun l hl => (hA C hCA l hl).1
        have hsplit : (lineAt L k).lhs a =
            partOn P (lineAt L k) a + partOn Q (lineAt L k) a := by
          rw [hI, lhs_eq_sum_of_support hsupp, partOn_union hPQ]
        have hraw2 : cnfSat a A → (lineAt L k).rhs - partOn P (lineAt L k) a ≤
            partOn Q (lineAt L k) a := by
          intro ha
          have := clauseIneq_sat (ha C hCA)
          unfold Ineq.Sat at this
          rw [← hI] at this; omega
        obtain ⟨c1, c2, c3⟩ := clamp_ok (y := 0) (r := (lineAt L k).rhs)
          (pp := partOn P (lineAt L k) a) hS hqp hqn (by simp) hraw2
        exact ⟨c1, c2, c3, fun _ => by omega⟩
      · simp only [if_neg hCA]
        have hCB : C ∈ B := by
          rcases Finset.mem_union.1 hC with h | h
          · exact absurd h hCA
          · exact h
        have hzQ : partOn Q (lineAt L k) a = 0 := by
          rw [hI]
          exact partOn_eq_zero (fun j hj => clauseIneq_coef_eq_zero fun l hl he => by
            have hv := hB C hCB l hl
            rw [he] at hv
            rcases Finset.mem_union.1 hv with h | h
            · exact Finset.disjoint_left.1 hPQ h hj
            · exact Finset.disjoint_left.1 hQR hj h) a
        refine ⟨⟨by omega, by omega⟩, Or.inr (by omega), fun _ => by omega, fun hb => ?_⟩
        have := clauseIneq_sat (hb C hCB)
        unfold Ineq.Sat at this
        rw [← hI] at this; omega
  | low i =>
      rw [hv]
      have hsat' := ax_sat_low a i
      by_cases hiQ : i ∈ Q
      · simp only [if_pos hiQ]
        have hiP : i ∉ P := Finset.disjoint_right.1 hPQ hiQ
        have hzP : partOn P (lowerAx i) a = 0 := partOn_eq_zero (fun j hj => by
          by_contra hne
          have := axiom_support_low i (Finsupp.mem_support_iff.2 hne)
          rw [Finset.mem_singleton] at this; subst this; exact hiP hj) a
        have hQ : (lowerAx i).lhs a = partOn Q (lowerAx i) a :=
          lhs_eq_sum_of_support ((axiom_support_low i).trans (Finset.singleton_subset_iff.2 hiQ)) a
        rw [hv] at hqp hqn
        obtain ⟨c1, c2, c3⟩ := clamp_ok (y := 0) (r := (lowerAx i).rhs) (pp := 0)
          (x := (lowerAx i).rhs) (hA := cnfSat a A) hS hqp hqn (by omega) (fun _ => by omega)
        rw [hzP]
        exact ⟨c1, by simpa using c2, c3, fun _ => by omega⟩
      · simp only [if_neg hiQ]
        have hzQ : partOn Q (lowerAx i) a = 0 := partOn_eq_zero (fun j hj => by
          by_contra hne
          have := axiom_support_low i (Finsupp.mem_support_iff.2 hne)
          rw [Finset.mem_singleton] at this; subst this; exact hiQ hj) a
        exact ⟨⟨by omega, by omega⟩, Or.inr (by omega), fun _ => by omega, fun _ => by omega⟩
  | up i =>
      rw [hv]
      have hsat' := ax_sat_up a i
      by_cases hiQ : i ∈ Q
      · simp only [if_pos hiQ]
        have hiP : i ∉ P := Finset.disjoint_right.1 hPQ hiQ
        have hzP : partOn P (upperAx i) a = 0 := partOn_eq_zero (fun j hj => by
          by_contra hne
          have := axiom_support_up i (Finsupp.mem_support_iff.2 hne)
          rw [Finset.mem_singleton] at this; subst this; exact hiP hj) a
        have hQ : (upperAx i).lhs a = partOn Q (upperAx i) a :=
          lhs_eq_sum_of_support ((axiom_support_up i).trans (Finset.singleton_subset_iff.2 hiQ)) a
        rw [hv] at hqp hqn
        obtain ⟨c1, c2, c3⟩ := clamp_ok (y := 0) (r := (upperAx i).rhs) (pp := 0)
          (x := (upperAx i).rhs) (hA := cnfSat a A) hS hqp hqn (by omega) (fun _ => by omega)
        rw [hzP]
        exact ⟨c1, by simpa using c2, c3, fun _ => by omega⟩
      · simp only [if_neg hiQ]
        have hzQ : partOn Q (upperAx i) a = 0 := partOn_eq_zero (fun j hj => by
          by_contra hne
          have := axiom_support_up i (Finsupp.mem_support_iff.2 hne)
          rw [Finset.mem_singleton] at this; subst this; exact hiQ hj) a
        exact ⟨⟨by omega, by omega⟩, Or.inr (by omega), fun _ => by omega, fun _ => by omega⟩
  | add i j =>
      obtain ⟨hi, hj, hI⟩ := hv
      simp only [if_pos hi, if_pos hj]
      obtain ⟨a0, a1, a2, a3⟩ := ih i hi (by omega)
      obtain ⟨b0, b1, b2, b3⟩ := ih j hj (by omega)
      have e3 : cnfSat a B → (DC A B P Q L a i).2 + (DC A B P Q L a j).2 ≤
          (lineAt L k).lhs a - partOn P (lineAt L k) a - partOn Q (lineAt L k) a := by
        intro hb
        rw [hI, Ineq.lhs_add, partOn_add, partOn_add]
        have := a3 hb; have := b3 hb; omega
      split_ifs with hs
      · refine ⟨⟨by omega, le_rfl⟩, Or.inl rfl, fun ha => ?_, e3⟩
        rcases hs with hs | hs
        · exact absurd ha (hsat i hi hs)
        · exact absurd ha (hsat j hj hs)
      · push_neg at hs
        have a1' := a1.resolve_left hs.1
        have b1' := b1.resolve_left hs.2
        have hraw1 : (lineAt L k).rhs - partOn P (lineAt L k) a ≤
            ((DC A B P Q L a i).1 + (DC A B P Q L a j).1) +
              ((DC A B P Q L a i).2 + (DC A B P Q L a j).2) := by
          rw [hI, partOn_add]
          have hr : (lineAt L i + lineAt L j).rhs = (lineAt L i).rhs + (lineAt L j).rhs := rfl
          rw [hr]; omega
        have hraw2 : cnfSat a A → (DC A B P Q L a i).1 + (DC A B P Q L a j).1 ≤
            partOn Q (lineAt L k) a := by
          intro ha
          rw [hI, partOn_add]
          have := a2 ha; have := b2 ha; omega
        obtain ⟨c1, c2, c3⟩ := clamp_ok hS hqp hqn hraw1 hraw2
        exact ⟨c1, c2, c3, e3⟩
  | scale i c =>
      obtain ⟨hi, hI⟩ := hv
      simp only [if_pos hi]
      obtain ⟨a0, a1, a2, a3⟩ := ih i hi (by omega)
      have hc : (0 : ℤ) ≤ c := by positivity
      have e3 : cnfSat a B → (c : ℤ) * (DC A B P Q L a i).2 ≤
          (lineAt L k).lhs a - partOn P (lineAt L k) a - partOn Q (lineAt L k) a := by
        intro hb
        rw [hI, Ineq.lhs_scale, partOn_scale, partOn_scale]
        have := mul_le_mul_of_nonneg_left (a3 hb) hc; linarith
      split_ifs with hs
      · exact ⟨⟨by omega, le_rfl⟩, Or.inl rfl, fun ha => absurd ha (hsat i hi hs), e3⟩
      · have a1' := a1.resolve_left hs
        have hraw1 : (lineAt L k).rhs - partOn P (lineAt L k) a ≤
            (c : ℤ) * (DC A B P Q L a i).1 + (c : ℤ) * (DC A B P Q L a i).2 := by
          rw [hI, partOn_scale]
          have hr : ((lineAt L i).scale c).rhs = (c : ℤ) * (lineAt L i).rhs := rfl
          rw [hr]
          have := mul_le_mul_of_nonneg_left a1' hc; linarith
        have hraw2 : cnfSat a A → (c : ℤ) * (DC A B P Q L a i).1 ≤ partOn Q (lineAt L k) a := by
          intro ha
          rw [hI, partOn_scale]
          exact mul_le_mul_of_nonneg_left (a2 ha) hc
        obtain ⟨c1, c2, c3⟩ := clamp_ok hS hqp hqn hraw1 hraw2
        exact ⟨c1, c2, c3, e3⟩
  | div i c =>
      obtain ⟨hi, hc, hcoef, hrhs⟩ := hv
      simp only [if_pos hi]
      obtain ⟨a0, a1, a2, a3⟩ := ih i hi (by omega)
      have eP := partOn_of_coef a (S := P) hcoef
      have eQ := partOn_of_coef a (S := Q) hcoef
      have eL := lhs_of_coef a hcoef
      have e3 : cnfSat a B → ceilDiv (DC A B P Q L a i).2 c ≤
          (lineAt L k).lhs a - partOn P (lineAt L k) a - partOn Q (lineAt L k) a := by
        intro hb
        refine ceilDiv_le hc ?_
        have := a3 hb
        rw [eP, eQ, eL] at this
        have e : (c : ℤ) * (lineAt L k).lhs a - c * partOn P (lineAt L k) a -
            c * partOn Q (lineAt L k) a =
            (c : ℤ) * ((lineAt L k).lhs a - partOn P (lineAt L k) a - partOn Q (lineAt L k) a) := by
          ring
        linarith
      split_ifs with hs
      · exact ⟨⟨by omega, le_rfl⟩, Or.inl rfl, fun ha => absurd ha (hsat i hi hs), e3⟩
      · have a1' := a1.resolve_left hs
        rw [eP] at a1'
        have hraw1 : (lineAt L k).rhs - partOn P (lineAt L k) a ≤
            ceilDiv (DC A B P Q L a i).1 c + ceilDiv (DC A B P Q L a i).2 c := by
          refine le_trans (le_ceilDiv hc ?_) (ceilDiv_add_le hc)
          have : (c : ℤ) * ((lineAt L k).rhs - partOn P (lineAt L k) a - 1) =
              (c : ℤ) * ((lineAt L k).rhs - 1) - c * partOn P (lineAt L k) a := by ring
          rw [this]; linarith
        have hraw2 : cnfSat a A → ceilDiv (DC A B P Q L a i).1 c ≤ partOn Q (lineAt L k) a := by
          intro ha
          refine ceilDiv_le hc ?_
          have := a2 ha; rw [eQ] at this; exact this
        obtain ⟨c1, c2, c3⟩ := clamp_ok hS hqp hqn hraw1 hraw2
        exact ⟨c1, c2, c3, e3⟩

end Bounds

/-! ## Clamping on circuit values (`V = - DA`) -/

/-- Real clamp of `V = - DA` into `[-(S+1), S]`. -/
def cV (S : ℤ) (x : ℝ) : ℝ := if x ≤ -((S : ℝ) + 1) then -((S : ℝ) + 1) else min x S

theorem cV_mono {S : ℤ} (hS : 0 ≤ S) {x y : ℝ} (h : x ≤ y) : cV S x ≤ cV S y := by
  unfold cV
  have hS' : (0 : ℝ) ≤ S := by exact_mod_cast hS
  split_ifs with h1 h2 h2
  · exact le_rfl
  · push_neg at h2
    exact le_min h2.le (by linarith)
  · linarith
  · exact min_le_min h le_rfl

theorem cV_ge (S : ℤ) (hS : 0 ≤ S) (x : ℝ) : -((S : ℝ) + 1) ≤ cV S x := by
  unfold cV
  have hS' : (0 : ℝ) ≤ S := by exact_mod_cast hS
  split_ifs with h
  · exact le_rfl
  · push_neg at h
    exact le_min h.le (by linarith)

theorem cV_le (S : ℤ) (hS : 0 ≤ S) (x : ℝ) : cV S x ≤ S := by
  unfold cV
  have hS' : (0 : ℝ) ≤ S := by exact_mod_cast hS
  split_ifs
  · linarith
  · exact min_le_right _ _

theorem cV_neg_int {S : ℤ} (hS : 0 ≤ S) (z : ℤ) : cV S (-(z : ℝ)) = ((-clampA S z : ℤ) : ℝ) := by
  unfold cV clampA
  by_cases h : S + 1 ≤ z
  · have h' : -(z : ℝ) ≤ -((S : ℝ) + 1) := by
      have : ((S + 1 : ℤ) : ℝ) ≤ z := by exact_mod_cast h
      push_cast at this; linarith
    rw [if_pos h', if_pos h]; push_cast; ring
  · have hz : (z : ℝ) < S + 1 := by
      have : (z : ℝ) < ((S + 1 : ℤ) : ℝ) := by exact_mod_cast (lt_of_not_ge h)
      push_cast at this; linarith
    rw [if_neg (by linarith), if_neg h]
    rcases le_total z (-S) with h2 | h2
    · rw [max_eq_right h2]
      have : (z : ℝ) ≤ -S := by exact_mod_cast h2
      push_cast; rw [min_eq_right (by linarith)]; ring
    · rw [max_eq_left h2]
      have : (-S : ℝ) ≤ z := by exact_mod_cast h2
      push_cast; rw [min_eq_left (by linarith)]

/-! ## The clamped circuit (same layout as `interpCircuit`) -/

section CircuitC

variable (A B : CNF) (P Q : Finset ℕ) (L : List Ineq)

/-- Saturation level as a real. -/
def SR (k : ℕ) : ℝ := (SL Q L k : ℝ)

def firstGateC (k : ℕ) : MGate :=
  match ruleAt (A ∪ B) L k with
  | .hyp C => if C ∈ A then .cst (-((lineAt L k).rhs : ℝ)) else .cst 0
  | .low i => if i ∈ Q then .cst ((-clampA (SL Q L k) (lineAt L k).rhs : ℤ) : ℝ) else .cst 0
  | .up i => if i ∈ Q then .cst ((-clampA (SL Q L k) (lineAt L k).rhs : ℤ) : ℝ) else .cst 0
  | .add i j => .op (fun x y =>
      if cV (SL Q L i) x ≤ -(SR Q L i + 1) ∨ cV (SL Q L j) y ≤ -(SR Q L j + 1) then
        -(SR Q L k + 1)
      else cV (SL Q L k) (cV (SL Q L i) x + cV (SL Q L j) y)) (posN P i) (posN P j)
  | .scale i c => .op (fun x _ =>
      if cV (SL Q L i) x ≤ -(SR Q L i + 1) then -(SR Q L k + 1)
      else cV (SL Q L k) ((c : ℝ) * cV (SL Q L i) x)) (posN P i) (posN P i)
  | .div i c => .op (fun x _ =>
      if cV (SL Q L i) x ≤ -(SR Q L i + 1) then -(SR Q L k + 1)
      else cV (SL Q L k) ((⌊cV (SL Q L i) x / (c : ℝ)⌋ : ℤ) : ℝ)) (posN P i) (posN P i)

def finalGateC (f : ℕ) : MGate :=
  .op (fun x _ => if 0 ≤ cV (SL Q L f) x then 1 else 0) (posN P f) (posN P f)

def circGateC (f m : ℕ) : MGate :=
  if m < P.card then .inp ((Pl P).getD m 0)
  else if (m - P.card) / (P.card + 1) < L.length then
    (if (m - P.card) % (P.card + 1) = 0 then firstGateC A B P Q L ((m - P.card) / (P.card + 1))
     else chainGate A B P L ((m - P.card) / (P.card + 1)) ((m - P.card) % (P.card + 1) - 1))
  else finalGateC P Q L f

theorem circGateC_block {f k r : ℕ} (hk : k < L.length) (hr : r ≤ P.card) :
    circGateC A B P Q L f (bstart P k + r) =
      if r = 0 then firstGateC A B P Q L k else chainGate A B P L k (r - 1) := by
  unfold circGateC bstart
  have h1 : ¬ (P.card + k * (P.card + 1) + r < P.card) := by omega
  have e : P.card + k * (P.card + 1) + r - P.card = r + k * (P.card + 1) := by omega
  have hd : (r + k * (P.card + 1)) / (P.card + 1) = k := by
    rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]; simp
  have hm : (r + k * (P.card + 1)) % (P.card + 1) = r := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [if_neg h1, e, hd, hm, if_pos hk]

theorem circGateC_final {f : ℕ} : circGateC A B P Q L f (circLen P L) = finalGateC P Q L f := by
  unfold circGateC circLen
  have h1 : ¬ (P.card + L.length * (P.card + 1) < P.card) := by omega
  have e : P.card + L.length * (P.card + 1) - P.card = 0 + L.length * (P.card + 1) := by omega
  have hd : (0 + L.length * (P.card + 1)) / (P.card + 1) = L.length := by
    rw [Nat.add_mul_div_right _ _ (by omega)]; simp
  rw [if_neg h1, e, hd, if_neg (lt_irrefl _)]

theorem circGateC_input {f t : ℕ} (ht : t < P.card) :
    circGateC A B P Q L f t = .inp ((Pl P).getD t 0) := by
  unfold circGateC; rw [if_pos ht]

variable (a : Assignment) (f : ℕ)

theorem val_inputC {t : ℕ} (ht : t < P.card) :
    gateValue a (circGateC A B P Q L f) t = bitR a ((Pl P).getD t 0) := by
  unfold gateValue; rw [circGateC_input A B P Q L ht]; rfl

theorem val_chainC {k : ℕ} (hk : k < L.length) :
    ∀ t ≤ P.card, gateValue a (circGateC A B P Q L f) (bstart P k + t) =
      gateValue a (circGateC A B P Q L f) (bstart P k) +
        (if IsHypA A B L k then
          (((Pl P).take t).map fun v => wt L k v * bitR a v).sum else 0) := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      have hg := circGateC_block A B P Q L (f := f) hk (r := t + 1) ht
      simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at hg
      have hm : bstart P k + (t + 1) = bstart P k + t + 1 := by omega
      have htl : t < (Pl P).length := by rw [Pl_length]; omega
      have htake : (Pl P).take (t + 1) = (Pl P).take t ++ [(Pl P).getD t 0] := by
        rw [List.take_add_one, List.getElem?_eq_getElem htl,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl]
        rfl
      have hbs : t < bstart P k + t + 1 := by unfold bstart; omega
      have hval : gateValue a (circGateC A B P Q L f) (bstart P k + (t + 1)) =
          (chainGate A B P L k t).val a
            (mcVals a ((List.range (bstart P k + t + 1)).map (circGateC A B P Q L f))) := by
        unfold gateValue; rw [hg, hm]
      have r1 : (mcVals a ((List.range (bstart P k + t + 1)).map (circGateC A B P Q L f))).getD
          (bstart P k + t) 0 = gateValue a (circGateC A B P Q L f) (bstart P k + t) :=
        read_earlier a _ (by omega)
      rw [hval]
      unfold chainGate
      by_cases hH : IsHypA A B L k
      · have r2 : (mcVals a ((List.range (bstart P k + t + 1)).map (circGateC A B P Q L f))).getD
            t 0 = gateValue a (circGateC A B P Q L f) t := read_earlier a _ hbs
        rw [if_pos hH]
        simp only [MGate.val]
        rw [r1, r2, hprev, if_pos hH, if_pos hH, val_inputC A B P Q L a f (t := t) (by omega),
          htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
        ring
      · rw [if_neg hH]
        simp only [MGate.val]
        rw [r1, hprev, if_neg hH, if_neg hH]

end CircuitC

section ValuesC

variable (A B : CNF) (P Q : Finset ℕ) (L : List Ineq) (a : Assignment) (f : ℕ)

theorem clampA_idem {S : ℤ} (hS : 0 ≤ S) (x : ℤ) : clampA S (clampA S x) = clampA S x := by
  obtain ⟨h1, h2⟩ := clampA_range (x := x) hS
  unfold clampA at *
  split_ifs at * <;> omega

theorem clampA_zero {S : ℤ} (hS : 0 ≤ S) : clampA S 0 = 0 := by
  unfold clampA; split_ifs <;> omega

theorem clampA_top {S : ℤ} : clampA S (S + 1) = S + 1 := by
  unfold clampA; rw [if_pos le_rfl]

theorem cV_zero {S : ℤ} (hS : 0 ≤ S) : cV S 0 = 0 := by
  have := cV_neg_int hS 0
  simp only [Int.cast_zero, neg_zero] at this
  rw [this, clampA_zero hS]; simp

theorem SL_nonneg (k : ℕ) : 0 ≤ SL Q L k := absQ_nonneg _ _

variable {A B P Q L} in
/-- Each block computes `- DA'` after clamping. -/
theorem val_posNC {R : Finset ℕ} (hL : CPProof (A ∪ B) L)
    (hA : ∀ C ∈ A, ∀ l ∈ C, l.var ∈ P ∪ Q ∧ (l.var ∈ P → l.pos = true))
    (hB : ∀ C ∈ B, ∀ l ∈ C, l.var ∈ P ∪ R) (hPQ : Disjoint P Q) (hQR : Disjoint Q R) :
    ∀ k < L.length, cV (SL Q L k) (gateValue a (circGateC A B P Q L f) (posN P k)) =
      ((-(DC A B P Q L a k).1 : ℤ) : ℝ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  have hS := SL_nonneg Q L k
  have hchain := val_chainC A B P Q L a f hk P.card le_rfl
  have hfirst := circGateC_block A B P Q L (f := f) hk (r := 0) (Nat.zero_le _)
  simp only [if_true, Nat.add_zero] at hfirst
  have hv := ruleAt_valid hL hk
  unfold posN
  rw [hchain]
  have hfv : gateValue a (circGateC A B P Q L f) (bstart P k) =
      (firstGateC A B P Q L k).val a (mcVals a ((List.range (bstart P k)).map
        (circGateC A B P Q L f))) := by
    unfold gateValue; rw [hfirst]
  rw [hfv, DC_eq]
  have hlt : ∀ i < k, posN P i < bstart P k := fun i hi => posN_lt_bstart P hi
  -- children: saturation test and value
  have hchild : ∀ i < k, cV (SL Q L i) ((mcVals a ((List.range (bstart P k)).map
      (circGateC A B P Q L f))).getD (posN P i) 0) = ((-(DC A B P Q L a i).1 : ℤ) : ℝ) := by
    intro i hi
    rw [read_earlier a _ (hlt i hi)]
    exact ih i hi (by omega)
  have hsatiff : ∀ i < k, ((-(DC A B P Q L a i).1 : ℤ) : ℝ) ≤ -(SR Q L i + 1) ↔
      (DC A B P Q L a i).1 = SL Q L i + 1 := by
    intro i hi
    have hr := (DC_inv a (R := R) hL hA hB hPQ hQR i (by omega)).1
    unfold SR
    constructor
    · intro h
      have : ((-(DC A B P Q L a i).1 : ℤ) : ℝ) ≤ ((-(SL Q L i + 1) : ℤ) : ℝ) := by
        push_cast at h ⊢; linarith
      have := Int.cast_le.1 this
      omega
    · intro h; rw [h]; push_cast; linarith
  unfold firstGateC stepC
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
        have e : -((lineAt L k).rhs : ℝ) + ∑ v ∈ P, (((lineAt L k).coef v * bitZ a v : ℤ) : ℝ) =
            -(((lineAt L k).rhs - partOn P (lineAt L k) a : ℤ) : ℝ) := by
          unfold partOn; push_cast; ring
        rw [e, cV_neg_int hS]
      · simp only [if_neg hCA, MGate.val]
        have hH : ¬ ∃ C', Rule.hyp C = Rule.hyp C' ∧ C' ∈ A := by
          rintro ⟨C', h1, h2⟩; cases h1; exact hCA h2
        rw [if_neg hH, add_zero, cV_zero hS]; simp
  | low i =>
      have hH : ¬ ∃ C', Rule.low i = Rule.hyp C' ∧ C' ∈ A := by rintro ⟨C', h1, _⟩; cases h1
      rw [if_neg hH, add_zero]
      by_cases hi : i ∈ Q
      · simp only [if_pos hi, MGate.val]
        rw [show ((-clampA (SL Q L k) (lineAt L k).rhs : ℤ) : ℝ) =
            -((clampA (SL Q L k) (lineAt L k).rhs : ℤ) : ℝ) by push_cast; ring,
          cV_neg_int hS, clampA_idem hS]
        push_cast; ring
      · simp only [if_neg hi, MGate.val]; rw [cV_zero hS]; simp
  | up i =>
      have hH : ¬ ∃ C', Rule.up i = Rule.hyp C' ∧ C' ∈ A := by rintro ⟨C', h1, _⟩; cases h1
      rw [if_neg hH, add_zero]
      by_cases hi : i ∈ Q
      · simp only [if_pos hi, MGate.val]
        rw [show ((-clampA (SL Q L k) (lineAt L k).rhs : ℤ) : ℝ) =
            -((clampA (SL Q L k) (lineAt L k).rhs : ℤ) : ℝ) by push_cast; ring,
          cV_neg_int hS, clampA_idem hS]
        push_cast; ring
      · simp only [if_neg hi, MGate.val]; rw [cV_zero hS]; simp
  | add i j =>
      obtain ⟨hi, hj, _⟩ := hv
      have hH : ¬ ∃ C', Rule.add i j = Rule.hyp C' ∧ C' ∈ A := by rintro ⟨C', h1, _⟩; cases h1
      rw [if_neg hH, add_zero]
      simp only [MGate.val, if_pos hi, if_pos hj]
      rw [hchild i hi, hchild j hj]
      simp only [hsatiff i hi, hsatiff j hj]
      split_ifs with hs
      · rw [show -(SR Q L k + 1) = -((SL Q L k + 1 : ℤ) : ℝ) by unfold SR; push_cast; ring,
          cV_neg_int hS, clampA_top]
      · rw [show ((-(DC A B P Q L a i).1 : ℤ) : ℝ) + ((-(DC A B P Q L a j).1 : ℤ) : ℝ) =
            -(((DC A B P Q L a i).1 + (DC A B P Q L a j).1 : ℤ) : ℝ) by push_cast; ring,
          cV_neg_int hS, show ((-clampA (SL Q L k) ((DC A B P Q L a i).1 +
            (DC A B P Q L a j).1) : ℤ) : ℝ) = -((clampA (SL Q L k) ((DC A B P Q L a i).1 +
            (DC A B P Q L a j).1) : ℤ) : ℝ) by push_cast; ring, cV_neg_int hS, clampA_idem hS]
        push_cast; ring
  | scale i c =>
      obtain ⟨hi, _⟩ := hv
      have hH : ¬ ∃ C', Rule.scale i c = Rule.hyp C' ∧ C' ∈ A := by rintro ⟨C', h1, _⟩; cases h1
      rw [if_neg hH, add_zero]
      simp only [MGate.val, if_pos hi]
      rw [hchild i hi]
      simp only [hsatiff i hi]
      split_ifs with hs
      · rw [show -(SR Q L k + 1) = -((SL Q L k + 1 : ℤ) : ℝ) by unfold SR; push_cast; ring,
          cV_neg_int hS, clampA_top]
      · rw [show (c : ℝ) * ((-(DC A B P Q L a i).1 : ℤ) : ℝ) =
            -(((c : ℤ) * (DC A B P Q L a i).1 : ℤ) : ℝ) by push_cast; ring,
          cV_neg_int hS, show ((-clampA (SL Q L k) ((c : ℤ) * (DC A B P Q L a i).1) : ℤ) : ℝ) =
            -((clampA (SL Q L k) ((c : ℤ) * (DC A B P Q L a i).1) : ℤ) : ℝ) by push_cast; ring,
          cV_neg_int hS, clampA_idem hS]
        push_cast; ring
  | div i c =>
      obtain ⟨hi, hc, _⟩ := hv
      have hH : ¬ ∃ C', Rule.div i c = Rule.hyp C' ∧ C' ∈ A := by rintro ⟨C', h1, _⟩; cases h1
      rw [if_neg hH, add_zero]
      simp only [MGate.val, if_pos hi]
      rw [hchild i hi]
      simp only [hsatiff i hi]
      split_ifs with hs
      · rw [show -(SR Q L k + 1) = -((SL Q L k + 1 : ℤ) : ℝ) by unfold SR; push_cast; ring,
          cV_neg_int hS, clampA_top]
      · rw [Int.floor_div_natCast, Int.floor_intCast]
        rw [show (((-(DC A B P Q L a i).1) / (c : ℤ) : ℤ) : ℝ) =
            -((ceilDiv (DC A B P Q L a i).1 c : ℤ) : ℝ) by unfold ceilDiv; push_cast; ring,
          cV_neg_int hS, show ((-clampA (SL Q L k) (ceilDiv (DC A B P Q L a i).1 c) : ℤ) : ℝ) =
            -((clampA (SL Q L k) (ceilDiv (DC A B P Q L a i).1 c) : ℤ) : ℝ) by push_cast; ring,
          cV_neg_int hS, clampA_idem hS]
        push_cast; ring

end ValuesC

section MonoC

variable (A B : CNF) (P Q : Finset ℕ) (L : List Ineq)

theorem satIf_mono {S Si Sj : ℤ} (hS : 0 ≤ S) (hSi : 0 ≤ Si) (hSj : 0 ≤ Sj)
    {g : ℝ → ℝ → ℝ} (hg : ∀ x x' y y', x ≤ x' → y ≤ y' → g x y ≤ g x' y') :
    ∀ x x' y y' : ℝ, x ≤ x' → y ≤ y' →
      (if cV Si x ≤ -((Si : ℝ) + 1) ∨ cV Sj y ≤ -((Sj : ℝ) + 1) then -((S : ℝ) + 1)
        else cV S (g (cV Si x) (cV Sj y))) ≤
      (if cV Si x' ≤ -((Si : ℝ) + 1) ∨ cV Sj y' ≤ -((Sj : ℝ) + 1) then -((S : ℝ) + 1)
        else cV S (g (cV Si x') (cV Sj y'))) := by
  intro x x' y y' hx hy
  have mx := cV_mono hSi hx
  have my := cV_mono hSj hy
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact cV_ge S hS _
  · exfalso
    rcases h2 with h2 | h2
    · exact h1 (Or.inl (mx.trans h2))
    · exact h1 (Or.inr (my.trans h2))
  · exact cV_mono hS (hg _ _ _ _ mx my)

theorem firstGateC_mono (k : ℕ) : (firstGateC A B P Q L k).Mono := by
  have hk := SL_nonneg Q L k
  unfold firstGateC
  cases ruleAt (A ∪ B) L k with
  | hyp C => dsimp only; split_ifs <;> trivial
  | low i => dsimp only; split_ifs <;> trivial
  | up i => dsimp only; split_ifs <;> trivial
  | add i j =>
      intro x x' y y' hx hy
      unfold SR
      exact satIf_mono hk (SL_nonneg Q L i) (SL_nonneg Q L j) (g := fun u v => u + v)
        (fun _ _ _ _ h1 h2 => add_le_add h1 h2) x x' y y' hx hy
  | scale i c =>
      intro x x' y y' hx _
      unfold SR
      have := satIf_mono hk (SL_nonneg Q L i) (SL_nonneg Q L i) (g := fun u _ => (c : ℝ) * u)
        (fun _ _ _ _ h1 _ => mul_le_mul_of_nonneg_left h1 (by positivity)) x x' x x' hx hx
      simpa only [or_self] using this
  | div i c =>
      intro x x' y y' hx _
      unfold SR
      have := satIf_mono hk (SL_nonneg Q L i) (SL_nonneg Q L i)
        (g := fun u _ => ((⌊u / (c : ℝ)⌋ : ℤ) : ℝ))
        (fun _ _ _ _ h1 _ => Int.cast_le.mpr (Int.floor_le_floor
          (div_le_div_of_nonneg_right h1 (by positivity)))) x x' x x' hx hx
      simpa only [or_self] using this

theorem finalGateC_mono (f : ℕ) : (finalGateC P Q L f).Mono := by
  intro x x' y y' hx _
  have := cV_mono (SL_nonneg Q L f) hx
  simp only
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h1.trans this) h2
  · norm_num
  · exact le_rfl

theorem circGateC_mono (f m : ℕ) : (circGateC A B P Q L f m).Mono := by
  unfold circGateC
  split_ifs
  · trivial
  · exact firstGateC_mono A B P Q L _
  · exact chainGate_mono A B P L _ _
  · exact finalGateC_mono P Q L f

end MonoC

section Bdd

variable (A B : CNF) (P Q : Finset ℕ) (L : List Ineq) (a : Assignment) (f : ℕ)

/-- Integer value of absolute value at most `R`. -/
def IntB (R : ℤ) (x : ℝ) : Prop := ∃ z : ℤ, x = z ∧ |z| ≤ R

theorem cV_intB {S : ℤ} (hS : 0 ≤ S) {R : ℤ} (hR : S + 1 ≤ R) (z : ℤ) :
    IntB R (cV S (z : ℝ)) := by
  have h := cV_neg_int hS (-z)
  rw [Int.cast_neg, neg_neg] at h
  refine ⟨-clampA S (-z), h, ?_⟩
  obtain ⟨h1, h2⟩ := clampA_range (x := -z) hS
  rw [abs_le]; constructor <;> omega

theorem lineAt_bound {M : ℕ} (hM : ∀ I ∈ L, (∀ i, |I.coef i| ≤ M) ∧ |I.rhs| ≤ M) (k : ℕ) :
    (∀ i, |(lineAt L k).coef i| ≤ M) ∧ |(lineAt L k).rhs| ≤ M := by
  by_cases hk : k < L.length
  · rw [lineAt_of_lt hk]; exact hM _ (List.get_mem _ _)
  · have : lineAt L k = zeroIneq := by
      unfold lineAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hk)]; rfl
    rw [this]; simp [zeroIneq]

theorem SL_le {M : ℕ} (hM : ∀ I ∈ L, (∀ i, |I.coef i| ≤ M) ∧ |I.rhs| ≤ M) (k : ℕ) :
    SL Q L k ≤ M * Q.card := by
  unfold SL absQ
  calc ∑ i ∈ Q, |(lineAt L k).coef i| ≤ ∑ _i ∈ Q, (M : ℤ) :=
        Finset.sum_le_sum fun i _ => (lineAt_bound L hM k).1 i
    _ = M * Q.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem read_intB {g : ℕ → MGate} {R : ℤ} (hR : 0 ≤ R) {m : ℕ}
    (ih : ∀ m' < m, IntB R (gateValue a g m')) (i : ℕ) :
    IntB R ((mcVals a ((List.range m).map g)).getD i 0) := by
  rw [read_val g a m i]
  split_ifs with h
  · exact ih i h
  · exact ⟨0, by simp, by simpa using hR⟩

variable {A B P Q L} in
theorem vals_bdd {M : ℕ} (hM : ∀ I ∈ L, (∀ i, |I.coef i| ≤ M) ∧ |I.rhs| ≤ M) :
    ∀ m, IntB (M * (P.card + Q.card + 1) + 1) (gateValue a (circGateC A B P Q L f) m) := by
  set R : ℤ := M * (P.card + Q.card + 1) + 1 with hRdef
  have hR0 : (0 : ℤ) ≤ R := by positivity
  have hSR : ∀ k, SL Q L k + 1 ≤ R := by
    intro k
    have := SL_le Q L hM k
    have : (M : ℤ) * Q.card ≤ M * (P.card + Q.card + 1) :=
      mul_le_mul_of_nonneg_left (by omega) (by positivity)
    omega
  have hrhs : ∀ k, |(lineAt L k).rhs| ≤ R := by
    intro k
    have := (lineAt_bound L hM k).2
    have : (M : ℤ) ≤ M * (P.card + Q.card + 1) :=
      le_mul_of_one_le_right (by positivity) (by omega)
    omega
  have h01 : ∀ x : ℝ, (x = 0 ∨ x = 1) → IntB R x := by
    rintro x (rfl | rfl)
    · exact ⟨0, by simp, by simpa using hR0⟩
    · refine ⟨1, by simp, ?_⟩
      rw [abs_one, hRdef]
      have : (0 : ℤ) ≤ M * (P.card + Q.card + 1) := by positivity
      omega
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  have hread := read_intB a hR0 ih
  -- first gate values
  have hfirstB : ∀ k, bstart P k ≤ m → (∀ m' < bstart P k, IntB R
      (gateValue a (circGateC A B P Q L f) m')) →
      IntB R ((firstGateC A B P Q L k).val a
        (mcVals a ((List.range (bstart P k)).map (circGateC A B P Q L f)))) := by
    intro k _ ihk
    have hrd := read_intB a hR0 ihk
    have hS := SL_nonneg Q L k
    unfold firstGateC
    cases ruleAt (A ∪ B) L k with
    | hyp C =>
        dsimp only
        split_ifs
        · exact ⟨-(lineAt L k).rhs, by simp [MGate.val], by rw [abs_neg]; exact hrhs k⟩
        · exact h01 _ (Or.inl rfl)
    | low i =>
        dsimp only
        split_ifs
        · refine ⟨-clampA (SL Q L k) (lineAt L k).rhs, rfl, ?_⟩
          obtain ⟨h1, h2⟩ := clampA_range (x := (lineAt L k).rhs) hS
          have := hSR k
          rw [abs_le]; constructor <;> omega
        · exact h01 _ (Or.inl rfl)
    | up i =>
        dsimp only
        split_ifs
        · refine ⟨-clampA (SL Q L k) (lineAt L k).rhs, rfl, ?_⟩
          obtain ⟨h1, h2⟩ := clampA_range (x := (lineAt L k).rhs) hS
          have := hSR k
          rw [abs_le]; constructor <;> omega
        · exact h01 _ (Or.inl rfl)
    | add i j =>
        dsimp only; simp only [MGate.val]
        obtain ⟨zi, hzi, _⟩ := hrd (posN P i)
        obtain ⟨zj, hzj, _⟩ := hrd (posN P j)
        rw [hzi, hzj]
        obtain ⟨wi, hwi, _⟩ := cV_intB (SL_nonneg Q L i) (hSR i) zi
        obtain ⟨wj, hwj, _⟩ := cV_intB (SL_nonneg Q L j) (hSR j) zj
        rw [hwi, hwj]
        split_ifs
        · refine ⟨-(SL Q L k + 1), by unfold SR; push_cast; ring, ?_⟩
          have := hSR k; rw [abs_le]; constructor <;> omega
        · rw [show ((wi : ℝ) + wj) = ((wi + wj : ℤ) : ℝ) by push_cast; ring]
          exact cV_intB hS (hSR k) _
    | scale i c =>
        dsimp only; simp only [MGate.val]
        obtain ⟨zi, hzi, _⟩ := hrd (posN P i)
        rw [hzi]
        obtain ⟨wi, hwi, _⟩ := cV_intB (SL_nonneg Q L i) (hSR i) zi
        rw [hwi]
        split_ifs
        · refine ⟨-(SL Q L k + 1), by unfold SR; push_cast; ring, ?_⟩
          have := hSR k; rw [abs_le]; constructor <;> omega
        · rw [show ((c : ℝ) * wi) = (((c : ℤ) * wi : ℤ) : ℝ) by push_cast; ring]
          exact cV_intB hS (hSR k) _
    | div i c =>
        dsimp only; simp only [MGate.val]
        obtain ⟨zi, hzi, _⟩ := hrd (posN P i)
        rw [hzi]
        obtain ⟨wi, hwi, _⟩ := cV_intB (SL_nonneg Q L i) (hSR i) zi
        rw [hwi]
        split_ifs
        · refine ⟨-(SL Q L k + 1), by unfold SR; push_cast; ring, ?_⟩
          have := hSR k; rw [abs_le]; constructor <;> omega
        · exact cV_intB hS (hSR k) _
  -- case split on the gate index
  by_cases hin : m < P.card
  · have : gateValue a (circGateC A B P Q L f) m = bitR a ((Pl P).getD m 0) :=
      val_inputC A B P Q L a f hin
    rw [this]; unfold bitR; split_ifs
    · exact h01 _ (Or.inr rfl)
    · exact h01 _ (Or.inl rfl)
  by_cases hblk : (m - P.card) / (P.card + 1) < L.length
  · set k := (m - P.card) / (P.card + 1)
    set r := (m - P.card) % (P.card + 1)
    have hmr : m = bstart P k + r := by
      unfold bstart
      have h : (P.card + 1) * k + r = m - P.card := Nat.div_add_mod _ _
      have hcomm : (P.card + 1) * k = k * (P.card + 1) := Nat.mul_comm _ _
      omega
    have hr : r ≤ P.card := by have := Nat.mod_lt (m - P.card) (show 0 < P.card + 1 by omega); omega
    have hbk : bstart P k ≤ m := by omega
    have ihk : ∀ m' < bstart P k, IntB R (gateValue a (circGateC A B P Q L f) m') :=
      fun m' hm' => ih m' (by omega)
    have hF := hfirstB k hbk ihk
    have hfirstV : gateValue a (circGateC A B P Q L f) (bstart P k) =
        (firstGateC A B P Q L k).val a
          (mcVals a ((List.range (bstart P k)).map (circGateC A B P Q L f))) := by
      unfold gateValue
      rw [show bstart P k = bstart P k + 0 by rfl, circGateC_block A B P Q L hblk (Nat.zero_le _)]
      rfl
    rw [hmr, val_chainC A B P Q L a f hblk r hr, hfirstV]
    by_cases hH : IsHypA A B L k
    · rw [if_pos hH]
      obtain ⟨C, hrule, hCA⟩ := hH
      have hval : (firstGateC A B P Q L k).val a
          (mcVals a ((List.range (bstart P k)).map (circGateC A B P Q L f))) =
          -((lineAt L k).rhs : ℝ) := by
        unfold firstGateC; rw [hrule]; simp [hCA, MGate.val]
      rw [hval]
      -- the partial sum is an integer between 0 and r M
      have hsum : ∀ t ≤ P.card, ∃ z : ℤ,
          (((Pl P).take t).map fun v => wt L k v * bitR a v).sum = z ∧ 0 ≤ z ∧ z ≤ t * M := by
        intro t
        induction t with
        | zero => intro _; exact ⟨0, by simp, le_rfl, by simp⟩
        | succ t iht =>
            intro ht
            obtain ⟨z, hz, hz0, hzt⟩ := iht (by omega)
            have htl : t < (Pl P).length := by rw [Pl_length]; omega
            rw [List.take_add_one, List.getElem?_eq_getElem htl]
            simp only [Option.toList_some, List.map_append, List.sum_append, List.map_singleton,
              List.sum_singleton]
            set v := (Pl P)[t]
            have hc := (lineAt_bound L hM k).1 v
            set w := max ((lineAt L k).coef v) 0
            have hw0 : 0 ≤ w := le_max_right _ _
            have hwM : w ≤ M := max_le (le_of_abs_le hc) (by positivity)
            have hwt : wt L k v = (w : ℝ) := by unfold wt; simp only [w, Int.cast_max, Int.cast_zero]
            rw [hwt, bitR_eq, hz]
            refine ⟨z + w * bitZ a v, by push_cast; ring, ?_, ?_⟩
            · have := bitZ_nonneg a v; positivity
            · have h1 := bitZ_le_one a v
              have h0 := bitZ_nonneg a v
              have : w * bitZ a v ≤ M := by nlinarith
              push_cast; nlinarith
      obtain ⟨z, hz, hz0, hzr⟩ := hsum r hr
      rw [hz]
      refine ⟨-(lineAt L k).rhs + z, by push_cast; ring, ?_⟩
      have h1 := (lineAt_bound L hM k).2
      have h2 : (r : ℤ) * M ≤ P.card * M := mul_le_mul_of_nonneg_right (by exact_mod_cast hr)
        (by positivity)
      have h3 : (P.card : ℤ) * M + M ≤ M * (P.card + Q.card + 1) := by nlinarith
      rw [abs_le] at h1 ⊢
      constructor <;> push_cast at hzr <;> nlinarith
    · rw [if_neg hH, add_zero]; exact hF
  · -- the output gate (and beyond)
    have hval : gateValue a (circGateC A B P Q L f) m = 0 ∨
        gateValue a (circGateC A B P Q L f) m = 1 := by
      unfold gateValue circGateC
      rw [if_neg hin, if_neg hblk]
      unfold finalGateC; simp only [MGate.val]
      split_ifs
      · right; rfl
      · left; rfl
    exact h01 _ hval

end Bdd

end

end SATurday.ProofComplexity
