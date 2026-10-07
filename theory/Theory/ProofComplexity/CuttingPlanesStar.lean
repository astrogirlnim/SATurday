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

end

end SATurday.ProofComplexity
