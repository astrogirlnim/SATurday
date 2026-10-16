import Theory.ProofComplexity.PangDag
import Theory.ProofComplexity.Resolution

/-!
# Nonvacuity for `Pang.Refutation`: every unsatisfiable CNF has a refutation (referee repair, 2b)

Resolution (`Derivation`) is simulated step by step in the dag-like syntactic `Res(lin F_p)` of
`PangDag`: the resolution step on `x` is a linear combination of `1 - x = 0` and `x = 0` giving the
false constant `1 = 0` (rule `comb`), which the rule `falseConst` then deletes.  Together with
`resolution_complete` this gives `Pang.refutation_of_unsat`: for any unsatisfiable CNF `Φ` whose
variables lie in `V`, a `Pang.Refutation Φ V p` exists (no size control: existence only).
-/

open SATurday.ProofComplexity MvPolynomial

namespace Pang

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime]

/-- `n` nodes `0..n-1` of a refutation-in-progress. -/
def Good (Φ : CNF) (V : Finset ℕ) (n : ℕ) (line : ℕ → Line p) (prem : ℕ → List ℕ) : Prop :=
  (∀ i < n, ∀ j ∈ prem i, j < i) ∧ (∀ i < n, Infer Φ V ((prem i).map line) (line i)) ∧
    ∀ i < n, WF V (line i)

theorem good_snoc {Φ : CNF} {V : Finset ℕ} {n : ℕ} {line : ℕ → Line p} {prem : ℕ → List ℕ}
    (hg : Good Φ V n line prem) (pr : List ℕ) (L : Line p) (hpr : ∀ j ∈ pr, j < n)
    (hI : Infer Φ V (pr.map line) L) (hW : WF V L) :
    Good Φ V (n + 1) (Function.update line n L) (Function.update prem n pr) := by
  obtain ⟨h1, h2, h3⟩ := hg
  refine ⟨fun i hi j hj => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
    · rw [Function.update_of_ne (by omega)] at hj; exact h1 i hlt j hj
    · rw [Function.update_self] at hj; exact hpr j hj
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      have : ((prem i).map (Function.update line n L)) = (prem i).map line :=
        List.map_congr_left fun j hj => Function.update_of_ne (by have := h1 i hlt j hj; omega) _ _
      rw [this]; exact h2 i hlt
    · rw [Function.update_self, Function.update_self]
      have : (pr.map (Function.update line i L)) = pr.map line :=
        List.map_congr_left fun j hj => Function.update_of_ne (by have := hpr j hj; omega) _ _
      rw [this]; exact hI
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
    · rw [Function.update_of_ne (by omega)]; exact h3 i hlt
    · rw [Function.update_self]; exact hW

theorem good_append {Φ : CNF} {V : Finset ℕ} {n₁ n₂ : ℕ} {l₁ l₂ : ℕ → Line p}
    {p₁ p₂ : ℕ → List ℕ} (h₁ : Good Φ V n₁ l₁ p₁) (h₂ : Good Φ V n₂ l₂ p₂) :
    Good Φ V (n₁ + n₂) (fun i => if i < n₁ then l₁ i else l₂ (i - n₁))
      (fun i => if i < n₁ then p₁ i else (p₂ (i - n₁)).map (· + n₁)) := by
  obtain ⟨a1, a2, a3⟩ := h₁
  obtain ⟨b1, b2, b3⟩ := h₂
  refine ⟨fun i hi j hj => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · by_cases h : i < n₁
    · simp only [h, if_true] at hj; exact a1 i h j hj
    · simp only [h, if_false, List.mem_map] at hj
      obtain ⟨k, hk, rfl⟩ := hj
      have := b1 (i - n₁) (by omega) k hk
      omega
  · by_cases h : i < n₁
    · simp only [h, if_true]
      have : (p₁ i).map (fun i => if i < n₁ then l₁ i else l₂ (i - n₁)) = (p₁ i).map l₁ :=
        List.map_congr_left fun j hj => by simp [(a1 i h j hj).trans h]
      rw [this]; exact a2 i h
    · simp only [h, if_false]
      have : ((p₂ (i - n₁)).map (· + n₁)).map (fun i => if i < n₁ then l₁ i else l₂ (i - n₁)) =
          (p₂ (i - n₁)).map l₂ := by
        rw [List.map_map]
        exact List.map_congr_left fun j hj => by simp
      rw [this]; exact b2 (i - n₁) (by omega)
  · by_cases h : i < n₁
    · simp only [h, if_true]; exact a3 i h
    · simp only [h, if_false]; exact b3 (i - n₁) (by omega)

theorem wf_clauseLine {V : Finset ℕ} {C : Clause} (h : ∀ l ∈ C, l.var ∈ V) :
    WF V (clauseLine (p := p) C) := by
  intro f hf
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hf
  refine ⟨?_, fun v hv => ?_⟩
  · unfold litPoly
    split_ifs
    · exact (totalDegree_sub _ _).trans (max_le (by simp) (by simp))
    · simp
  · have : v = l.var := by
      unfold litPoly at hv
      split_ifs at hv
      · rw [sub_eq_add_neg] at hv
        have := vars_add_subset _ _ hv
        simpa [vars_neg, vars_X] using this
      · simpa [vars_X] using hv
    exact this ▸ h l hl

theorem wf_const {V : Finset ℕ} (c : ZMod p) : WF V ({(C c : Poly p)} : Line p) := by
  intro f hf
  rw [Finset.mem_singleton] at hf
  subst hf
  simp

/-- Every resolution derivation is simulated by a node list ending in the derived clause. -/
theorem good_of_derivation {Φ : CNF} {V : Finset ℕ} (hV : ∀ C ∈ Φ, ∀ l ∈ C, l.var ∈ V) :
    ∀ {C : Clause} (d : Derivation Φ C), (∀ l ∈ C, l.var ∈ V) ∧
      ∃ (n : ℕ) (line : ℕ → Line p) (prem : ℕ → List ℕ) (i : ℕ),
        Good Φ V n line prem ∧ i < n ∧ line i = clauseLine C := by
  intro C d
  induction d with
  | hyp C hC =>
    refine ⟨hV C hC, 1, fun _ => clauseLine C, fun _ => [], 0, ⟨?_, ?_, ?_⟩, by omega, rfl⟩
    · intro i _ j hj; simp at hj
    · intro i _; exact Infer.init C hC
    · intro i _; exact wf_clauseLine (hV C hC)
  | @res x A B dC dD hx hnx ihC ihD =>
    obtain ⟨hVC, n₁, l₁, p₁, i₁, g₁, hi₁, e₁⟩ := ihC
    obtain ⟨hVD, n₂, l₂, p₂, i₂, g₂, hi₂, e₂⟩ := ihD
    have hVr : ∀ l ∈ SATurday.ProofComplexity.resolvent A B x, l.var ∈ V := by
      intro l hl
      unfold SATurday.ProofComplexity.resolvent at hl
      rcases Finset.mem_union.1 hl with h | h
      · exact hVC l (Finset.mem_of_mem_erase h)
      · exact hVD l (Finset.mem_of_mem_erase h)
    refine ⟨hVr, n₁ + n₂ + 1 + 1, ?_⟩
    set l := fun i => if i < n₁ then l₁ i else l₂ (i - n₁) with hl
    set pr := fun i => if i < n₁ then p₁ i else (p₂ (i - n₁)).map (· + n₁) with hpr
    have g := good_append g₁ g₂
    set R := SATurday.ProofComplexity.resolvent A B x with hR
    set f : Poly p := litPoly ⟨x, true⟩ with hf
    set g' : Poly p := litPoly ⟨x, false⟩ with hg'
    have hfC : f ∈ l i₁ := by
      simp only [hl, hi₁, if_true, e₁]
      exact Finset.mem_image.2 ⟨_, hx, rfl⟩
    have hgD : g' ∈ l (n₁ + i₂) := by
      simp only [hl, show ¬ (n₁ + i₂ < n₁) by omega, if_false, Nat.add_sub_cancel_left, e₂]
      exact Finset.mem_image.2 ⟨_, hnx, rfl⟩
    have hsum : (MvPolynomial.C (1 : ZMod p) : Poly p) * f + MvPolynomial.C 1 * g' = MvPolynomial.C 1 := by
      simp only [hf, hg', litPoly, if_true, Bool.false_eq_true, if_false]
      simp only [map_one, one_mul]
      ring
    set L₀ : Line p := insert (MvPolynomial.C 1) (clauseLine R) with hL₀
    have hI₁ : Infer Φ V [l i₁, l (n₁ + i₂)] L₀ := by
      refine Infer.comb hfC hgD 1 1 L₀ ?_
      rw [hsum]
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        rcases Finset.mem_union.1 hy with hy | hy
        · have hy' := Finset.mem_of_mem_erase hy
          rw [hl] at hy'
          simp only [hi₁, if_true, e₁] at hy'
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hy'
          refine Finset.mem_image.2 ⟨m, ?_, rfl⟩
          rw [hR]; unfold SATurday.ProofComplexity.resolvent
          refine Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, hm⟩)
          rintro rfl
          exact (Finset.mem_erase.1 hy).1 rfl
        · have hy' := Finset.mem_of_mem_erase hy
          simp only [hl, show ¬ (n₁ + i₂ < n₁) by omega, if_false, Nat.add_sub_cancel_left, e₂] at hy'
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hy'
          refine Finset.mem_image.2 ⟨m, ?_, rfl⟩
          rw [hR]; unfold SATurday.ProofComplexity.resolvent
          refine Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, hm⟩)
          rintro rfl
          exact (Finset.mem_erase.1 hy).1 rfl
    have hwf₀ : WF V L₀ := by
      intro y hy
      rcases Finset.mem_insert.1 hy with h | h
      · rw [h]; exact wf_const (V := V) 1 _ (Finset.mem_singleton_self _)
      · exact wf_clauseLine hVr y h
    have hp₁ : ∀ j ∈ [i₁, n₁ + i₂], j < n₁ + n₂ := by
      intro j hj; simp at hj; omega
    have g2 := good_snoc g [i₁, n₁ + i₂] L₀ hp₁
      (by
        have : [i₁, n₁ + i₂].map l = [l i₁, l (n₁ + i₂)] := rfl
        rw [this]; exact hI₁) hwf₀
    have hI₂ : Infer Φ V [L₀] (clauseLine R) := by
      refine Infer.falseConst (L := L₀) (1 : ZMod p) one_ne_zero (Finset.mem_insert_self _ _) _ ?_
      intro y hy
      exact (Finset.mem_insert.1 (Finset.mem_of_mem_erase hy)).resolve_left (Finset.mem_erase.1 hy).1
    have g3 := good_snoc g2 [n₁ + n₂] (clauseLine R) (by intro j hj; simp at hj; omega)
      (by simpa [Function.update_self] using hI₂) (wf_clauseLine hVr)
    refine ⟨_, _, n₁ + n₂ + 1, g3, by omega, ?_⟩
    rw [Function.update_self]

/-- **Nonvacuity**: every unsatisfiable CNF whose variables lie in `V` has a dag-like syntactic
`Res(lin F_p)` refutation (existence only, no size control). -/
theorem refutation_of_unsat {Φ : CNF} {V : Finset ℕ} (hV : ∀ C ∈ Φ, ∀ l ∈ C, l.var ∈ V)
    (h : ¬ Satisfiable Φ) : Nonempty (Refutation Φ V p) := by
  obtain ⟨d⟩ := resolution_complete h
  obtain ⟨-, n, line, prem, i, ⟨g1, g2, g3⟩, hi, he⟩ := good_of_derivation (p := p) hV d
  refine ⟨⟨i + 1, line, prem, by omega, fun k hk => g1 k (by omega), fun k hk => g2 k (by omega),
    fun k hk => g3 k (by omega), ?_⟩⟩
  simpa [he] using (show clauseLine (p := p) (∅ : Clause) = ∅ from rfl)

end

end Pang
