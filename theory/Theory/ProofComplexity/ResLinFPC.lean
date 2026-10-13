import Theory.ProofComplexity.ResLinF

/-!
# Res(lin F) width gives polynomial calculus degree (Ladder Rung R4, Phase 2.2, layer 2)

Part and Tzameret, Theorem 45: replace each linear clause `∨ (f_i = a_i)` by the product
`∏ (f_i - a_i)` (`clPoly`); every rule of `Res(lin F_p)` is then simulated by multiplications and
linear combinations. For a tree-like derivation whose lines have at most `w` equations the
translation has degree `≤ w + p` (`rld_to_pcd₀`). The `+ p` repairs the combination rule when
the new equation already occurs among the side clauses (then the product carries the factor
twice; `eq^p - eq` is a multiple of Boolean axioms by Frobenius, which removes the square at
degree `p`). CNF specialisation: `rld_cnf_pcd`.

LOG: R4 Phase 2.2 ResLinFPC module (Theorem 45 of Part-Tzameret)
-/

namespace SATurday.ProofComplexity

namespace RLF

open MvPolynomial
open scoped Classical

noncomputable section

variable {F : Type} [Field F]

/-- The polynomial of a linear form. -/
def linPoly (c : ℕ →₀ F) : MvPolynomial ℕ F := c.sum fun i a => C a * X i

/-- The polynomial `f - a` of an equation `f = a`. -/
def eqPoly (e : LEq F) : MvPolynomial ℕ F := linPoly e.1 - C e.2

/-- The arithmetization of a linear clause: the product of its equation polynomials. -/
def clPoly (L : Finset (LEq F)) : MvPolynomial ℕ F := ∏ e ∈ L, eqPoly e

theorem linPoly_add (c d : ℕ →₀ F) : linPoly (c + d) = linPoly c + linPoly d := by
  unfold linPoly
  exact Finsupp.sum_add_index' (fun i => by simp) (fun i a b => by rw [C_add, add_mul])

theorem linPoly_smul (α : F) (c : ℕ →₀ F) : linPoly (α • c) = C α * linPoly c := by
  unfold linPoly
  rw [Finsupp.sum_smul_index' (fun i => by simp), Finsupp.mul_sum]
  simp [mul_assoc]

theorem totalDegree_linPoly (c : ℕ →₀ F) : (linPoly c).totalDegree ≤ 1 := by
  unfold linPoly Finsupp.sum
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, totalDegree_X]

theorem totalDegree_eqPoly (e : LEq F) : (eqPoly e).totalDegree ≤ 1 := by
  unfold eqPoly
  refine (totalDegree_sub _ _).trans (max_le (totalDegree_linPoly _) ?_)
  rw [totalDegree_C]; omega

theorem totalDegree_clPoly (L : Finset (LEq F)) : (clPoly L).totalDegree ≤ L.card := by
  unfold clPoly
  refine (totalDegree_finset_prod _ _).trans ?_
  calc ∑ e ∈ L, (eqPoly e).totalDegree ≤ ∑ _e ∈ L, 1 := Finset.sum_le_sum fun e _ => totalDegree_eqPoly e
    _ = L.card := by simp

theorem eqPoly_comb (e1 e2 : LEq F) (α β : F) :
    eqPoly (cmb α β e1 e2) = C α * eqPoly e1 + C β * eqPoly e2 := by
  unfold eqPoly cmb
  simp only [linPoly_add, linPoly_smul, C_add, C_mul]
  ring

theorem clPoly_boolCl (i : ℕ) : clPoly (boolCl i : Finset (LEq F)) = X i ^ 2 - X i := by
  have h01 : ((0 : F)) ≠ 1 := zero_ne_one
  have hne : ((Finsupp.single i (1 : F), (0 : F)) : LEq F) ≠ (Finsupp.single i (1 : F), 1) := by
    intro h; exact h01 (congrArg Prod.snd h)
  unfold clPoly boolCl
  rw [Finset.prod_pair hne]
  unfold eqPoly linPoly
  rw [Finsupp.sum_single_index (by simp)]
  simp only [map_zero, map_one, sub_zero, one_mul]
  ring

/-- Axiom set of the polynomial translation: arithmetized axiom clauses plus Boolean axioms. -/
def PAx (Ax : Set (Finset (LEq F))) : Set (MvPolynomial ℕ F) :=
  {f | ∃ C ∈ Ax, f = clPoly C} ∪ {f | ∃ i, f = X i ^ 2 - X i}

section Fp

variable {p : ℕ} [Fact p.Prime] [CharP F p] (hfrob : ∀ a : F, a ^ p = a)
include hfrob

theorem eqPoly_frob (e : LEq F) :
    eqPoly e ^ p - eqPoly e = ∑ i ∈ e.1.support, C (e.1 i) * (X i ^ p - X i) := by
  unfold eqPoly linPoly
  rw [sub_pow_char, Finsupp.sum, sum_pow_char]
  have h1 : ∀ i ∈ e.1.support, (C (e.1 i) * (X i : MvPolynomial ℕ F)) ^ p
      = C (e.1 i) * X i ^ p := by
    intro i _
    rw [mul_pow, ← C_pow, hfrob]
  rw [Finset.sum_congr rfl h1, ← C_pow, hfrob]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem pcd₀_boolMul {Ax : Set (Finset (LEq F))} {D : ℕ} (i : ℕ)
    (R : MvPolynomial ℕ F) (hD : p + R.totalDegree ≤ D) :
    PCD₀ (PAx Ax) D ((X i ^ p - X i) * R) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hgeom : (X i ^ p - X i : MvPolynomial ℕ F) =
      (X i ^ 2 - X i) * ∑ k ∈ Finset.range (p - 1), X i ^ k := by
    have : p = (p - 2) + 2 := by omega
    have h := mul_geom_sum (X i : MvPolynomial ℕ F) (p - 1)
    -- (x - 1) * Σ_{k<p-1} x^k = x^(p-1) - 1
    calc (X i ^ p - X i : MvPolynomial ℕ F) = X i * (X i ^ (p - 1) - 1) := by
          rw [mul_sub, ← pow_succ']; simp [Nat.sub_add_cancel (by omega : 1 ≤ p)]
      _ = _ := by
          rw [← h]; ring
  have hax : PCD₀ (PAx Ax) D (X i ^ 2 - X i) := by
    refine PCD₀.ax (Or.inr ⟨i, rfl⟩) ?_
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_pow _ _).trans ?_
      rw [totalDegree_X]; omega
    · rw [totalDegree_X]; omega
  have hcomm : (X i ^ p - X i) * R =
      ((∑ k ∈ Finset.range (p - 1), (X i : MvPolynomial ℕ F) ^ k) * R) * (X i ^ 2 - X i) := by
    rw [hgeom]; ring
  rw [hcomm]
  refine pcd₀_mul hax ?_
  have hx2 : (X i ^ 2 - X i : MvPolynomial ℕ F).totalDegree ≤ 2 := by
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_pow _ _).trans (by simp [totalDegree_X])
    · simp [totalDegree_X]
  have hg : (∑ k ∈ Finset.range (p - 1), (X i : MvPolynomial ℕ F) ^ k).totalDegree ≤ p - 2 := by
    refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun k hk => ?_)
    refine (totalDegree_pow _ _).trans ?_
    rw [totalDegree_X]
    have := Finset.mem_range.1 hk
    omega
  have := totalDegree_mul (∑ k ∈ Finset.range (p - 1), (X i : MvPolynomial ℕ F) ^ k) R
  omega

/-- **Theorem 45 (Part-Tzameret)**: a tree-like `Res(lin F_p)` derivation with lines of at most
`w` equations translates into a plain polynomial calculus derivation of degree at most `w + p`. -/
theorem rld_to_pcd₀ {Ax : Set (Finset (LEq F))} {w : ℕ} {L : Finset (LEq F)} {s : ℕ}
    (h : RLD Ax w L s) : PCD₀ (PAx Ax) (w + p) (clPoly L) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  induction h with
  | @ax C hC hw =>
    exact PCD₀.ax (Or.inl ⟨_, hC, rfl⟩) ((totalDegree_clPoly _).trans (by omega))
  | @weak L0 L' s0 hL hsub hw ih =>
    have e := Finset.prod_sdiff (f := eqPoly) hsub
    have hcard : (L' \ L0).card + L0.card = L'.card := by
      rw [Finset.card_sdiff_of_subset hsub]; have := Finset.card_le_card hsub; omega
    have : clPoly L' = (∏ e ∈ L' \ L0, eqPoly e) * clPoly L0 := e.symm
    rw [this]
    refine pcd₀_mul ih ?_
    have h1 : (∏ e ∈ L' \ L0, eqPoly e).totalDegree ≤ (L' \ L0).card := totalDegree_clPoly _
    have h2 : (clPoly L0).totalDegree ≤ L0.card := totalDegree_clPoly _
    omega
  | @comb A B s1 s2 e1 e2 α β hA hB he1 he2 hcard ihA ihB =>
    set C0 := A.erase e1 with hC0
    set D0 := B.erase e2 with hD0
    set e3 : LEq F := cmb α β e1 e2 with he3
    show PCD₀ (PAx Ax) (w + p) (clPoly (C0 ∪ D0 ∪ {e3}))
    have hA' : clPoly A = eqPoly e1 * clPoly C0 := by
      unfold clPoly; exact (Finset.mul_prod_erase A eqPoly he1).symm
    have hB' : clPoly B = eqPoly e2 * clPoly D0 := by
      unfold clPoly; exact (Finset.mul_prod_erase B eqPoly he2).symm
    have cA : C0.card + 1 = A.card := Finset.card_erase_add_one he1
    have cB : D0.card + 1 = B.card := Finset.card_erase_add_one he2
    have hAw : A.card ≤ w := rld_card hA
    have hBw : B.card ≤ w := rld_card hB
    by_cases hnot : e3 ∉ C0 ∪ D0
    · have hM : clPoly (C0 ∪ D0 ∪ {e3}) = eqPoly e3 * clPoly (C0 ∪ D0) := by
        unfold clPoly
        rw [Finset.prod_union (Finset.disjoint_singleton_right.2 hnot), Finset.prod_singleton, mul_comm]
      have m1 : clPoly (C0 ∪ D0) = clPoly C0 * clPoly (D0 \ C0) := by
        unfold clPoly
        rw [← Finset.union_sdiff_self_eq_union, Finset.prod_union Finset.disjoint_sdiff]
      have m2 : clPoly (C0 ∪ D0) = clPoly D0 * clPoly (C0 \ D0) := by
        unfold clPoly
        rw [Finset.union_comm, ← Finset.union_sdiff_self_eq_union,
          Finset.prod_union Finset.disjoint_sdiff]
      have key : clPoly (C0 ∪ D0 ∪ {e3}) =
          C α * (clPoly (D0 \ C0) * clPoly A) + C β * (clPoly (C0 \ D0) * clPoly B) := by
        rw [hM, he3, eqPoly_comb, hA', hB']
        calc _ = C α * eqPoly e1 * (clPoly C0 * clPoly (D0 \ C0)) +
              C β * eqPoly e2 * (clPoly D0 * clPoly (C0 \ D0)) := by
                rw [← m1, ← m2]; ring
          _ = _ := by ring
      rw [key]
      have cU1 : (C0 ∪ D0).card = C0.card + (D0 \ C0).card := by
        rw [← Finset.union_sdiff_self_eq_union]
        exact Finset.card_union_of_disjoint Finset.disjoint_sdiff
      have cU2 : (C0 ∪ D0).card = D0.card + (C0 \ D0).card := by
        rw [Finset.union_comm, ← Finset.union_sdiff_self_eq_union]
        exact Finset.card_union_of_disjoint Finset.disjoint_sdiff
      have cI : (C0 ∪ D0 ∪ {e3}).card = (C0 ∪ D0).card + 1 := by
        rw [Finset.union_comm, ← Finset.insert_eq, Finset.card_insert_of_notMem
          (by rw [Finset.mem_union]; intro h; exact hnot (by rw [Finset.mem_union]; tauto))]
      refine PCD₀.lin α β (pcd₀_mul ihA ?_) (pcd₀_mul ihB ?_)
      · have h1 : (clPoly (D0 \ C0)).totalDegree ≤ (D0 \ C0).card := totalDegree_clPoly _
        have h2 : (clPoly A).totalDegree ≤ A.card := totalDegree_clPoly _
        omega
      · have h1 : (clPoly (C0 \ D0)).totalDegree ≤ (C0 \ D0).card := totalDegree_clPoly _
        have h2 : (clPoly B).totalDegree ≤ B.card := totalDegree_clPoly _
        omega
    · -- the new equation already occurs among the side clauses: repair
      rw [not_not] at hnot
      have hSeq : C0 ∪ D0 ∪ {e3} = C0 ∪ D0 := by
        ext x; simp only [Finset.mem_union, Finset.mem_singleton]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr h
          · subst h; exact (Finset.mem_union.1 hnot)
        · rintro (h | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
      rw [hSeq]
      have hSw : (C0 ∪ D0).card ≤ w := by
        have := hcard; rw [hSeq] at this; exact this
      have hC0S : C0 ⊆ C0 ∪ D0 := Finset.subset_union_left
      have hD0S : D0 ⊆ C0 ∪ D0 := Finset.subset_union_right
      generalize C0 ∪ D0 = S at hSeq hnot hSw hC0S hD0S
      have mC : clPoly S = clPoly (S \ C0) * clPoly C0 := by
        unfold clPoly; exact (Finset.prod_sdiff hC0S).symm
      have mD : clPoly S = clPoly (S \ D0) * clPoly D0 := by
        unfold clPoly; exact (Finset.prod_sdiff hD0S).symm
      have cC : (S \ C0).card + C0.card = S.card := by
        rw [Finset.card_sdiff_of_subset hC0S]; have := Finset.card_le_card hC0S; omega
      have cD : (S \ D0).card + D0.card = S.card := by
        rw [Finset.card_sdiff_of_subset hD0S]; have := Finset.card_le_card hD0S; omega
      -- eq3 * P(S) is derivable at degree |S| + 1
      have hsq : PCD₀ (PAx Ax) (w + p) (eqPoly e3 * clPoly S) := by
        have key : eqPoly e3 * clPoly S =
            C α * (clPoly (S \ C0) * clPoly A) + C β * (clPoly (S \ D0) * clPoly B) := by
          rw [he3, eqPoly_comb]
          have e1' : eqPoly e1 * clPoly S = clPoly (S \ C0) * clPoly A := by
            rw [hA', mC]; ring
          have e2' : eqPoly e2 * clPoly S = clPoly (S \ D0) * clPoly B := by
            rw [hB', mD]; ring
          calc _ = C α * (eqPoly e1 * clPoly S) + C β * (eqPoly e2 * clPoly S) := by ring
            _ = _ := by rw [e1', e2']
        rw [key]
        refine PCD₀.lin α β (pcd₀_mul ihA ?_) (pcd₀_mul ihB ?_)
        · have h1 : (clPoly (S \ C0)).totalDegree ≤ (S \ C0).card := totalDegree_clPoly _
          have h2 : (clPoly A).totalDegree ≤ A.card := totalDegree_clPoly _
          omega
        · have h1 : (clPoly (S \ D0)).totalDegree ≤ (S \ D0).card := totalDegree_clPoly _
          have h2 : (clPoly B).totalDegree ≤ B.card := totalDegree_clPoly _
          omega
      -- multiply by eq3^(p-2) to reach eq3^p * R
      set R := clPoly (S.erase e3) with hR
      have hPS : clPoly S = eqPoly e3 * R := by
        unfold clPoly; exact (Finset.mul_prod_erase S eqPoly hnot).symm
      have hRdeg : R.totalDegree + 1 ≤ S.card := by
        have h1 : R.totalDegree ≤ (S.erase e3).card := totalDegree_clPoly _
        have h2 := Finset.card_erase_add_one hnot
        omega
      have hpow : PCD₀ (PAx Ax) (w + p) (eqPoly e3 ^ p * R) := by
        have hh : eqPoly e3 ^ p * R = eqPoly e3 ^ (p - 2) * (eqPoly e3 * clPoly S) := by
          rw [hPS]
          have : p = (p - 2) + 2 := by omega
          conv_lhs => rw [this, pow_add]
          ring
        rw [hh]
        refine pcd₀_mul hsq ?_
        have h1 : (eqPoly e3 ^ (p - 2)).totalDegree ≤ p - 2 :=
          (totalDegree_pow _ _).trans (by
            have := totalDegree_eqPoly e3
            calc (p - 2) * (eqPoly e3).totalDegree ≤ (p - 2) * 1 := Nat.mul_le_mul_left _ this
              _ = p - 2 := by ring)
        have h2 : (eqPoly e3 * clPoly S).totalDegree ≤ 1 + S.card := by
          refine (totalDegree_mul _ _).trans ?_
          have := totalDegree_eqPoly e3
          have := totalDegree_clPoly S
          omega
        omega
      -- the Frobenius correction
      have hcorr : PCD₀ (PAx Ax) (w + p) ((eqPoly e3 ^ p - eqPoly e3) * R) := by
        rw [eqPoly_frob hfrob, Finset.sum_mul]
        refine pcd₀_sum _ _ (pcd₀_zero hpow) fun i _ => ?_
        rw [mul_assoc]
        refine pcd₀_smul _ (pcd₀_boolMul hfrob i R ?_)
        omega
      have hfin : clPoly S = 1 * (eqPoly e3 ^ p * R) + (-1) * ((eqPoly e3 ^ p - eqPoly e3) * R) := by
        rw [hPS]; ring
      rw [hfin]
      have := PCD₀.lin (1 : F) (-1) hpow hcorr
      simpa using this
  | @simp L0 s0 c hc hL ih =>
    by_cases hm : ((0 : ℕ →₀ F), c) ∈ L0
    · rwa [Finset.insert_eq_of_mem hm] at ih
    · have hz : eqPoly ((0 : ℕ →₀ F), c) = C (-c) := by simp [eqPoly, linPoly]
      have : clPoly L0 = C (-c⁻¹) * clPoly (insert ((0 : ℕ →₀ F), c) L0) := by
        unfold clPoly
        rw [Finset.prod_insert hm]
        change _ = C (-c⁻¹) * (eqPoly ((0 : ℕ →₀ F), c) * _)
        rw [hz, ← mul_assoc, ← C_mul]
        have : -c⁻¹ * -c = 1 := by field_simp
        rw [this]; simp
      rw [this]
      exact pcd₀_smul _ ih

end Fp

/-! ## CNF specialisation -/

/-- A literal as the equation `x_v = 1` (positive) or `x_v = 0` (negative). -/
def litEq (l : Literal) : LEq F := (Finsupp.single l.var 1, if l.pos then 1 else 0)

/-- A clause as a linear clause. -/
def ofCl (C : Clause) : Finset (LEq F) := C.image litEq

theorem ofCl_card_le (C : Clause) : (ofCl C : Finset (LEq F)).card ≤ C.card :=
  Finset.card_image_le

theorem litEq_inj : Function.Injective (litEq (F := F)) := by
  rintro ⟨v, b⟩ ⟨v', b'⟩ h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [litEq] at h1 h2
  rw [Finsupp.single_left_inj one_ne_zero] at h1
  subst h1
  cases b <;> cases b' <;> simp_all

theorem eqPoly_litEq (l : Literal) :
    eqPoly (litEq (F := F) l) = C (if l.pos then -1 else 1) * litPoly l := by
  unfold eqPoly litEq linPoly litPoly
  rw [Finsupp.sum_single_index (by simp)]
  cases l.pos <;> simp

theorem clPoly_ofCl (C : Clause) :
    clPoly (ofCl (F := F) C) = MvPolynomial.C (∏ l ∈ C, (if l.pos then (-1 : F) else 1)) * clausePoly C := by
  unfold clPoly ofCl clausePoly
  rw [Finset.prod_image (fun a _ b _ h => litEq_inj h)]
  simp only [eqPoly_litEq]
  rw [Finset.prod_mul_distrib, map_prod]

theorem totalDegree_clausePoly (C : Clause) : (clausePoly (F := F) C).totalDegree ≤ C.card := by
  unfold clausePoly
  refine (totalDegree_finset_prod _ _).trans ?_
  calc ∑ l ∈ C, (litPoly (F := F) l).totalDegree ≤ ∑ _l ∈ C, 1 :=
        Finset.sum_le_sum fun l _ => by
          unfold litPoly
          split_ifs
          · refine (totalDegree_sub _ _).trans (max_le ?_ ?_) <;> simp [totalDegree_X]
          · simp [totalDegree_X]
    _ = C.card := by simp

theorem pcd₀_transfer {A B : Set (MvPolynomial ℕ F)} {d : ℕ} {f : MvPolynomial ℕ F}
    (h : PCD₀ A d f) (hAB : ∀ g ∈ A, g.totalDegree ≤ d → PCD₀ B d g) : PCD₀ B d f := by
  induction h with
  | ax hf hd => exact hAB _ hf hd
  | lin a b _ _ ihf ihg => exact PCD₀.lin a b ihf ihg
  | mul i _ hd ih => exact PCD₀.mul i ih hd

theorem pcd₀_to_pcd {Ax : Set (MvPolynomial ℕ F)} {d : ℕ} (hd : 2 ≤ d) {f : MvPolynomial ℕ F}
    (h : PCD₀ (Ax ∪ {g | ∃ i, g = X i ^ 2 - X i}) d f) : PCD Ax d f := by
  induction h with
  | ax hf hdeg =>
    rcases hf with hf | ⟨i, rfl⟩
    · exact PCD.ax hf hdeg
    · exact PCD.bool i hd
  | lin a b _ _ ihf ihg => exact PCD.lin a b ihf ihg
  | mul i _ hdeg ih => exact PCD.mul i ih hdeg

/-- **Width gives degree for CNFs**: a tree-like `Res(lin F_p)` refutation (with Boolean axioms)
of a CNF with all lines of at most `w` equations (`2 ≤ w`, clauses of at most `w` literals) gives
a polynomial calculus refutation of degree `w + p`. -/
theorem rld_cnf_pcd {p : ℕ} [Fact p.Prime] [CharP F p] (hfrob : ∀ a : F, a ^ p = a) {Φ : CNF} {w s : ℕ} (hw : 2 ≤ w)
    (hΦ : ∀ C ∈ Φ, C.card ≤ w)
    (h : RLD (((fun C => (ofCl C : Finset (LEq F))) '' Φ) ∪ boolAx) w ∅ s) :
    PCD (cnfAx (F := F) Φ) (w + p) 1 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h0 := rld_to_pcd₀ hfrob h
  have e : clPoly (∅ : Finset (LEq F)) = 1 := by simp [clPoly]
  rw [e] at h0
  refine pcd₀_to_pcd (by omega) (pcd₀_transfer h0 ?_)
  rintro g (⟨_, (⟨C, hC, rfl⟩ | ⟨i, rfl⟩), rfl⟩ | ⟨i, rfl⟩) hdeg
  · rw [clPoly_ofCl]
    refine pcd₀_smul _ (PCD₀.ax (Or.inl ⟨C, hC, rfl⟩) ?_)
    exact (totalDegree_clausePoly C).trans (by have := hΦ C hC; omega)
  · rw [clPoly_boolCl] at hdeg ⊢
    exact PCD₀.ax (Or.inr ⟨i, rfl⟩) hdeg
  · exact PCD₀.ax (Or.inr ⟨i, rfl⟩) hdeg

end

end RLF

end SATurday.ProofComplexity
