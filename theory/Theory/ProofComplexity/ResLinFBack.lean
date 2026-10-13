import Theory.ProofComplexity.ResLinFAtom

/-!
# Khaniki's translation, backward half (Ladder Rung R4, Phase 2.2, K4)

A tree Resolution refutation of width `w` of the atom hypotheses `AtomHyp Φ` gives a polynomial
calculus refutation of `Φ` over `F_p` of degree `(p-1)(w+1)` (`atom_tree_pcd`). The atom `y_e` of
the equation `e = (f = a)` stands for the Boolean-point value `1 - (f - a)^(p-1)` (the indicator
of `f = a`); the falsity polynomial of the literal `y_e` is `(f-a)^(p-1)`, that of `¬y_e` is
`1 - (f-a)^(p-1)`, and a clause polynomial is the product of the falsity polynomials. The
resolution step is an EXACT polynomial identity (the two falsity polynomials of a variable add up
to `1`), so no polynomial calculus rule beyond multiplication and linear combination is needed.
The hypotheses are derived using Frobenius (`u^p - u` is a combination of Boolean axioms): the
implication clause `¬y_e1 ∨ ¬y_e2 ∨ y_(αe1+βe2)` has polynomial divisible by `u1^p - u1` and
`u2^p - u2` (in the sense of a degree `3(p-1)` combination).

LOG: R4 Phase 2.2 ResLinFBack module (back translation of Resolution width into PC degree)
-/

namespace SATurday.ProofComplexity

namespace RLF

open MvPolynomial
open scoped Classical
open Finset

noncomputable section

variable {F : Type} [Field F]

/-- Falsity polynomial of an atom literal; `dec` decodes the atom number into its equation. -/
def flit (p : ℕ) (dec : ℕ → LEq F) (l : Literal) : MvPolynomial ℕ F :=
  if l.pos then eqPoly (dec l.var) ^ (p - 1) else 1 - eqPoly (dec l.var) ^ (p - 1)

/-- Polynomial of an atom clause: the product of the falsity polynomials of its literals. -/
def cpoly (p : ℕ) (dec : ℕ → LEq F) (C : Clause) : MvPolynomial ℕ F := ∏ l ∈ C, flit p dec l

theorem totalDegree_flit (p : ℕ) (dec : ℕ → LEq F) (l : Literal) :
    (flit p dec l).totalDegree ≤ p - 1 := by
  have h1 : (eqPoly (dec l.var) ^ (p - 1)).totalDegree ≤ p - 1 :=
    (totalDegree_pow _ _).trans (by
      calc (p - 1) * (eqPoly (dec l.var)).totalDegree ≤ (p - 1) * 1 :=
            Nat.mul_le_mul_left _ (totalDegree_eqPoly _)
        _ = p - 1 := by ring)
  unfold flit
  split_ifs
  · exact h1
  · exact (totalDegree_sub _ _).trans (max_le (by simp) h1)

theorem totalDegree_cpoly (p : ℕ) (dec : ℕ → LEq F) (C : Clause) :
    (cpoly p dec C).totalDegree ≤ (p - 1) * C.card := by
  unfold cpoly
  refine (totalDegree_finset_prod _ _).trans ?_
  calc ∑ l ∈ C, (flit p dec l).totalDegree ≤ ∑ _l ∈ C, (p - 1) :=
        Finset.sum_le_sum fun l _ => totalDegree_flit p dec l
    _ = (p - 1) * C.card := by simp [mul_comm]

theorem flit_add (p : ℕ) (dec : ℕ → LEq F) (x : ℕ) :
    flit p dec ⟨x, true⟩ + flit p dec ⟨x, false⟩ = 1 := by
  simp [flit]

/-- Exact resolution step for clause polynomials. -/
theorem res_step (p : ℕ) (dec : ℕ → LEq F) {A : Set (MvPolynomial ℕ F)} {D : ℕ} {C E : Clause}
    {x : ℕ} (hC : PCD₀ A D (cpoly p dec C)) (hE : PCD₀ A D (cpoly p dec E))
    (hx : (⟨x, true⟩ : Literal) ∈ C) (hnx : (⟨x, false⟩ : Literal) ∈ E)
    (hdeg : (p - 1) * ((resolvent C E x).card + 1) ≤ D) :
    PCD₀ A D (cpoly p dec (resolvent C E x)) := by
  set C0 := C.erase ⟨x, true⟩ with hC0
  set E0 := E.erase ⟨x, false⟩ with hE0
  have hR : resolvent C E x = C0 ∪ E0 := rfl
  rw [hR] at hdeg ⊢
  have hCp : cpoly p dec C = flit p dec ⟨x, true⟩ * cpoly p dec C0 := by
    unfold cpoly; exact (Finset.mul_prod_erase C (flit p dec) hx).symm
  have hEp : cpoly p dec E = flit p dec ⟨x, false⟩ * cpoly p dec E0 := by
    unfold cpoly; exact (Finset.mul_prod_erase E (flit p dec) hnx).symm
  have cC : C0.card + 1 = C.card := Finset.card_erase_add_one hx
  have m1 : cpoly p dec (C0 ∪ E0) = cpoly p dec C0 * cpoly p dec (E0 \ C0) := by
    unfold cpoly
    rw [← Finset.union_sdiff_self_eq_union, Finset.prod_union Finset.disjoint_sdiff]
  have m2 : cpoly p dec (C0 ∪ E0) = cpoly p dec E0 * cpoly p dec (C0 \ E0) := by
    unfold cpoly
    rw [Finset.union_comm, ← Finset.union_sdiff_self_eq_union,
      Finset.prod_union Finset.disjoint_sdiff]
  have key : cpoly p dec (C0 ∪ E0) =
      cpoly p dec (E0 \ C0) * cpoly p dec C + cpoly p dec (C0 \ E0) * cpoly p dec E := by
    have h1 := flit_add p dec x
    calc cpoly p dec (C0 ∪ E0) = (flit p dec ⟨x, true⟩ + flit p dec ⟨x, false⟩) * cpoly p dec (C0 ∪ E0) := by
          rw [h1, one_mul]
      _ = flit p dec ⟨x, true⟩ * (cpoly p dec C0 * cpoly p dec (E0 \ C0)) +
          flit p dec ⟨x, false⟩ * (cpoly p dec E0 * cpoly p dec (C0 \ E0)) := by
          rw [add_mul, ← m1, ← m2]
      _ = _ := by rw [hCp, hEp]; ring
  rw [key]
  have cU1 : (C0 ∪ E0).card = C0.card + (E0 \ C0).card := by
    rw [← Finset.union_sdiff_self_eq_union]
    exact Finset.card_union_of_disjoint Finset.disjoint_sdiff
  have cU2 : (C0 ∪ E0).card = E0.card + (C0 \ E0).card := by
    rw [Finset.union_comm, ← Finset.union_sdiff_self_eq_union]
    exact Finset.card_union_of_disjoint Finset.disjoint_sdiff
  have cE : E0.card + 1 = E.card := Finset.card_erase_add_one hnx
  refine pcd₀_add (pcd₀_mul hC ?_) (pcd₀_mul hE ?_)
  · have h1 := totalDegree_cpoly p dec (E0 \ C0)
    have h2 := totalDegree_cpoly p dec C
    have : (p - 1) * (E0 \ C0).card + (p - 1) * C.card ≤ D := by
      rw [← Nat.mul_add]
      refine le_trans (Nat.mul_le_mul_left _ ?_) hdeg
      omega
    omega
  · have h1 := totalDegree_cpoly p dec (C0 \ E0)
    have h2 := totalDegree_cpoly p dec E
    have : (p - 1) * (C0 \ E0).card + (p - 1) * E.card ≤ D := by
      rw [← Nat.mul_add]
      refine le_trans (Nat.mul_le_mul_left _ ?_) hdeg
      omega
    omega

section Fp

variable {p : ℕ} [Fact p.Prime] [CharP F p] (hfrob : ∀ a : F, a ^ p = a)
include hfrob

theorem pow_pred_eq_one' {s : F} (hs : s ≠ 0) : s ^ (p - 1) = 1 := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have h : s ^ (p - 1) * s = 1 * s := by
    rw [← pow_succ, Nat.sub_add_cancel hp1, hfrob, one_mul]
  exact mul_right_cancel₀ hs h

/-- `(u^p - u) * R` is derivable from the Boolean axioms (Frobenius), at degree `p + deg R`. -/
theorem frob_mul {Φ : CNF} {D : ℕ} (e : LEq F) (R : MvPolynomial ℕ F)
    (hD : p + R.totalDegree ≤ D) :
    PCD₀ (cnfAx (F := F) Φ ∪ {g | ∃ i, g = X i ^ 2 - X i}) D ((eqPoly e ^ p - eqPoly e) * R) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hbool : PCD₀ (cnfAx (F := F) Φ ∪ {g | ∃ i, g = X i ^ 2 - X i}) D (X 0 ^ 2 - X 0) := by
    refine PCD₀.ax (Or.inr ⟨0, rfl⟩) ?_
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_pow _ _).trans (by rw [totalDegree_X]; omega)
    · rw [totalDegree_X]; omega
  rw [eqPoly_frob hfrob, Finset.sum_mul]
  refine pcd₀_sum _ _ (pcd₀_zero hbool) fun i _ => ?_
  rw [mul_assoc]
  refine pcd₀_smul _ ?_
  have key := pcd₀_boolMul (Ax := (∅ : Set (Finset (LEq F)))) hfrob i R hD
  refine pcd₀_transfer key ?_
  rintro g (⟨C, hC, _⟩ | ⟨j, rfl⟩) hdeg
  · exact absurd hC (Set.notMem_empty _)
  · exact PCD₀.ax (Or.inr ⟨j, rfl⟩) hdeg

end Fp


theorem qident {R : Type*} [CommRing R] (u1 u2 α β : R) (p : ℕ) (hp : 2 ≤ p) :
    (1 - u1 ^ (p - 1)) * ((1 - u2 ^ (p - 1)) * ((α * u1 + β * u2) ^ (p - 1))) =
      (-α) * ((u1 ^ p - u1) * ((1 - u2 ^ (p - 1)) * (α * u1 + β * u2) ^ (p - 2))) +
      (-β) * ((u2 ^ p - u2) * ((1 - u1 ^ (p - 1)) * (α * u1 + β * u2) ^ (p - 2))) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have e1 : q + 2 - 1 = q + 1 := rfl
  have e2 : q + 2 - 2 = q := rfl
  rw [e1, e2]
  ring

theorem qident' {R : Type*} [CommRing R] (u s : R) (p : ℕ) (hp : 2 ≤ p) :
    (1 - u ^ (p - 1)) * ((s * u) ^ (p - 1)) =
      (-s) * ((u ^ p - u) * (s * u) ^ (p - 2)) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have e1 : q + 2 - 1 = q + 1 := rfl
  have e2 : q + 2 - 2 = q := rfl
  rw [e1, e2]
  ring

theorem totalDegree_apow (e : LEq F) (n : ℕ) : (eqPoly e ^ n).totalDegree ≤ n :=
  (totalDegree_pow _ _).trans (by
    calc n * (eqPoly e).totalDegree ≤ n * 1 := Nat.mul_le_mul_left _ (totalDegree_eqPoly _)
      _ = n := by ring)

theorem totalDegree_aneg (e : LEq F) (n : ℕ) : (1 - eqPoly e ^ n).totalDegree ≤ n :=
  (totalDegree_sub _ _).trans (max_le (by simp) (totalDegree_apow e n))

section Hyps

variable {p : ℕ} [Fact p.Prime] [CharP F p] (hfrob : ∀ a : F, a ^ p = a)
  {aid : LEq F → ℕ} (haid : Function.Injective aid) {dec : ℕ → LEq F}
  (hdec : ∀ e, dec (aid e) = e)

include hdec in
theorem flit_apos (e : LEq F) : flit p dec (apos aid e) = eqPoly e ^ (p - 1) := by
  simp [flit, apos, hdec]

include hdec in
theorem flit_aneg (e : LEq F) : flit p dec (aneg aid e) = 1 - eqPoly e ^ (p - 1) := by
  simp [flit, aneg, hdec]

include haid hdec in
theorem cpoly_aCl (L : Finset (LEq F)) : cpoly p dec (aCl aid L) = clPoly L ^ (p - 1) := by
  unfold cpoly aCl clPoly
  rw [Finset.prod_image (fun a _ b _ h => apos_inj haid h), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun e _ => ?_
  exact flit_apos hdec e

include haid in
theorem aCl_card (L : Finset (LEq F)) : (aCl aid L).card = L.card :=
  Finset.card_image_of_injective _ (apos_inj haid)

omit hfrob haid hdec in
theorem pow_ax_pcd {Φ : CNF} {D : ℕ} {f : MvPolynomial ℕ F} {n : ℕ}
    (hf : PCD₀ (cnfAx (F := F) Φ ∪ {g | ∃ i, g = X i ^ 2 - X i}) D f) (hdeg : f.totalDegree ≤ n)
    (hD : (p - 1) * n ≤ D) :
    PCD₀ (cnfAx (F := F) Φ ∪ {g | ∃ i, g = X i ^ 2 - X i}) D (f ^ (p - 1)) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have : f ^ (p - 1) = f ^ (p - 2) * f := by
    rw [← pow_succ]; congr 1; omega
  rw [this]
  refine pcd₀_mul hf ?_
  have h1 : (f ^ (p - 2)).totalDegree ≤ (p - 2) * n :=
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hdeg)
  have : (p - 2) * n + n = (p - 1) * n := by
    have : p - 1 = (p - 2) + 1 := by omega
    rw [this]; ring
  omega

include hfrob haid hdec in
/-- The hypotheses of the atom translation have polynomial calculus derivations of degree
`(p-1)(w+1)` (`w ≥ 3` bounds the width of the hypothesis). -/
theorem hyp_pcd {Φ : CNF} {w : ℕ} (hw : 3 ≤ w) {X' : Clause} (hX : AtomHyp aid Φ X')
    (hXw : X'.card ≤ w) :
    PCD₀ (cnfAx (F := F) Φ ∪ {g | ∃ i, g = X i ^ 2 - X i}) ((p - 1) * (w + 1)) (cpoly p dec X') := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  cases hX with
  | phi C hC =>
    rw [cpoly_aCl haid hdec, clPoly_ofCl]
    have hs : (∏ l ∈ C, (if l.pos then (-1 : F) else 1)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun l _ => by split_ifs <;> simp
    rw [mul_pow, ← C_pow, pow_pred_eq_one' hfrob hs, C_1, one_mul]
    have hcard : C.card ≤ w := by
      have := aCl_card haid (ofCl (F := F) C)
      have h2 : (ofCl (F := F) C).card = C.card :=
        Finset.card_image_of_injective _ litEq_inj
      omega
    refine pow_ax_pcd (PCD₀.ax (Or.inl ⟨C, hC, rfl⟩) ?_)
      (totalDegree_clausePoly C) (Nat.mul_le_mul_left _ (by omega))
    exact (totalDegree_clausePoly C).trans (by
      have : C.card ≤ (p - 1) * (w + 1) := by
        have : 1 ≤ p - 1 := by omega
        nlinarith
      exact this)
  | bool i =>
    rw [cpoly_aCl haid hdec, clPoly_boolCl]
    have hax : PCD₀ (cnfAx (F := F) Φ ∪ {g | ∃ i, g = X i ^ 2 - X i}) ((p - 1) * (w + 1))
        (X i ^ 2 - X i) := by
      refine PCD₀.ax (Or.inr ⟨i, rfl⟩) ?_
      have : 1 ≤ p - 1 := by omega
      refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
      · exact (totalDegree_pow _ _).trans (by rw [totalDegree_X]; nlinarith)
      · rw [totalDegree_X]; nlinarith
    refine pow_ax_pcd hax (n := 2) ?_ (Nat.mul_le_mul_left _ (by omega))
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_pow _ _).trans (by rw [totalDegree_X])
    · rw [totalDegree_X]; omega
  | imp e1 e2 α β h31 h32 =>
    set e3 := cmb α β e1 e2 with he3
    have hu3 : eqPoly e3 = MvPolynomial.C α * eqPoly e1 + MvPolynomial.C β * eqPoly e2 :=
      eqPoly_comb e1 e2 α β
    have hDge : 4 * (p - 1) ≤ (p - 1) * (w + 1) := by nlinarith
    by_cases h12 : e1 = e2
    · subst h12
      have hset : qCl aid e1 e1 e3 = {aneg aid e1, apos aid e3} := by
        simp [qCl]
      have hne : aneg aid e1 ∉ ({apos aid e3} : Finset Literal) := by
        simp [aneg, apos]
      have hc : cpoly p dec (qCl aid e1 e1 e3) =
          (1 - eqPoly e1 ^ (p - 1)) * (eqPoly e3 ^ (p - 1)) := by
        rw [hset]; unfold cpoly
        rw [Finset.prod_insert hne, Finset.prod_singleton, flit_aneg hdec, flit_apos hdec]
      rw [hc]
      have hu : eqPoly e3 = (MvPolynomial.C (α + β)) * eqPoly e1 := by
        rw [hu3, map_add]; ring
      rw [hu, qident' _ _ p hp2]
      have hx := frob_mul hfrob (Φ := Φ) (D := (p - 1) * (w + 1)) e1
        ((MvPolynomial.C (α + β) * eqPoly e1) ^ (p - 2)) (by
          have h1 : ((MvPolynomial.C (α + β) * eqPoly e1) ^ (p - 2)).totalDegree ≤ p - 2 := by
            rw [← hu]; exact totalDegree_apow e3 _
          omega)
      have := PCD₀.lin (-(α + β)) 0 hx hx
      simpa [map_neg] using this
    · have hne1 : aneg aid e1 ∉ ({aneg aid e2, apos aid e3} : Finset Literal) := by
        simp only [mem_insert, mem_singleton, not_or]
        refine ⟨fun h => h12 (haid (congrArg Literal.var h)), ?_⟩
        simp [aneg, apos]
      have hne2 : aneg aid e2 ∉ ({apos aid e3} : Finset Literal) := by simp [aneg, apos]
      have hc : cpoly p dec (qCl aid e1 e2 e3) =
          (1 - eqPoly e1 ^ (p - 1)) * ((1 - eqPoly e2 ^ (p - 1)) * (eqPoly e3 ^ (p - 1))) := by
        unfold cpoly qCl
        rw [Finset.prod_insert hne1, Finset.prod_insert hne2, Finset.prod_singleton,
          flit_aneg hdec, flit_aneg hdec, flit_apos hdec]
      have hq := qident (eqPoly e1) (eqPoly e2) (MvPolynomial.C α) (MvPolynomial.C β) p hp2
      rw [← hu3] at hq
      rw [hc, hq]
      have hR1 : p + ((1 - eqPoly e2 ^ (p - 1)) * eqPoly e3 ^ (p - 2)).totalDegree ≤
          (p - 1) * (w + 1) := by
        have h1 := totalDegree_mul (1 - eqPoly e2 ^ (p - 1)) (eqPoly e3 ^ (p - 2))
        have h2 := totalDegree_aneg e2 (p - 1)
        have h3 := totalDegree_apow e3 (p - 2)
        omega
      have hR2 : p + ((1 - eqPoly e1 ^ (p - 1)) * eqPoly e3 ^ (p - 2)).totalDegree ≤
          (p - 1) * (w + 1) := by
        have h1 := totalDegree_mul (1 - eqPoly e1 ^ (p - 1)) (eqPoly e3 ^ (p - 2))
        have h2 := totalDegree_aneg e1 (p - 1)
        have h3 := totalDegree_apow e3 (p - 2)
        omega
      have hx1 := frob_mul hfrob (Φ := Φ) (D := (p - 1) * (w + 1)) e1 _ hR1
      have hx2 := frob_mul hfrob (Φ := Φ) (D := (p - 1) * (w + 1)) e2 _ hR2
      have := PCD₀.lin (-α) (-β) hx1 hx2
      simpa [map_neg] using this
  | unit c hc =>
    have hne : aneg aid ((0 : ℕ →₀ F), c) ∉ (∅ : Finset Literal) := by simp
    have hz : eqPoly ((0 : ℕ →₀ F), c) = MvPolynomial.C (-c) := by simp [eqPoly, linPoly]
    have : cpoly p dec (uCl aid c) = 0 := by
      unfold cpoly uCl
      rw [Finset.prod_singleton, flit_aneg hdec, hz, ← C_pow,
        pow_pred_eq_one' hfrob (neg_ne_zero.2 hc), C_1, sub_self]
    rw [this]
    refine pcd₀_zero (g := X 0 ^ 2 - X 0) ?_
    refine PCD₀.ax (Or.inr ⟨0, rfl⟩) ?_
    have : 1 ≤ p - 1 := by omega
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_pow _ _).trans (by rw [totalDegree_X]; nlinarith)
    · rw [totalDegree_X]; nlinarith

end Hyps
section Tree

variable {p : ℕ} [Fact p.Prime] [CharP F p] (hfrob : ∀ a : F, a ^ p = a)
  {aid : LEq F → ℕ} (haid : Function.Injective aid) {dec : ℕ → LEq F}
  (hdec : ∀ e, dec (aid e) = e)

include hfrob haid hdec in
/-- A tree Resolution derivation of width `w` from atom hypotheses gives a polynomial calculus
derivation of the clause polynomial of degree `(p-1)(w+1)`. -/
theorem atom_tree_pcd {Φ : CNF} {w : ℕ} (hw : 3 ≤ w) {Γ : CNF}
    (hΓ : ∀ X ∈ Γ, AtomHyp aid Φ X) {C : Clause} (d : Derivation Γ C) (hd : d.width ≤ w) :
    PCD₀ (cnfAx (F := F) Φ ∪ {g | ∃ i, g = X i ^ 2 - X i}) ((p - 1) * (w + 1))
      (cpoly p dec C) := by
  induction d with
  | hyp C hC =>
    exact hyp_pcd hfrob haid hdec hw (hΓ C hC) (by simpa [Derivation.width] using hd)
  | res x dC dD hx hnx ihC ihD =>
    simp only [Derivation.width] at hd
    refine res_step p dec (ihC ((le_max_left _ _).trans ((le_max_left _ _).trans hd)))
      (ihD ((le_max_right _ _).trans ((le_max_left _ _).trans hd))) hx hnx ?_
    exact Nat.mul_le_mul_left _ (Nat.succ_le_succ (le_trans (le_max_right _ _) hd))

include hfrob haid hdec in
/-- **Back translation (Khaniki, Lemma 4.3(2), for `d = 1`)**: a tree Resolution refutation of
width `w` of atom hypotheses gives a polynomial calculus refutation of `Φ` of degree
`(p-1)(w+1)`. -/
theorem atom_refutation_pcd {Φ : CNF} {w : ℕ} (hw : 3 ≤ w) {Γ : CNF}
    (hΓ : ∀ X ∈ Γ, AtomHyp aid Φ X) (d : Derivation Γ (∅ : Clause)) (hd : d.width ≤ w) :
    PCD (cnfAx (F := F) Φ) ((p - 1) * (w + 1)) 1 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h := atom_tree_pcd hfrob haid hdec hw hΓ d hd
  have e : cpoly p dec (∅ : Clause) = 1 := by simp [cpoly]
  rw [e] at h
  have hp1 : 1 ≤ p - 1 := by omega
  exact pcd₀_to_pcd (by nlinarith) h

end Tree

end

end RLF

end SATurday.ProofComplexity
