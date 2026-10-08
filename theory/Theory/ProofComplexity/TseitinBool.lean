import Theory.ProofComplexity.TseitinPC
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Tseitin mod q, Boolean one hot encoding (Ladder Rung R4, 1C.2b)

Transfer of the binomial degree lower bound (`TseitinPC.tseitin_pc_degree`) to the Boolean one
hot encoding of Tseitin mod `q` (variables `x_{e,j}`, "edge `e` carries `j`").

* `lag e j`: the Lagrange indicator of `y_e = ω^j` on the `q`-th roots of unity.
* `derive_grid`: a polynomial in the edge variables vanishing on all points with coordinates
  `q`-th roots of unity is derived from the axioms `y_e^q - 1` in its own degree (Alon's
  Combinatorial Nullstellensatz).

LOG: R4 TseitinBool module (Boolean Tseitin mod q)
-/

namespace SATurday.ProofComplexity

namespace TseitinPC

open Finset MvPolynomial

noncomputable section

open Classical

section Grid

variable {n : ℕ} {G : FinGraph n} {q : ℕ} [NeZero q] {K : Type} [Field K]

/-- The `q`-th roots of unity. -/
abbrev RU (K : Type) [Field K] (q : ℕ) : Finset K := Polynomial.nthRootsFinset q (1 : K)

theorem mem_RU {x : K} : x ∈ RU K q ↔ x ^ q = 1 :=
  Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero (NeZero.ne q)) 1

/-- Lagrange indicator of `y_e = ω^j` on the roots of unity. -/
def lag (ω : K) (q : ℕ) (e : G) (j : ℕ) : MvPolynomial G K :=
  ∏ r ∈ (RU K q).erase (ω ^ j), (C ((ω ^ j - r)⁻¹) * (X e - C r))

theorem eval_lag {ω : K} (hω : IsPrimitiveRoot ω q) (e : G) (j : ℕ) {y : G → K}
    (hy : y e ^ q = 1) : eval y (lag ω q e j) = if y e = ω ^ j then 1 else 0 := by
  unfold lag
  rw [map_prod]
  split_ifs with h
  · refine prod_eq_one fun r hr => ?_
    have hne : ω ^ j - r ≠ 0 := sub_ne_zero.2 (Ne.symm (ne_of_mem_erase hr))
    simp only [map_mul, eval_C, map_sub, eval_X, h]
    exact inv_mul_cancel₀ hne
  · refine prod_eq_zero (i := y e) (mem_erase.2 ⟨h, mem_RU.2 hy⟩) ?_
    simp

theorem totalDegree_lag {ω : K} (hω : IsPrimitiveRoot ω q) (e : G) (j : ℕ) :
    (lag ω q e j).totalDegree ≤ q - 1 := by
  unfold lag
  refine (totalDegree_finset_prod _ _).trans ?_
  calc ∑ r ∈ (RU K q).erase (ω ^ j), (C ((ω ^ j - r)⁻¹) * (X e - C r)).totalDegree
      ≤ ∑ r ∈ (RU K q).erase (ω ^ j), 1 := by
        refine sum_le_sum fun r _ => (totalDegree_mul _ _).trans ?_
        rw [totalDegree_C, zero_add]
        refine (totalDegree_sub _ _).trans ?_
        rw [totalDegree_X, totalDegree_C]; simp
    _ = ((RU K q).erase (ω ^ j)).card := by simp
    _ ≤ q - 1 := by
        have hm : ω ^ j ∈ RU K q := mem_RU.2 (by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one,
          one_pow])
        rw [card_erase_of_mem hm, hω.card_nthRootsFinset]

theorem totalDegree_Xq_le {σ : Type} (i : σ) : (X i ^ q - 1 : MvPolynomial σ K).totalDegree ≤ q :=
  (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X_pow]) (by simp))

theorem le_totalDegree_Xq {σ : Type} (i : σ) : q ≤ (X i ^ q - 1 : MvPolynomial σ K).totalDegree := by
  have hq : q ≠ 0 := NeZero.ne q
  have hmem : Finsupp.single i q ∈ (X i ^ q - 1 : MvPolynomial σ K).support := by
    rw [mem_support_iff, coeff_sub, coeff_X_pow, coeff_one, if_pos rfl, if_neg]
    · simp
    · intro h; exact hq (by simpa using congrArg (fun f => f i) h.symm)
  have := le_totalDegree hmem
  simpa using this

theorem Xq_ne_zero {σ : Type} (i : σ) : (X i ^ q - 1 : MvPolynomial σ K) ≠ 0 := by
  intro h
  have := le_totalDegree_Xq (K := K) (q := q) i
  rw [h, totalDegree_zero] at this
  exact NeZero.ne q (by omega)

theorem prod_RU {ω : K} (hω : IsPrimitiveRoot ω q) (e : G) :
    (∏ r ∈ RU K q, (X e - C r) : MvPolynomial G K) = X e ^ q - 1 := by
  have := congrArg (Polynomial.aeval (X e : MvPolynomial G K))
    (Polynomial.X_pow_sub_one_eq_prod (Nat.pos_of_ne_zero (NeZero.ne q)) hω)
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_prod, Polynomial.aeval_C,
    MvPolynomial.algebraMap_eq] at this
  exact this.symm

/-- **Grid lemma**: a polynomial in the edge variables vanishing on all points whose
coordinates are `q`-th roots of unity is derived from the axioms `y_e^q - 1` in its own
degree. -/
theorem derive_grid {ω : K} (hω : IsPrimitiveRoot ω q) (b : Fin n → ZMod q) {D : ℕ}
    {e0 : FinEdge n} (he0 : e0 ∈ G) (hqD : q ≤ D) (f : MvPolynomial G K)
    (hvan : ∀ y : G → K, (∀ e, y e ^ q = 1) → eval y f = 0) (hD : f.totalDegree ≤ D) :
    PCD₀ (BTAx G ω b) D (rename (fun e : G => edgeVar e.1) f) := by
  obtain ⟨h, hdeg, hf⟩ := combinatorial_nullstellensatz_exists_linearCombination
    (fun _ => RU K q) (fun _ => ⟨1, mem_RU.2 (one_pow _)⟩) f
    (fun y hy => hvan y (fun e => mem_RU.1 (hy e)))
  have hax : ∀ e : G, PCD₀ (BTAx G ω b) D (X (edgeVar e.1) ^ q - 1) := fun e =>
    PCD₀.ax (Or.inl ⟨e.1, e.2, rfl⟩) ((totalDegree_Xq_le _).trans hqD)
  have h0 := pcd₀_zero (hax ⟨e0, he0⟩)
  rw [hf, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  refine pcd₀_sum _ _ h0 fun e _ => ?_
  rw [smul_eq_mul, map_mul, prod_RU hω, map_sub, map_pow, rename_X, map_one]
  by_cases hz : h e = 0
  · rw [hz, map_zero, zero_mul]; exact h0
  · refine pcd₀_mul (hax e) ?_
    have h1 := hdeg e
    rw [prod_RU hω, totalDegree_mul_of_isDomain (Xq_ne_zero e) hz] at h1
    have h2 := le_totalDegree_Xq (K := K) (q := q) e
    have h3 := totalDegree_rename_le (fun e : G => edgeVar e.1) (h e)
    have h4 := totalDegree_Xq_le (K := K) (q := q) (edgeVar e.1)
    omega

end Grid

/-! ## The one hot CNF -/

section CNFDef

variable {n : ℕ} (G : FinGraph n) (q : ℕ) [NeZero q]

/-- Variable `x_{e,j}`: edge `e` carries value `j`. -/
def xv (e : FinEdge n) (j : ℕ) : ℕ := Nat.pair (edgeVar e) j

/-- Edge `e` carries some value. -/
def aloC (e : G) : Clause := (range q).image fun j => ⟨xv e.1 j, true⟩

/-- Edge `e` does not carry both `j` and `j'`. -/
def amoC (e : G) (j j' : ℕ) : Clause := {⟨xv e.1 j, false⟩, ⟨xv e.1 j', false⟩}

/-- Edges at `v`. -/
def incE (v : Fin n) : Finset G := univ.filter fun e => e.1 ∈ incident G v

/-- Net flow of an edge labelling at `v`. -/
def netAt (v : Fin n) (α : G → ZMod q) : ZMod q :=
  ∑ e, ((if e.1.val.1 = v then α e else 0) - (if e.1.val.2 = v then α e else 0))

/-- The labelling `α` around `v` is forbidden. -/
def vC (v : Fin n) (α : G → ZMod q) : Clause := (incE G v).image fun e => ⟨xv e.1 (α e).val, false⟩

/-- Tseitin mod `q`, Boolean one hot encoding. -/
def tcnf (b : Fin n → ZMod q) : CNF :=
  (univ.image (aloC G q)) ∪
    ((univ ×ˢ (range q ×ˢ range q)).filter (fun x : G × ℕ × ℕ => x.2.1 ≠ x.2.2)).image
      (fun x => amoC G x.1 x.2.1 x.2.2) ∪
    ((univ ×ˢ univ).filter (fun x : Fin n × (G → ZMod q) => netAt G q x.1 x.2 ≠ b x.1)).image
      (fun x => vC G q x.1 x.2)

variable {G q}

theorem mem_tcnf {b : Fin n → ZMod q} {C : Clause} (h : C ∈ tcnf G q b) :
    (∃ e, C = aloC G q e) ∨ (∃ e j j', j < q ∧ j' < q ∧ j ≠ j' ∧ C = amoC G e j j') ∨
      ∃ v α, netAt G q v α ≠ b v ∧ C = vC G q v α := by
  simp only [tcnf, mem_union, mem_image, mem_filter, mem_product, mem_univ, mem_range,
    true_and] at h
  rcases h with (⟨e, -, rfl⟩ | ⟨⟨e, j, j'⟩, ⟨⟨hj, hj'⟩, hne⟩, rfl⟩) | ⟨⟨v, α⟩, hv, rfl⟩
  · exact Or.inl ⟨e, rfl⟩
  · exact Or.inr (Or.inl ⟨e, j, j', hj, hj', hne, rfl⟩)
  · exact Or.inr (Or.inr ⟨v, α, hv, rfl⟩)

theorem xv_inj (hn : 0 < n) {e e' : FinEdge n} {j j' : ℕ} (h : xv e j = xv e' j') :
    e = e' ∧ j = j' := by
  unfold xv at h
  have := Nat.pair_eq_pair.1 h
  exact ⟨edgeVar_injective n hn this.1, this.2⟩

/-- The Boolean encoding is unsatisfiable when the total charge is nonzero. -/
theorem tcnf_unsat {b : Fin n → ZMod q} (hb : ∑ v, b v ≠ 0) : ¬ Satisfiable (tcnf G q b) := by
  rintro ⟨a, ha⟩
  have hex : ∀ e : G, ∃ j < q, a (xv e.1 j) = true := by
    intro e
    obtain ⟨l, hl, hs⟩ := ha _ (mem_union.2 (Or.inl (mem_union.2 (Or.inl
      (mem_image.2 ⟨e, mem_univ _, rfl⟩)))))
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hl
    exact ⟨j, mem_range.1 hj, hs⟩
  choose f hf hfa using hex
  set α : G → ZMod q := fun e => (f e : ZMod q)
  have hval : ∀ e, (α e).val = f e := fun e => ZMod.val_cast_of_lt (hf e)
  have hnet : ∀ v, netAt G q v α = b v := by
    intro v
    by_contra hne
    obtain ⟨l, hl, hs⟩ := ha _ (mem_union.2 (Or.inr (mem_image.2 ⟨(v, α),
      mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, mem_univ _⟩, hne⟩, rfl⟩)))
    obtain ⟨e, -, rfl⟩ := mem_image.1 hl
    simp only [litSat, hval] at hs
    rw [hfa e] at hs; cases hs
  have hsum : ∑ v, netAt G q v α = 0 := by
    unfold netAt
    rw [sum_comm]
    refine sum_eq_zero fun e _ => ?_
    rw [sum_sub_distrib, sum_ite_eq, sum_ite_eq]
    simp
  exact hb (by rw [← hsum]; exact sum_congr rfl fun v _ => (hnet v).symm)

end CNFDef

/-! ## The substitution `x_{e,j} ↦ L_j(y_e)` -/

section Subst

variable {n : ℕ} {G : FinGraph n} {q : ℕ} [NeZero q] {K : Type} [Field K]

/-- Image of a variable: the Lagrange indicator for one hot variables, `0` otherwise. -/
def sig (G : FinGraph n) (q : ℕ) (ω : K) (i : ℕ) : MvPolynomial ℕ K :=
  if h : ∃ e : G, ∃ j, j < q ∧ i = xv e.1 j then
    rename (fun e : G => edgeVar e.1) (lag ω q (Classical.choose h) (Classical.choose (Classical.choose_spec h)))
  else 0

theorem sig_xv (hn : 0 < n) (ω : K) (e : G) {j : ℕ} (hj : j < q) :
    sig G q ω (xv e.1 j) = rename (fun e : G => edgeVar e.1) (lag ω q e j) := by
  have h : ∃ e' : G, ∃ j', j' < q ∧ xv e.1 j = xv e'.1 j' := ⟨e, j, hj, rfl⟩
  unfold sig; rw [dif_pos h]
  have hs := Classical.choose_spec (Classical.choose_spec h)
  obtain ⟨he, hjj⟩ := xv_inj hn hs.2
  rw [← hjj, show Classical.choose h = e from (Subtype.ext he).symm]

theorem sig_off {ω : K} {i : ℕ} (h : ¬ ∃ e : G, ∃ j, j < q ∧ i = xv e.1 j) : sig G q ω i = 0 := by
  unfold sig; rw [dif_neg h]

theorem totalDegree_sig {ω : K} (hω : IsPrimitiveRoot ω q) (i : ℕ) :
    (sig G q ω i).totalDegree ≤ q - 1 := by
  unfold sig
  split_ifs
  · exact (totalDegree_rename_le _ _).trans (totalDegree_lag hω _ _)
  · simp

variable {F : Type} [Field F]

/-- The substitution, with coefficients mapped along `φ`. -/
def Psi (φ : F →+* K) (G : FinGraph n) (q : ℕ) (ω : K) : MvPolynomial ℕ F →+* MvPolynomial ℕ K :=
  eval₂Hom ((C : K →+* MvPolynomial ℕ K).comp φ) (sig G q ω)

theorem totalDegree_Psi {φ : F →+* K} {ω : K} (hω : IsPrimitiveRoot ω q) (f : MvPolynomial ℕ F) :
    (Psi φ G q ω f).totalDegree ≤ (q - 1) * f.totalDegree := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [Psi, eval₂Hom_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [RingHom.comp_apply, totalDegree_C, zero_add]
  unfold Finsupp.prod
  refine (totalDegree_finset_prod _ _).trans ?_
  calc ∑ i ∈ s.support, (sig G q ω i ^ s i).totalDegree ≤ ∑ i ∈ s.support, s i * (q - 1) :=
        sum_le_sum fun i _ => (totalDegree_pow _ _).trans
          (Nat.mul_le_mul_left _ (totalDegree_sig hω i))
    _ = (q - 1) * (s.sum fun _ e => e) := by rw [← sum_mul, mul_comm]; rfl
    _ ≤ (q - 1) * f.totalDegree := Nat.mul_le_mul_left _ (le_totalDegree hs)

theorem Psi_litPoly (φ : F →+* K) (ω : K) (l : Literal) :
    Psi φ G q ω (litPoly l) = if l.pos then 1 - sig G q ω l.var else sig G q ω l.var := by
  unfold litPoly; split_ifs <;> simp [Psi]

end Subst

/-! ## Simulating Boolean derivations -/

section Sim

variable {n : ℕ} {G : FinGraph n} {q : ℕ} [NeZero q] {K : Type} [Field K] {F : Type} [Field F]

theorem lag_zero_or_one {ω : K} (hω : IsPrimitiveRoot ω q) (e : G) (j : ℕ) {y : G → K}
    (hy : y e ^ q = 1) : eval y (lag ω q e j) = 0 ∨ eval y (lag ω q e j) = 1 := by
  rw [eval_lag hω e j hy]; split_ifs <;> simp

theorem card_incE_le (v : Fin n) : (incE G v).card ≤ degree G v :=
  card_le_card_of_injOn Subtype.val (fun e he => (mem_filter.1 he).2)
    (fun a _ b _ h => Subtype.ext h)

/-- The vertex binomial over the edge variables. -/
def bG (G : FinGraph n) (q : ℕ) (ω : K) (b : Fin n → ZMod q) (v : Fin n) : MvPolynomial G K :=
  (∏ e ∈ univ.filter (fun e : G => e.1.val.1 = v), X e) -
    C (pw ω (b v)) * ∏ e ∈ univ.filter (fun e : G => e.1.val.2 = v), X e

theorem monomial_lift_ind (hq : 2 ≤ q) (S : G → Prop) :
    monomial (lift (fun e : G => if S e then (1 : ZMod q) else 0)) (1 : K)
      = rename (fun e : G => edgeVar e.1) (∏ e ∈ univ.filter S, X e) := by
  haveI : Fact (1 < q) := ⟨hq⟩
  unfold lift
  rw [monomial_sum_one, map_prod, prod_filter]
  refine prod_congr rfl fun e _ => ?_
  by_cases h : S e
  · simp only [h, if_true, ZMod.val_one, rename_X]; rfl
  · simp [h]

theorem rename_bG (hq : 2 ≤ q) (ω : K) (b : Fin n → ZMod q) (v : Fin n) :
    rename (fun e : G => edgeVar e.1) (bG G q ω b v) = vertexAx G ω b v := by
  unfold bG vertexAx outV inV
  rw [map_sub, map_mul, rename_C]
  congr 1
  · convert (monomial_lift_ind (K := K) hq (fun e : G => e.1.val.1 = v)).symm
  · congr 1
    convert (monomial_lift_ind (K := K) hq (fun e : G => e.1.val.2 = v)).symm

theorem totalDegree_prod_X (T : Finset G) : (∏ e ∈ T, (X e : MvPolynomial G K)).totalDegree ≤ T.card := by
  refine (totalDegree_finset_prod _ _).trans ?_
  simp

theorem totalDegree_bG (ω : K) (b : Fin n → ZMod q) (v : Fin n) :
    (bG G q ω b v).totalDegree ≤ degree G v := by
  have hsub1 : univ.filter (fun e : G => e.1.val.1 = v) ⊆ incE G v := fun e he =>
    mem_filter.2 ⟨mem_univ _, mem_incident_iff.2 ⟨e.2, Or.inl (mem_filter.1 he).2⟩⟩
  have hsub2 : univ.filter (fun e : G => e.1.val.2 = v) ⊆ incE G v := fun e he =>
    mem_filter.2 ⟨mem_univ _, mem_incident_iff.2 ⟨e.2, Or.inr (mem_filter.1 he).2⟩⟩
  have hc := card_incE_le (G := G) v
  unfold bG
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_prod_X _).trans ((card_le_card hsub1).trans hc)
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_prod_X _).trans ((card_le_card hsub2).trans hc)

/-- **Simulation**: a degree `d` Boolean derivation from the one hot Tseitin CNF maps to a
degree `D` derivation from the binomial system. -/
theorem simulate (φ : F →+* K) {ω : K} (hω : IsPrimitiveRoot ω q) (hq : 2 ≤ q) (hn : 0 < n)
    (b : Fin n → ZMod q) {e0 : FinEdge n} (he0 : e0 ∈ G) {Δ d D : ℕ}
    (hΔ : ∀ v, degree G v ≤ Δ) (hD : (q - 1) * d + q * q + q * Δ ≤ D) :
    ∀ f, PCD (cnfAx (F := F) (tcnf G q b)) d f → PCD₀ (BTAx G ω b) D (Psi φ G q ω f) := by
  set ι : G → ℕ := fun e => edgeVar e.1
  have hqq : q ≤ q * q := Nat.le_mul_self q
  have hqD : q ≤ D := by omega
  have h0 : PCD₀ (BTAx G ω b) D 0 :=
    pcd₀_zero (PCD₀.ax (Or.inl ⟨e0, he0, rfl⟩) ((totalDegree_Xq_le _).trans hqD))
  have hvan_deg : ∀ g : MvPolynomial G K, (∀ y : G → K, (∀ e, y e ^ q = 1) → eval y g = 0) →
      g.totalDegree ≤ D → PCD₀ (BTAx G ω b) D (rename ι g) :=
    fun g hg hgd => derive_grid hω b he0 hqD g hg hgd
  intro f hf
  induction hf with
  | ax hC _ =>
    rename_i f
    obtain ⟨C, hC, rfl⟩ := hC
    unfold clausePoly
    rw [map_prod]
    rcases mem_tcnf hC with ⟨e, rfl⟩ | ⟨e, j, j', hj, hj', hne, rfl⟩ | ⟨v, α, hv, rfl⟩
    · -- at least one value
      unfold aloC
      rw [prod_image (fun x _ y _ h => (xv_inj hn (Literal.mk.inj h).1).2)]
      simp only [Psi_litPoly, if_true]
      rw [prod_congr rfl fun j hj => by rw [sig_xv hn ω e (mem_range.1 hj)]]
      have : ∏ j ∈ range q, (1 - rename ι (lag ω q e j)) = rename ι (∏ j ∈ range q, (1 - lag ω q e j)) := by
        rw [map_prod]; simp
      rw [this]
      refine hvan_deg _ (fun y hy => ?_) ?_
      · obtain ⟨i, hi, hiy⟩ := hω.eq_pow_of_pow_eq_one (hy e)
        rw [map_prod]
        refine prod_eq_zero (mem_range.2 hi) ?_
        rw [map_sub, map_one, eval_lag hω e i (hy e), if_pos hiy.symm, sub_self]
      · refine (totalDegree_finset_prod _ _).trans ?_
        calc ∑ j ∈ range q, (1 - lag ω q e j).totalDegree ≤ ∑ j ∈ range q, (q - 1) :=
              sum_le_sum fun j _ => (totalDegree_sub _ _).trans
                (max_le (by simp) (totalDegree_lag hω e j))
          _ ≤ D := by
              rw [sum_const, card_range, smul_eq_mul]
              have : q * (q - 1) ≤ q * q := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
              omega
    · -- at most one value
      unfold amoC
      have hl : (⟨xv e.1 j, false⟩ : Literal) ≠ ⟨xv e.1 j', false⟩ := fun h =>
        hne (xv_inj hn (Literal.mk.inj h).1).2
      rw [prod_pair hl]
      simp only [Psi_litPoly, Bool.false_eq_true, if_false]
      rw [sig_xv hn ω e hj, sig_xv hn ω e hj', ← map_mul]
      refine hvan_deg _ (fun y hy => ?_) ?_
      · rw [map_mul, eval_lag hω e j (hy e), eval_lag hω e j' (hy e)]
        split_ifs with h1 h2
        · exact absurd (hω.pow_inj hj hj' (h1.symm.trans h2)) hne
        all_goals simp
      · refine (totalDegree_mul _ _).trans ?_
        have := totalDegree_lag hω e j; have := totalDegree_lag hω e j'
        have : 2 * (q - 1) ≤ q * q := by
          have := Nat.mul_le_mul_right q hq; omega
        omega
    · -- vertex clause
      unfold vC
      rw [prod_image (fun x _ y _ h => Subtype.ext (xv_inj hn (Literal.mk.inj h).1).1)]
      simp only [Psi_litPoly, Bool.false_eq_true, if_false]
      rw [prod_congr rfl fun e _ => by rw [sig_xv hn ω e (ZMod.val_lt (α e))], ← map_prod]
      set P := ∏ e ∈ incE G v, lag ω q e (α e).val
      set c : K := (∏ e ∈ univ.filter (fun e : G => e.1.val.1 = v), ω ^ (α e).val) -
        pw ω (b v) * ∏ e ∈ univ.filter (fun e : G => e.1.val.2 = v), ω ^ (α e).val
      have hc : c ≠ 0 := by
        intro hc0
        apply hv
        rw [sub_eq_zero, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum, pw, ← pow_add] at hc0
        have hred : ∀ A : ℕ, ω ^ A = ω ^ (A % q) := fun A => by
          conv_lhs => rw [← Nat.div_add_mod A q, pow_add, pow_mul, hω.pow_eq_one, one_pow, one_mul]
        rw [hred, hred ((b v).val + _)] at hc0
        have hmod := hω.pow_inj (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q)))
          (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))) hc0
        have := (ZMod.natCast_eq_natCast_iff' _ _ _).2 hmod
        push_cast at this
        simp only [ZMod.natCast_zmod_val] at this
        unfold netAt
        rw [sum_sub_distrib, ← sum_filter, ← sum_filter, this]; ring
      set R := P * bG G q ω b v - C c * P
      have hP : P.totalDegree ≤ (q - 1) * Δ := by
        refine (totalDegree_finset_prod _ _).trans ?_
        calc ∑ e ∈ incE G v, (lag ω q e (α e).val).totalDegree ≤ ∑ e ∈ incE G v, (q - 1) :=
              sum_le_sum fun e _ => totalDegree_lag hω _ _
          _ = (incE G v).card * (q - 1) := by rw [sum_const, smul_eq_mul]
          _ ≤ Δ * (q - 1) := Nat.mul_le_mul_right _ ((card_incE_le v).trans (hΔ v))
          _ = (q - 1) * Δ := mul_comm _ _
      have hBd := (totalDegree_bG (G := G) ω b v).trans (hΔ v)
      have hqΔ : (q - 1) * Δ + Δ = q * Δ := by
        rw [Nat.sub_one_mul]
        have : Δ ≤ q * Δ := Nat.le_mul_of_pos_left _ (by omega)
        omega
      have hRvan : ∀ y : G → K, (∀ e, y e ^ q = 1) → eval y R = 0 := by
        intro y hy
        by_cases hall : ∀ e ∈ incE G v, y e = ω ^ (α e).val
        · have hPe : eval y P = 1 := by
            rw [map_prod]
            exact prod_eq_one fun e he => by rw [eval_lag hω e _ (hy e), if_pos (hall e he)]
          have hBe : eval y (bG G q ω b v) = c := by
            unfold bG
            simp only [map_sub, map_mul, map_prod, eval_X, eval_C, c]
            congr 1
            · exact prod_congr rfl fun e he => hall e (mem_filter.2 ⟨mem_univ _,
                mem_incident_iff.2 ⟨e.2, Or.inl (mem_filter.1 he).2⟩⟩)
            · congr 1
              exact prod_congr rfl fun e he => hall e (mem_filter.2 ⟨mem_univ _,
                mem_incident_iff.2 ⟨e.2, Or.inr (mem_filter.1 he).2⟩⟩)
          simp only [R, map_sub, map_mul, eval_C, hPe, hBe]; ring
        · push Not at hall
          obtain ⟨e, he, hne⟩ := hall
          have hPe : eval y P = 0 := by
            rw [map_prod]
            exact prod_eq_zero he (by rw [eval_lag hω e _ (hy e), if_neg hne])
          simp only [R, map_sub, map_mul, eval_C, hPe]; ring
      have hRd : R.totalDegree ≤ D := by
        refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · refine (totalDegree_mul _ _).trans ?_; nlinarith
        · refine (totalDegree_mul _ _).trans ?_; rw [totalDegree_C]; nlinarith
      have hR := hvan_deg R hRvan hRd
      have hB : PCD₀ (BTAx G ω b) D (vertexAx G ω b v) := by
        refine PCD₀.ax (Or.inr ⟨v, rfl⟩) ?_
        rw [← rename_bG hq]; exact (totalDegree_rename_le _ _).trans (by nlinarith)
      have hPB : PCD₀ (BTAx G ω b) D (rename ι P * vertexAx G ω b v) := by
        refine pcd₀_mul hB ?_
        rw [← rename_bG hq]
        have := totalDegree_rename_le ι P; have := totalDegree_rename_le ι (bG G q ω b v)
        nlinarith
      have hlin := PCD₀.lin c⁻¹ (-c⁻¹) hPB hR
      convert hlin using 1
      have hcc : (C c⁻¹ : MvPolynomial ℕ K) * C c = 1 := by rw [← C_mul, inv_mul_cancel₀ hc, C_1]
      simp only [R, map_sub, map_mul, rename_C, ← rename_bG hq (G := G) ω b v, map_neg]
      linear_combination (-(rename ι P)) * hcc
  | bool i h2 =>
    rw [map_sub, map_pow]
    simp only [Psi, coe_eval₂Hom, eval₂_X]
    by_cases hi : ∃ e : G, ∃ j, j < q ∧ i = xv e.1 j
    · obtain ⟨e, j, hj, rfl⟩ := hi
      rw [sig_xv hn ω e hj, ← map_pow, ← map_sub]
      refine hvan_deg _ (fun y hy => ?_) ?_
      · rcases lag_zero_or_one hω e j (hy e) with h | h <;> simp [h]
      · refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · refine (totalDegree_pow _ _).trans ?_; have := totalDegree_lag hω e j; nlinarith
        · have := totalDegree_lag hω e j; nlinarith
    · rw [sig_off hi]; simpa using h0
  | lin a c _ _ ihf ihg =>
    simp only [map_add, map_mul, Psi, coe_eval₂Hom, eval₂_C, RingHom.coe_comp, Function.comp] at ihf ihg ⊢
    exact PCD₀.lin (φ a) (φ c) ihf ihg
  | mul i hg hdg ih =>
    rename_i g
    rw [map_mul]
    by_cases hg0 : g = 0
    · rw [hg0, map_zero, mul_zero]; exact h0
    · have hdeg : g.totalDegree + 1 ≤ d := by
        rw [totalDegree_mul_of_isDomain (X_ne_zero i) hg0, totalDegree_X] at hdg; omega
      refine pcd₀_mul ih ?_
      have h1 : Psi φ G q ω (X i) = sig G q ω i := by simp [Psi]
      rw [h1]
      have h2 := totalDegree_sig (G := G) hω i
      have h3 := totalDegree_Psi (G := G) (φ := φ) hω g
      have h4 : (q - 1) * g.totalDegree ≤ (q - 1) * (d - 1) := Nat.mul_le_mul_left _ (by omega)
      have h5 : (q - 1) + (q - 1) * (d - 1) = (q - 1) * d := by
        rw [Nat.mul_sub_one]
        have : q - 1 ≤ (q - 1) * d := Nat.le_mul_of_pos_right _ (by omega)
        omega
      omega

end Sim

/-! ## The lower bound for the Boolean encoding -/

section Final

variable {n : ℕ} {G : FinGraph n} {q : ℕ} [NeZero q]

/-- **Tseitin mod `q`, one hot encoding**: no degree `d` polynomial calculus refutation (with
Boolean axioms) over `F`, given an extension `φ : F → K` with a primitive `q`-th root of unity,
expansion `k`, maximum degree `Δ` and `8 k ((q-1) d + q² + q Δ) + 2 ≤ n`. -/
theorem tseitin_bool_degree {F K : Type} [Field F] [Field K] (φ : F →+* K) {ω : K}
    (hω : IsPrimitiveRoot ω q) (hq : 2 ≤ q) (hn : 0 < n) {k : ℕ} (hG : HasExpansionInv G k)
    (b : Fin n → ZMod q) {e0 : FinEdge n} (he0 : e0 ∈ G) {Δ d : ℕ} (hΔ : ∀ v, degree G v ≤ Δ)
    (h8 : 8 * k * ((q - 1) * d + q * q + q * Δ) + 2 ≤ n) :
    ¬ PCD (cnfAx (F := F) (tcnf G q b)) d 1 := by
  intro h
  have := simulate φ hω hq hn b he0 hΔ le_rfl 1 h
  rw [map_one] at this
  refine tseitin_pc_degree hn hG hω.pow_eq_one h8 (fun v => (hΔ v).trans ?_) this
  have : Δ ≤ q * Δ := Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- **Over `F_p`, on cubic expanders**: for primes `p ∤ q` (`q ≥ 2`) and every `N` there is a
cubic graph on `n ≥ N` vertices such that, for every charge, the one hot Tseitin mod `q` CNF has
no degree `((n - 2) / 1312 - q (q + 3)) / (q - 1)` polynomial calculus refutation over
`ZMod p`. -/
theorem tseitin_bool_degree_Fp (p : ℕ) [Fact p.Prime] (hq : 2 ≤ q) (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ ∀ b : Fin n → ZMod q,
      ¬ PCD (cnfAx (F := ZMod p) (tcnf G q b)) (((n - 2) / 1312 - q * (q + 3)) / (q - 1)) 1 := by
  obtain ⟨n, G, hN, hreg, hconn, hexp⟩ :=
    exists_mggF2Cub_hasExpansionInv_family (max N (4000 + 1312 * (q * (q + 3)) + 2))
  refine ⟨n, G, le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN), hreg, fun b => ?_⟩
  have hn : 4000 + 1312 * (q * (q + 3)) + 2 ≤ n :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  haveI : NeZero ((q : ℕ) : ZMod p) := ⟨fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)⟩
  haveI : IsCyclotomicExtension {q} (ZMod p) (CyclotomicField q (ZMod p)) :=
    CyclotomicField.isCyclotomicExtension q (ZMod p)
  have hω := IsCyclotomicExtension.zeta_spec q (ZMod p) (CyclotomicField q (ZMod p))
  -- an edge exists: vertex `0` has degree 3
  have hdeg0 := hreg ⟨0, by omega⟩
  obtain ⟨e0, he0⟩ : (incident G ⟨0, by omega⟩).Nonempty := by
    rw [← card_pos]; unfold degree at hdeg0; omega
  have he0G : e0 ∈ G := (mem_incident_iff.1 he0).1
  have hk : mggF2CubK = 164 := rfl
  set d := ((n - 2) / 1312 - q * (q + 3)) / (q - 1)
  refine tseitin_bool_degree (algebraMap (ZMod p) (CyclotomicField q (ZMod p))) hω hq (by omega) hexp b he0G
    (Δ := 3) (fun v => (hreg v).le) ?_
  rw [hk]
  have h1 : (q - 1) * d ≤ (n - 2) / 1312 - q * (q + 3) := by
    have := Nat.div_mul_le_self ((n - 2) / 1312 - q * (q + 3)) (q - 1)
    rw [mul_comm]; exact this
  have h2 : (n - 2) / 1312 * 1312 ≤ n - 2 := Nat.div_mul_le_self _ _
  have h3 : q * q + q * 3 = q * (q + 3) := by ring
  have hX : q * (q + 3) ≤ (n - 2) / 1312 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 1312), mul_comm]
    omega
  omega

end Final

end

end TseitinPC

end SATurday.ProofComplexity
