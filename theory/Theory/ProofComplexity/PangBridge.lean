import Theory.ProofComplexity.PangCor34
import Theory.ProofComplexity.PangHilbert
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Pang route, layer F (part 1): multilinear polynomials versus polynomials

`polyOf : ML → P` sends a term set `S` to the squarefree monomial `∏_{i ∈ S} x_i`; `ml ∘ polyOf = id`.
Modulo `C_D`, `x_i * polyOf f` equals `polyOf (shl {i} f)` (`cd_polyOf_shl`), and every polynomial
equals `polyOf (ml g)` (`cd_sub_polyOf_ml`).  `hilbert_lin` is Lemma 4.1 for the maps
`T : V_K → Y` whose kernel is closed under variables.
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.PCL MvPolynomial

namespace Pang

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime]

/-- Squarefree monomials: term set `S` goes to `∏_{i∈S} x_i`. -/
def polyOf : ML (ZMod p) →ₗ[ZMod p] PP p :=
  Finsupp.linearCombination (ZMod p) (fun S : Finset ℕ => ∏ i ∈ S, (X i : PP p))

lemma polyOf_single (S : Finset ℕ) (c : ZMod p) :
    polyOf (Finsupp.single S c) = C c * ∏ i ∈ S, (X i : PP p) := by
  simp [polyOf, MvPolynomial.smul_eq_C_mul]

lemma ml_polyOf (f : ML (ZMod p)) : PCL.ml (polyOf f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg]
  | single S c =>
    rw [polyOf_single]
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, mul_one]
      have : (C c : PP p) = MvPolynomial.monomial 0 c := rfl
      rw [this, ml_monomial]; simp
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, show (C c : PP p) * (X a * ∏ i ∈ S, X i) = X a * (C c * ∏ i ∈ S, X i) by ring,
        ml_X_mul, ih, shl_single]
      congr 1
      ext x; simp [Finset.mem_insert, ]

lemma totalDegree_polyOf_le (f : ML (ZMod p)) : (polyOf f).totalDegree ≤ PCL.deg f := by
  have : polyOf f = ∑ S ∈ f.support, C (f S) * ∏ i ∈ S, (X i : PP p) := by
    conv_lhs => rw [← Finsupp.sum_single f]
    simp only [map_sum, polyOf_single, Finsupp.sum]
  rw [this]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun S hS => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finset_prod _ _).trans ?_
  simp only [totalDegree_X, Finset.sum_const, smul_eq_mul, mul_one]
  exact PCL.le_deg hS

lemma deg_shl_le (i : ℕ) (f : ML (ZMod p)) : PCL.deg (shl {i} f) ≤ PCL.deg f + 1 := by
  refine PCL.deg_le fun U hU => ?_
  obtain ⟨T, hT, rfl⟩ := support_shl_subset {i} f U hU
  have := PCL.le_deg hT
  have h2 := Finset.card_union_le T {i}
  rw [Finset.card_singleton] at h2; omega

section Reduction
variable {Ax : Set (PP p)} {D : ℕ}

lemma cd_sub_polyOf_ml (hD : 2 ≤ D) {g : PP p} (hg : g.totalDegree ≤ D) :
    g - polyOf (PCL.ml g) ∈ CD Ax D := by
  refine cd_of_ml_eq_zero hD ?_ (by rw [map_sub, ml_polyOf, sub_self])
  refine (totalDegree_sub _ _).trans (max_le hg ((totalDegree_polyOf_le _).trans ?_))
  exact PCL.deg_le fun T hT => (card_le_totalDegree hT).trans hg

lemma cd_polyOf_shl (hD : 2 ≤ D) (u : PP p) (f : ML (ZMod p)) (i : ℕ)
    (h : u.totalDegree + PCL.deg f + 1 ≤ D) :
    u * (X i * polyOf f - polyOf (shl {i} f)) ∈ CD Ax D := by
  have hdeg : (X i * polyOf f - polyOf (shl {i} f) : PP p).totalDegree ≤ PCL.deg f + 1 := by
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_mul _ _).trans ?_
      have := totalDegree_polyOf_le f
      rw [totalDegree_X]; omega
    · exact (totalDegree_polyOf_le _).trans (deg_shl_le i f)
  have hg : (X i * polyOf f - polyOf (shl {i} f) : PP p) ∈ CD Ax D :=
    cd_of_ml_eq_zero hD (by omega) (by rw [map_sub, ml_X_mul, ml_polyOf, ml_polyOf, sub_self])
  exact cd_mul hg (by omega)

end Reduction



/-! ## Linear algebra: `dim Z' ≥ dim ker T + rank (T ∘ φ)` -/

theorem finrank_ker_add_rank_le {Dm Z Y' : Type*} [AddCommGroup Dm] [Module (ZMod p) Dm]
    [FiniteDimensional (ZMod p) Dm] [AddCommGroup Z] [Module (ZMod p) Z] [AddCommGroup Y']
    [Module (ZMod p) Y']
    (T : Dm →ₗ[ZMod p] Y') (φ : Z →ₗ[ZMod p] Dm) (Z' : Submodule (ZMod p) Dm)
    (h1 : LinearMap.ker T ≤ Z') (h2 : LinearMap.range φ ≤ Z') :
    Module.finrank (ZMod p) (LinearMap.ker T) + Module.finrank (ZMod p) (LinearMap.range (T ∘ₗ φ)) ≤
      Module.finrank (ZMod p) Z' := by
  set W : Submodule (ZMod p) Dm := LinearMap.ker T ⊔ LinearMap.range φ with hW
  have hWZ : W ≤ Z' := sup_le h1 h2
  have hrn := LinearMap.finrank_range_add_finrank_ker (T.domRestrict W)
  have hker : Module.finrank (ZMod p) (LinearMap.ker (T.domRestrict W)) =
      Module.finrank (ZMod p) (LinearMap.ker T) := by
    rw [LinearMap.ker_domRestrict]
    exact (Submodule.comapSubtypeEquivOfLe (le_sup_left : LinearMap.ker T ≤ W)).finrank_eq
  have hrange : LinearMap.range (T.domRestrict W) = LinearMap.range (T ∘ₗ φ) := by
    rw [LinearMap.range_domRestrict, LinearMap.range_comp]
    apply le_antisymm
    · rintro y ⟨w, hw, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
      refine ⟨b, hb, ?_⟩
      simp [LinearMap.mem_ker.1 ha]
    · exact Submodule.map_mono le_sup_right
  rw [hker, hrange] at hrn
  have := Submodule.finrank_mono hWZ
  omega

section VkMaps
variable (V : Finset ℕ)

lemma Vk_mono {k k' : ℕ} (h : k ≤ k') : Vk (F := ZMod p) V k ≤ Vk V k' :=
  Finsupp.supported_mono fun _ hT => ⟨hT.1, hT.2.trans h⟩

lemma mem_Vk {z : ML (ZMod p)} {k : ℕ} : z ∈ Vk V k ↔ ∀ T ∈ z.support, T ⊆ V ∧ T.card ≤ k := Iff.rfl

lemma deg_le_of_mem_Vk {z : ML (ZMod p)} {k : ℕ} (hz : z ∈ Vk V k) : PCL.deg z ≤ k :=
  PCL.deg_le fun T hT => ((mem_Vk V).1 hz T hT).2

lemma shl_mem_Vk {z : ML (ZMod p)} {K : ℕ} (hz : z ∈ Vk V K) (hdeg : PCL.deg z < K) {i : ℕ}
    (hi : i ∈ V) : shl {i} z ∈ Vk V K := by
  rw [mem_Vk]
  intro U hU
  obtain ⟨T, hT, rfl⟩ := support_shl_subset {i} z U hU
  have h1 := (mem_Vk V).1 hz T hT
  have h2 := PCL.le_deg hT
  have h3 := Finset.card_union_le T {i}
  rw [Finset.card_singleton] at h3
  exact ⟨Finset.union_subset h1.1 (by simpa using hi), by omega⟩

/-- The polynomial attached to a multilinear polynomial of degree `≤ k`. -/
def iotaV (k : ℕ) : Vk (F := ZMod p) V k →ₗ[ZMod p] PP p := polyOf ∘ₗ (Vk V k).subtype

lemma totalDegree_iotaV {k : ℕ} (x : Vk (F := ZMod p) V k) : (iotaV V k x).totalDegree ≤ k :=
  (totalDegree_polyOf_le _).trans (deg_le_of_mem_Vk V x.2)

lemma iotaV_incl {k k' : ℕ} (h : k ≤ k') (x : Vk (F := ZMod p) V k) :
    iotaV V k' (Submodule.inclusion (Vk_mono V h) x) = iotaV V k x := rfl

variable {Y : Type*} [AddCommGroup Y] [Module (ZMod p) Y]

/-- **Pang Lemma 4.1** for a linear map `T` on `V_K` whose kernel is closed under multiplication by
variables below degree `K`: the ranks `rk(k)` of `T` restricted to `V_k` satisfy
`rk(K) N(k) ≤ rk(k) N(K)`. -/
theorem hilbert_lin {K : ℕ} (T : Vk (F := ZMod p) V K →ₗ[ZMod p] Y) (hKn : K ≤ V.card)
    (hclos : ∀ (z : Vk (F := ZMod p) V K) (hz : PCL.deg z.1 < K) (i : ℕ) (hi : i ∈ V),
      T z = 0 → T ⟨shl {i} z.1, shl_mem_Vk V z.2 hz hi⟩ = 0) {k : ℕ} (hk : k ≤ K) :
    Module.finrank (ZMod p) (LinearMap.range T) * Nn V.card k ≤
      Module.finrank (ZMod p) (LinearMap.range (T ∘ₗ Submodule.inclusion (Vk_mono V hk))) *
        Nn V.card K := by
  set Z : Submodule (ZMod p) (ML (ZMod p)) := (LinearMap.ker T).map (Vk V K).subtype with hZ
  have hZg : ∀ z ∈ Z, ∀ U ∈ z.support, U ⊆ V := by
    rintro z ⟨w, _, rfl⟩ U hU
    exact ((mem_Vk V).1 w.2 U hU).1
  have hZc : ∀ z ∈ Z, ∀ i ∈ V, PCL.deg z < K → shl {i} z ∈ Z := by
    rintro z ⟨w, hw, rfl⟩ i hi hdeg
    exact ⟨⟨shl {i} w.1, shl_mem_Vk V w.2 hdeg hi⟩, hclos w hdeg i hi hw, rfl⟩
  have key := hilbert Z V hZg hZc hKn hk
  have hfin : ∀ {k'} (hk' : k' ≤ K), Module.finrank (ZMod p) ↥(Z ⊓ Vk (F := ZMod p) V k') =
      Module.finrank (ZMod p)
        (LinearMap.ker (T ∘ₗ Submodule.inclusion (Vk_mono V hk'))) := by
    intro k' hk'
    have hset : Z ⊓ Vk V k' = (LinearMap.ker (T ∘ₗ Submodule.inclusion (Vk_mono V hk'))).map
        (Vk V k').subtype := by
      ext x
      constructor
      · rintro ⟨⟨w, hw, rfl⟩, hx⟩
        exact ⟨⟨w.1, hx⟩, by simpa using hw, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨⟨Submodule.inclusion (Vk_mono V hk') y, by simpa using hy, rfl⟩, y.2⟩
    rw [hset]
    exact (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).finrank_eq.symm
  have hrank : ∀ {k'} (hk' : k' ≤ K), Module.finrank (ZMod p)
      (LinearMap.range (T ∘ₗ Submodule.inclusion (Vk_mono V hk'))) =
        Nn V.card k' - Module.finrank (ZMod p) ↥(Z ⊓ Vk (F := ZMod p) V k') := by
    intro k' hk'
    have h1 := LinearMap.finrank_range_add_finrank_ker (T ∘ₗ Submodule.inclusion (Vk_mono V hk'))
    rw [finrank_Vk] at h1
    rw [hfin hk']; omega
  have hrK := hrank (le_refl K)
  have hrk := hrank hk
  have e : T ∘ₗ Submodule.inclusion (Vk_mono V (le_refl K)) = T := by
    ext x; rfl
  rw [e] at hrK
  rw [hrK, hrk]
  exact key

end VkMaps

end

end Pang
