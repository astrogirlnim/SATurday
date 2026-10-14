import Theory.ProofComplexity.PCReduction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Pang route, layer E: monotonicity of the normalized rank (Lemma 4.1 "hilbert")

For a subspace `Z` of the multilinear polynomials in `n` variables that is closed under
multiplication by variables below degree `K`, the number of irreducible terms (a basis of the
quotient) of degree at most `k`, divided by `N_n(k) = ∑_{j ≤ k} C(n, j)`, is nonincreasing in
`k ≤ K`.  Only the term order of `PCReduction` is used.
-/

open SATurday.ProofComplexity
open SATurday.ProofComplexity.PCL

namespace Pang

noncomputable section
open Classical Finset

variable {F : Type} [Field F]

lemma enc_insert {i : ℕ} {U : Finset ℕ} (h : i ∉ U) : enc (insert i U) = enc U + 2 ^ i := by
  unfold enc; rw [Finset.sum_insert h]; ring

/-- Adding a new variable keeps the term order. -/
lemma key_insert_le {i : ℕ} {U S : Finset ℕ} (hS : i ∉ S) (h : key U ≤ key S) :
    key (U ∪ {i}) ≤ key (insert i S) := by
  by_cases hU : i ∈ U
  · have : U ∪ {i} = U := by ext x; simp; intro hx; rw [hx]; exact hU
    rw [this]
    refine h.trans (key_lt_of_card_lt ?_).le
    rw [Finset.card_insert_of_notMem hS]; omega
  · have e : U ∪ {i} = insert i U := by ext x; simp
    rw [e]
    unfold key at h ⊢
    rw [Prod.Lex.toLex_le_toLex] at h ⊢
    rw [Finset.card_insert_of_notMem hU, Finset.card_insert_of_notMem hS, enc_insert hU, enc_insert hS]
    rcases h with h | ⟨h1, h2⟩
    · left; omega
    · right; exact ⟨by omega, by omega⟩

/-- The leading term of `x_i z` is `S ∪ {i}` when `S` leads `z` and `i ∉ S`. -/
lemma shl_leading {z : ML F} {S : Finset ℕ} {i : ℕ} (hi : i ∉ S) (hS : S ∈ z.support)
    (hmax : ∀ U ∈ z.support, key U ≤ key S) :
    insert i S ∈ (shl {i} z).support ∧ ∀ U ∈ (shl {i} z).support, key U ≤ key (insert i S) := by
  constructor
  · rw [Finsupp.mem_support_iff]
    have hcoef : (shl {i} z) (insert i S) = z S := by
      have : (shl {i} z) = Finsupp.mapDomain (· ∪ {i}) z := rfl
      rw [this, Finsupp.mapDomain, Finsupp.sum, Finsupp.finset_sum_apply]
      simp only [Finsupp.single_apply]
      rw [Finset.sum_eq_single S]
      · have : S ∪ {i} = insert i S := by ext x; simp
        simp [this]
      · intro U hU hne
        rw [if_neg]
        intro h
        have hmem : (U ∪ {i}) = insert i S := h
        by_cases hUi : i ∈ U
        · have : U = insert i S := by
            have : U ∪ {i} = U := by ext x; simp; intro hx; rw [hx]; exact hUi
            rw [← hmem, this]
          have h1 := hmax U hU
          rw [this] at h1
          have := key_lt_of_card_lt (show S.card < (insert i S).card by
            rw [Finset.card_insert_of_notMem hi]; omega)
          exact absurd h1 (not_le.2 this)
        · apply hne
          have : insert i U = insert i S := by rw [← hmem]; ext x; simp
          have h2 := congrArg (fun T => T.erase i) this
          simpa [Finset.erase_insert hUi, Finset.erase_insert hi] using h2
      · intro h; exact absurd hS h
    rw [hcoef]; exact Finsupp.mem_support_iff.1 hS
  · intro U hU
    obtain ⟨V, hV, rfl⟩ := support_shl_subset {i} z U hU
    exact key_insert_le hi (hmax V hV)


lemma shl_empty (z : ML F) : shl ∅ z = z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, hf, hg]
  | single T c => rw [shl_single]; simp

lemma shl_shl (s t : Finset ℕ) (z : ML F) : shl t (shl s z) = shl (s ∪ t) z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | single T c =>
    rw [shl_single, shl_single, shl_single, Finset.union_assoc]

/-- Multiplying a leading-term element by variables below degree `K` stays in `Z`. -/
lemma shl_closed (Z : Submodule F (ML F)) {V : Finset ℕ} {K : ℕ}
    (hZ : ∀ z ∈ Z, ∀ i ∈ V, deg z < K → shl {i} z ∈ Z)
    {z : ML F} (hz : z ∈ Z) {S : Finset ℕ} (hS : S ∈ z.support)
    (hmax : ∀ U ∈ z.support, key U ≤ key S) :
    ∀ R : Finset ℕ, R ⊆ V → Disjoint R S → (S ∪ R).card ≤ K →
      shl R z ∈ Z ∧ (S ∪ R) ∈ (shl R z).support ∧
        ∀ U ∈ (shl R z).support, key U ≤ key (S ∪ R) := by
  intro R
  induction R using Finset.induction_on with
  | empty =>
    intro _ _ _
    rw [shl_empty]; simp only [Finset.union_empty]; exact ⟨hz, hS, hmax⟩
  | insert i R' hi ih =>
    intro hR hdis hK
    have hR' : R' ⊆ V := (Finset.subset_insert _ _).trans hR
    have hdis' : Disjoint R' S := Disjoint.mono_left (Finset.subset_insert _ _) hdis
    have hiS : i ∉ S := fun h => Finset.disjoint_left.1 hdis (Finset.mem_insert_self _ _) h
    have hK' : (S ∪ R').card ≤ K := by
      refine le_trans (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl S) (Finset.subset_insert _ _))) hK
    obtain ⟨hm, hs, hx⟩ := ih hR' hdis' hK'
    have hnotin : i ∉ S ∪ R' := by simp [hiS, hi]
    have hcard : (S ∪ insert i R').card = (S ∪ R').card + 1 := by
      rw [Finset.union_insert, Finset.card_insert_of_notMem hnotin]
    have hdeg : deg (shl R' z) < K := by
      rw [← card_of_leading hs hx]; omega
    have hlt : i ∈ V := hR (Finset.mem_insert_self _ _)
    have hm' := hZ _ hm i hlt hdeg
    obtain ⟨hs', hx'⟩ := shl_leading hnotin hs hx
    have e : shl {i} (shl R' z) = shl (insert i R') z := by
      rw [shl_shl]; congr 1; ext x; simp
    rw [e] at hm' hs' hx'
    have e2 : insert i (S ∪ R') = S ∪ insert i R' := by rw [Finset.union_insert]
    rw [e2] at hs' hx'
    exact ⟨hm', hs', hx'⟩

/-- Irreducible terms form a down-closed family (up to degree `K`). -/
lemma irr_of_subset (Z : Submodule F (ML F)) {V : Finset ℕ} {K : ℕ}
    (hZ : ∀ z ∈ Z, ∀ i ∈ V, deg z < K → shl {i} z ∈ Z) {T S : Finset ℕ}
    (hT : T ⊆ V) (hTK : T.card ≤ K) (hirr : Irr Z T) (hST : S ⊆ T) : Irr Z S := by
  rintro ⟨z, hz, hS, hmax⟩
  have hdis : Disjoint (T \ S) S := Finset.sdiff_disjoint
  have hU : S ∪ (T \ S) = T := Finset.union_sdiff_of_subset hST
  obtain ⟨hm, hs, hx⟩ := shl_closed Z hZ hz hS hmax (T \ S)
    ((Finset.sdiff_subset).trans hT) hdis (by rw [hU]; exact hTK)
  rw [hU] at hs hx
  exact hirr ⟨_, hm, hs, hx⟩


/-! ## Dimension count -/

/-- Multilinear polynomials in the first `n` variables of degree at most `k`. -/
def Vk (V : Finset ℕ) (k : ℕ) : Submodule F (ML F) :=
  Finsupp.supported F F {T : Finset ℕ | T ⊆ V ∧ T.card ≤ k}

/-- The irreducible terms of degree `≤ k` in the first `n` variables. -/
def irrK (Z : Submodule F (ML F)) (V : Finset ℕ) (k : ℕ) : Finset (Finset ℕ) :=
  (V).powerset.filter fun T => T.card ≤ k ∧ Irr Z T

/-- The number of terms of degree `≤ k` in `n` variables. -/
def Nn (n k : ℕ) : ℕ := ∑ j ∈ range (k + 1), n.choose j

lemma terms_card (V : Finset ℕ) (k : ℕ) :
    ((V).powerset.filter fun T : Finset ℕ => T.card ≤ k).card = Nn V.card k := by
  unfold Nn
  rw [Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := range (k + 1))]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have : ((V).powerset.filter fun T : Finset ℕ => T.card ≤ k).filter (fun T => T.card = j)
        = powersetCard j (V) := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        refine ⟨⟨h1, ?_⟩, h3⟩
        have := Finset.mem_range.1 hj; omega
    rw [this, Finset.card_powersetCard]
  · intro T hT
    have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hT)).2
    rw [Finset.mem_coe, Finset.mem_range]; omega

lemma finrank_Vk (V : Finset ℕ) (k : ℕ) : Module.finrank F (Vk (F := F) V k) = Nn V.card k := by
  let S : Finset (Finset ℕ) := (V).powerset.filter fun T => T.card ≤ k
  have hS : {T : Finset ℕ | T ⊆ V ∧ T.card ≤ k} = (S : Set (Finset ℕ)) := by
    ext T; simp [S]
  unfold Vk
  rw [hS]
  rw [(Finsupp.supportedEquivFinsupp (M := F) (R := F) (S : Set (Finset ℕ))).finrank_eq]
  simp [terms_card, S]

instance (V : Finset ℕ) (k : ℕ) : FiniteDimensional F (Vk (F := F) V k) := by
  unfold Vk
  let S : Finset (Finset ℕ) := (V).powerset.filter fun T => T.card ≤ k
  have hS : {T : Finset ℕ | T ⊆ V ∧ T.card ≤ k} = (S : Set (Finset ℕ)) := by
    ext T; simp [S]
  rw [hS]
  exact LinearEquiv.finiteDimensional (Finsupp.supportedEquivFinsupp (M := F) (R := F) (S : Set (Finset ℕ))).symm


section Decomp
variable (Z : Submodule F (ML F)) {V : Finset ℕ}

lemma rdc_card_le_of {g : ML F} {k : ℕ} (hg : ∀ U ∈ g.support, U.card ≤ k) :
    ∀ T ∈ (rdc Z g).support, T.card ≤ k := by
  have h2 : rdc Z g = ∑ U ∈ g.support, rdc Z (Finsupp.single U (g U)) := by
    conv_lhs => rw [← Finsupp.sum_single g]
    simp [Finsupp.sum, map_sum]
  intro T hT
  rw [h2] at hT
  obtain ⟨U, hU, hTU⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hT)
  exact (rdc_card_le Z U (g U) T hTU).trans (hg U hU)

lemma finrank_Vk_split (hZg : ∀ z ∈ Z, ∀ T ∈ z.support, T ⊆ V) (k : ℕ) :
    Module.finrank F (Vk (F := F) V k) =
      Module.finrank F ↥(Z ⊓ Vk (F := F) V k) + (irrK Z V k).card := by
  set A : Submodule F (ML F) := Z ⊓ Vk V k with hA
  set B : Submodule F (ML F) := Finsupp.supported F F (irrK Z V k : Set (Finset ℕ)) with hB
  have hBV : B ≤ Vk V k := by
    refine Finsupp.supported_mono fun T hT => ?_
    simp only [irrK, Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq] at hT
    exact ⟨hT.1, hT.2.1⟩
  have hAV : A ≤ Vk V k := inf_le_right
  haveI : FiniteDimensional F A := Submodule.finiteDimensional_of_le hAV
  haveI : FiniteDimensional F B := Submodule.finiteDimensional_of_le hBV
  have hsup : A ⊔ B = Vk V k := by
    refine le_antisymm (sup_le hAV hBV) fun g hg => ?_
    have hgs : ∀ T ∈ g.support, T ⊆ V ∧ T.card ≤ k := fun T hT => hg hT
    have hspec := rdc_spec Z g
    have hr : rdc Z g ∈ B := by
      intro T hT
      have hcard := rdc_card_le_of Z (fun U hU => (hgs U hU).2) T hT
      have hgr : g - rdc Z g ∈ Z := hspec.mem
      have hground : T ⊆ V := by
        have : rdc Z g = g - (g - rdc Z g) := by abel
        rw [this] at hT
        rcases Finset.mem_union.1 (Finsupp.support_sub hT) with h | h
        · exact (hgs T h).1
        · exact hZg _ hgr T h
      simp only [irrK, Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq]
      exact ⟨hground, hcard, hspec.irr T hT⟩
    have hgm : g - rdc Z g ∈ A := by
      refine ⟨hspec.mem, ?_⟩
      intro T hT
      rcases Finset.mem_union.1 (Finsupp.support_sub hT) with h | h
      · exact hg h
      · exact hBV hr h
    have : g = (g - rdc Z g) + rdc Z g := by abel
    rw [this]
    exact Submodule.add_mem_sup hgm hr
  have hinf : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro z ⟨⟨hzZ, _⟩, hzB⟩
    by_contra hz
    have hz0 : z ≠ 0 := hz
    obtain ⟨U0, hU0, hmax⟩ := Finset.exists_max_image z.support key
      (Finsupp.support_nonempty_iff.2 hz0)
    have hirr : U0 ∈ (irrK Z V k : Set (Finset ℕ)) := hzB hU0
    simp only [irrK, Finset.coe_filter, Set.mem_setOf_eq] at hirr
    exact hirr.2.2 ⟨z, hzZ, hU0, hmax⟩
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hsup, hinf, finrank_bot, add_zero] at h1
  have h2 : Module.finrank F B = (irrK Z V k).card := by
    rw [hB, (Finsupp.supportedEquivFinsupp (M := F) (R := F) (irrK Z V k : Set (Finset ℕ))).finrank_eq]
    simp
  rw [h1, h2]

end Decomp


section Count
variable (Z : Submodule F (ML F)) (V : Finset ℕ)

/-- Number of irreducible terms of exact degree `j`. -/
def bb (j : ℕ) : ℕ := ((powersetCard j (V)).filter (Irr Z)).card

lemma irrK_succ (k : ℕ) : (irrK Z V (k + 1)).card = (irrK Z V k).card + bb Z V (k + 1) := by
  unfold bb
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext T
    simp only [irrK, Finset.mem_union, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases h : T.card ≤ k
      · exact Or.inl ⟨h1, h, h3⟩
      · exact Or.inr ⟨⟨h1, by omega⟩, h3⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨h1, by omega, h3⟩
      · exact ⟨h1, by omega, h3⟩
  · rw [Finset.disjoint_left]
    intro T h1 h2
    simp only [irrK, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard] at h1 h2
    omega

lemma irrK_zero : (irrK Z V 0).card = bb Z V 0 := by
  unfold bb
  congr 1
  ext T
  simp only [irrK, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by omega, h3⟩

lemma irrK_sum (k : ℕ) : (irrK Z V k).card = ∑ j ∈ range (k + 1), bb Z V j := by
  induction k with
  | zero => simp [irrK_zero]
  | succ k ih => rw [irrK_succ, ih, Finset.sum_range_succ _ (k + 1)]

/-- The double counting inequality `(j+1) b_{j+1} ≤ (n-j) b_j`. -/
lemma count_ineq {K : ℕ} (hZ : ∀ z ∈ Z, ∀ i ∈ V, deg z < K → shl {i} z ∈ Z) {j : ℕ}
    (hK : j + 1 ≤ K) : (j + 1) * bb Z V (j + 1) ≤ (V.card - j) * bb Z V j := by
  set s := (powersetCard (j + 1) (V)).filter (Irr Z) with hs
  set t := (powersetCard j (V)).filter (Irr Z) with ht
  have h1 : ∀ T ∈ s, j + 1 ≤ (t.bipartiteAbove (fun T S => S ⊆ T) T).card := by
    intro T hT
    simp only [hs, Finset.mem_filter, Finset.mem_powersetCard] at hT
    obtain ⟨⟨hTn, hTc⟩, hTirr⟩ := hT
    have : T.card ≤ (t.bipartiteAbove (fun T S => S ⊆ T) T).card := by
      refine Finset.card_le_card_of_injOn (fun x => T.erase x) ?_ ?_
      · intro x hx
        have hx' : x ∈ T := hx
        rw [Finset.mem_coe, Finset.mem_bipartiteAbove]
        refine ⟨?_, Finset.erase_subset _ _⟩
        rw [ht, Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨(Finset.erase_subset _ _).trans hTn, ?_⟩, ?_⟩
        · rw [Finset.card_erase_of_mem hx']; omega
        · exact irr_of_subset Z hZ hTn (by omega) hTirr (Finset.erase_subset _ _)
      · intro x hx y hy hxy
        have hx' : x ∈ T := hx
        have hy' : y ∈ T := hy
        have hxy' : T.erase x = T.erase y := hxy
        by_contra hne
        have : x ∈ T.erase y := Finset.mem_erase.2 ⟨hne, hx'⟩
        rw [← hxy'] at this
        simp at this
    omega
  have h2 : ∀ S ∈ t, (s.bipartiteBelow (fun T S => S ⊆ T) S).card ≤ V.card - j := by
    intro S hS
    simp only [ht, Finset.mem_filter, Finset.mem_powersetCard] at hS
    obtain ⟨⟨hSn, hSc⟩, _⟩ := hS
    have hsub : s.bipartiteBelow (fun T S => S ⊆ T) S ⊆ (V \ S).image (fun x => insert x S) := by
      intro T hT
      simp only [Finset.mem_bipartiteBelow, hs, Finset.mem_filter, Finset.mem_powersetCard] at hT
      obtain ⟨⟨⟨hTn, hTc⟩, _⟩, hST⟩ := hT
      have hc : (T \ S).card = 1 := by rw [Finset.card_sdiff_of_subset hST]; omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hc
      rw [Finset.mem_image]
      refine ⟨x, ?_, ?_⟩
      · have hxT : x ∈ T \ S := by rw [hx]; simp
        rw [Finset.mem_sdiff] at hxT ⊢
        exact ⟨Finset.mem_of_subset hTn hxT.1, hxT.2⟩
      · have hxy : ∀ y, y ∈ T \ S ↔ y = x := by intro y; rw [hx]; simp
        ext y
        rw [Finset.mem_insert]
        constructor
        · rintro (rfl | h)
          · exact ((Finset.mem_sdiff.1 ((hxy _).2 rfl)).1)
          · exact hST h
        · intro h
          by_cases h' : y ∈ S
          · exact Or.inr h'
          · exact Or.inl ((hxy y).1 (Finset.mem_sdiff.2 ⟨h, h'⟩))
    calc _ ≤ ((V \ S).image (fun x => insert x S)).card := Finset.card_le_card hsub
      _ ≤ (V \ S).card := Finset.card_image_le
      _ = V.card - j := by rw [Finset.card_sdiff_of_subset hSn]; simp [hSc]
  have := Finset.card_mul_le_card_mul (fun T S => S ⊆ T) h1 h2
  show (j + 1) * s.card ≤ (V.card - j) * t.card
  rw [mul_comm (j + 1), mul_comm (V.card - j)]; exact this

end Count


section Arith
variable (Z : Submodule F (ML F)) (V : Finset ℕ)

lemma step_b {K : ℕ} (hZ : ∀ z ∈ Z, ∀ i ∈ V, deg z < K → shl {i} z ∈ Z) {j : ℕ}
    (hK : j + 1 ≤ K) :
    bb Z V (j + 1) * V.card.choose j ≤ bb Z V j * V.card.choose (j + 1) := by
  have h := count_ineq Z V hZ hK
  have hc : V.card.choose (j + 1) * (j + 1) = V.card.choose j * (V.card - j) := Nat.choose_succ_right_eq V.card j
  refine Nat.le_of_mul_le_mul_left (c := j + 1) ?_ (Nat.succ_pos j)
  calc (j + 1) * (bb Z V (j + 1) * V.card.choose j) = ((j + 1) * bb Z V (j + 1)) * V.card.choose j := by ring
    _ ≤ ((V.card - j) * bb Z V j) * V.card.choose j := Nat.mul_le_mul_right _ h
    _ = bb Z V j * (V.card.choose j * (V.card - j)) := by ring
    _ = bb Z V j * (V.card.choose (j + 1) * (j + 1)) := by rw [hc]
    _ = (j + 1) * (bb Z V j * V.card.choose (j + 1)) := by ring

lemma chain_b {K : ℕ} (hZ : ∀ z ∈ Z, ∀ i ∈ V, deg z < K → shl {i} z ∈ Z) (hKn : K ≤ V.card) :
    ∀ d j, j + d ≤ K → bb Z V (j + d) * V.card.choose j ≤ bb Z V j * V.card.choose (j + d) := by
  intro d
  induction d with
  | zero => intro j _; simp
  | succ d ih =>
    intro j hj
    have h1 := ih (j + 1) (by omega)
    have h2 := step_b Z V hZ (j := j) (by omega)
    have hpos : 0 < V.card.choose (j + 1) := Nat.choose_pos (by omega)
    have e : j + (d + 1) = j + 1 + d := by omega
    rw [e]
    refine Nat.le_of_mul_le_mul_right (c := V.card.choose (j + 1)) ?_ hpos
    calc bb Z V (j + 1 + d) * V.card.choose j * V.card.choose (j + 1)
        = (bb Z V (j + 1 + d) * V.card.choose (j + 1)) * V.card.choose j := by ring
      _ ≤ (bb Z V (j + 1) * V.card.choose (j + 1 + d)) * V.card.choose j := Nat.mul_le_mul_right _ h1
      _ = (bb Z V (j + 1) * V.card.choose j) * V.card.choose (j + 1 + d) := by ring
      _ ≤ (bb Z V j * V.card.choose (j + 1)) * V.card.choose (j + 1 + d) := Nat.mul_le_mul_right _ h2
      _ = bb Z V j * V.card.choose (j + 1 + d) * V.card.choose (j + 1) := by ring

lemma Nn_succ (k : ℕ) : Nn V.card (k + 1) = Nn V.card k + V.card.choose (k + 1) := by
  unfold Nn; rw [Finset.sum_range_succ _ (k + 1)]

lemma Nn_pos (k : ℕ) : 0 < Nn V.card k := by
  unfold Nn
  exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, by simp, by simp⟩

/-- One step of the monotonicity of the normalized rank: `c(k+1)/N(k+1) ≤ c(k)/N(k)`. -/
theorem normalized_rank_step {K : ℕ} (hZ : ∀ z ∈ Z, ∀ i ∈ V, deg z < K → shl {i} z ∈ Z)
    (hKn : K ≤ V.card) {k : ℕ} (hk : k + 1 ≤ K) :
    (irrK Z V (k + 1)).card * Nn V.card k ≤ (irrK Z V k).card * Nn V.card (k + 1) := by
  rw [irrK_succ, Nn_succ]
  have key : bb Z V (k + 1) * Nn V.card k ≤ (irrK Z V k).card * V.card.choose (k + 1) := by
    unfold Nn
    rw [irrK_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have := chain_b Z V hZ hKn (k + 1 - j) j (by omega)
    rw [show j + (k + 1 - j) = k + 1 by omega] at this
    exact this
  nlinarith [key]

/-- **Pang Lemma 4.1 ("hilbert")**: for `k ≤ K`, `c(K) N(k) ≤ c(k) N(K)`, i.e. the normalized rank
`c(k)/N_n(k)` is nonincreasing, where `c(k)` counts the irreducible terms of degree `≤ k`. -/
theorem normalized_rank_antitone {K : ℕ} (hZ : ∀ z ∈ Z, ∀ i ∈ V, deg z < K → shl {i} z ∈ Z)
    (hKn : K ≤ V.card) : ∀ d k, k + d ≤ K →
      (irrK Z V (k + d)).card * Nn V.card k ≤ (irrK Z V k).card * Nn V.card (k + d) := by
  intro d
  induction d with
  | zero => intro k _; simp
  | succ d ih =>
    intro k hk
    have h1 := ih (k + 1) (by omega)
    have h2 := normalized_rank_step Z V hZ hKn (k := k) (by omega)
    have e : k + (d + 1) = k + 1 + d := by omega
    rw [e]
    refine Nat.le_of_mul_le_mul_right (c := Nn V.card (k + 1)) ?_ (Nn_pos V _)
    calc (irrK Z V (k + 1 + d)).card * Nn V.card k * Nn V.card (k + 1)
        = ((irrK Z V (k + 1 + d)).card * Nn V.card (k + 1)) * Nn V.card k := by ring
      _ ≤ ((irrK Z V (k + 1)).card * Nn V.card (k + 1 + d)) * Nn V.card k := Nat.mul_le_mul_right _ h1
      _ = ((irrK Z V (k + 1)).card * Nn V.card k) * Nn V.card (k + 1 + d) := by ring
      _ ≤ ((irrK Z V k).card * Nn V.card (k + 1)) * Nn V.card (k + 1 + d) := Nat.mul_le_mul_right _ h2
      _ = (irrK Z V k).card * Nn V.card (k + 1 + d) * Nn V.card (k + 1) := by ring

end Arith


section Final
variable (Z : Submodule F (ML F)) (V : Finset ℕ)

lemma card_irrK_add (hZg : ∀ z ∈ Z, ∀ T ∈ z.support, T ⊆ V) (k : ℕ) :
    (irrK Z V k).card + Module.finrank F ↥(Z ⊓ Vk (F := F) V k) = Nn V.card k := by
  have := finrank_Vk_split Z hZg k
  rw [finrank_Vk] at this
  omega

/-- **Pang Lemma 4.1** in dimension form.  `Z` is a subspace of the multilinear polynomials in `n`
variables, closed under multiplication by a variable below degree `K ≤ n`.  With
`c(k) = N_n(k) - dim (Z ∩ V_k)` (the rank of any map on `V_k` with kernel `Z ∩ V_k`), for
`k ≤ K` we have `c(K) N_n(k) ≤ c(k) N_n(K)`, i.e. `c(k)/N_n(k)` is nonincreasing. -/
theorem hilbert {K : ℕ} (hZg : ∀ z ∈ Z, ∀ T ∈ z.support, T ⊆ V)
    (hZ : ∀ z ∈ Z, ∀ i ∈ V, deg z < K → shl {i} z ∈ Z) (hKn : K ≤ V.card) {k : ℕ} (hk : k ≤ K) :
    (Nn V.card K - Module.finrank F ↥(Z ⊓ Vk (F := F) V K)) * Nn V.card k ≤
      (Nn V.card k - Module.finrank F ↥(Z ⊓ Vk (F := F) V k)) * Nn V.card K := by
  have h := normalized_rank_antitone Z V hZ hKn (K - k) k (by omega)
  rw [show k + (K - k) = K by omega] at h
  have e1 := card_irrK_add Z V hZg K
  have e2 := card_irrK_add Z V hZg k
  rw [show Nn V.card K - Module.finrank F ↥(Z ⊓ Vk (F := F) V K) = (irrK Z V K).card by omega,
    show Nn V.card k - Module.finrank F ↥(Z ⊓ Vk (F := F) V k) = (irrK Z V k).card by omega]
  exact h

end Final

end

end Pang
