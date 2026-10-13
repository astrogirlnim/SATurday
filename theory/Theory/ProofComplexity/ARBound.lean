import Theory.ProofComplexity.ARSup3

/-!
# Alekhnovich-Razborov Theorem 3.8 (Ladder Rung R4, AR-A, final layer)

Semantic form: rows `i` carry column sets `J i` and root sets `Z i` (local to `J i`, `ℓ`-immune); the
axioms are polynomials whose multilinearization is supported in some `J i` and vanishes on `Z i`.
If the incidence structure is an `(r,s,c)`-expander (boundary form), `4(s-c) < ℓ`, `1 ≤ r`, `1 ≤ ℓ` and
`s ≤ r(ℓ/4-(s-c))`, then there is no polynomial calculus refutation of degree `≤ r(ℓ/4-(s-c))`.

LOG: R4 AR-A Theorem 3.8
-/

namespace SATurday.ProofComplexity.PCL

open Finset

noncomputable section
open Classical

variable {F : Type} [Field F] {ι : Type} [Fintype ι] {J : ι → Finset ℕ} {ℓ : ℕ}

theorem rdc_supp_sub {Z : Set (Set ℕ)} {W : Finset ℕ} (hZ : ∀ a ∈ Z, a ∩ (↑W : Set ℕ) ∈ Z)
    {g : ML F} (hg : ∀ U ∈ g.support, U ⊆ W) :
    ∀ U ∈ (rdc (vsub (F := F) Z) g).support, U ⊆ W := by
  set V := vsub (F := F) Z
  set r := rdc V g with hr
  have hgW : kW (↑W : Set ℕ) g = g := kW_of_supp fun U hU => by exact_mod_cast hg U hU
  have hspec : Spec V g (kW (↑W : Set ℕ) r) := by
    refine ⟨fun T hT => ?_, ?_⟩
    · rw [support_kW, Finset.mem_filter] at hT
      exact (rdc_spec _ g).irr T hT.1
    · have : g - kW (↑W : Set ℕ) r = kW (↑W : Set ℕ) (g - r) := by rw [map_sub, hgW]
      rw [this]
      intro a ha
      rw [ev_kW]
      exact (rdc_spec V g).mem _ (hZ a ha)
  have hrW : r = kW (↑W : Set ℕ) r := rdc_eq_of_spec hspec
  intro U hU
  have : U ∈ (kW (↑W : Set ℕ) r).support := by rw [← hrW]; exact hU
  rw [support_kW, Finset.mem_filter] at this
  exact_mod_cast this.2

/-- The local reduction of a term: reduce modulo the rows in its support. -/
def Rt (J : ι → Finset ℕ) (ℓ : ℕ) (Z : ι → Set (Set ℕ)) (T : Finset ℕ) : ML F :=
  rdc (vsub (F := F) (ZI Z (Sup J ℓ T))) (Finsupp.single T (1 : F))

/-- The operator of Theorem 3.8. -/
def Rop (J : ι → Finset ℕ) (ℓ : ℕ) (Z : ι → Set (Set ℕ)) : ML F →ₗ[F] ML F :=
  Finsupp.linearCombination F (Rt J ℓ Z)

theorem Rop_single (Z : ι → Set (Set ℕ)) (T : Finset ℕ) :
    Rop (F := F) J ℓ Z (Finsupp.single T 1) = Rt J ℓ Z T := by
  unfold Rop; rw [Finsupp.linearCombination_single, one_smul]

theorem ZI_restrict {Z : ι → Set (Set ℕ)} {r : ℕ} {s c : ℝ} (G : Good F J Z ℓ r s c)
    (I : Finset ι) {W : Finset ℕ} (hW : I.biUnion J ⊆ W) :
    ∀ a ∈ ZI Z I, a ∩ (↑W : Set ℕ) ∈ ZI Z I := by
  intro a ha k hk
  refine G.loc k a _ (fun x hx => ?_) (ha k hk)
  have : x ∈ W := hW (Finset.mem_biUnion.2 ⟨k, hk, hx⟩)
  simp [this]

theorem Rop_eq_rdc {Z : ι → Set (Set ℕ)} {r : ℕ} {s c : ℝ} (G : Good F J Z ℓ r s c)
    (I : Finset ι) (hIr : I.card ≤ r) {g : ML F}
    (hg : ∀ T ∈ g.support, Sup J ℓ T ⊆ I) :
    Rop J ℓ Z g = rdc (vsub (F := F) (ZI Z I)) g := by
  have hsum : g = ∑ T ∈ g.support, g T • Finsupp.single T (1 : F) := by
    conv_lhs => rw [← Finsupp.sum_single g]
    unfold Finsupp.sum
    exact Finset.sum_congr rfl fun T _ => (Finsupp.smul_single_one T (g T)).symm
  conv_lhs => rw [hsum]
  conv_rhs => rw [hsum]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Rop_single]
  unfold Rt
  rw [← rdc_Sup_eq G T _ I (hg T hT) hIr rfl]


theorem Rop_axiom {Z : ι → Set (Set ℕ)} {r : ℕ} {s c : ℝ} (G : Good F J Z ℓ r s c)
    (hsD : s ≤ Dbd ℓ r s c) {p : ML F} {i : ι} (hsupp : ∀ T ∈ p.support, T ⊆ J i)
    (hvan : p ∈ vsub (F := F) (Z i)) : Rop J ℓ Z p = 0 := by
  by_cases hlt : (J i).card < ℓ
  · have : p = 0 := by
      by_contra hne
      have h1 := G.imm i p hne (fun a ha => hvan a ha)
      have h2 : deg p ≤ (J i).card := deg_le fun T hT => Finset.card_le_card (hsupp T hT)
      omega
    rw [this, map_zero]
  · push Not at hlt
    have hiS : i ∈ Sup J ℓ (J i) := by
      refine Sup_closed (J i) i ?_
      have : (J i).card ≤ (J i ∩ (J i ∪ (Sup J ℓ (J i)).biUnion J)).card :=
        Finset.card_le_card fun x hx => Finset.mem_inter.2 ⟨hx, Finset.mem_union_left _ hx⟩
      have := G.hl
      omega
    have hcard : (Sup J ℓ (J i)).card < r :=
      Sup_card G ((G.wt i).trans hsD)
    rw [Rop_eq_rdc G (Sup J ℓ (J i)) hcard.le (fun T hT => Sup_mono (hsupp T hT))]
    apply rdc_of_mem
    intro a ha
    exact hvan a (ha i hiS)

theorem Rop_step {Z : ι → Set (Set ℕ)} {r : ℕ} {s c : ℝ} (G : Good F J Z ℓ r s c) {d : ℕ}
    (hd : (d : ℝ) ≤ Dbd ℓ r s c) (T : Finset ℕ) (i : ℕ) (hT : T.card < d) :
    Rop J ℓ Z (shl {i} (Finsupp.single T (1 : F))) =
      Rop J ℓ Z (shl {i} (Rop J ℓ Z (Finsupp.single T (1 : F)))) := by
  set tx : Finset ℕ := T ∪ {i} with htx
  have hdeg : (tx.card : ℝ) ≤ Dbd ℓ r s c := by
    have h1 : tx.card ≤ T.card + 1 := by
      calc tx.card ≤ T.card + ({i} : Finset ℕ).card := Finset.card_union_le _ _
        _ = T.card + 1 := by simp
    have : (tx.card : ℝ) ≤ d := by exact_mod_cast (by omega : tx.card ≤ d)
    linarith
  have hS'r : (Sup J ℓ tx).card < r := Sup_card G hdeg
  set S' := Sup J ℓ tx with hS'
  have hTS : Sup J ℓ T ⊆ S' := Sup_mono Finset.subset_union_left
  have hρ : Rt J ℓ Z T = rdc (vsub (F := F) (ZI Z S')) (Finsupp.single T 1) := by
    unfold Rt
    exact (rdc_Sup_eq G T _ S' hTS hS'r.le rfl).symm
  have hsup : ∀ U ∈ (Rt (F := F) J ℓ Z T).support, U ⊆ T ∪ (Sup J ℓ T).biUnion J := by
    refine rdc_supp_sub (ZI_restrict G _ Finset.subset_union_right) ?_
    intro U hU
    have := Finsupp.support_single_subset hU
    rw [Finset.mem_singleton] at this
    rw [this]; exact Finset.subset_union_left
  rw [Rop_single, shl_single, Rop_single]
  have hL : Rt (F := F) J ℓ Z tx = rdc (vsub (F := F) (ZI Z S')) (Finsupp.single tx 1) := rfl
  have hR : Rop J ℓ Z (shl {i} (Rt (F := F) J ℓ Z T)) =
      rdc (vsub (F := F) (ZI Z S')) (shl {i} (Rt J ℓ Z T)) := by
    refine Rop_eq_rdc G S' hS'r.le fun W hW => ?_
    obtain ⟨U, hU, rfl⟩ := support_shl_subset {i} _ W hW
    refine Sup_sub_of ?_
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · rcases Finset.mem_union.1 (hsup U hU hx) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · obtain ⟨m, hm, hxm⟩ := Finset.mem_biUnion.1 h
        exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨m, hTS hm, hxm⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  rw [hL, hR]
  symm
  refine rdc_congr ?_
  have hmem : Rt (F := F) J ℓ Z T - Finsupp.single T 1 ∈ vsub (F := F) (ZI Z S') := by
    rw [hρ]
    have := (rdc_spec (vsub (F := F) (ZI Z S')) (Finsupp.single T 1)).mem
    have e : rdc (vsub (F := F) (ZI Z S')) (Finsupp.single T 1) - Finsupp.single T 1 =
        -(Finsupp.single T 1 - rdc (vsub (F := F) (ZI Z S')) (Finsupp.single T 1)) := by abel
    rw [e]; exact Submodule.neg_mem _ this
  have := shl_mem_vsub hmem {i}
  rw [map_sub, shl_single] at this
  exact this

theorem Rop_one {Z : ι → Set (Set ℕ)} (hl : 1 ≤ ℓ) :
    Rop (F := F) J ℓ Z (Finsupp.single ∅ 1) ≠ 0 := by
  rw [Rop_single]
  unfold Rt
  rw [Sup_empty]
  have : rdc (vsub (F := F) (ZI Z ∅)) (Finsupp.single (∅ : Finset ℕ) 1) =
      Finsupp.single ∅ 1 := by
    refine rdc_eq_of_spec ⟨fun T hT hLT => ?_, by simp⟩
    obtain ⟨g, hg, hTg, _⟩ := hLT
    have : g = 0 := eq_zero_of_ev fun a => hg a (by intro k hk; simp at hk)
    rw [this] at hTg
    simp at hTg
  rw [this]
  exact Finsupp.single_ne_zero.2 one_ne_zero

/-- **Theorem 3.8** (Alekhnovich-Razborov), semantic form: no polynomial calculus refutation of degree
`≤ r (ℓ/4 - (s-c))` of axioms that are local to `ℓ`-immune rows of an `(r,s,c)`-expander. -/
theorem ar_no_refutation {Z : ι → Set (Set ℕ)} {r : ℕ} {s c : ℝ} (G : Good F J Z ℓ r s c)
    (hsD : s ≤ Dbd ℓ r s c) {Ax : Set (MvPolynomial ℕ F)}
    (hAx : ∀ p ∈ Ax, ∃ i, (∀ T ∈ (ml p).support, T ⊆ J i) ∧ ml p ∈ vsub (F := F) (Z i))
    {d : ℕ} (hd : (d : ℝ) ≤ Dbd ℓ r s c) : ¬ PCD Ax d 1 :=
  no_refutation_of_operator (Rop J ℓ Z) d
    (fun p hp => by
      obtain ⟨i, h1, h2⟩ := hAx p hp
      exact Rop_axiom G hsD h1 h2)
    (fun T i hT => Rop_step G hd T i hT)
    (Rop_one G.hl)

end

end SATurday.ProofComplexity.PCL
