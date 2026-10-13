import Theory.ProofComplexity.PCLocal

/-!
# Alekhnovich-Razborov Thm 3.1, Lemma 3.5, Cor 3.7 (Ladder Rung R4, AR-A, layer 5)

`Lam_mem` is the paper's Lemma 3.5: the local operator `Lam` maps the consequences of `ZP ∩ ZQ` into the
consequences of `ZP`.  `isLT_of_isLT_inter` is Theorem 3.1 and `rdc_inter` is Corollary 3.7, in the
semantic form: `ZP` does not depend on the variables `z`, `ZQ` depends only on `v ∪ z`, and `ZQ` is
`(2|v|+1)`-immune.

LOG: R4 AR-A Theorem 3.1
-/

namespace SATurday.ProofComplexity.PCL

open Finset

noncomputable section
open Classical

variable {F : Type} [Field F]

/-- The set of points `ZP` does not depend on the variables in `z`. -/
def NoZ (z : Finset ℕ) (ZP : Set (Set ℕ)) : Prop :=
  ∀ a b : Set ℕ, (∀ x, x ∉ z → (x ∈ a ↔ x ∈ b)) → a ∈ ZP → b ∈ ZP

/-- The set of points `ZQ` depends only on the variables in `W`. -/
def LocalOn (W : Finset ℕ) (ZQ : Set (Set ℕ)) : Prop :=
  ∀ a b : Set ℕ, (∀ x ∈ W, (x ∈ a ↔ x ∈ b)) → a ∈ ZQ → b ∈ ZQ

theorem coe_subset_split (z T : Finset ℕ) (b : Set ℕ) :
    (↑T : Set ℕ) ⊆ b ↔ (↑(T \ z) : Set ℕ) ⊆ b ∧ (↑(T ∩ z) : Set ℕ) ⊆ b := by
  constructor
  · intro h; exact ⟨fun x hx => h (Finset.mem_sdiff.1 (Finset.mem_coe.1 hx)).1,
      fun x hx => h (Finset.mem_inter.1 (Finset.mem_coe.1 hx)).1⟩
  · rintro ⟨h1, h2⟩ x hx
    by_cases hxz : x ∈ z
    · exact h2 (Finset.mem_coe.2 (Finset.mem_inter.2 ⟨hx, hxz⟩))
    · exact h1 (Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨hx, hxz⟩))

theorem coe_subset_compl_iff (T z : Finset ℕ) : (↑T : Set ℕ) ⊆ (↑z : Set ℕ)ᶜ ↔ Disjoint T z := by
  rw [Finset.disjoint_left]
  constructor
  · intro h x hx hz; exact h (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hz)
  · intro h x hx hz; exact h (Finset.mem_coe.1 hx) (Finset.mem_coe.1 hz)

/-- Restriction of `g` to the assignment `a` outside `z`: a polynomial in the variables `z`. -/
def ga (z : Finset ℕ) (a : Set ℕ) : ML F →ₗ[F] ML F :=
  Finsupp.linearCombination F (fun T : Finset ℕ =>
    if (↑(T \ z) : Set ℕ) ⊆ a then Finsupp.single (T ∩ z) (1 : F) else 0)

theorem ga_single (z : Finset ℕ) (a : Set ℕ) (T : Finset ℕ) (c : F) :
    ga z a (Finsupp.single T c) =
      if (↑(T \ z) : Set ℕ) ⊆ a then Finsupp.single (T ∩ z) c else 0 := by
  unfold ga
  rw [Finsupp.linearCombination_single]
  split_ifs <;> simp

theorem supp_ga (z : Finset ℕ) (a : Set ℕ) (g : ML F) : ∀ U ∈ (ga z a g).support, U ⊆ z := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    intro U hU
    rw [map_add] at hU
    rcases Finset.mem_union.1 (Finsupp.support_add hU) with h | h
    · exact hf U h
    · exact hg U h
  | single T c =>
    intro U hU
    rw [ga_single] at hU
    split_ifs at hU with h
    · have := Finsupp.support_single_subset hU
      rw [Finset.mem_singleton] at this
      rw [this]; exact Finset.inter_subset_right
    · simp at hU

theorem ev_ga (z : Finset ℕ) (a : Set ℕ) (g : ML F) (b : Set ℕ)
    (hb : ∀ x, x ∉ z → (x ∈ b ↔ x ∈ a)) : ev b (ga z a g) = ev b g := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
  | single T c =>
    rw [ga_single, ev_single]
    have hiff : (↑(T \ z) : Set ℕ) ⊆ b ↔ (↑(T \ z) : Set ℕ) ⊆ a := by
      constructor
      · intro h x hx
        exact (hb x (Finset.mem_sdiff.1 (Finset.mem_coe.1 hx)).2).1 (h hx)
      · intro h x hx
        exact (hb x (Finset.mem_sdiff.1 (Finset.mem_coe.1 hx)).2).2 (h hx)
    by_cases h : (↑(T \ z) : Set ℕ) ⊆ a
    · rw [if_pos h, ev_single]
      have h' := hiff.2 h
      have e : (↑T : Set ℕ) ⊆ b ↔ (↑(T ∩ z) : Set ℕ) ⊆ b := by
        rw [coe_subset_split z T b]; exact ⟨fun h => h.2, fun h2 => ⟨h', h2⟩⟩
      simp only [e]
    · rw [if_neg h, map_zero, if_neg]
      intro hs
      exact h (hiff.1 ((coe_subset_split z T b).1 hs).1)

theorem ev_congr_z {z : Finset ℕ} {h : ML F} (hz : ∀ U ∈ h.support, U ⊆ z) {b b' : Set ℕ}
    (hbb : ∀ x ∈ z, (x ∈ b ↔ x ∈ b')) : ev b h = ev b' h := by
  rw [ev_apply, ev_apply]
  refine Finset.sum_congr rfl fun T hT => ?_
  have : (↑T : Set ℕ) ⊆ b ↔ (↑T : Set ℕ) ⊆ b' := by
    constructor
    · intro hs x hx; exact (hbb x (hz T hT (Finset.mem_coe.1 hx))).1 (hs hx)
    · intro hs x hx; exact (hbb x (hz T hT (Finset.mem_coe.1 hx))).2 (hs hx)
  simp only [this]

theorem ev_Lam {v z : Finset ℕ} (ZQ : Set (Set ℕ)) (hvz : Disjoint v z) (a : Set ℕ) (g : ML F) :
    ev a (Lam v z ZQ g) = ev a (Re v z ZQ (v.filter (fun x => x ∈ a)) (ga z a g)) := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single T c =>
    have e1 : Lam v z ZQ (Finsupp.single T c) = c • Lterm v z ZQ T := by
      unfold Lam; rw [Finsupp.linearCombination_single]
    rw [e1, ga_single, map_smul, ev_Lterm ZQ hvz]
    by_cases h : (↑(T \ z) : Set ℕ) ⊆ a
    · rw [if_pos h, if_pos h]
      have : Finsupp.single (T ∩ z) c = c • Finsupp.single (T ∩ z) (1 : F) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [this, map_smul, map_smul]
    · rw [if_neg h, if_neg h]; simp

/-- **Lemma 3.5**: `Lam` maps the consequences of `ZP ∩ ZQ` into the consequences of `ZP`. -/
theorem Lam_mem {v z : Finset ℕ} {ZP ZQ : Set (Set ℕ)} (hvz : Disjoint v z) (hZP : NoZ z ZP)
    (hZQ : LocalOn (v ∪ z) ZQ) {g : ML F} (hg : g ∈ vsub (F := F) (ZP ∩ ZQ)) :
    Lam v z ZQ g ∈ vsub (F := F) ZP := by
  intro a ha
  rw [ev_Lam ZQ hvz]
  have hmem : ga z a g ∈ Ve v z ZQ (v.filter (fun x => x ∈ a)) := by
    refine ⟨supp_ga z a g, fun a'' ha'' he => ?_⟩
    set a' : Set ℕ := (a \ ↑z) ∪ (a'' ∩ ↑z) with ha'
    have h1 : ∀ x, x ∉ z → (x ∈ a' ↔ x ∈ a) := by
      intro x hx
      simp [ha', hx]
    have h2 : ∀ x ∈ z, (x ∈ a'' ↔ x ∈ a') := by
      intro x hx
      simp [ha', hx]
    have h3 : ∀ x ∈ v ∪ z, (x ∈ a'' ↔ x ∈ a') := by
      intro x hx
      rcases Finset.mem_union.1 hx with hxv | hxz
      · have hxz : x ∉ z := fun h => Finset.disjoint_left.1 hvz hxv h
        rw [h1 x hxz]
        have := Set.ext_iff.1 he x
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_coe] at this
        constructor
        · intro h; exact (this.2 ⟨h, hxv⟩).2
        · intro h; exact (this.1 ⟨hxv, h⟩).1
      · exact h2 x hxz
    have hz := supp_ga z a g
    rw [ev_congr_z hz h2, ev_ga z a g a' h1]
    exact hg a' ⟨hZP a a' (fun x hx => (h1 x hx).symm) ha, hZQ a'' a' h3 ha''⟩
  have : Re v z ZQ (v.filter (fun x => x ∈ a)) (ga z a g) = 0 := rdc_of_mem hmem
  rw [this]; simp

theorem supp_Lam (v z : Finset ℕ) (ZQ : Set (Set ℕ)) (g : ML F) :
    ∀ U ∈ (Lam v z ZQ g).support, ∃ T ∈ g.support, U ∈ (Lterm (F := F) v z ZQ T).support := by
  intro U hU
  unfold Lam at hU
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hU
  obtain ⟨T, hT, h⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hU)
  exact ⟨T, hT, Finsupp.support_smul h⟩

theorem Lam_apply (v z : Finset ℕ) (ZQ : Set (Set ℕ)) (g : ML F) (U : Finset ℕ) :
    Lam v z ZQ g U = ∑ T ∈ g.support, g T * (Lterm (F := F) v z ZQ T) U := by
  unfold Lam
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finset_sum_apply]
  simp

/-- Terms of `Lterm T` free of `z` have lower key than `t` when `key T ≤ key t`. -/
theorem key_Lterm_lt_or {v z : Finset ℕ} {ZQ : Set (Set ℕ)} (hvz : Disjoint v z)
    (himm : ∀ g : ML F, g ≠ 0 → (∀ a ∈ ZQ, ev a g = 0) → 2 * v.card + 1 ≤ deg g)
    {T t U : Finset ℕ} (hTt : key T ≤ key t) (hU : U ∈ (Lterm (F := F) v z ZQ T).support)
    (hUz : Disjoint U z) : key U ≤ key t := by
  by_cases hT : (T ∩ z).card ≤ v.card
  · rw [Lterm_fix hvz himm hT] at hU
    have := Finsupp.support_single_subset hU
    rw [Finset.mem_singleton] at this
    rw [this]; exact hTt
  · have h1 := card_Lterm_le hU hUz
    have h2 : (T \ (v ∪ z)).card + (T ∩ z).card ≤ T.card := by
      rw [← Finset.card_union_of_disjoint]
      · exact Finset.card_le_card (Finset.union_subset Finset.sdiff_subset Finset.inter_subset_left)
      · rw [Finset.disjoint_left]
        intro x hx hx2
        exact (Finset.mem_sdiff.1 hx).2 (Finset.mem_union_right _ (Finset.mem_inter.1 hx2).2)
    have h3 := card_le_of_key_le hTt
    have : U.card < t.card := by omega
    exact (key_lt_of_card_lt this).le

/-- **Theorem 3.1** (Alekhnovich-Razborov). -/
theorem isLT_of_isLT_inter {v z : Finset ℕ} {ZP ZQ : Set (Set ℕ)} (hvz : Disjoint v z)
    (hZP : NoZ z ZP) (hZQ : LocalOn (v ∪ z) ZQ)
    (himm : ∀ g : ML F, g ≠ 0 → (∀ a ∈ ZQ, ev a g = 0) → 2 * v.card + 1 ≤ deg g)
    {t : Finset ℕ} (htz : Disjoint t z) (h : IsLT (vsub (F := F) (ZP ∩ ZQ)) t) :
    IsLT (vsub (F := F) ZP) t := by
  obtain ⟨g, hg, htg, hmax⟩ := h
  set G := Lam v z ZQ g with hG
  have hGmem : G ∈ vsub (F := F) ZP := Lam_mem hvz hZP hZQ hg
  set W : Set ℕ := (↑z : Set ℕ)ᶜ with hW
  have hK2 : G t = g t := by
    rw [hG, Lam_apply, Finset.sum_eq_single t]
    · rw [Lterm_fix hvz himm (by simp [Finset.disjoint_iff_inter_eq_empty.1 htz])]
      simp
    · intro T hT hne
      have : (Lterm (F := F) v z ZQ T) t = 0 := by
        by_contra hc
        have hmem : t ∈ (Lterm (F := F) v z ZQ T).support := Finsupp.mem_support_iff.2 hc
        by_cases hTz : (T ∩ z).card ≤ v.card
        · rw [Lterm_fix hvz himm hTz] at hmem
          have := Finsupp.support_single_subset hmem
          rw [Finset.mem_singleton] at this
          exact hne this.symm
        · have h1 := key_Lterm_lt_or hvz himm (hmax T hT) hmem htz
          have h1' : (T \ (v ∪ z)).card + (T ∩ z).card ≤ T.card := by
            rw [← Finset.card_union_of_disjoint]
            · exact Finset.card_le_card
                (Finset.union_subset Finset.sdiff_subset Finset.inter_subset_left)
            · rw [Finset.disjoint_left]
              intro x hx hx2
              exact (Finset.mem_sdiff.1 hx).2 (Finset.mem_union_right _ (Finset.mem_inter.1 hx2).2)
          have h2 := card_Lterm_le hmem htz
          have h3 := card_le_of_key_le (hmax T hT)
          omega
      rw [this, mul_zero]
    · intro hn; exact absurd htg hn
  refine ⟨kW W G, ?_, ?_, ?_⟩
  · intro a ha
    rw [ev_kW]
    refine hGmem _ (hZP a _ ?_ ha)
    intro x hx
    simp [hW, hx]
  · rw [Finsupp.mem_support_iff, kW_apply, if_pos ((coe_subset_compl_iff t z).2 htz), hK2]
    exact Finsupp.mem_support_iff.1 htg
  · intro U hU
    rw [support_kW, Finset.mem_filter] at hU
    obtain ⟨hU1, hU2⟩ := hU
    obtain ⟨T, hT, hUT⟩ := supp_Lam v z ZQ g U hU1
    exact key_Lterm_lt_or hvz himm (hmax T hT) hUT ((coe_subset_compl_iff U z).1 hU2)

theorem kW_of_supp {W : Set ℕ} {g : ML F} (h : ∀ U ∈ g.support, (↑U : Set ℕ) ⊆ W) : kW W g = g := by
  ext U
  rw [kW_apply]
  split_ifs with hs
  · rfl
  · by_contra hne
    exact hs (h U (Finsupp.mem_support_iff.2 (Ne.symm hne)))

theorem kW_mem_vsub {z : Finset ℕ} {ZP : Set (Set ℕ)} (hZP : NoZ z ZP) {g : ML F}
    (hg : g ∈ vsub (F := F) ZP) : kW (↑z : Set ℕ)ᶜ g ∈ vsub (F := F) ZP := by
  intro a ha
  rw [ev_kW]
  refine hg _ (hZP a _ ?_ ha)
  intro x hx
  simp [hx]

/-- **Corollary 3.7**: for `z`-free `g` the reductions modulo `ZP ∩ ZQ` and `ZP` coincide. -/
theorem rdc_inter {v z : Finset ℕ} {ZP ZQ : Set (Set ℕ)} (hvz : Disjoint v z)
    (hZP : NoZ z ZP) (hZQ : LocalOn (v ∪ z) ZQ)
    (himm : ∀ g : ML F, g ≠ 0 → (∀ a ∈ ZQ, ev a g = 0) → 2 * v.card + 1 ≤ deg g)
    {g : ML F} (hg : ∀ U ∈ g.support, Disjoint U z) :
    rdc (vsub (F := F) (ZP ∩ ZQ)) g = rdc (vsub (F := F) ZP) g := by
  set W : Set ℕ := (↑z : Set ℕ)ᶜ with hW
  set r := rdc (vsub (F := F) ZP) g with hr
  have hgW : kW W g = g := kW_of_supp fun U hU => (coe_subset_compl_iff U z).2 (hg U hU)
  have hspec : Spec (vsub (F := F) ZP) g (kW W r) := by
    refine ⟨fun T hT => ?_, ?_⟩
    · rw [support_kW, Finset.mem_filter] at hT
      exact (rdc_spec _ g).irr T hT.1
    · have : g - kW W r = kW W (g - r) := by rw [map_sub, hgW]
      rw [this]
      exact kW_mem_vsub hZP (rdc_spec _ g).mem
  have hrW : r = kW W r := rdc_eq_of_spec hspec
  have hrz : ∀ U ∈ r.support, Disjoint U z := by
    intro U hU
    have : U ∈ (kW W r).support := by rw [← hrW]; exact hU
    rw [support_kW, Finset.mem_filter] at this
    exact (coe_subset_compl_iff U z).1 this.2
  refine rdc_eq_of_spec ⟨fun T hT hLT => ?_, ?_⟩
  · exact (rdc_spec _ g).irr T hT (isLT_of_isLT_inter hvz hZP hZQ himm (hrz T hT) hLT)
  · exact vsub_mono Set.inter_subset_left (rdc_spec (vsub (F := F) ZP) g).mem

end

end SATurday.ProofComplexity.PCL
