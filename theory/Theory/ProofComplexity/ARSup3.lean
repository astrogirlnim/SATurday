import Theory.ProofComplexity.ARSup2

/-!
# Alekhnovich-Razborov Lemma 3.12 (Ladder Rung R4, AR-A, layer 8)

For `I ⊇ Sup t` with `|I| ≤ r`, reducing `t` modulo the consequences of the rows `I` gives the same
result as reducing modulo the rows `Sup t`.  Proof by eliminating one row at a time with Corollary 3.7.

LOG: R4 AR-A Lemma 3.12
-/

namespace SATurday.ProofComplexity.PCL

open Finset

noncomputable section
open Classical

variable {F : Type} [Field F] {ι : Type} [Fintype ι] {J : ι → Finset ℕ} {ℓ : ℕ}

/-- Pigeonhole: a nonempty set of rows within the expansion range has a row with `≥ c` private columns. -/
theorem exists_private {Z : ι → Set (Set ℕ)} {r : ℕ} {s c : ℝ} (G : Good F J Z ℓ r s c)
    {I'' : Finset ι} (hne : I''.Nonempty) (hr : I''.card ≤ r) :
    ∃ i ∈ I'', c ≤ ((J i \ (I''.erase i).biUnion J).card : ℝ) := by
  by_contra hcon
  push Not at hcon
  have hsub : bdry J I'' ⊆ I''.biUnion (fun i => J i \ (I''.erase i).biUnion J) := by
    intro j hj
    unfold bdry at hj
    rw [Finset.mem_filter] at hj
    obtain ⟨hj1, hj2⟩ := hj
    obtain ⟨k, hk⟩ := Finset.card_eq_one.1 hj2
    have hkm : k ∈ I''.filter (fun m => j ∈ J m) := by rw [hk]; exact Finset.mem_singleton_self _
    rw [Finset.mem_filter] at hkm
    refine Finset.mem_biUnion.2 ⟨k, hkm.1, Finset.mem_sdiff.2 ⟨hkm.2, ?_⟩⟩
    intro hmem
    obtain ⟨m, hm, hjm⟩ := Finset.mem_biUnion.1 hmem
    have hm' : m ∈ I''.filter (fun m => j ∈ J m) := Finset.mem_filter.2 ⟨Finset.mem_of_mem_erase hm, hjm⟩
    rw [hk, Finset.mem_singleton] at hm'
    exact (Finset.ne_of_mem_erase hm) hm'
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := I'') (t := fun i => J i \ (I''.erase i).biUnion J)
  have h3 : (∑ i ∈ I'', (((J i \ (I''.erase i).biUnion J).card : ℕ) : ℝ)) <
      ∑ i ∈ I'', c := Finset.sum_lt_sum_of_nonempty hne hcon
  rw [Finset.sum_const, nsmul_eq_mul] at h3
  have h4 : (((bdry J I'').card : ℕ) : ℝ) ≤ ∑ i ∈ I'', (((J i \ (I''.erase i).biUnion J).card : ℕ) : ℝ) := by
    exact_mod_cast h1.trans h2
  have := G.exp I'' hr
  linarith

theorem ZI_eq_inter (Z : ι → Set (Set ℕ)) {I : Finset ι} {i : ι} (hi : i ∈ I) :
    ZI Z I = ZI Z (I.erase i) ∩ Z i := by
  ext a
  simp only [ZI, Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_erase]
  constructor
  · intro h; exact ⟨fun k hk => h k hk.2, h i hi⟩
  · rintro ⟨h1, h2⟩ k hk
    by_cases hki : k = i
    · rw [hki]; exact h2
    · exact h1 k ⟨hki, hk⟩

/-- **Lemma 3.12** (Alekhnovich-Razborov). -/
theorem rdc_Sup_eq {Z : ι → Set (Set ℕ)} {r : ℕ} {s c : ℝ} (G : Good F J Z ℓ r s c) (t : Finset ℕ) :
    ∀ (n : ℕ) (I : Finset ι), Sup J ℓ t ⊆ I → I.card ≤ r → (I \ Sup J ℓ t).card = n →
      rdc (vsub (F := F) (ZI Z I)) (Finsupp.single t (1 : F)) =
        rdc (vsub (F := F) (ZI Z (Sup J ℓ t))) (Finsupp.single t (1 : F)) := by
  intro n
  induction n with
  | zero =>
    intro I hS _ hn
    have : I ⊆ Sup J ℓ t := by
      intro x hx
      by_contra hxs
      have : x ∈ I \ Sup J ℓ t := Finset.mem_sdiff.2 ⟨hx, hxs⟩
      rw [Finset.card_eq_zero.1 hn] at this
      simp at this
    rw [Finset.Subset.antisymm this hS]
  | succ n ih =>
    intro I hS hIr hn
    set S := Sup J ℓ t with hSdef
    set I'' := I \ S with hI''
    have hne : I''.Nonempty := Finset.card_pos.1 (by omega)
    have hI''r : I''.card ≤ r := (Finset.card_le_card Finset.sdiff_subset).trans hIr
    obtain ⟨i, hiI'', hpriv⟩ := exists_private G hne hI''r
    obtain ⟨hiI, hiS⟩ := Finset.mem_sdiff.1 hiI''
    set I' := I.erase i with hI'
    have hSI' : S ⊆ I' := fun x hx => Finset.mem_erase.2 ⟨fun h => hiS (h ▸ hx), hS hx⟩
    have hI'r : I'.card ≤ r := (Finset.card_erase_le).trans hIr
    have hI'n : (I' \ S).card = n := by
      have : I' \ S = I''.erase i := by
        ext x
        simp only [hI', hI'', Finset.mem_sdiff, Finset.mem_erase]
        tauto
      rw [this, Finset.card_erase_of_mem hiI'']; omega
    have IH := ih I' hSI' hI'r hI'n
    -- the split into v and z
    set v : Finset ℕ := J i ∩ (t ∪ I'.biUnion J) with hv
    set z : Finset ℕ := J i \ v with hz
    have hvz : Disjoint v z := Finset.disjoint_sdiff
    -- size of v
    have hvsub : v ⊆ (J i ∩ (I''.erase i).biUnion J) ∪ (J i ∩ (t ∪ S.biUnion J)) := by
      intro x hx
      rw [hv, Finset.mem_inter] at hx
      obtain ⟨hxJ, hx2⟩ := hx
      rcases Finset.mem_union.1 hx2 with h | h
      · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hxJ, Finset.mem_union_left _ h⟩)
      · obtain ⟨m, hm, hxm⟩ := Finset.mem_biUnion.1 h
        by_cases hmS : m ∈ S
        · exact Finset.mem_union_right _
            (Finset.mem_inter.2 ⟨hxJ, Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨m, hmS, hxm⟩)⟩)
        · refine Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hxJ, Finset.mem_biUnion.2 ⟨m, ?_, hxm⟩⟩)
          exact Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hm,
            Finset.mem_sdiff.2 ⟨Finset.mem_of_mem_erase hm, hmS⟩⟩
    have hvcard := (Finset.card_le_card hvsub).trans (Finset.card_union_le _ _)
    have hsplit := Finset.card_sdiff_add_card_inter (J i) ((I''.erase i).biUnion J)
    have hsplit' : (((J i \ (I''.erase i).biUnion J).card : ℝ) +
        ((J i ∩ (I''.erase i).biUnion J).card : ℝ)) = ((J i).card : ℝ) := by exact_mod_cast hsplit
    have hB : 4 * (J i ∩ (t ∪ S.biUnion J)).card ≤ ℓ := by
      by_contra hcon
      exact hiS (Sup_closed t i (not_le.1 hcon))
    have hvR : ((v.card : ℕ) : ℝ) ≤ ((J i ∩ (I''.erase i).biUnion J).card : ℝ) +
        ((J i ∩ (t ∪ S.biUnion J)).card : ℝ) := by exact_mod_cast hvcard
    have hBR : 4 * ((J i ∩ (t ∪ S.biUnion J)).card : ℝ) ≤ ℓ := by exact_mod_cast hB
    have hwt := G.wt i
    have hsc := G.hsc
    have h2v : 2 * v.card + 1 ≤ ℓ := by
      have : (2 * v.card : ℝ) < ℓ := by linarith
      have : 2 * v.card < ℓ := by exact_mod_cast this
      omega
    -- apply Corollary 3.7
    have hZQ : LocalOn (v ∪ z) (Z i) := by
      have : v ∪ z = J i := Finset.union_sdiff_of_subset Finset.inter_subset_left
      rw [this]
      exact fun a b h ha => G.loc i a b h ha
    have hZP : NoZ z (ZI Z I') := by
      intro a b hab ha k hk
      refine G.loc k a b (fun x hx => ?_) (ha k hk)
      have hxz : x ∉ z := by
        intro hxz
        rw [hz, Finset.mem_sdiff] at hxz
        apply hxz.2
        rw [hv, Finset.mem_inter]
        exact ⟨hxz.1, Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨k, hk, hx⟩)⟩
      exact hab x hxz
    have himm : ∀ g : ML F, g ≠ 0 → (∀ a ∈ Z i, ev a g = 0) → 2 * v.card + 1 ≤ deg g :=
      fun g hg0 hgv => h2v.trans (G.imm i g hg0 hgv)
    have hg : ∀ U ∈ (Finsupp.single t (1 : F)).support, Disjoint U z := by
      intro U hU
      have := Finsupp.support_single_subset hU
      rw [Finset.mem_singleton] at this
      subst this
      rw [Finset.disjoint_left]
      intro x hxU hxz
      rw [hz, Finset.mem_sdiff] at hxz
      apply hxz.2
      rw [hv, Finset.mem_inter]
      exact ⟨hxz.1, Finset.mem_union_left _ hxU⟩
    rw [ZI_eq_inter Z hiI]
    exact (rdc_inter hvz hZP hZQ himm hg).trans IH

end

end SATurday.ProofComplexity.PCL
