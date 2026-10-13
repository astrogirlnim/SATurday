import Theory.ProofComplexity.PCMultilinear

/-!
# Term order and the reduction operator of a subspace (Ladder Rung R4, AR-A, layer 2)

Terms are ordered by `key` (cardinality, then binary expansion): a well-founded total order refining
the degree.  For a subspace `V` of the multilinear polynomials, a term is *reducible* (`IsLT`) if it is
the leading term of an element of `V`, *irreducible* (`Irr`) otherwise.  Every polynomial `g` has a
unique `rdc V g` supported on irreducible terms with `g - rdc V g ∈ V` (Alekhnovich-Razborov Def. 2.9);
`rdc V` is linear and its terms never exceed those of `g` in the term order.

`vsub Z` is the subspace of polynomials vanishing at every point of `Z`: the ideal of consequences of a
system whose set of Boolean roots is `Z`.

LOG: R4 AR-A reduction layer
-/

namespace SATurday.ProofComplexity.PCL

open Finset

noncomputable section
open Classical

variable {F : Type} [Field F]

/-! ## The term order -/

/-- Binary expansion of a term. -/
def enc (T : Finset ℕ) : ℕ := ∑ i ∈ T, 2 ^ i

/-- Sort key of a term: degree first, then binary expansion (colexicographic order). -/
def key (T : Finset ℕ) : ℕ ×ₗ ℕ := toLex (T.card, enc T)

theorem key_inj : Function.Injective key := by
  intro T U h
  have h' : (T.card, enc T) = (U.card, enc U) := toLex.injective h
  exact Finset.geomSum_injective (n := 2) le_rfl (Prod.ext_iff.1 h').2

theorem card_le_of_key_le {T U : Finset ℕ} (h : key T ≤ key U) : T.card ≤ U.card := by
  unfold key at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | h
  · exact h.le
  · exact h.1.le

theorem key_lt_of_card_lt {T U : Finset ℕ} (h : T.card < U.card) : key T < key U := by
  unfold key
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

/-! ## Reducible and irreducible terms -/

/-- `T` is the leading term of some element of `V`. -/
def IsLT (V : Submodule F (ML F)) (T : Finset ℕ) : Prop :=
  ∃ g ∈ V, T ∈ g.support ∧ ∀ U ∈ g.support, key U ≤ key T

/-- Irreducible term. -/
def Irr (V : Submodule F (ML F)) (T : Finset ℕ) : Prop := ¬ IsLT V T

theorem isLT_mono {V W : Submodule F (ML F)} (h : V ≤ W) {T : Finset ℕ} (hT : IsLT V T) :
    IsLT W T := by
  obtain ⟨g, hg, h1, h2⟩ := hT
  exact ⟨g, h hg, h1, h2⟩

/-- `r` is a reduct of `g` modulo `V`: supported on irreducible terms and congruent to `g`. -/
structure Spec (V : Submodule F (ML F)) (g r : ML F) : Prop where
  irr : ∀ T ∈ r.support, Irr V T
  mem : g - r ∈ V

theorem exists_spec_le (V : Submodule F (ML F)) (M : ℕ ×ₗ ℕ) :
    ∀ g : ML F, (∀ U ∈ g.support, key U ≤ M) →
      ∃ r, Spec V g r ∧ ∀ T ∈ r.support, key T ≤ M := by
  induction M using WellFoundedLT.induction with
  | _ M ih =>
  have H : ∀ g : ML F, (∀ U ∈ g.support, key U < M) →
      ∃ r, Spec V g r ∧ ∀ T ∈ r.support, key T < M := by
    intro g hg
    by_cases h0 : g = 0
    · exact ⟨0, ⟨by simp, by simp [h0]⟩, by simp⟩
    · obtain ⟨U0, hU0, hmax⟩ := Finset.exists_max_image g.support key
        (Finsupp.support_nonempty_iff.2 h0)
      obtain ⟨r, hr, hb⟩ := ih (key U0) (hg U0 hU0) g hmax
      exact ⟨r, hr, fun T hT => lt_of_le_of_lt (hb T hT) (hg U0 hU0)⟩
  intro g hg
  by_cases hex : ∃ U ∈ g.support, key U = M
  · obtain ⟨U, hU, hUM⟩ := hex
    have hgU : g U ≠ 0 := Finsupp.mem_support_iff.1 hU
    by_cases hirr : Irr V U
    · set g' : ML F := g - Finsupp.single U (g U) with hg'
      have hlt : ∀ T ∈ g'.support, key T < M := by
        intro T hT
        have hTU : T ≠ U := by
          rintro rfl
          simp [hg'] at hT
        have hTg : T ∈ g.support := by
          rw [Finsupp.mem_support_iff] at hT ⊢
          intro h0
          apply hT
          simp [hg', h0, hTU]
        refine lt_of_le_of_ne (hg T hTg) ?_
        intro h
        exact hTU (key_inj (h.trans hUM.symm))
      obtain ⟨r', hr', hb'⟩ := H g' hlt
      refine ⟨r' + Finsupp.single U (g U), ⟨?_, ?_⟩, ?_⟩
      · intro T hT
        rcases Finset.mem_union.1 (Finsupp.support_add hT) with h | h
        · exact hr'.irr T h
        · have := Finsupp.support_single_subset h
          rw [Finset.mem_singleton] at this
          rw [this]; exact hirr
      · have : g - (r' + Finsupp.single U (g U)) = g' - r' := by rw [hg']; abel
        rw [this]; exact hr'.mem
      · intro T hT
        rcases Finset.mem_union.1 (Finsupp.support_add hT) with h | h
        · exact (hb' T h).le
        · have := Finsupp.support_single_subset h
          rw [Finset.mem_singleton] at this
          rw [this, hUM]
    · obtain ⟨h, hV, hUh, hmax⟩ := not_not.1 hirr
      have hhU : h U ≠ 0 := Finsupp.mem_support_iff.1 hUh
      set g' : ML F := g - (g U / h U) • h with hg'
      have hlt : ∀ T ∈ g'.support, key T < M := by
        intro T hT
        have hTU : T ≠ U := by
          rintro rfl
          simp [hg', hhU] at hT
        have hmem : T ∈ g.support ∪ h.support := by
          have := Finsupp.support_sub hT
          rcases Finset.mem_union.1 this with h1 | h1
          · exact Finset.mem_union_left _ h1
          · exact Finset.mem_union_right _ (Finsupp.support_smul h1)
        refine lt_of_le_of_ne ?_ ?_
        · rcases Finset.mem_union.1 hmem with h1 | h1
          · exact hg T h1
          · exact (hmax T h1).trans_eq hUM
        · intro h'
          exact hTU (key_inj (h'.trans hUM.symm))
      obtain ⟨r', hr', hb'⟩ := H g' hlt
      refine ⟨r', ⟨hr'.irr, ?_⟩, fun T hT => (hb' T hT).le⟩
      have : g - r' = (g' - r') + (g U / h U) • h := by rw [hg']; abel
      rw [this]
      exact V.add_mem hr'.mem (V.smul_mem _ hV)
  · have hlt : ∀ U ∈ g.support, key U < M := fun U hU =>
      lt_of_le_of_ne (hg U hU) (fun h => hex ⟨U, hU, h⟩)
    obtain ⟨r, hr, hb⟩ := H g hlt
    exact ⟨r, hr, fun T hT => (hb T hT).le⟩

theorem exists_spec (V : Submodule F (ML F)) (g : ML F) : ∃ r, Spec V g r := by
  by_cases h0 : g = 0
  · exact ⟨0, ⟨by simp, by simp [h0]⟩⟩
  · obtain ⟨U0, hU0, hmax⟩ := Finset.exists_max_image g.support key
      (Finsupp.support_nonempty_iff.2 h0)
    obtain ⟨r, hr, _⟩ := exists_spec_le V (key U0) g hmax
    exact ⟨r, hr⟩

theorem spec_unique {V : Submodule F (ML F)} {g r r' : ML F} (h : Spec V g r) (h' : Spec V g r') :
    r = r' := by
  by_contra hne
  have hd : r - r' ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨U0, hU0, hmax⟩ := Finset.exists_max_image (r - r').support key
    (Finsupp.support_nonempty_iff.2 hd)
  have hmem : r - r' ∈ V := by
    have := V.sub_mem h'.mem h.mem
    have e : g - r' - (g - r) = r - r' := by abel
    rwa [e] at this
  have hirr : Irr V U0 := by
    rcases Finset.mem_union.1 (Finsupp.support_sub hU0) with h1 | h1
    · exact h.irr _ h1
    · exact h'.irr _ h1
  exact hirr ⟨r - r', hmem, hU0, hmax⟩

theorem Spec.add {V : Submodule F (ML F)} {f g r s : ML F} (h : Spec V f r) (h' : Spec V g s) :
    Spec V (f + g) (r + s) := by
  refine ⟨fun T hT => ?_, ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_add hT) with h1 | h1
    · exact h.irr T h1
    · exact h'.irr T h1
  · have : f + g - (r + s) = (f - r) + (g - s) := by abel
    rw [this]; exact V.add_mem h.mem h'.mem

theorem Spec.smul {V : Submodule F (ML F)} {g r : ML F} (c : F) (h : Spec V g r) :
    Spec V (c • g) (c • r) := by
  refine ⟨fun T hT => h.irr T (Finsupp.support_smul hT), ?_⟩
  have : c • g - c • r = c • (g - r) := by rw [smul_sub]
  rw [this]; exact V.smul_mem _ h.mem

/-- The reduction operator of `V`. -/
def rdc (V : Submodule F (ML F)) : ML F →ₗ[F] ML F where
  toFun g := Classical.choose (exists_spec V g)
  map_add' f g := spec_unique (Classical.choose_spec (exists_spec V (f + g)))
    ((Classical.choose_spec (exists_spec V f)).add (Classical.choose_spec (exists_spec V g)))
  map_smul' c g := spec_unique (Classical.choose_spec (exists_spec V (c • g)))
    ((Classical.choose_spec (exists_spec V g)).smul c)

theorem rdc_spec (V : Submodule F (ML F)) (g : ML F) : Spec V g (rdc V g) :=
  Classical.choose_spec (exists_spec V g)

theorem rdc_eq_of_spec {V : Submodule F (ML F)} {g r : ML F} (h : Spec V g r) : rdc V g = r :=
  spec_unique (rdc_spec V g) h

theorem rdc_of_mem {V : Submodule F (ML F)} {g : ML F} (h : g ∈ V) : rdc V g = 0 :=
  rdc_eq_of_spec ⟨by simp, by simpa using h⟩

theorem rdc_congr {V : Submodule F (ML F)} {g g' : ML F} (h : g - g' ∈ V) : rdc V g = rdc V g' := by
  refine rdc_eq_of_spec ⟨(rdc_spec V g').irr, ?_⟩
  have : g - rdc V g' = (g - g') + (g' - rdc V g') := by abel
  rw [this]; exact V.add_mem h (rdc_spec V g').mem

theorem rdc_key_le (V : Submodule F (ML F)) (U : Finset ℕ) (c : F) :
    ∀ T ∈ (rdc V (Finsupp.single U c)).support, key T ≤ key U := by
  obtain ⟨r, hr, hb⟩ := exists_spec_le V (key U) (Finsupp.single U c) (by
    intro U' hU'
    have := Finsupp.support_single_subset hU'
    rw [Finset.mem_singleton] at this
    rw [this])
  rw [rdc_eq_of_spec hr]
  exact hb

theorem rdc_card_le (V : Submodule F (ML F)) (U : Finset ℕ) (c : F) :
    ∀ T ∈ (rdc V (Finsupp.single U c)).support, T.card ≤ U.card :=
  fun T hT => card_le_of_key_le (rdc_key_le V U c T hT)

/-- Leading terms of nonzero elements have the degree of the element. -/
theorem card_of_leading {g : ML F} {T : Finset ℕ} (hT : T ∈ g.support)
    (hmax : ∀ U ∈ g.support, key U ≤ key T) : T.card = deg g := by
  apply le_antisymm (le_deg hT)
  exact deg_le fun U hU => card_le_of_key_le (hmax U hU)

/-! ## Vanishing subspaces -/

/-- Polynomials vanishing at every point of `Z`. -/
def vsub (Z : Set (Set ℕ)) : Submodule F (ML F) where
  carrier := {g | ∀ a ∈ Z, ev a g = 0}
  add_mem' := by
    intro f g hf hg a ha
    simp [hf a ha, hg a ha]
  zero_mem' := by intro a _; simp
  smul_mem' := by
    intro c g hg a ha
    simp [hg a ha]

theorem mem_vsub {Z : Set (Set ℕ)} {g : ML F} : g ∈ vsub (F := F) Z ↔ ∀ a ∈ Z, ev a g = 0 := Iff.rfl

theorem vsub_mono {Z Z' : Set (Set ℕ)} (h : Z ⊆ Z') : vsub (F := F) Z' ≤ vsub Z :=
  fun _ hg a ha => hg a (h ha)

theorem shl_mem_vsub {Z : Set (Set ℕ)} {g : ML F} (hg : g ∈ vsub (F := F) Z) (s : Finset ℕ) :
    shl s g ∈ vsub (F := F) Z := by
  intro a ha
  rw [ev_shl, hg a ha]; simp

end

end SATurday.ProofComplexity.PCL
