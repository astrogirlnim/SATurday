import Theory.ProofComplexity.BraunMomentChains

/-!
# Matching moment cycles (R4 Phase 2.1, layer 6c)

Credit. Port, with our own proofs where they differ, of K. Braun (arXiv 2609.23015, author's Lean development) `MatchingMomentCycles.lean` (`lem:matching-marginal-cycle`): compatible lower matching moments form an augmented F2 cycle in cell count `s-1`. His filling statement `matching_moment_filling` rests on the chessboard homology and is here the explicit hypothesis `MatchingMomentFilling`.

LOG: R4 BraunMatchingMomentCycles module (Phase 2.1 layer 6c)
-/

namespace SATurday.ProofComplexity.BraunPC

noncomputable section

open scoped BigOperators Classical

def momentLayer (m N k : ℕ) (z : Finset (Cell m N) → ZMod 2) : Coeff (Cell m N) :=
  fun T => if IsMatching T ∧ T.card=k then z T else 0

theorem momentLayer_supported (m N k : ℕ) (z : Finset (Cell m N) → ZMod 2) :
    Supported k (momentLayer m N k z) := by
  intro T hT
  by_cases h : IsMatching T ∧ T.card=k
  · exact False.elim (hT.elim (fun hT => hT h.1) (fun hT => hT h.2))
  · simp [momentLayer,h]

def rowBoundary (m N k : ℕ) (z : Finset (Cell m N) → ZMod 2)
    (U : Finset (Cell m N)) (i : Fin m) : ZMod 2 :=
  ∑ j : Fin N, if (i,j) ∈ U then 0 else momentLayer m N (k+1) z (insert (i,j) U)

theorem rowBoundary_unused (m N k : ℕ) (z : Finset (Cell m N) → ZMod 2)
    (U : Finset (Cell m N)) (hU : IsMatching U) (hcard : U.card=k)
    (i : Fin m) (hi : RowUnused i U) :
    rowBoundary m N k z U i = ∑ j : Fin N, if ColUnused j U then z (insert (i,j) U) else 0 := by
  apply Finset.sum_congr rfl
  intro j _
  have hij : (i,j) ∉ U := fun h => hi (i,j) h rfl
  have hd : (insert (i,j) U).card=k+1 := by rw [Finset.card_insert_of_notMem hij,hcard]
  simp only [hij,↓reduceIte,momentLayer,hd,and_true]
  rw [matching_insert_unused U hU i hi j]

theorem rowBoundary_occupied (m N k : ℕ) (z : Finset (Cell m N) → ZMod 2)
    (U : Finset (Cell m N)) (hU : IsMatching U)
    (i : Fin m) (hi : ¬RowUnused i U) : rowBoundary m N k z U i=0 := by
  change ¬(∀ x ∈ U, x.1 ≠ i) at hi
  push Not at hi
  obtain ⟨⟨i',j₀⟩,hj₀,he⟩ := hi
  change i'=i at he
  subst i'
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : (i,j) ∈ U
  · simp [hj]
  · have hm : ¬IsMatching (insert (i,j) U) := by
      intro h
      have he := (matching_insert_occupied U hU i j₀ hj₀ j).mp h
      exact hj (he.symm ▸ hj₀)
    simp [hj,momentLayer,hm]

theorem rowUnused_iff_not_mem_image {m N : ℕ} (U : Finset (Cell m N)) (i : Fin m) :
    RowUnused i U ↔ i ∉ U.image Prod.fst := by
  constructor
  · intro h hn
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hn
    exact h x hx he
  · intro h x hx he
    exact h (Finset.mem_image.mpr ⟨x,hx,he⟩)

theorem unused_rows_card {m N : ℕ} (U : Finset (Cell m N)) (hU : IsMatching U) :
    (Finset.univ.filter (fun i : Fin m => RowUnused i U)).card=m-U.card := by
  have he : Finset.univ.filter (fun i : Fin m => RowUnused i U) = Finset.univ \ U.image Prod.fst := by
    ext i
    simp [rowUnused_iff_not_mem_image]
  rw [he,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_image_of_injOn hU.1]
  simp

theorem momentLayer_boundary_marginals (m N k : ℕ) (z : Finset (Cell m N) → ZMod 2)
    (hz : MatchingMarginals m N (k+1) z) (U : Finset (Cell m N))
    (hU : IsMatching U) (hcard : U.card=k) :
    boundary (momentLayer m N (k+1) z) U =
      ∑ i : Fin m, if RowUnused i U then z U else 0 := by
  change (∑ x : Fin m × Fin N, if x ∈ U then 0 else momentLayer m N (k+1) z (insert x U))=_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change rowBoundary m N k z U i=_
  by_cases hi : RowUnused i U
  · simp only [hi,↓reduceIte]
    rw [rowBoundary_unused m N k z U hU hcard i hi]
    exact hz U hU (by omega) i hi
  · simpa [hi] using rowBoundary_occupied m N k z U hU i hi

private theorem matching_moment_cycle_two (s N : ℕ) (hs : 2≤s) (z : Finset (Cell s N) → ZMod 2)
    (hz : MatchingMarginals s N (s-1) z) : boundary (momentLayer s N (s-1) z)=0 := by
  funext U
  by_cases h : IsMatching U ∧ U.card=s-2
  · have he : s-2+1=s-1 := by omega
    have hb := momentLayer_boundary_marginals s N (s-2) z (by simpa [he] using hz) U h.1 h.2
    rw [he] at hb
    rw [hb]
    have hc : (Finset.univ.filter (fun i : Fin s => RowUnused i U)).card=2 := by
      rw [unused_rows_card U h.1,h.2]
      omega
    rw [← Finset.sum_filter]
    rw [Finset.sum_const,hc,two_nsmul]
    exact ZModModule.add_self _
  · have he : s-2+1=s-1 := by omega
    have hsupp : Supported (s-2+1) (momentLayer s N (s-1) z) := by
      simpa [he] using momentLayer_supported s N (s-1) z
    have hd := boundary_supported (s-2) (momentLayer s N (s-1) z) hsupp
    apply hd
    simpa only [IsMatching,not_and_or] using h
theorem matching_moment_cycle (s N : ℕ) (hs : 1≤s) (z : Finset (Cell s N) → ZMod 2)
    (hz : MatchingMarginals s N (s-1) z) : boundary (momentLayer s N (s-1) z)=0 := by
  by_cases h : s=1
  · subst s
    exact boundary_empty _ (momentLayer_supported 1 N 0 z)
  · exact matching_moment_cycle_two s N (by omega) z hz

/-- Chessboard filling input (homology). Braun proves it from the homological bound of the
chessboard complex (`chessboard_homological_bound`, stable range `N ≥ 2s-1`); that part of the
development is not ported yet, so the layers that need it take this statement as an explicit
hypothesis, exactly in the shape of his `matching_moment_filling`. -/
def MatchingMomentFilling : Prop :=
  ∀ (s N : ℕ), 1≤s → 2*s-1≤N → ∀ z : Finset (Cell s N) → ZMod 2,
    MatchingMarginals s N (s-1) z →
    ∃ y : Coeff (Cell s N), Supported s y ∧ boundary y=momentLayer s N (s-1) z

theorem matching_moment_filling (hfill : MatchingMomentFilling) (s N : ℕ) (hs : 1≤s)
    (hN : 2*s-1≤N) (z : Finset (Cell s N) → ZMod 2) (hz : MatchingMarginals s N (s-1) z) :
    ∃ y : Coeff (Cell s N), Supported s y ∧ boundary y=momentLayer s N (s-1) z :=
  hfill s N hs hN z hz

theorem MatchingMarginals.mono {m N B C : ℕ} {z : Finset (Cell m N) → ZMod 2}
    (hz : MatchingMarginals m N B z) (hCB : C≤B) : MatchingMarginals m N C z := by
  intro S hS hcard i hi
  exact hz S hS (lt_of_lt_of_le hcard hCB) i hi

end

end SATurday.ProofComplexity.BraunPC
