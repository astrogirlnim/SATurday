import Theory.ProofComplexity.BraunMatchingMomentCompleteness
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Fintype.Powerset

/-!
# Augmented F2 chains on the chessboard complex, minimal API (R4 Phase 2.1, layer 6c)

Credit. The part of K. Braun's third party chain files (arXiv 2609.23015, author's Lean
development) `AugmentedChains.lean` (`Coeff`, `Supported`, `boundary`, `boundary_supported`,
`boundary_empty`) and `AugmentedChainMaps.lean` (`InRange`, `push`, `boundary_push`, `push_supported`)
that the matching moment files use, specialized to the chessboard complex (faces are the matchings
`IsMatching`, so we do not carry his abstract `Complex` structure). The homology of the chessboard
complex itself is not here; it is isolated as the hypothesis `MatchingMomentFilling` in
`BraunMatchingMomentCycles`.

LOG: R4 BraunMomentChains module (Phase 2.1 layer 6c)
-/

namespace SATurday.ProofComplexity.BraunPC

noncomputable section

open scoped BigOperators Classical

abbrev Coeff (V : Type*) := Finset V → ZMod 2

/-- Chains of cell count `k` supported on matchings of the `s × N` board (`k` counts cells). -/
def Supported {s N : ℕ} (k : ℕ) (c : Coeff (Cell s N)) : Prop :=
  ∀ T, ¬IsMatching T ∨ T.card ≠ k → c T = 0

/-- Ambient augmented boundary, simultaneously in all degrees. -/
def boundary {V : Type*} [Fintype V] [DecidableEq V] (c : Coeff V) : Coeff V :=
  fun s => ∑ v : V, if v ∈ s then 0 else c (insert v s)

theorem IsMatching.subset {s N : ℕ} {A B : Finset (Cell s N)} (h : A ⊆ B) (hB : IsMatching B) :
    IsMatching A :=
  ⟨hB.1.mono (by exact_mod_cast h), hB.2.mono (by exact_mod_cast h)⟩

theorem boundary_supported {s N : ℕ} (k : ℕ) (c : Coeff (Cell s N))
    (hc : Supported (k + 1) c) : Supported k (boundary c) := by
  intro T hT
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : v ∈ T
  · simp [hv]
  · simp only [hv, ↓reduceIte]
    apply hc
    rcases hT with hT | hT
    · exact Or.inl (fun h => hT (IsMatching.subset (Finset.subset_insert v T) h))
    · exact Or.inr (by simpa [Finset.card_insert_of_notMem hv] using hT)

theorem boundary_empty {s N : ℕ} (c : Coeff (Cell s N)) (hc : Supported 0 c) :
    boundary c = 0 := by
  funext T
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : v ∈ T
  · simp [hv]
  · simp only [hv, ↓reduceIte]
    apply hc
    right
    simp [Finset.card_insert_of_notMem hv]

section Push
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def InRange (e : V ↪ W) (T : Finset W) : Prop :=
  ∀ w ∈ T, ∃ v, e v = w

def push (e : V ↪ W) (c : Coeff V) : Coeff W :=
  fun T => if InRange e T then c (T.preimage e e.injective.injOn) else 0

omit [Fintype V] [Fintype W] in
theorem preimage_insert (e : V ↪ W) (v : V) (T : Finset W) :
    (insert (e v) T).preimage e e.injective.injOn =
      insert v (T.preimage e e.injective.injOn) := by
  ext x
  simp [Finset.mem_preimage, e.injective.eq_iff]

omit [Fintype V] [DecidableEq V] [Fintype W] in
theorem inRange_insert (e : V ↪ W) (v : V) (T : Finset W) :
    InRange e (insert (e v) T) ↔ InRange e T := by
  simp [InRange]

theorem boundary_push (e : V ↪ W) (c : Coeff V) :
    boundary (push e c) = push e (boundary c) := by
  funext T
  by_cases hT : InRange e T
  · have hout (w : W) (hw : w ∉ Finset.univ.image e) :
        (if w ∈ T then 0 else push e c (insert w T)) = 0 := by
      have hr : ¬ InRange e (insert w T) := by
        intro h
        obtain ⟨v, hv⟩ := h w (Finset.mem_insert_self w T)
        exact hw (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩)
      simp [push, hr]
    calc
      boundary (push e c) T =
          ∑ w ∈ Finset.univ.image e, if w ∈ T then 0 else push e c (insert w T) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro w _ hw
        exact hout w hw
      _ = ∑ v : V, if e v ∈ T then 0 else push e c (insert (e v) T) := by
        rw [Finset.sum_image]
        intro x _ y _ h
        exact e.injective h
      _ = push e (boundary c) T := by
        simp only [push, hT, ↓reduceIte, boundary]
        apply Finset.sum_congr rfl
        intro v _
        simp [inRange_insert, hT, preimage_insert, Finset.mem_preimage]
  · have hi (w : W) : ¬ InRange e (insert w T) := by
      intro h
      exact hT (fun x hx => h x (Finset.mem_insert_of_mem hx))
    simp [boundary, push, hT, hi]

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem map_preimage (e : V ↪ W) (T : Finset W) (hT : InRange e T) :
    (T.preimage e e.injective.injOn).map e = T := by
  ext w
  simp only [Finset.mem_map, Finset.mem_preimage]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact hv
  · intro hw
    obtain ⟨v, rfl⟩ := hT w hw
    exact ⟨v, hw, rfl⟩

theorem push_supported {r m N : ℕ} (e : Cell r N ↪ Cell m N)
    (he : ∀ S : Finset (Cell r N), IsMatching S → IsMatching (S.map e)) (k : ℕ)
    (c : Coeff (Cell r N)) (hc : Supported k c) : Supported k (push e c) := by
  intro T hT
  by_cases hr : InRange e T
  · simp only [push, hr, ↓reduceIte]
    apply hc
    have hmap := map_preimage e T hr
    rcases hT with hT | hT
    · left
      intro h
      exact hT (hmap ▸ he _ h)
    · right
      intro h
      apply hT
      rw [← hmap, Finset.card_map, h]
  · simp [push, hr]

end Push

end

end SATurday.ProofComplexity.BraunPC
