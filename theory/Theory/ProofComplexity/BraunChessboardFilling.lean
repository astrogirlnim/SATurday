import Theory.ProofComplexity.BraunMatchingMomentCycles
import Theory.ProofComplexity.BraunAugChessboard
import Theory.ProofComplexity.BraunCubeResidualDualSeparation

/-!
# The chessboard filling lemma (R4 Phase 2.1, layer 6k)

Credit. K. Braun (arXiv 2609.23015, author's Lean development): `ChessboardFillingProof.lean`
(`chessboard_filling`, derived from `chessboard_homological_bound`) and his
`matching_moment_filling` in `MatchingMomentCycles.lean`. Here the augmented chessboard homology
of `BraunAugChessboard` discharges the explicit hypothesis `MatchingMomentFilling` of
`BraunMatchingMomentCycles`: `matchingMomentFilling : MatchingMomentFilling` is proved
unconditionally, so every `hfill` hypothesis of layer 6 and 7 can be supplied by it.

LOG: R4 BraunChessboardFilling module (Phase 2.1 layer 6k)
-/

namespace SATurday.ProofComplexity.BraunPC

noncomputable section

open scoped BigOperators Classical

/-- Braun's `matching_moment_filling`: every compatible family of lower matching moments, being a
reduced F2 cycle on the chessboard complex in cell count `s-1`, bounds a chain in cell count `s`,
for `N >= 2s-1`. -/
theorem matchingMomentFilling : MatchingMomentFilling := by
  intro s N hs hN z hz
  have hcyc : Aug.boundary (momentLayer s N (s-1) z) = 0 := matching_moment_cycle s N hs z hz
  have hsupp : Aug.Supported (Aug.chessboardComplex s N) (s-1) (momentLayer s N (s-1) z) := by
    intro T hT
    apply momentLayer_supported s N (s-1) z T
    rcases hT with hT | hT
    · exact Or.inl hT
    · exact Or.inr hT
  have hac := Aug.chessboard_homological_bound s N hs (by omega)
  rw [Aug.chessboardNu_stable_range hN] at hac
  obtain ⟨b, hb, hbc⟩ := hac (s-1) (by omega) _ hsupp hcyc
  have hs1 : s - 1 + 1 = s := by omega
  rw [hs1] at hb
  exact ⟨b, fun T hT => hb T hT, hbc⟩

/-! ### Unconditional versions (hypothesis `hfill` discharged) -/

theorem matching_normalized_annihilator_unconditional (m N B : ℕ) (hN : 1≤N)
    (hNB : 2*B-1≤N) :
    ∃ L : Poly (ZMod 2) (Cell m N) →ₗ[ZMod 2] ZMod 2,
      AnnihilatesNS (functionalUnaryBase m N) B L ∧ L 1=1 :=
  matching_normalized_annihilator matchingMomentFilling m N B hN hNB

theorem functionalUnary_no_pc_refutation_unconditional (m N B : ℕ) (hN : 1≤N)
    (hNB : 2*B-1≤N) :
    ¬Derives (functionalUnaryBase m N) B (1 : Poly (ZMod 2) (Cell m N)) :=
  functionalUnary_no_pc_refutation matchingMomentFilling m N B hN hNB

theorem cube_residual_dual_separation_unconditional (m ℓ k B : ℕ) (hℓ : 2≤ℓ) (hk : 1≤k)
    (hkB : k≤B) (hpack : 4*(k-1)<2^ℓ) (hB : 2*B-1≤2^ℓ)
    (P : Poly (ZMod 2) (Fin m × Fin ℓ))
    (hp : P ∈ rowLinearSpace (ZMod 2) m ℓ k) (hne : P≠0) :
    ∃ μ : Poly (ZMod 2) (Cell m (2^ℓ)) →ₗ[ZMod 2] ZMod 2,
      (∀ Q ∈ pcSpace (functionalUnaryBase m (2^ℓ)) B, μ Q=0) ∧
      μ (compactDecoder m ℓ P)=1 ∧
      (0<P.totalDegree → μ 1=0) ∧
      (P.totalDegree=0 → μ 1=1) ∧
      compactDecoder m ℓ P ∉ pcSpace (functionalUnaryBase m (2^ℓ)) B ∧
      P ∉ pcSpace (compactBitBase m ℓ) B :=
  cube_residual_dual_separation matchingMomentFilling m ℓ k B hℓ hk hkB hpack hB P hp hne

end

end SATurday.ProofComplexity.BraunPC
