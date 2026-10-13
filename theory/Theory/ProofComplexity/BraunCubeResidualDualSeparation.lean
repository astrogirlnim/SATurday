import Theory.ProofComplexity.BraunMatchingFiltration
import Theory.ProofComplexity.BraunRowCubeIsolation
import Theory.ProofComplexity.BraunRowCube
import Theory.ProofComplexity.BraunCompactTransfer

/-!
# Cube residual dual separation (R4 Phase 2.1, layer 6g; deferred from layer 7)

Credit. Port of K. Braun (arXiv 2609.23015, author's Lean development)
`CubeResidualDualSeparation.lean` (`lem:cube-residual-dual-separation`): a nonzero row linear
polynomial `P` on `m × ℓ` bits has a functional on the unary board polynomials that annihilates
`PC_B` of the functional unary base, takes value `1` on the compact decoder image of `P`, and
separates `P` from `PC_B` of the compact bit base. The proof composes the row cube restriction
(layer 7), the coefficient isolation (layer 7), the normalized annihilator
`matching_normalized_annihilator` (layer 6) and `compactDecoder_PC` (layer 5).

Conditional statement. As in the rest of layer 6 it takes the hypothesis `MatchingMomentFilling`
(the chessboard homology input, see `BraunMatchingMomentCycles`) as first argument; it is discharged
once the homology part of layer 6 is ported.

LOG: R4 BraunCubeResidualDualSeparation module (Phase 2.1 layer 6g)
-/

namespace SATurday.ProofComplexity.BraunPC

noncomputable section

open MvPolynomial
open scoped BigOperators Classical

theorem cube_residual_dual_separation (hfill : MatchingMomentFilling) (m ℓ k B : ℕ) (hℓ : 2≤ℓ) (hk : 1≤k)
    (hkB : k≤B) (hpack : 4*(k-1)<2^ℓ) (hB : 2*B-1≤2^ℓ)
    (P : Poly (ZMod 2) (Fin m × Fin ℓ))
    (hp : P ∈ rowLinearSpace (ZMod 2) m ℓ k) (hne : P≠0) :
    ∃ μ : Poly (ZMod 2) (Cell m (2^ℓ)) →ₗ[ZMod 2] ZMod 2,
      (∀ Q ∈ pcSpace (functionalUnaryBase m (2^ℓ)) B, μ Q=0) ∧
      μ (compactDecoder m ℓ P)=1 ∧
      (0<P.totalDegree → μ 1=0) ∧
      (P.totalDegree=0 → μ 1=1) ∧
      compactDecoder m ℓ P ∉ pcSpace (functionalUnaryBase m (2^ℓ)) B ∧
      P ∉ pcSpace (compactBitBase m ℓ) B := by
  obtain ⟨x,hcoeff,hdegree⟩ := rowLinearSpace_top_coefficient hp hne
  let S := x.2.1.val
  have hcard : S.card=x.1.val := (Finset.mem_powersetCard.mp x.2.1.property).2
  have htk : S.card≤k := by rw [hcard]; exact Nat.le_of_lt_succ x.1.isLt
  let d : Fin m → Fin ℓ := fun i => if hi : i∈S then x.2.2 ⟨i,hi⟩ else ⟨0,by omega⟩
  obtain ⟨c,hc⟩ := exists_disjoint_coordinate_pairs ℓ S d
    (lt_of_le_of_lt (Nat.mul_le_mul_left 4 (Nat.sub_le_sub_right htk 1)) hpack)
  let D := coordinateRowCube m ℓ S d c hc
  have hrows : D.rows=S := rfl
  have hcols : D.cols.card=2*S.card := coordinateRowCube_cols_card m ℓ S d c hc
  have hres := cube_residual_parameters ℓ k B S.card hℓ hk htk hkB hpack hB
  obtain ⟨L,hL,hL1⟩ := matching_normalized_annihilator hfill (m-D.rows.card) (2^ℓ-D.cols.card)
    (B-D.rows.card) (by simpa only [hcols] using hres.1)
    (by simpa only [hcols,hrows] using hres.2)
  let μ := L.comp (rowCubeDifference D)
  have hann : ∀ Q ∈ pcSpace (functionalUnaryBase m (2^ℓ)) B, μ Q=0 := by
    intro Q hQ
    apply hL
    apply rowCubeDifference_ns D B Q
    rwa [functionalUnary_pc_eq_ns hfill m (2^ℓ) B (Nat.succ_le_of_lt (pow_pos (by decide) ℓ)) hB] at hQ
  let Φ := fun e : S → ZMod 2 => fun v : Fin m × Fin ℓ => rowCubeMap D e (decoderInput m ℓ v)
  have hisolate := row_cube_coefficient_isolation P hp x (by omega) (fun i => c i.val) Φ
    (by
      intro e i t
      change rowCubeMap D e (decoderInput m ℓ (i.val,t)) = _
      rw [rowCube_decoder_selected D e i t]
      simp [D,coordinateRowCube,d])
    (by
      intro e e' v hv
      exact rowCube_decoder_outside D e e' v.1 hv v.2)
  have hcoefone : P.coeff (rowMonomialExponent x)=1 := by
    have h := hcoeff
    generalize P.coeff (rowMonomialExponent x)=b at *
    fin_cases b
    · exact False.elim (h rfl)
    · rfl
  have hiso : rowCubeDifference D (compactDecoder m ℓ P)=1 := by
    rw [rowCubeDifference_apply]
    simp_rw [rowCube_decoder_comp]
    change (∑ e : S → ZMod 2, aeval (Φ e) P)=1
    rw [hisolate,hcoefone,map_one]
  have hvalue : μ (compactDecoder m ℓ P)=1 := by
    change L (rowCubeDifference D (compactDecoder m ℓ P))=1
    rw [hiso,hL1]
  have hnon : compactDecoder m ℓ P ∉ pcSpace (functionalUnaryBase m (2^ℓ)) B := by
    intro h
    have := hann _ h
    rw [hvalue] at this
    exact one_ne_zero this
  refine ⟨μ,hann,hvalue,?_,?_,hnon,?_⟩
  · intro hpos
    change L (rowCubeDifference D 1)=0
    have hz : rowCubeDifference D 1=0 := by
      apply cubeDifference_low_degree
      simp only [totalDegree_one,Fintype.card_coe]
      rw [hrows,hcard,hdegree]
      exact hpos
    rw [hz,map_zero]
  · intro hz
    have hP : P=1 := by
      have he := totalDegree_eq_zero_iff_eq_C.mp hz
      have hn : P.coeff 0≠0 := by intro h; apply hne; simpa [h] using he
      have hc1 : P.coeff 0=1 := by
        generalize P.coeff 0=b at *
        fin_cases b
        · exact False.elim (hn rfl)
        · rfl
      simpa [hc1] using he
    simpa [hP] using hvalue
  · intro h
    exact hnon (compactDecoder_PC hℓ h)

end

end SATurday.ProofComplexity.BraunPC
