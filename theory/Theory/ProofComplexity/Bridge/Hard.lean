import Theory.ProofComplexity.Bridge.Reduction
import Theory.ProofComplexity.Bridge.GeneratorBound
import Theory.ProofComplexity.Bridge.CookLevin

/-!
# Hard direction of bridge theorem 1 (Ladder Rung R5)

A polynomially bounded propositional proof system gives `NP = coNP`: every `L ∈ NP`
reduces its complement to `TAUT` by the tableau generator, and `TAUT ∈ NP`.

LOG: R5 Bridge Hard module (complement_in_NP_of_TAUT_NP, bridge_theorem_1_hard)
-/

open Turing
open SATurday.Bridge.SP
open scoped Polynomial

namespace SATurday.Bridge
namespace CL

/-- A polynomial is bounded by `C * (n + 1)^e`. -/
theorem poly_le_pow (q : Polynomial ℕ) : ∃ C e : ℕ, ∀ n, q.eval n ≤ C * (n + 1) ^ e := by
  refine ⟨∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i, q.natDegree, fun n => ?_⟩
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ q.natDegree := by simpa [Nat.lt_succ_iff] using hi
  refine Nat.mul_le_mul_left _ ?_
  calc n ^ i ≤ (n + 1) ^ i := Nat.pow_le_pow_left (Nat.le_succ n) i
    _ ≤ (n + 1) ^ q.natDegree := Nat.pow_le_pow_right (Nat.succ_pos n) hi'

theorem gen_computable (cm : CM) (hc : 0 < cm.c) (hkin : cm.kin < cm.K) (hkout : cm.kout < cm.K)
    (C e : ℕ) :
    Nonempty (TM2ComputableInPolyTime idBitEnc idBitEnc
      (fun x : List Bool => encodeFormula
        (tabFormula cm (C * (x.length + 1) ^ e) (C * (x.length + 1) ^ e) x))) :=
  ⟨(fp_computes cm.nR (cm.genProg C e) (cm.genProg_Ok C e hc hkin hkout) _ (cm.genCostPoly C e)
    (fun x => cm.run_genProg hc hkin hkout C e x)
    (fun x => cm.cost_genProg_le hc hkin hkout C e x)).toPoly⟩

theorem TAUT_encode (φ : PropFormula) : TAUT (encodeFormula φ) ↔ φ.Tautology := by
  constructor
  · rintro ⟨ψ, h1, h2⟩
    rw [decodeFormula_encodeFormula] at h1
    cases h1; exact h2
  · intro h; exact ⟨φ, decodeFormula_encodeFormula φ, h⟩

/-- The tableau reduction: the complement of an NP language reduces to `TAUT`. -/
theorem reduction_exists (L : Language) (hL : InNP L) :
    ∃ g : List Bool → List Bool,
      Nonempty (TM2ComputableInPolyTime idBitEnc idBitEnc g) ∧
      ∀ x, TAUT (g x) ↔ ¬ L x := by
  obtain ⟨p, V, hV, hLx⟩ := hL
  obtain ⟨C, e, hCe⟩ := poly_le_pow (reqPoly p V hV)
  have hwf := verCM_WF (gatedVerifier p V hV) (W := 2 * cc (gatedVerifier p V hV).tm) le_rfl
  have hc : 0 < (redCM p V hV).c := Nat.succ_pos _
  refine ⟨_, gen_computable (redCM p V hV) hc hwf.hkin hwf.hkout C e, fun x => ?_⟩
  rw [TAUT_encode, tab_iff_not_L p V hV x (hCe x.length), hLx]

end CL

/-- A polynomially bounded proof system puts the complement of every NP language in NP. -/
theorem complement_InNP_of_polyBounded {f : List Bool → List Bool}
    (hf : IsPropProofSystem f) (hb : PolynomiallyBounded f) (L : Language) (hL : InNP L) :
    InNP (complement L) := by
  obtain ⟨g, ⟨hg⟩, hgx⟩ := CL.reduction_exists L hL
  obtain ⟨q, hq⟩ := outBound_of_computable hg
  have hq' : ∀ s : List Bool, (g s).length ≤ q.eval s.length := by
    intro s; simpa [idBitEnc] using hq s
  have hmap := mapFstComputableInPolyTime hg q hq'
  have hchk := proofCheckComputableInPolyTime hf.poly
  have hcomp := comp_enc hmap hchk (mapFstPairOutBound q) (by
    intro pw
    have h1 : pw.1.length ≤ (encodePair pw).length := by rw [length_encodePair]; omega
    have h2 := poly_eval_mono q h1
    have h3 := hq' pw.1
    simp only [mapFstPairOutBound_eval, length_encodePair] at *
    omega)
  refine ⟨(Classical.choose hb).comp q, fun x w => proofCheck f (g x) w, hcomp, fun x => ?_⟩
  have hshort := TAUT_short_proofs_of_polyBounded' hf hb (g x)
  show ¬ L x ↔ _
  rw [← hgx x]
  constructor
  · intro h
    obtain ⟨π, h1, h2⟩ := hshort.1 h
    refine ⟨π, ?_, h2⟩
    rw [Polynomial.eval_comp]
    exact h1.trans (poly_eval_mono _ (hq' x))
  · rintro ⟨π, _, h2⟩
    have hπ : f π = g x := (proofCheck_iff f (g x) π).1 h2
    have := hf.sound π
    rwa [hπ] at this

/-- Hard direction of bridge theorem 1. -/
theorem bridge_theorem_1_hard
    (h : ∃ f, Nonempty (IsPropProofSystem f) ∧ PolynomiallyBounded f) :
    ClassNP_eq_ClassCoNP := by
  obtain ⟨f, ⟨hf⟩, hb⟩ := h
  intro L
  constructor
  · exact complement_InNP_of_polyBounded hf hb L
  · intro hc
    have := complement_InNP_of_polyBounded hf hb (complement L) hc
    rwa [complement_complement] at this

end SATurday.Bridge
