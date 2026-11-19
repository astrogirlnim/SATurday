import Theory.ProofComplexity.FregeDegBridge

/-!
# Frontier: the low degree fragment at degree `(log n)^2`

OPEN.  `FDeg.lowdeg_frege_tseitin_idx` proves a size bound for refutations in the sequent calculus
`FProof`, of any formula depth, whose translated lines have syntactic degree at most `(p-1) ρ` with
`ρ ≤ ε ln n` and `(κ+1) ε < 1`.  The statement below asks for a super polynomial bound when the
degree bound is `(log₂ n)^2`.  No proof is known.  The method of `PolyIndCalc.lean` loses a factor
`cLam^d` in the exponent at degree `d` and gives nothing once `d` exceeds a small multiple of `ln n`.
This is the smallest instance of the wall "degree beyond `ε log n`"; it is implied by the R4 pin for
this family (`AC0pFregeFrontier.r4_target`) and is not known to imply it.  Nothing may depend on it.

LOG: R4 ac0p fable session, Frontier pin for degree log squared
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.TseitinPC

namespace FDegFrontier

/-- OPEN (intentional `sorry`, Frontier quarantine).  Super polynomial size for refutations of the
explicit one hot Tseitin mod `q` family, `p ∤ q`, in the low degree fragment with degree bound
`(log₂ n)^2`, `n = 8 m^2`, at every formula depth. -/
theorem log2_degree_target (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (c : ℕ) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → ∀ L : List Seq,
      FProof p (tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q)) L → (([], []) : Seq) ∈ L →
      (∀ S ∈ L, FDeg.VarS (tVars (cubFam m) q) S) →
      (∀ S ∈ L, FDeg.DegS p (Nat.log 2 (m * m * 8) ^ 2) S) →
      (m * m * 8) ^ c < fSize L + L.length := by
  sorry

end FDegFrontier
