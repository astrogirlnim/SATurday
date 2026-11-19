import Theory.ProofComplexity.FregeRankBridge

/-!
# Frontier: depth one AC0[p] Frege on one hot Tseitin, without the rank condition

OPEN.  `FBridge.depth1_rank_frege_tseitin_idx` proves a size bound for depth one refutations
(`FRefutes p 1`) that use only variables of the formula and in which every `AND` in positive
position and every `OR` in negative position has at most `ρ ≤ ε ln n` members.  The statement
below drops both side conditions and asks only for a super polynomial bound.  No proof is known.
It is the first case of the R4 pin (`AC0pFregeFrontier.r4_target` at `d = 1`, for one candidate
family) that the bridge does not reach.  Nothing may depend on it.

LOG: R4 depth-2 fable session, Frontier pin for the unrestricted depth one statement
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.TseitinPC

namespace FBridgeFrontier

/-- OPEN (intentional `sorry`, Frontier quarantine).  Super polynomial size for depth one
AC0[p] Frege refutations of the explicit one hot Tseitin mod `q` family, `p ∤ q`. -/
theorem depth1_tseitin_target (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (c : ℕ) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → ∀ L : List Seq,
      FRefutes p 1 (tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q)) L →
      (m * m * 8) ^ c < fSize L + L.length := by
  sorry

end FBridgeFrontier
