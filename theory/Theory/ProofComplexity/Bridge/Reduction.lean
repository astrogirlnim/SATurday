import Theory.ProofComplexity.Bridge.Generator
import Theory.ProofComplexity.Bridge.TM2CM
import Theory.ProofComplexity.Bridge.CookReckhow

/-!
# The Cook Levin reduction (Ladder Rung R5, hard direction)

For an NP language `L` with verifier `V` the tableau formula of the verifier machine is a
tautology exactly when `x ∉ L`.

LOG: R5 Bridge Reduction module (tableau of the verifier, semantic equivalence)
-/

open Turing
open scoped Polynomial

namespace SATurday.Bridge
namespace CL

section Semantic

open Classical

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable (p : Polynomial ℕ) (V : List Bool → List Bool → Bool)
  (hV : TM2ComputableInPolyTime encodePair bitEnc (fun pw => V pw.1 pw.2))

/-- The machine with the length gate built in. -/
noncomputable def gatedVerifier :
    TM2ComputableInPolyTime encodePair bitEnc (fun pw => acceptWitness p V pw.1 pw.2) :=
  acceptWitnessComputableInPolyTime p V hV

/-- Polynomial that bounds everything the tableau needs, in the input length. -/
noncomputable def reqPoly : Polynomial ℕ :=
  (2 * Polynomial.X + 1 + p) +
    (((gatedVerifier p V hV).time.comp (2 * Polynomial.X + 1 + p)) *
      Polynomial.C (TM2Bound.stepBudget (gatedVerifier p V hV).tm)) +
    (gatedVerifier p V hV).time.comp (2 * Polynomial.X + 1 + p) +
    Polynomial.C (2 * cc (gatedVerifier p V hV).tm + 1)

/-- The coded machine of the gated verifier. -/
noncomputable def redCM : CM := verCM (gatedVerifier p V hV)

theorem redCM_c : (redCM p V hV).c = cc (gatedVerifier p V hV).tm := rfl

theorem reqPoly_eval (n : ℕ) :
    (reqPoly p V hV).eval n =
      (2 * n + 1 + p.eval n) +
      (gatedVerifier p V hV).time.eval (2 * n + 1 + p.eval n) *
        TM2Bound.stepBudget (gatedVerifier p V hV).tm +
      (gatedVerifier p V hV).time.eval (2 * n + 1 + p.eval n) +
      (2 * cc (gatedVerifier p V hV).tm + 1) := by
  simp [reqPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat, Polynomial.eval_one]

theorem tab_iff_not_L (x : List Bool) {P : ℕ} (hP : (reqPoly p V hV).eval x.length ≤ P) :
    (tabFormula (redCM p V hV) P P x).Tautology ↔
      ¬ ∃ w : List Bool, w.length ≤ p.eval x.length ∧ V x w = true := by
  set h := gatedVerifier p V hV with hh
  have hreq := reqPoly_eval p V hV x.length
  rw [← hh] at hreq
  set N0 := 2 * x.length + 1 + p.eval x.length with hN0
  have hk : 0 < cc h.tm := Nat.succ_pos _
  have hPge : N0 + h.time.eval N0 * TM2Bound.stepBudget h.tm + h.time.eval N0 +
      (2 * cc h.tm + 1) ≤ P := by omega
  have hwf : (redCM p V hV).WF P := verCM_WF h (by omega)
  have hW : 2 * x.length + 1 + 2 * (redCM p V hV).c ≤ P := by
    have : (redCM p V hV).c = cc h.tm := rfl
    have : 2 * x.length + 1 ≤ N0 := by omega
    omega
  rw [tabFormula_taut_iff (redCM p V hV) hwf hW]
  constructor
  · intro hn ⟨w, hw, hVw⟩
    apply hn
    have hacc : (fun pw : List Bool × List Bool => acceptWitness p V pw.1 pw.2) (x, w) = true := by
      simp only [acceptWitness_iff]; exact ⟨hw, hVw⟩
    have hlen : (encodePair (x, w)).length = 2 * x.length + 1 + w.length := length_encodePair' x w
    have hle : (encodePair (x, w)).length ≤ N0 := by omega
    have hT : h.time.eval (encodePair (x, w)).length ≤ h.time.eval N0 := poly_eval_mono _ hle
    have hTb : h.time.eval (encodePair (x, w)).length * TM2Bound.stepBudget h.tm ≤
        h.time.eval N0 * TM2Bound.stepBudget h.tm := Nat.mul_le_mul_right _ hT
    refine ⟨w, ?_, ?_⟩
    · have : (redCM p V hV).c = cc h.tm := rfl
      omega
    · exact accept_of_true h x w hacc (W := P) (B := P) (by omega) (by omega) (by omega)
  · intro hn ⟨w, hsz, hno, hacc⟩
    apply hn
    have := true_of_accepts h x w (W := P) (B := P) (by omega) hno hacc
    simp only [acceptWitness_iff] at this
    exact ⟨w, this⟩

end Semantic

end CL
end SATurday.Bridge
