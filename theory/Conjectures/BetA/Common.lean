import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Theory.Circuits

/-!
# Common Definitions for Bet A

Shared definitions used across all Bet A conjectures and proofs.

## Contents
- Parity function (polymorphic)
- Common circuit properties
- Shared lemmas

LOG: Common definitions for Bet A circuit lower bounds
-/

namespace SATurday.Conjectures.BetA

open SATurday.Circuits

/-! ## Target Functions -/

/-- Parity function on n inputs: true if odd number of inputs are true.
    
    This is the polymorphic definition used across all parity theorems.
-/
def parity (n : ℕ) (inputs : Fin n → Bool) : Bool :=
  (Finset.univ.sum fun i => if inputs i then (1 : ℕ) else 0) % 2 = 1

/-! ## Common Lemmas -/

/-- Parity of empty input is false. -/
lemma parity_zero : parity 0 = fun _ => false := by
  funext _
  simp [parity]

/-- Parity on single input is identity. -/
lemma parity_one : parity 1 = fun inputs => inputs ⟨0, Nat.zero_lt_one⟩ := by
  funext inputs
  simp [parity]
  sorry  -- TODO: Complete simple proof

/-! ## Monotone Circuit Properties -/

/-- Helper: Any monotone circuit computing parity needs multiple gates. -/
lemma monotone_parity_needs_gates (n : ℕ) (hn : 1 < n) :
  ∀ (C : Circuit), C.num_inputs = n → isMonotone C = true →
    C.computes (parity C.num_inputs) → 1 < C.size := by
  intro C _ _ _
  -- Parity requires non-trivial computation
  sorry  -- TODO: Formalize

end SATurday.Conjectures.BetA
