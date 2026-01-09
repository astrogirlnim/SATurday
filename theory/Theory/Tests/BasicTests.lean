import Theory.Basic

/-!
# Basic Tests for SATurday Theory

Unit tests to verify the Lean 4 setup and basic lemmas.

## Test Cases
- Verify basic arithmetic properties
- Test lemma instantiation
- Ensure mathlib tactics work

LOG: Test module initialized
-/

namespace SATurday.Tests

/-! ## Unit Tests -/

/-- Test that our basic lemmas can be instantiated with concrete values. -/
example : 5 + 0 = 5 := by
  -- LOG: Testing add_zero_eq with n=5
  exact add_zero_eq 5

/-- Test zero_add with a concrete value. -/
example : 0 + 7 = 7 := by
  -- LOG: Testing zero_add_eq with n=7
  exact zero_add_eq 7

/-- Test multiplication by one. -/
example : 1 * 42 = 42 := by
  -- LOG: Testing one_mul_eq with n=42
  exact one_mul_eq 42

/-- Test that we can use mathlib tactics. -/
example (a b : ℕ) : a + b = b + a := by
  -- LOG: Testing mathlib Nat.add_comm tactic
  exact Nat.add_comm a b

/-- Verify basic induction works (important for future proofs). -/
theorem nat_induction_test (n : ℕ) : n + n = 2 * n := by
  -- LOG: Testing induction tactic
  induction n with
  | zero => 
    -- LOG: Base case: 0 + 0 = 2 * 0
    rfl
  | succ n ih =>
    -- LOG: Inductive case: (n+1) + (n+1) = 2 * (n+1)
    rw [Nat.mul_succ, ← ih]
    ring

end SATurday.Tests
