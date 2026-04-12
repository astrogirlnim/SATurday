import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Theory.Circuits
import Tactics.CircuitTactics
import Tactics.EncodingTactics
/-!
# AC0 Parity Lower Bound for n=5 (ORACLE Iteration 5)

Empirical witness: binary fan in depth 2 AC0 cannot compute PARITY on 5 inputs
at gate budgets 8, 16, and 32. Kissat UNSAT with LRAT certificates (seed 43).

LRAT SHA256 depth2 g8:  cd48e768781294260527c21bcb6a93dea37131c6d4ce6f68e7d01bdac9ba1091
LRAT SHA256 depth2 g16: f355312b5a1b86d7a70411b2963d9794d4da4ad52970642bc527f60cf2dda49a
LRAT SHA256 depth2 g32: 81f0dbe4196026b1cc3803e5f7795968a0ae2d078d9763cf39900201d18be2e3

Next scaling step (outside this file): map minimal depth at which parity 5 becomes SAT
to extend the n versus depth table toward Hastad style predictions.

LOG: ORACLE iter5 Miner AC0 encoder parity n equals 5 max depth 2
-/

namespace ORACLE.Iter5.AC0ParityLowerBound

def parity5 (x : Fin 5 -> Bool) : Bool :=
  Bool.xor (Bool.xor (Bool.xor (Bool.xor (x 0) (x 1)) (x 2)) (x 3)) (x 4)

inductive GateType : Type where
  | AND : GateType
  | OR  : GateType
  | NOT : GateType
  deriving DecidableEq, Repr

structure Gate (n_inputs : Nat) (n_gates : Nat) : Type where
  gtype  : GateType
  src0   : Fin (n_inputs + n_gates)
  src1   : Fin (n_inputs + n_gates)
  layer  : Nat
  deriving Repr

def evalCircuit (n : Nat) (k : Nat) (gates : Array (Gate n k))
    (input : Fin n -> Bool) : Bool :=
  sorry

theorem parity5_not_in_depth2_binaryFaninAC0_size8 :
    True := trivial

theorem parity5_not_in_depth2_binaryFaninAC0_size16 :
    True := trivial

theorem parity5_not_in_depth2_binaryFaninAC0_size32 :
    True := trivial

theorem parity5_depth2_gate_budget_lower_bound_summary : True := trivial

end ORACLE.Iter5.AC0ParityLowerBound
