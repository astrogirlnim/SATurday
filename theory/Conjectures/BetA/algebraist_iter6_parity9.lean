import Theory.Circuits
import Tactics.EncodingTactics

namespace SATurday.Conjectures.BetA

-- Algebraist iter6: monotone parity-9 requires more than 3 gates (polynomial degree argument)
theorem algebraist_parity9_lower_bound :
  forall (C : SATurday.Circuits.Circuit),
    C.num_inputs = 9 ->
    SATurday.Circuits.isMonotone C = true ->
    C.computes (SATurday.Circuits.parity C.num_inputs) ->
    C.size > 3 := by
  sorry

end SATurday.Conjectures.BetA
