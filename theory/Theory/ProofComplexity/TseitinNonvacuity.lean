import Theory.ProofComplexity.TseitinExplicit
import Theory.ProofComplexity.TseitinSat
import Theory.ProofComplexity.PangComplete

/-!
# Nonvacuity of the explicit Tseitin lower bounds (referee repair, 2)

For the explicit connected cubic instance with charge `1` at one vertex: the CNF is unsatisfiable
(`tcnf_charge1_unsat`), a `Pang.Refutation` exists (`pang_refutation_exists_charge1`, existence
only, no size control, via simulation of resolution completeness), and every such refutation has
`2^(n / C)` nodes (`tseitin_dag_exp_explicit`).  On connected graphs the one hot formula is
satisfiable exactly when the total charge is `0` (`TseitinPC.tcnf_sat_iff`).
-/

namespace SATurday.ProofComplexity

open TseitinPC

/-- A `Pang.Refutation` exists for the explicit unsatisfiable instance on every cubic graph. -/
theorem pang_refutation_exists_charge1 (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {n : ℕ} (hn : 0 < n) {G : FinGraph n} (hreg : IsRegular G 3) :
    Nonempty (Pang.Refutation (tcnf G q (tseitinCharge1 n q)) (tVars G q) p) :=
  Pang.refutation_of_unsat
    (fun C hC l hl => (tcnf_clause_props hreg hC).1 (Finset.mem_image.2 ⟨l, hl, rfl⟩))
    (tcnf_charge1_unsat hn G q hq)

/-- Explicit, connected, nonvacuous exponential lower bound for dag-like `Res(lin F_p)`
(Pang's calculus): the instance is unsatisfiable, refutations exist, and all have `≥ 2^(n/C)` nodes. -/
theorem tseitin_dag_exp_explicit_nonvacuous (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧
      ∑ v, tseitinCharge1 n q v ≠ 0 ∧ ¬ Satisfiable (tcnf G q (tseitinCharge1 n q)) ∧
      Nonempty (Pang.Refutation (tcnf G q (tseitinCharge1 n q)) (tVars G q) p) ∧
      ∀ R : Pang.Refutation (tcnf G q (tseitinCharge1 n q)) (tVars G q) p,
        2 ^ (n / Pang.cC p q) ≤ R.S := by
  obtain ⟨n, G, hN, hreg, hconn, hs, hu, H⟩ := tseitin_dag_exp_explicit p hq hpq (N + 1)
  have hn : 0 < n := by omega
  exact ⟨n, G, by omega, hreg, hconn, hs, hu, pang_refutation_exists_charge1 p hq hn hreg, H⟩

end SATurday.ProofComplexity
