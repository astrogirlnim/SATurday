import Theory.ProofComplexity.ResLinDagSize
import Theory.ProofComplexity.PangTseitin
import Theory.ProofComplexity.C1Final

/-!
# Explicit hard instances with connectedness (referee repair, work item 1 and 2a)

The headline one hot Tseitin theorems are stated `∃ n G, ... IsRegular G 3 ∧ ∀ b, ...`: they hide
(i) that the graphs are connected (this is proved by `exists_mggF2Cub_hasExpansionInv_family` but
dropped) and (ii) that the quantifier `∀ b` includes satisfiable charges.  This module restates each
of them (`*_conn`, with `G.IsConnected`; proofs are the original proofs verbatim) and then gives
`*_explicit`: the same bound for the single explicit charge `tseitinCharge1 n q` (charge 1 at
vertex 0, charge 0 elsewhere), whose total is `1 ≠ 0`, together with `¬ Satisfiable`.
The original theorems are unchanged.
-/

namespace SATurday.ProofComplexity

open TseitinPC

/-- The explicit charge: `1` at vertex `0`, `0` elsewhere. -/
def tseitinCharge1 (n q : ℕ) [NeZero q] : Fin n → ZMod q := fun v => if v.val = 0 then 1 else 0

theorem tseitinCharge1_sum {n : ℕ} (hn : 0 < n) (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    ∑ v, tseitinCharge1 n q v ≠ 0 := by
  haveI : Fact (1 < q) := ⟨hq⟩
  have : ∑ v, tseitinCharge1 n q v = 1 := by
    rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
    · simp [tseitinCharge1]
    · intro v _ hv
      have : v.val ≠ 0 := fun h => hv (Fin.ext h)
      simp [tseitinCharge1, this]
    · simp
  rw [this]; exact one_ne_zero

/-- The explicit instance is unsatisfiable. -/
theorem tcnf_charge1_unsat {n : ℕ} (hn : 0 < n) (G : FinGraph n) (q : ℕ) [NeZero q] (hq : 2 ≤ q) :
    ¬ Satisfiable (tcnf G q (tseitinCharge1 n q)) :=
  tcnf_unsat (tseitinCharge1_sum hn q hq)

namespace TseitinPC
open Finset
noncomputable section
open Classical

/-- `tseitin_bool_degree_Fp` with the connectedness conjunct kept. -/
theorem tseitin_bool_degree_Fp_conn {q : ℕ} [NeZero q] (p : ℕ) [Fact p.Prime] (hq : 2 ≤ q) (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧ ∀ b : Fin n → ZMod q,
      ¬ PCD (cnfAx (F := ZMod p) (tcnf G q b)) (((n - 2) / 1312 - q * (q + 3)) / (q - 1)) 1 := by
  obtain ⟨n, G, hN, hreg, hconn, hexp⟩ :=
    exists_mggF2Cub_hasExpansionInv_family (max N (4000 + 1312 * (q * (q + 3)) + 2))
  refine ⟨n, G, le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN), hreg, hconn, fun b => ?_⟩
  have hn : 4000 + 1312 * (q * (q + 3)) + 2 ≤ n :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  haveI : NeZero ((q : ℕ) : ZMod p) := ⟨fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)⟩
  haveI : IsCyclotomicExtension {q} (ZMod p) (CyclotomicField q (ZMod p)) :=
    CyclotomicField.isCyclotomicExtension q (ZMod p)
  have hω := IsCyclotomicExtension.zeta_spec q (ZMod p) (CyclotomicField q (ZMod p))
  -- an edge exists: vertex `0` has degree 3
  have hdeg0 := hreg ⟨0, by omega⟩
  obtain ⟨e0, he0⟩ : (incident G ⟨0, by omega⟩).Nonempty := by
    rw [← card_pos]; unfold degree at hdeg0; omega
  have he0G : e0 ∈ G := (mem_incident_iff.1 he0).1
  have hk : mggF2CubK = 164 := rfl
  set d := ((n - 2) / 1312 - q * (q + 3)) / (q - 1)
  refine tseitin_bool_degree (algebraMap (ZMod p) (CyclotomicField q (ZMod p))) hω hq (by omega) hexp b he0G
    (Δ := 3) (fun v => (hreg v).le) ?_
  rw [hk]
  have h1 : (q - 1) * d ≤ (n - 2) / 1312 - q * (q + 3) := by
    have := Nat.div_mul_le_self ((n - 2) / 1312 - q * (q + 3)) (q - 1)
    rw [mul_comm]; exact this
  have h2 : (n - 2) / 1312 * 1312 ≤ n - 2 := Nat.div_mul_le_self _ _
  have h3 : q * q + q * 3 = q * (q + 3) := by ring
  have hX : q * (q + 3) ≤ (n - 2) / 1312 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 1312), mul_comm]
    omega
  omega

end
end TseitinPC

/-- `reslin_tseitin_size` with `G.IsConnected`. -/
theorem reslin_tseitin_size_conn (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧ ∀ b : Fin n → ZMod q, ∀ w s : ℕ,
      RLF.RLD (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' tcnf G q b) ∪ RLF.boolAx)
        w ∅ s →
      2 ^ ((((n - 2) / 1312 - q * (q + 3)) / (q - 1) - (q + 3) - p) / (p - 1)) ≤ 2 * s := by
  obtain ⟨n, G, hN, hreg, hconn, hdeg⟩ := tseitin_bool_degree_Fp_conn p hq hpq N
  refine ⟨n, G, hN, hreg, hconn, fun b w s h => ?_⟩
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hs1 : 1 ≤ s := RLF.rld_pos h
  set D := ((n - 2) / 1312 - q * (q + 3)) / (q - 1) with hD
  set k := Nat.clog 2 s with hk
  have hlt : D < (q + 3) + (p - 1) * k + p := by
    by_contra hcon
    rw [not_lt] at hcon
    refine hdeg b (pcd_mono hcon (RLF.rld_cnf_size (by omega) (fun C hC => ?_) h))
    exact (tcnf_clause_props hreg hC).2
  have h1 : (D - (q + 3) - p) / (p - 1) ≤ k := Nat.div_le_of_le_mul (by omega)
  refine le_trans (Nat.pow_le_pow_right (by norm_num) h1) ?_
  rcases Nat.lt_or_ge 1 s with hs | hs
  · have h2 : 2 ^ (k - 1) < s := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hs
    have hk1 : 1 ≤ k := Nat.clog_pos (by norm_num) hs
    have : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  · have : s = 1 := by omega
    subst this
    simp [hk]

/-- `reslin_tseitin_dag_size` with `G.IsConnected`. -/
theorem reslin_tseitin_dag_size_conn (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧ q + 5 ≤ tseitinW p q n ∧
      ∀ b : Fin n → ZMod q, ∀ 𝓛 : Finset (Finset (RLF.LEq (ZMod p))),
        RLF.RLDag (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' tcnf G q b) ∪
          RLF.boolAx) 𝓛 → (∅ : Finset (RLF.LEq (ZMod p))) ∈ 𝓛 →
        ((tseitinW p q n - (q + 3)) * (tseitinW p q n - (q + 3)) <
          72 * (q + 3) * 𝓛.card * (Nat.log 2 (3 * 𝓛.card) + 1)) ∧
        (tseitinW p q n - (q + 3)) * (tseitinW p q n - (q + 3)) /
          (72 * (q + 3) * (Nat.log 2 (3 * ((tseitinW p q n - (q + 3)) *
            (tseitinW p q n - (q + 3))) ) + 1)) ≤ 𝓛.card := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  set N0 := 2 + 1312 * (q * (q + 3) + (q - 1) * (p - 1) * (q + 5)) with hN0
  obtain ⟨n, G, hN, hreg, hconn, hdeg⟩ := TseitinPC.tseitin_bool_degree_Fp_conn p hq hpq (max N N0)
  have hnN : N ≤ n := (le_max_left _ _).trans hN
  have hn0 : N0 ≤ n := (le_max_right _ _).trans hN
  set D := ((n - 2) / 1312 - q * (q + 3)) / (q - 1) with hD
  have hq1 : 0 < q - 1 := by omega
  have hp1 : 0 < p - 1 := by omega
  have hW : q + 5 ≤ tseitinW p q n := by
    unfold tseitinW
    rw [Nat.le_div_iff_mul_le hp1]
    have hDq : (p - 1) * (q + 5) ≤ D := by
      rw [hD, Nat.le_div_iff_mul_le hq1]
      have h1 : q * (q + 3) + (q - 1) * (p - 1) * (q + 5) ≤ (n - 2) / 1312 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        omega
      have : (p - 1) * (q + 5) * (q - 1) = (q - 1) * (p - 1) * (q + 5) := by ring
      omega
    nlinarith
  refine ⟨n, G, hnN, hreg, hconn, hW, fun b 𝓛 h h0 => ?_⟩
  have hmain := RLF.reslin_dag_size_of_pc_degree p (Φ := tcnf G q b) (w0 := q + 3)
    (fun C hC => (tcnf_clause_props hreg hC).2) (D := D) (by have : q + 5 ≤ D / (p - 1) := hW; omega) (hdeg b) h h0
  have hmax : max (q + 3) 3 = q + 3 := max_eq_left (by omega)
  rw [hmax] at hmain
  exact ⟨hmain, RLF.lines_lower_bound _ _ _ (by omega) hmain⟩

end SATurday.ProofComplexity

open SATurday.ProofComplexity SATurday.ProofComplexity.TseitinPC

namespace Pang
/-- `tseitin_dag_exp` with `G.IsConnected`. -/
theorem tseitin_dag_exp_conn (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧ ∀ b : Fin n → ZMod q,
      ∀ R : Pang.Refutation (tcnf G q b) (tVars G q) p, 2 ^ (n / cC p q) ≤ R.S := by
  obtain ⟨n, G, hN, hreg, hconn, hdeg⟩ := tseitin_bool_degree_Fp_conn p hq hpq (max N (cN0 p q))
  have hn : cN0 p q ≤ n := (le_max_right _ _).trans hN
  have hn0 : 0 < n := by unfold cN0 at hn; omega
  refine ⟨n, G, (le_max_left _ _).trans hN, hreg, hconn, fun b R => ?_⟩
  refine exp_of_degree R hq hn ?_ ?_ (fun C hC => (tcnf_clause_props hreg hC).2) ?_
  · have := card_G_ge hreg
    have := card_tVars_ge (q := q) hn0 G
    omega
  · have h1 := card_tVars_le (q := q) G
    have h2 := card_G_le hreg
    calc (tVars G q).card ≤ G.card * q := h1
      _ ≤ (3 * n) * q := Nat.mul_le_mul_right _ h2
  · intro h
    rcases h with h0 | hp
    · exact one_ne_zero h0
    · exact hdeg b hp

end Pang

namespace C1
/-- `c1_tseitin_exp'` with `G.IsConnected`. -/
theorem c1_tseitin_exp_conn (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧ ∀ b : Fin n → ZMod q,
      ∀ ρ : ℕ, 1 ≤ ρ → cN0R p q ((p - 1) * ρ) ≤ n →
      ∀ R : RRefutation (tcnf G q b) (tVars G q) ρ p,
        2 ^ (n / cCR p q ((p - 1) * ρ)) ≤ R.S := by
  obtain ⟨n, G, hN, hreg, hconn, hdeg⟩ := tseitin_bool_degree_Fp_conn p hq hpq N
  refine ⟨n, G, hN, hreg, hconn, fun b ρ hρ hn R => ?_⟩
  have hn0 : 0 < n := by unfold cN0R at hn; omega
  refine exp_of_degree_R R rfl hρ hq hn ?_ ?_ (fun C hC => (tcnf_clause_props hreg hC).2) ?_
  · have := card_G_ge hreg
    have := card_tVars_ge (q := q) hn0 G
    omega
  · have h1 := Pang.card_tVars_le (q := q) G
    have h2 := Pang.card_G_le hreg
    calc (tVars G q).card ≤ G.card * q := h1
      _ ≤ (3 * n) * q := Nat.mul_le_mul_right _ h2
  · intro h
    rcases h with h0 | hp
    · exact one_ne_zero h0
    · exact hdeg b hp

/-- `c1_main` with `G.IsConnected`. -/
theorem c1_main_conn (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (ε : ℝ) (hε : 0 < ε) (hεκ : (kappa p q + 1) * ε < 1) (M : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), M ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧ ∀ b : Fin n → ZMod q,
      ∀ ρ : ℕ, 1 ≤ ρ → (ρ : ℝ) ≤ ε * Real.log n →
      ∀ R : RRefutation (tcnf G q b) (tVars G q) ρ p,
        Real.exp ((n : ℝ) ^ (1 - (kappa p q + 1) * ε)) ≤ R.S := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨M₀, hM₀⟩ := eventually_conditions p q hp ε hε
  obtain ⟨n, G, hN, hreg, hconn, H⟩ := c1_tseitin_exp_conn p hq hpq (max M M₀)
  have hnM₀ : M₀ ≤ n := (le_max_right _ _).trans hN
  obtain ⟨h2, hE1, hE2⟩ := hM₀ n hnM₀
  refine ⟨n, G, (le_max_left _ _).trans hN, hreg, hconn, fun b ρ hρ1 hρ R => ?_⟩
  obtain ⟨hc, hex⟩ := real_chain p q ρ n hp hq ε hε hεκ hρ1 hρ h2 hE1 hE2
  have hS := H b ρ hρ1 hc R
  refine hex.trans ?_
  exact_mod_cast hS

end C1

namespace SATurday.ProofComplexity

open TseitinPC

theorem reslin_tseitin_size_explicit (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧
      ∑ v, tseitinCharge1 n q v ≠ 0 ∧ ¬ Satisfiable (tcnf G q (tseitinCharge1 n q)) ∧
      ∀ w s : ℕ,
        RLF.RLD (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' tcnf G q (tseitinCharge1 n q)) ∪
          RLF.boolAx) w ∅ s →
        2 ^ ((((n - 2) / 1312 - q * (q + 3)) / (q - 1) - (q + 3) - p) / (p - 1)) ≤ 2 * s := by
  obtain ⟨n, G, hN, hreg, hconn, H⟩ := reslin_tseitin_size_conn p hq hpq (N + 1)
  exact ⟨n, G, by omega, hreg, hconn, tseitinCharge1_sum (by omega) q hq,
    tcnf_charge1_unsat (by omega) G q hq, fun w s h => H _ w s h⟩

theorem reslin_tseitin_dag_size_explicit (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧ q + 5 ≤ tseitinW p q n ∧
      ∑ v, tseitinCharge1 n q v ≠ 0 ∧ ¬ Satisfiable (tcnf G q (tseitinCharge1 n q)) ∧
      ∀ 𝓛 : Finset (Finset (RLF.LEq (ZMod p))),
        RLF.RLDag (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' tcnf G q (tseitinCharge1 n q)) ∪
          RLF.boolAx) 𝓛 → (∅ : Finset (RLF.LEq (ZMod p))) ∈ 𝓛 →
        ((tseitinW p q n - (q + 3)) * (tseitinW p q n - (q + 3)) <
          72 * (q + 3) * 𝓛.card * (Nat.log 2 (3 * 𝓛.card) + 1)) ∧
        (tseitinW p q n - (q + 3)) * (tseitinW p q n - (q + 3)) /
          (72 * (q + 3) * (Nat.log 2 (3 * ((tseitinW p q n - (q + 3)) *
            (tseitinW p q n - (q + 3))) ) + 1)) ≤ 𝓛.card := by
  obtain ⟨n, G, hN, hreg, hconn, hW, H⟩ := reslin_tseitin_dag_size_conn p hq hpq (N + 1)
  exact ⟨n, G, by omega, hreg, hconn, hW, tseitinCharge1_sum (by omega) q hq,
    tcnf_charge1_unsat (by omega) G q hq, fun 𝓛 h h0 => H _ 𝓛 h h0⟩

theorem tseitin_dag_exp_explicit (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧
      ∑ v, tseitinCharge1 n q v ≠ 0 ∧ ¬ Satisfiable (tcnf G q (tseitinCharge1 n q)) ∧
      ∀ R : Pang.Refutation (tcnf G q (tseitinCharge1 n q)) (tVars G q) p,
        2 ^ (n / Pang.cC p q) ≤ R.S := by
  obtain ⟨n, G, hN, hreg, hconn, H⟩ := Pang.tseitin_dag_exp_conn p hq hpq (N + 1)
  exact ⟨n, G, by omega, hreg, hconn, tseitinCharge1_sum (by omega) q hq,
    tcnf_charge1_unsat (by omega) G q hq, fun R => H _ R⟩

theorem c1_main_explicit (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (ε : ℝ) (hε : 0 < ε) (hεκ : (C1.kappa p q + 1) * ε < 1) (M : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), M ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧
      ∑ v, tseitinCharge1 n q v ≠ 0 ∧ ¬ Satisfiable (tcnf G q (tseitinCharge1 n q)) ∧
      ∀ ρ : ℕ, 1 ≤ ρ → (ρ : ℝ) ≤ ε * Real.log n →
      ∀ R : C1.RRefutation (tcnf G q (tseitinCharge1 n q)) (tVars G q) ρ p,
        Real.exp ((n : ℝ) ^ (1 - (C1.kappa p q + 1) * ε)) ≤ R.S := by
  obtain ⟨n, G, hN, hreg, hconn, H⟩ := C1.c1_main_conn p hq hpq ε hε hεκ (M + 1)
  exact ⟨n, G, by omega, hreg, hconn, tseitinCharge1_sum (by omega) q hq,
    tcnf_charge1_unsat (by omega) G q hq, fun ρ h1 h2 R => H _ ρ h1 h2 R⟩

end SATurday.ProofComplexity
