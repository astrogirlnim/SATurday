import Theory.ProofComplexity.TseitinExplicit
import Theory.ProofComplexity.PangTseitin

/-!
# Indexed (uniform) Tseitin families (referee repair, quantifier shape U)

`cubFam m` is the explicit graph `mggF2CubGraph` on `n = 8 m^2` vertices (`m * m * 8` in Lean).  For
every `m >= tseitinFloor q` (explicit, computable) the one hot Tseitin formula `tcnf (cubFam m) q b`
is hard, for all `b` (`*_idx`) and for the explicit charge `tseitinCharge1 (m*m*8) q` (`*_idx_explicit`,
together with unsatisfiability).  This replaces `forall N, exists n >= N` by `forall m >= m0`.
It is NOT padding to every `n`: the sizes are `8 m^2` only (consecutive ratio `((m+1)/m)^2`).
-/

namespace SATurday.ProofComplexity
open TseitinPC

/-- The explicit cubic expander family on `m*m*8` vertices (empty graph at `m = 0`). -/
noncomputable def cubFam (m : ℕ) : FinGraph (m * m * 8) :=
  if h : 0 < m then mggF2CubGraph h else ∅

/-- Index floor (not optimized): `m` is at least every threshold used by the proofs. -/
def tseitinFloor (p q : ℕ) : ℕ :=
  mggInformativeFloor + mggF2CubFloor + 4002 + 1312 * (q * (q + 3)) + Pang.cN0 p q +
    (2 + 1312 * (q * (q + 3) + (q - 1) * (p - 1) * (q + 5)))

theorem tseitinFloor_pos (p q : ℕ) : 0 < tseitinFloor p q := by
  unfold tseitinFloor; have : 0 < mggF2CubFloor := by decide
  omega

theorem cubFam_props {m : ℕ} (hI : mggInformativeFloor ≤ m) :
    IsRegular (cubFam m) 3 ∧ (cubFam m).IsConnected ∧ HasExpansionInv (cubFam m) mggF2CubK := by
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < mggInformativeFloor) hI
  simp only [cubFam, dif_pos hm0]
  exact ⟨mggF2Cub_isRegular hm0, mggF2Cub_isConnected hm0, mggF2Cub_hasExpansionInv hm0 hI⟩

theorem cubFam_floor_le {p q m : ℕ} (hm : tseitinFloor p q ≤ m) :
    mggInformativeFloor ≤ m ∧ 4000 + 1312 * (q * (q + 3)) + 2 ≤ m * m * 8 ∧
      Pang.cN0 p q ≤ m * m * 8 ∧
      2 + 1312 * (q * (q + 3) + (q - 1) * (p - 1) * (q + 5)) ≤ m * m * 8 := by
  have h : m ≤ m * m * 8 := by nlinarith [Nat.zero_le m, tseitinFloor_pos p q]
  unfold tseitinFloor at hm
  refine ⟨by omega, by omega, by omega, by omega⟩

namespace TseitinPC
open Finset
noncomputable section
open Classical

/-- Indexed `tseitin_bool_degree_Fp`: for every `m ≥ tseitinFloor p q`. -/
theorem tseitin_bool_degree_Fp_idx {q : ℕ} [NeZero q] (p : ℕ) [Fact p.Prime] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    {m : ℕ} (hm : tseitinFloor p q ≤ m) :
    IsRegular (cubFam m) 3 ∧ (cubFam m).IsConnected ∧ ∀ b : Fin (m * m * 8) → ZMod q,
      ¬ PCD (cnfAx (F := ZMod p) (tcnf (cubFam m) q b)) ((((m * m * 8) - 2) / 1312 - q * (q + 3)) / (q - 1)) 1 := by
  obtain ⟨hI, hn, -, -⟩ := cubFam_floor_le hm
  obtain ⟨hreg, hconn, hexp⟩ := cubFam_props hI
  set n := m * m * 8 with hndef
  set G := cubFam m
  refine ⟨hreg, hconn, fun b => ?_⟩
  haveI : NeZero ((q : ℕ) : ZMod p) := ⟨fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)⟩
  haveI : IsCyclotomicExtension {q} (ZMod p) (CyclotomicField q (ZMod p)) :=
    CyclotomicField.isCyclotomicExtension q (ZMod p)
  have hω := IsCyclotomicExtension.zeta_spec q (ZMod p) (CyclotomicField q (ZMod p))
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

/-- Indexed `reslin_tseitin_size`. -/
theorem reslin_tseitin_size_idx (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) {m : ℕ} (hm : tseitinFloor p q ≤ m) (b : Fin (m * m * 8) → ZMod q) (w s : ℕ) :
    RLF.RLD (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' tcnf (cubFam m) q b) ∪ RLF.boolAx)
        w ∅ s →
      2 ^ (((((m * m * 8) - 2) / 1312 - q * (q + 3)) / (q - 1) - (q + 3) - p) / (p - 1)) ≤ 2 * s := by
  intro h
  obtain ⟨hreg, -, hdeg⟩ := TseitinPC.tseitin_bool_degree_Fp_idx p hq hpq hm
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hs1 : 1 ≤ s := RLF.rld_pos h
  set D := (((m * m * 8) - 2) / 1312 - q * (q + 3)) / (q - 1) with hD
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

/-- Indexed `reslin_tseitin_dag_size`. -/
theorem reslin_tseitin_dag_size_idx (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) {m : ℕ} (hm : tseitinFloor p q ≤ m) :
    q + 5 ≤ tseitinW p q (m * m * 8) ∧
      ∀ b : Fin (m * m * 8) → ZMod q, ∀ 𝓛 : Finset (Finset (RLF.LEq (ZMod p))),
        RLF.RLDag (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' tcnf (cubFam m) q b) ∪
          RLF.boolAx) 𝓛 → (∅ : Finset (RLF.LEq (ZMod p))) ∈ 𝓛 →
        ((tseitinW p q (m * m * 8) - (q + 3)) * (tseitinW p q (m * m * 8) - (q + 3)) <
          72 * (q + 3) * 𝓛.card * (Nat.log 2 (3 * 𝓛.card) + 1)) ∧
        (tseitinW p q (m * m * 8) - (q + 3)) * (tseitinW p q (m * m * 8) - (q + 3)) /
          (72 * (q + 3) * (Nat.log 2 (3 * ((tseitinW p q (m * m * 8) - (q + 3)) *
            (tseitinW p q (m * m * 8) - (q + 3))) ) + 1)) ≤ 𝓛.card := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨-, -, -, hn0⟩ := cubFam_floor_le hm
  obtain ⟨hreg, hconn, hdeg⟩ := TseitinPC.tseitin_bool_degree_Fp_idx p hq hpq hm
  set n := m * m * 8 with hn
  set N0 := 2 + 1312 * (q * (q + 3) + (q - 1) * (p - 1) * (q + 5)) with hN0
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
  refine ⟨hW, fun b 𝓛 h h0 => ?_⟩
  have hmain := RLF.reslin_dag_size_of_pc_degree p (Φ := tcnf (cubFam m) q b) (w0 := q + 3)
    (fun C hC => (tcnf_clause_props hreg hC).2) (D := D) (by have : q + 5 ≤ D / (p - 1) := hW; omega) (hdeg b) h h0
  have hmax : max (q + 3) 3 = q + 3 := max_eq_left (by omega)
  rw [hmax] at hmain
  exact ⟨hmain, RLF.lines_lower_bound _ _ _ (by omega) hmain⟩

end SATurday.ProofComplexity

open SATurday.ProofComplexity SATurday.ProofComplexity.TseitinPC

namespace Pang
/-- Indexed `tseitin_dag_exp`. -/
theorem tseitin_dag_exp_idx (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    {m : ℕ} (hm : tseitinFloor p q ≤ m) (b : Fin (m * m * 8) → ZMod q) :
    ∀ R : Pang.Refutation (tcnf (cubFam m) q b) (tVars (cubFam m) q) p,
      2 ^ ((m * m * 8) / cC p q) ≤ R.S := by
  obtain ⟨-, -, hn, -⟩ := cubFam_floor_le hm
  obtain ⟨hreg, hconn, hdeg⟩ := tseitin_bool_degree_Fp_idx p hq hpq hm
  have hn0 : 0 < m * m * 8 := by unfold cN0 at hn; omega
  intro R
  refine exp_of_degree R hq hn ?_ ?_ (fun C hC => (tcnf_clause_props hreg hC).2) ?_
  · have := card_G_ge hreg
    have := card_tVars_ge (q := q) hn0 (cubFam m)
    omega
  · have h1 := card_tVars_le (q := q) (cubFam m)
    have h2 := card_G_le hreg
    calc (tVars (cubFam m) q).card ≤ (cubFam m).card * q := h1
      _ ≤ (3 * (m * m * 8)) * q := Nat.mul_le_mul_right _ h2
  · intro h
    rcases h with h0 | hp
    · exact one_ne_zero h0
    · exact hdeg b hp

end Pang

namespace C1
/-- Indexed `c1_tseitin_exp`. -/
theorem c1_tseitin_exp_idx (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    {m : ℕ} (hm : tseitinFloor p q ≤ m) (b : Fin (m * m * 8) → ZMod q) :
    ∀ ρ : ℕ, 1 ≤ ρ → cN0R p q ((p - 1) * ρ) ≤ m * m * 8 →
      ∀ R : RRefutation (tcnf (cubFam m) q b) (tVars (cubFam m) q) ρ p,
        2 ^ ((m * m * 8) / cCR p q ((p - 1) * ρ)) ≤ R.S := by
  obtain ⟨hreg, hconn, hdeg⟩ := tseitin_bool_degree_Fp_idx p hq hpq hm
  intro ρ hρ hn R
  have hn0 : 0 < m * m * 8 := by unfold cN0R at hn; omega
  refine exp_of_degree_R R rfl hρ hq hn ?_ ?_ (fun C hC => (tcnf_clause_props hreg hC).2) ?_
  · have := card_G_ge hreg
    have := card_tVars_ge (q := q) hn0 (cubFam m)
    omega
  · have h1 := Pang.card_tVars_le (q := q) (cubFam m)
    have h2 := Pang.card_G_le hreg
    calc (tVars (cubFam m) q).card ≤ (cubFam m).card * q := h1
      _ ≤ (3 * (m * m * 8)) * q := Nat.mul_le_mul_right _ h2
  · intro h
    rcases h with h0 | hp
    · exact one_ne_zero h0
    · exact hdeg b hp

/-- Indexed `c1_main`: there is a threshold `m0` (depending on `p, q, ε`) such that for every
`m ≥ m0` the bound holds on `cubFam m`, `n = 8 m^2`. -/
theorem c1_main_idx (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (ε : ℝ) (hε : 0 < ε) (hεκ : (kappa p q + 1) * ε < 1) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → ∀ b : Fin (m * m * 8) → ZMod q,
      ∀ ρ : ℕ, 1 ≤ ρ → (ρ : ℝ) ≤ ε * Real.log (m * m * 8 : ℕ) →
      ∀ R : RRefutation (tcnf (cubFam m) q b) (tVars (cubFam m) q) ρ p,
        Real.exp (((m * m * 8 : ℕ) : ℝ) ^ (1 - (kappa p q + 1) * ε)) ≤ R.S := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨M₀, hM₀⟩ := eventually_conditions p q hp ε hε
  refine ⟨max M₀ (tseitinFloor p q), fun m hm b ρ hρ1 hρ R => ?_⟩
  have hmF : tseitinFloor p q ≤ m := (le_max_right _ _).trans hm
  have hmM : M₀ ≤ m := (le_max_left _ _).trans hm
  have hmn : m ≤ m * m * 8 := by nlinarith [tseitinFloor_pos p q]
  obtain ⟨h2, hE1, hE2⟩ := hM₀ (m * m * 8) (hmM.trans hmn)
  obtain ⟨hc, hex⟩ := real_chain p q ρ (m * m * 8) hp hq ε hε hεκ hρ1 hρ h2 hE1 hE2
  have hS := c1_tseitin_exp_idx p hq hpq hmF b ρ hρ1 hc R
  refine hex.trans ?_
  exact_mod_cast hS

end C1

namespace SATurday.ProofComplexity

/-- The explicit hard instance of size index `m`: `cubFam m` with charge 1 at vertex 0. -/
theorem tseitin_idx_explicit_unsat (p : ℕ) {q : ℕ} [NeZero q] (hq : 2 ≤ q) {m : ℕ}
    (hm : tseitinFloor p q ≤ m) :
    ∑ v, tseitinCharge1 (m * m * 8) q v ≠ 0 ∧
      ¬ Satisfiable (tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q)) := by
  have h : 0 < m * m * 8 := by
    have := tseitinFloor_pos p q
    have : 0 < m := by omega
    positivity
  exact ⟨tseitinCharge1_sum h q hq, tcnf_charge1_unsat h _ q hq⟩

/-- Consecutive sizes: `(m+1)^2 * 8 ≤ 2 * (m^2 * 8)` for `m ≥ 3`, so the family has no gap larger
than a factor `2` (this is all that the `8 m^2` family offers; it is not a family for every `n`). -/
theorem cubFam_size_gap {m : ℕ} (hm : 3 ≤ m) : (m + 1) * (m + 1) * 8 ≤ 2 * (m * m * 8) := by
  nlinarith

end SATurday.ProofComplexity
