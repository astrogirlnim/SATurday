import Theory.ProofComplexity.TseitinIndexed
import Theory.ProofComplexity.ResLinDagSize
import Theory.ProofComplexity.ResLinTseitin
import Theory.ProofComplexity.C1Final

/-!
# Follow-ups to the outside referee review (statement fidelity)

See `docs/reports/response-to-expert-review-2026-11-19.md`, Section C.

1. Expander forms: the headline Tseitin theorems with the conjuncts `G.IsConnected` and
   `HasExpansionInv G mggF2CubK` in the conclusion, so the statement itself displays that the family
   consists of connected cubic edge expanders.  New theorems; the originals are unchanged.
2. Prime `q` corollaries: `q.Prime`, `q ≠ p` (the hypothesis of Pang, arXiv:2610.00837, Theorem
   7.2(b)) instead of `2 ≤ q`, `¬ p ∣ q`.
4. Explicit exponent thresholds: for which `n` the displayed exponents are at least `k`.
-/

namespace SATurday.ProofComplexity

open TseitinPC

/-- Facts about `cubFam m` used by all expander forms. -/
theorem cubFam_expander {p q N m : ℕ} (hm : max N (tseitinFloor p q) ≤ m) :
    N ≤ m * m * 8 ∧ IsRegular (cubFam m) 3 ∧ (cubFam m).IsConnected ∧
      HasExpansionInv (cubFam m) mggF2CubK := by
  have hF : tseitinFloor p q ≤ m := (le_max_right _ _).trans hm
  have hN : N ≤ m := (le_max_left _ _).trans hm
  have h0 := tseitinFloor_pos p q
  have : m ≤ m * m * 8 := by nlinarith [Nat.zero_le m]
  obtain ⟨hI, -, -, -⟩ := cubFam_floor_le hF
  exact ⟨hN.trans this, cubFam_props hI⟩

/-- `p ∤ q` for distinct primes. -/
theorem not_dvd_of_prime_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p) : ¬ p ∣ q :=
  fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hq).1 h).symm

/-! ## 1. Expander forms -/

/-- **`Pang.tseitin_dag_exp` with expansion.** -/
theorem tseitin_dag_exp_expander (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧
      HasExpansionInv G mggF2CubK ∧ ∀ b : Fin n → ZMod q,
      ∀ R : Pang.Refutation (tcnf G q b) (tVars G q) p, 2 ^ (n / Pang.cC p q) ≤ R.S := by
  obtain ⟨hN, hreg, hconn, hexp⟩ := cubFam_expander (p := p) (q := q) (N := N)
    (m := max N (tseitinFloor p q)) le_rfl
  exact ⟨_, cubFam (max N (tseitinFloor p q)), hN, hreg, hconn, hexp, fun b R =>
    Pang.tseitin_dag_exp_idx p hq hpq (le_max_right _ _) b R⟩

/-- **`reslin_tseitin_size` with expansion.** -/
theorem reslin_tseitin_size_expander (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧
      HasExpansionInv G mggF2CubK ∧ ∀ b : Fin n → ZMod q, ∀ w s : ℕ,
      RLF.RLD (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' tcnf G q b) ∪ RLF.boolAx)
        w ∅ s →
      2 ^ ((((n - 2) / 1312 - q * (q + 3)) / (q - 1) - (q + 3) - p) / (p - 1)) ≤ 2 * s := by
  obtain ⟨hN, hreg, hconn, hexp⟩ := cubFam_expander (p := p) (q := q) (N := N)
    (m := max N (tseitinFloor p q)) le_rfl
  exact ⟨_, cubFam (max N (tseitinFloor p q)), hN, hreg, hconn, hexp, fun b w s h =>
    reslin_tseitin_size_idx p hq hpq (le_max_right _ _) b w s h⟩

/-- **`reslin_tseitin_dag_size` with expansion.** -/
theorem reslin_tseitin_dag_size_expander (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧
      HasExpansionInv G mggF2CubK ∧ q + 5 ≤ tseitinW p q n ∧
      ∀ b : Fin n → ZMod q, ∀ 𝓛 : Finset (Finset (RLF.LEq (ZMod p))),
        RLF.RLDag (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' tcnf G q b) ∪
          RLF.boolAx) 𝓛 → (∅ : Finset (RLF.LEq (ZMod p))) ∈ 𝓛 →
        ((tseitinW p q n - (q + 3)) * (tseitinW p q n - (q + 3)) <
          72 * (q + 3) * 𝓛.card * (Nat.log 2 (3 * 𝓛.card) + 1)) ∧
        (tseitinW p q n - (q + 3)) * (tseitinW p q n - (q + 3)) /
          (72 * (q + 3) * (Nat.log 2 (3 * ((tseitinW p q n - (q + 3)) *
            (tseitinW p q n - (q + 3))) ) + 1)) ≤ 𝓛.card := by
  obtain ⟨hN, hreg, hconn, hexp⟩ := cubFam_expander (p := p) (q := q) (N := N)
    (m := max N (tseitinFloor p q)) le_rfl
  obtain ⟨hW, H⟩ := reslin_tseitin_dag_size_idx p hq hpq (le_max_right N (tseitinFloor p q))
  exact ⟨_, cubFam (max N (tseitinFloor p q)), hN, hreg, hconn, hexp, hW, H⟩

/-- **`C1.c1_main` with expansion** (bounded rank calculus; excluded from the fidelity request,
see the response document, item 11). -/
theorem c1_main_expander (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (ε : ℝ) (hε : 0 < ε) (hεκ : (C1.kappa p q + 1) * ε < 1) (M : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), M ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧
      HasExpansionInv G mggF2CubK ∧ ∀ b : Fin n → ZMod q,
      ∀ ρ : ℕ, 1 ≤ ρ → (ρ : ℝ) ≤ ε * Real.log n →
      ∀ R : C1.RRefutation (tcnf G q b) (tVars G q) ρ p,
        Real.exp ((n : ℝ) ^ (1 - (C1.kappa p q + 1) * ε)) ≤ R.S := by
  obtain ⟨m0, hm0⟩ := C1.c1_main_idx p hq hpq ε hε hεκ
  obtain ⟨hN, hreg, hconn, hexp⟩ := cubFam_expander (p := p) (q := q) (N := M)
    (m := max (max M (tseitinFloor p q)) m0) 
    (max_le (le_max_of_le_left (le_max_left _ _)) (le_max_of_le_left (le_max_right _ _)))
  have hm : m0 ≤ max (max M (tseitinFloor p q)) m0 := le_max_right _ _
  exact ⟨_, cubFam (max (max M (tseitinFloor p q)) m0), hN, hreg, hconn, hexp,
    fun b ρ h1 h2 R => hm0 _ hm b ρ h1 h2 R⟩

/-! ## 2. Prime `q` corollaries (Pang, Theorem 7.2(b): `q` prime, `q ≠ p`) -/

/-- Prime `q ≠ p`: dag-like `Res(lin F_p)` (Pang's calculus) on one hot Tseitin mod `q`. -/
theorem tseitin_dag_exp_primeq (p : ℕ) [Fact p.Prime] {q : ℕ} [Fact q.Prime] (hne : q ≠ p) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧
      HasExpansionInv G mggF2CubK ∧ ∀ b : Fin n → ZMod q,
      ∀ R : Pang.Refutation (tcnf G q b) (tVars G q) p, 2 ^ (n / Pang.cC p q) ≤ R.S := by
  have hq : q.Prime := Fact.out
  have hp : p.Prime := Fact.out
  exact tseitin_dag_exp_expander p hq.two_le (not_dvd_of_prime_ne hp hq hne) N

/-- Prime `q ≠ p`: tree-like `Res(lin F_p)` on one hot Tseitin mod `q`. -/
theorem reslin_tseitin_size_primeq (p : ℕ) [Fact p.Prime] {q : ℕ} [Fact q.Prime] (hne : q ≠ p) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧
      HasExpansionInv G mggF2CubK ∧ ∀ b : Fin n → ZMod q, ∀ w s : ℕ,
      RLF.RLD (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' tcnf G q b) ∪ RLF.boolAx)
        w ∅ s →
      2 ^ ((((n - 2) / 1312 - q * (q + 3)) / (q - 1) - (q + 3) - p) / (p - 1)) ≤ 2 * s := by
  have hq : q.Prime := Fact.out
  have hp : p.Prime := Fact.out
  exact reslin_tseitin_size_expander p hq.two_le (not_dvd_of_prime_ne hp hq hne) N

/-- Prime `q ≠ p`: dag-like `Res(lin F_p)` (Khaniki's calculus) on one hot Tseitin mod `q`. -/
theorem reslin_tseitin_dag_size_primeq (p : ℕ) [Fact p.Prime] {q : ℕ} [Fact q.Prime] (hne : q ≠ p)
    (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧
      HasExpansionInv G mggF2CubK ∧ q + 5 ≤ tseitinW p q n ∧
      ∀ b : Fin n → ZMod q, ∀ 𝓛 : Finset (Finset (RLF.LEq (ZMod p))),
        RLF.RLDag (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' tcnf G q b) ∪
          RLF.boolAx) 𝓛 → (∅ : Finset (RLF.LEq (ZMod p))) ∈ 𝓛 →
        ((tseitinW p q n - (q + 3)) * (tseitinW p q n - (q + 3)) <
          72 * (q + 3) * 𝓛.card * (Nat.log 2 (3 * 𝓛.card) + 1)) ∧
        (tseitinW p q n - (q + 3)) * (tseitinW p q n - (q + 3)) /
          (72 * (q + 3) * (Nat.log 2 (3 * ((tseitinW p q n - (q + 3)) *
            (tseitinW p q n - (q + 3))) ) + 1)) ≤ 𝓛.card := by
  have hq : q.Prime := Fact.out
  have hp : p.Prime := Fact.out
  exact reslin_tseitin_dag_size_expander p hq.two_le (not_dvd_of_prime_ne hp hq hne) N

/-- Prime `q ≠ p`: bounded rank calculus (excluded from the fidelity request). -/
theorem c1_main_primeq (p : ℕ) [Fact p.Prime] {q : ℕ} [Fact q.Prime] (hne : q ≠ p)
    (ε : ℝ) (hε : 0 < ε) (hεκ : (C1.kappa p q + 1) * ε < 1) (M : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), M ≤ n ∧ IsRegular G 3 ∧ G.IsConnected ∧
      HasExpansionInv G mggF2CubK ∧ ∀ b : Fin n → ZMod q,
      ∀ ρ : ℕ, 1 ≤ ρ → (ρ : ℝ) ≤ ε * Real.log n →
      ∀ R : C1.RRefutation (tcnf G q b) (tVars G q) ρ p,
        Real.exp ((n : ℝ) ^ (1 - (C1.kappa p q + 1) * ε)) ≤ R.S := by
  have hq : q.Prime := Fact.out
  have hp : p.Prime := Fact.out
  exact c1_main_expander p hq.two_le (not_dvd_of_prime_ne hp hq hne) ε hε hεκ M

/-! ## 4. Explicit exponent thresholds -/

/-- Pang's exponent `n / cC p q` is at least `k` once `n ≥ k * cC p q`; so
`2^k ≤ R.S` for all `n ≥ k * cC p q` in `tseitin_dag_exp`. -/
theorem pang_exponent_ge (p q k n : ℕ) (hC : 0 < Pang.cC p q) (h : k * Pang.cC p q ≤ n) :
    k ≤ n / Pang.cC p q := (Nat.le_div_iff_mul_le hC).2 h

/-- Tree-like exponent: for `n ≥ 2 + 1312 (q(q+3) + (q-1)((p-1)k + (q+3) + p))` the exponent of
`reslin_tseitin_size` is at least `k` (so `2^k ≤ 2 s`). -/
theorem reslin_tree_exponent_ge {p q : ℕ} (hq : 2 ≤ q) (hp : 2 ≤ p) (k n : ℕ)
    (h : 2 + 1312 * (q * (q + 3) + (q - 1) * ((p - 1) * k + (q + 3) + p)) ≤ n) :
    k ≤ ((((n - 2) / 1312 - q * (q + 3)) / (q - 1) - (q + 3) - p) / (p - 1)) := by
  have hp1 : 0 < p - 1 := by omega
  have hq1 : 0 < q - 1 := by omega
  rw [Nat.le_div_iff_mul_le hp1]
  have h1 : q * (q + 3) + (q - 1) * ((p - 1) * k + (q + 3) + p) ≤ (n - 2) / 1312 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
  have h2 : (p - 1) * k + (q + 3) + p ≤ ((n - 2) / 1312 - q * (q + 3)) / (q - 1) := by
    rw [Nat.le_div_iff_mul_le hq1]
    have e : ((p - 1) * k + (q + 3) + p) * (q - 1) = (q - 1) * ((p - 1) * k + (q + 3) + p) :=
      mul_comm _ _
    omega
  have e2 : k * (p - 1) = (p - 1) * k := mul_comm _ _
  omega

/-- Dag-like scale `W = tseitinW p q n` is at least `k` for
`n ≥ 2 + 1312 (q(q+3) + (q-1)(p-1) k)`. -/
theorem tseitinW_ge {p q : ℕ} (hq : 2 ≤ q) (hp : 2 ≤ p) (k n : ℕ)
    (h : 2 + 1312 * (q * (q + 3) + (q - 1) * (p - 1) * k) ≤ n) : k ≤ tseitinW p q n := by
  have hp1 : 0 < p - 1 := by omega
  have hq1 : 0 < q - 1 := by omega
  unfold tseitinW
  rw [Nat.le_div_iff_mul_le hp1, Nat.le_div_iff_mul_le hq1]
  have h1 : q * (q + 3) + (q - 1) * (p - 1) * k ≤ (n - 2) / 1312 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
  have : (q - 1) * (p - 1) * k = k * (p - 1) * (q - 1) := by ring
  omega

/-- In terms of the index `m` of `cubFam m` (`n = 8 m^2`): any threshold on `n` is met once
`m` is at least that threshold. -/
theorem cubFam_size_ge_of_index {m T : ℕ} (hm : 0 < m) (h : T ≤ m) : T ≤ m * m * 8 := by
  nlinarith

end SATurday.ProofComplexity
