import Theory.ProofComplexity.ReviewFollowups

/-!
# Hard instances at every scale (referee follow-up 6, partial)

Padding to every `n` in the strict sense (a hard instance with exactly `n` vertices) is NOT proved.
What is proved here: for every `n ≥ n0` there is `m` such that `cubFam m` has `n' = 8 m^2` vertices
with `n / 2 < n' ≤ n`, so every scale is covered by an explicit hard instance of size within a
factor `2`.  The bounds are then stated with the exact instance size `n'` and also as a function of
`n` (with the constant doubled).
-/

namespace SATurday.ProofComplexity

open TseitinPC

/-- For `n ≥ 8 F^2` (with `F ≥ 3`) there is `m ≥ F` with `8 m^2 ≤ n < 2 (8 m^2)`. -/
theorem exists_scale_index {F : ℕ} (hF : 3 ≤ F) {n : ℕ} (hn : 8 * (F * F) ≤ n) :
    ∃ m, F ≤ m ∧ m * m * 8 ≤ n ∧ n < 2 * (m * m * 8) := by
  refine ⟨Nat.sqrt (n / 8), ?_, ?_, ?_⟩
  · rw [Nat.le_sqrt']; rw [pow_two]; omega
  · have := Nat.sqrt_le' (n / 8)
    rw [pow_two] at this
    omega
  · have h1 : n / 8 < (Nat.sqrt (n / 8) + 1) * (Nat.sqrt (n / 8) + 1) := by
      have := Nat.lt_succ_sqrt' (n / 8)
      simpa [pow_two] using this
    have h3 : 3 ≤ Nat.sqrt (n / 8) := by
      refine hF.trans ?_
      rw [Nat.le_sqrt', pow_two]; omega
    have := cubFam_size_gap h3
    omega

/-- **Pang's exponential bound at every scale.**  There is `n0` such that for every `n ≥ n0` there
is an explicit connected cubic expander `cubFam m` on `n' = 8 m^2` vertices, `n/2 < n' ≤ n`, such that
every `Pang.Refutation` of every one hot Tseitin mod `q` instance on it has at least
`2^(n / (2 C))` nodes. -/
theorem tseitin_dag_exp_all_scales (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∃ m : ℕ, m * m * 8 ≤ n ∧ n < 2 * (m * m * 8) ∧
      IsRegular (cubFam m) 3 ∧ (cubFam m).IsConnected ∧ HasExpansionInv (cubFam m) mggF2CubK ∧
      ∀ b : Fin (m * m * 8) → ZMod q,
        ∀ R : Pang.Refutation (tcnf (cubFam m) q b) (tVars (cubFam m) q) p,
          2 ^ (n / (2 * Pang.cC p q)) ≤ R.S := by
  have hF3 : 3 ≤ tseitinFloor p q := by
    unfold tseitinFloor; have : 0 < mggF2CubFloor := by decide
    omega
  refine ⟨8 * (tseitinFloor p q * tseitinFloor p q), fun n hn => ?_⟩
  obtain ⟨m, hm, h1, h2⟩ := exists_scale_index hF3 hn
  obtain ⟨-, hreg, hconn, hexp⟩ := cubFam_expander (p := p) (q := q) (N := 0)
    (m := m) (max_le (Nat.zero_le _) hm)
  refine ⟨m, h1, h2, hreg, hconn, hexp, fun b R => ?_⟩
  refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) (Pang.tseitin_dag_exp_idx p hq hpq hm b R)
  calc n / (2 * Pang.cC p q) ≤ (2 * (m * m * 8)) / (2 * Pang.cC p q) :=
        Nat.div_le_div_right h2.le
    _ = (m * m * 8) / Pang.cC p q := Nat.mul_div_mul_left _ _ (by norm_num)

end SATurday.ProofComplexity
