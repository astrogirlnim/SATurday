import Theory.ProofComplexity.ExpanderMGG

/-!
# Explicit parameters of the Gabber-Galil walk multigraph family (Ladder Rung R4, layer E2b)

For a modulus `q ≥ 1` put `k0 q = 6 * clog₂ (32 q)` (logarithmic in `q`).  For every `k ≥ k0 q`
the second singular value of the `8^k`-regular bipartite walk multigraph satisfies
`(5√2)^k ≤ 8^k / (32 q)` (`mu_pow_le`), and consequently (`ggw_rsc`) every vertex set of at most
`m² / (16 q)` vertices has at least `(1 - 1/(16 q)) · 8^k` boundary edges per vertex: the graph is an
`(r, s, c)`-expander in the sense of Alekhnovich-Razborov with
`s = 8^k`, `s - c = 8^k / (16 q)`, `r = m² / (16 q)`.

This is the only place where the choice of graph family enters the quantitative hypotheses.

LOG: R4 expander layer E2b (explicit k0, r)
-/

namespace SATurday.ProofComplexity.Expander

open Finset

/-- Walk length from which the walk multigraph is a good enough expander for the modulus `q`. -/
def k0 (q : ℕ) : ℕ := 6 * Nat.clog 2 (32 * q)

/-- The size bound of small vertex sets: at most `m² / (16 q)` vertices (of both sides together). -/
def rBound (m q : ℕ) : ℕ := m * m / (16 * q)

theorem mu_pow_le {q : ℕ} (hq : 1 ≤ q) {k : ℕ} (hk : k0 q ≤ k) :
    (5 * Real.sqrt 2) ^ k ≤ (8 : ℝ) ^ k / (32 * q) := by
  set j := Nat.clog 2 (32 * q) with hj
  have hμ : (5 * Real.sqrt 2) ^ 2 = 50 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hμ0 : 0 ≤ 5 * Real.sqrt 2 := by positivity
  -- ρ = μ / 8
  set ρ : ℝ := 5 * Real.sqrt 2 / 8 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ2 : ρ ^ 2 = 25 / 32 := by
    rw [hρ, div_pow, hμ]; norm_num
  have hρ1 : ρ ≤ 1 := by
    by_contra h
    have h' := not_le.mp h
    nlinarith
  have h1 : ρ ^ k ≤ ρ ^ (6 * j) := pow_le_pow_of_le_one hρ0 hρ1 hk
  have h2 : ρ ^ (6 * j) ≤ (1 / 2 : ℝ) ^ j := by
    have : ρ ^ (6 * j) = ((ρ ^ 2) ^ 3) ^ j := by rw [← pow_mul, ← pow_mul]; congr 1; ring
    rw [this, hρ2]
    apply pow_le_pow_left₀ (by positivity)
    norm_num
  have h3 : (1 / 2 : ℝ) ^ j ≤ 1 / (32 * q) := by
    have hle : (32 * q : ℕ) ≤ 2 ^ j := Nat.le_pow_clog (by norm_num) _
    have hle' : (32 * q : ℝ) ≤ 2 ^ j := by exact_mod_cast hle
    have hqpos : (0 : ℝ) < 32 * q := by positivity
    rw [one_div_pow, one_div, one_div]
    exact inv_anti₀ hqpos hle'
  have h4 : ρ ^ k ≤ 1 / (32 * q) := h1.trans (h2.trans h3)
  have h5 : (5 * Real.sqrt 2) ^ k = 8 ^ k * ρ ^ k := by
    rw [hρ, div_pow, mul_div_cancel₀]; positivity
  rw [h5]
  calc (8 : ℝ) ^ k * ρ ^ k ≤ 8 ^ k * (1 / (32 * q)) := by gcongr
    _ = _ := by ring

/-- `(r, s, c)`-expansion of the walk multigraph with explicit constants. -/
theorem ggw_rsc (m : ℕ) (hm : 3 ≤ m) {q : ℕ} (hq : 1 ≤ q) {k : ℕ} (hk : k0 q ≤ k)
    (IL IR : Finset (MggTorus m)) (hI : IL.card + IR.card ≤ rBound m q) :
    ((IL.card + IR.card : ℕ) : ℝ) * ((8 : ℝ) ^ k * (1 - 1 / (16 * q))) ≤
      (ggwBoundary m hm k IL IR).card := by
  refine le_trans ?_ (ggw_expansion m hm k IL IR)
  have hN : (0 : ℝ) < (m * m : ℕ) := by
    have := lt_of_lt_of_le (by decide : 0 < 3) hm
    positivity
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have ht : ((IL.card + IR.card : ℕ) : ℝ) ≤ ((m * m : ℕ) : ℝ) / (16 * q) := by
    have h1 : ((IL.card + IR.card : ℕ) : ℝ) ≤ ((rBound m q : ℕ) : ℝ) := by exact_mod_cast hI
    refine h1.trans ?_
    unfold rBound
    have := Nat.cast_div_le (α := ℝ) (m := m * m) (n := 16 * q)
    simpa using this
  have h2 : ((IL.card + IR.card : ℕ) : ℝ) / (2 * (m * m : ℕ)) ≤ 1 / (32 * q) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : ((IL.card + IR.card : ℕ) : ℝ) * (16 * q) ≤ ((m * m : ℕ) : ℝ) := by
      rwa [le_div_iff₀ (by positivity)] at ht
    nlinarith
  have h3 := mu_pow_le hq hk
  have ht0 : (0 : ℝ) ≤ ((IL.card + IR.card : ℕ) : ℝ) := Nat.cast_nonneg _
  apply mul_le_mul_of_nonneg_left _ ht0
  have h8 : (0 : ℝ) < 8 ^ k := by positivity
  have : (8 : ℝ) ^ k * (((IL.card + IR.card : ℕ) : ℝ) / (2 * (m * m : ℕ))) ≤ 8 ^ k * (1 / (32 * q)) :=
    mul_le_mul_of_nonneg_left h2 h8.le
  have e : (8 : ℝ) ^ k * (1 - 1 / (16 * q)) = 8 ^ k * (1 - 1 / (32 * q)) - 8 ^ k / (32 * q) := by
    field_simp; ring
  rw [e]
  have e2 : (8 : ℝ) ^ k * (1 - ((IL.card + IR.card : ℕ) : ℝ) / (2 * (m * m : ℕ))) =
      8 ^ k - 8 ^ k * (((IL.card + IR.card : ℕ) : ℝ) / (2 * (m * m : ℕ))) := by ring
  rw [e2]
  have e3 : (8 : ℝ) ^ k * (1 - 1 / (32 * q)) = 8 ^ k - 8 ^ k * (1 / (32 * q)) := by ring
  rw [e3]
  have e4 : (8 : ℝ) ^ k * (1 / (32 * q)) = 8 ^ k / (32 * q) := by ring
  rw [e4] at this ⊢
  linarith

end SATurday.ProofComplexity.Expander
