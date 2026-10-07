import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Arithmetic for the clique lower bound (Ladder Rung R3)

Parameters as functions of the clique size `k`: `ℓ = ⌊√((k-1)/2)⌋`,
`L = 4 log₂ k + 5`, `p = 8 ℓ L`. With `k⁴ ≤ n < 16 k⁴` both inequalities of the
approximation method force more than `n ^ c` gates for `k` large.

LOG: R3 CliqueArith module (parameter arithmetic)
-/

namespace SATurday.ProofComplexity

/-- Petal size. -/
def cℓ (k : ℕ) : ℕ := Nat.sqrt ((k - 1) / 2)

/-- `log₂` budget. -/
def cL (k : ℕ) : ℕ := 4 * Nat.log 2 k + 5

/-- Number of petals. -/
def cp (k : ℕ) : ℕ := 8 * cℓ k * cL k

theorem cℓ_sq (k : ℕ) : 2 * (cℓ k * cℓ k) ≤ k - 1 := by
  unfold cℓ
  have := Nat.sqrt_le ((k - 1) / 2)
  omega

theorem le_cℓ {k t : ℕ} (h : 2 * (t * t) + 1 ≤ k) : t ≤ cℓ k := by
  unfold cℓ
  rw [Nat.le_sqrt]
  omega

/-- `(N - t)^t C(N - t, K - t) ≤ C(N, K) K^t`. -/
theorem choose_mul_pow (N K : ℕ) :
    ∀ t, t ≤ K → K ≤ N → (N - t) ^ t * (N - t).choose (K - t) ≤ N.choose K * K ^ t := by
  intro t
  induction t with
  | zero => intros; simp
  | succ t ih =>
      intro ht hKN
      have ih' := ih (by omega) hKN
      set a := N - (t + 1) with ha
      set b := K - (t + 1) with hb
      have e1 : N - t = a + 1 := by omega
      have e2 : K - t = b + 1 := by omega
      have hid := Nat.add_one_mul_choose_eq a b
      rw [e1, e2] at ih'
      have hb1 : b + 1 ≤ K := by omega
      calc a ^ (t + 1) * a.choose b = a ^ t * (a * a.choose b) := by ring
        _ ≤ (a + 1) ^ t * ((a + 1) * a.choose b) :=
            Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) t) (Nat.mul_le_mul_right _ (by omega))
        _ = (a + 1) ^ t * ((a + 1).choose (b + 1) * (b + 1)) := by rw [hid]
        _ = ((a + 1) ^ t * (a + 1).choose (b + 1)) * (b + 1) := by ring
        _ ≤ (N.choose K * K ^ t) * (b + 1) := Nat.mul_le_mul_right _ ih'
        _ ≤ (N.choose K * K ^ t) * K := Nat.mul_le_mul_left _ hb1
        _ = N.choose K * K ^ (t + 1) := by ring

/-- `1024 (4t + 5)^4 ≤ 2^t` for `t ≥ 60`. -/
theorem poly_le_two_pow : ∀ t, 60 ≤ t → 1024 * (4 * t + 5) ^ 4 ≤ 2 ^ t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
      have h1 : 10 * (4 * (t + 1) + 5) ≤ 11 * (4 * t + 5) := by omega
      have h2 := Nat.pow_le_pow_left h1 4
      rw [mul_pow, mul_pow] at h2
      have h3 : (4 * (t + 1) + 5) ^ 4 ≤ 2 * (4 * t + 5) ^ 4 := by
        norm_num at h2; omega
      rw [pow_succ 2 t]
      omega

theorem log_bound {k : ℕ} (hk : 2 ^ 60 ≤ k) : 1024 * cL k ^ 4 ≤ k := by
  unfold cL
  have hk0 : k ≠ 0 := by positivity
  have ht : 60 ≤ Nat.log 2 k := Nat.le_log_of_pow_le (by norm_num) hk
  exact (poly_le_two_pow _ ht).trans (Nat.pow_log_le_self 2 hk0)

theorem two_pow_cL {k : ℕ} (hk : 1 ≤ k) : 2 * k ^ 4 ≤ 2 ^ cL k := by
  unfold cL
  have h1 : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  have h2 : k ^ 4 ≤ (2 ^ (Nat.log 2 k + 1)) ^ 4 := Nat.pow_le_pow_left h1.le 4
  rw [← pow_mul] at h2
  have e : 2 ^ (4 * Nat.log 2 k + 5) = 2 * 2 ^ ((Nat.log 2 k + 1) * 4) := by
    rw [← pow_succ']; congr 1; ring
  rw [e]; omega

theorem cL_le {k : ℕ} (hk : 1 ≤ k) : cL k ≤ 9 * k := by
  unfold cL
  have := Nat.log_le_self 2 k
  omega

theorem pl_le {k : ℕ} (hk : 1 ≤ k) : cp k * cℓ k + 1 ≤ 4 * k * cL k := by
  unfold cp
  have h := cℓ_sq k
  have hL : 1 ≤ cL k := by unfold cL; omega
  have : 8 * cℓ k * cL k * cℓ k = 4 * (2 * (cℓ k * cℓ k)) * cL k := by ring
  rw [this]
  have := Nat.mul_le_mul_right (cL k) (Nat.mul_le_mul_left 4 h)
  have : 4 * (k - 1) * cL k + 1 ≤ 4 * k * cL k := by
    have : 4 * (k - 1) * cL k + 4 * cL k = 4 * k * cL k := by
      rw [← add_mul, ← Nat.mul_succ]; congr 2; omega
    omega
  omega

/-- Case B: `2^p ≤ 2 s M²` forces `s > n^c`. -/
theorem arith_B (c : ℕ) : ∃ K0, ∀ k ≥ K0, ∀ n, n < 16 * k ^ 4 → ∀ s M,
    M ≤ (cp k * cℓ k + 1) ^ cℓ k → 2 ^ cp k ≤ 2 * s * (M * M) → n ^ c < s := by
  refine ⟨2 * ((c + 1) * (c + 1)) + 1 + 36, fun k hk n hn s M hM h2 => ?_⟩
  have hk1 : 1 ≤ k := by omega
  have hk36 : 36 ≤ k := by omega
  have hℓ : c + 1 ≤ cℓ k := le_cℓ (by omega)
  set ℓ := cℓ k
  by_contra hs
  push_neg at hs
  -- M² ≤ k^(6ℓ)
  have hM2 : M * M ≤ k ^ (6 * ℓ) := by
    have hb : cp k * ℓ + 1 ≤ k ^ 3 := by
      have := pl_le hk1
      have h9 := cL_le hk1
      have : 4 * k * cL k ≤ 4 * k * (9 * k) := Nat.mul_le_mul_left _ h9
      have : 36 * k * k ≤ k * k * k := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hk36)
      nlinarith
    have : M ≤ (k ^ 3) ^ ℓ := hM.trans (Nat.pow_le_pow_left hb ℓ)
    calc M * M ≤ (k ^ 3) ^ ℓ * (k ^ 3) ^ ℓ := Nat.mul_le_mul this this
      _ = k ^ (6 * ℓ) := by rw [← pow_mul, ← pow_add]; ring_nf
  -- 2^p ≥ k^(32ℓ)
  have hp : k ^ (32 * ℓ) ≤ 2 ^ cp k := by
    have h1 := two_pow_cL hk1
    have : k ^ 4 ≤ 2 ^ cL k := by omega
    calc k ^ (32 * ℓ) = (k ^ 4) ^ (8 * ℓ) := by rw [← pow_mul]; ring_nf
      _ ≤ (2 ^ cL k) ^ (8 * ℓ) := Nat.pow_le_pow_left this _
      _ = 2 ^ cp k := by rw [← pow_mul]; unfold cp; ring_nf; rfl
  -- n^c ≤ 16^c k^(4c)
  have hn' : n ^ c ≤ 16 ^ c * k ^ (4 * c) := by
    calc n ^ c ≤ (16 * k ^ 4) ^ c := Nat.pow_le_pow_left hn.le c
      _ = 16 ^ c * k ^ (4 * c) := by rw [mul_pow, ← pow_mul]
  have hchain : k ^ (32 * ℓ) ≤ 2 * 16 ^ c * k ^ (4 * c) * k ^ (6 * ℓ) := by
    calc k ^ (32 * ℓ) ≤ 2 * s * (M * M) := hp.trans h2
      _ ≤ 2 * (16 ^ c * k ^ (4 * c)) * k ^ (6 * ℓ) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 (hs.trans hn')) hM2
      _ = _ := by ring
  -- contradiction: k^(26ℓ) > 2 * 16^c * k^(4c)
  have hkpos : 0 < k := by omega
  have e : k ^ (32 * ℓ) = k ^ (26 * ℓ) * k ^ (6 * ℓ) := by rw [← pow_add]; ring_nf
  rw [e] at hchain
  have hc2 := Nat.le_of_mul_le_mul_right hchain (Nat.pow_pos hkpos)
  have hbig : 2 * 16 ^ c * k ^ (4 * c) < k ^ (26 * ℓ) := by
    have h1 : k ^ (4 * c) * k ^ (c + 1) ≤ k ^ (26 * ℓ) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right hkpos (by omega)
    have h2 : 2 * 16 ^ c < 32 ^ (c + 1) := by
      have : 2 * 16 ^ c < 2 * 16 ^ c * 16 := by
        have := Nat.pow_pos (n := c) (show 0 < 16 by norm_num); omega
      calc 2 * 16 ^ c < 2 * 16 ^ c * 16 := this
        _ = 32 * 16 ^ c := by ring
        _ ≤ 32 * 32 ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by norm_num) c)
        _ = 32 ^ (c + 1) := by ring
    have h3 : 32 ^ (c + 1) ≤ k ^ (c + 1) := Nat.pow_le_pow_left (by omega) _
    have h4 : 0 < k ^ (4 * c) := Nat.pow_pos hkpos
    calc 2 * 16 ^ c * k ^ (4 * c) < 32 ^ (c + 1) * k ^ (4 * c) :=
          Nat.mul_lt_mul_of_pos_right h2 h4
      _ ≤ k ^ (c + 1) * k ^ (4 * c) := Nat.mul_le_mul_right _ h3
      _ = k ^ (4 * c) * k ^ (c + 1) := by ring
      _ ≤ _ := h1
  omega

/-- Case A: `(n - ℓ - 1)^(ℓ+1) ≤ s M² k^(ℓ+1)` forces `s > n^c`. -/
theorem arith_A (c : ℕ) : ∃ K0, ∀ k ≥ K0, ∀ n, k ^ 4 ≤ n → n < 16 * k ^ 4 → ∀ s M,
    M ≤ (cp k * cℓ k + 1) ^ cℓ k →
    (n - (cℓ k + 1)) ^ (cℓ k + 1) ≤ s * (M * M) * k ^ (cℓ k + 1) → n ^ c < s := by
  refine ⟨2 ^ 60 + 2 * ((8 * c + 8) * (8 * c + 8)) + 1 + 4 * 256 ^ c,
    fun k hk n hn1 hn2 s M hM hA => ?_⟩
  have hk1 : 1 ≤ k := by omega
  have hkpos : 0 < k := by omega
  have hℓ : 8 * c + 8 ≤ cℓ k := le_cℓ (by omega)
  have hlog := log_bound (k := k) (by omega)
  set ℓ := cℓ k
  set L := cL k
  by_contra hs
  push_neg at hs
  have hℓk : ℓ ≤ k := by
    have h1 : 2 * (ℓ * ℓ) ≤ k - 1 := cℓ_sq k
    have h2 : ℓ ≤ ℓ * ℓ := Nat.le_mul_self ℓ
    omega
  -- M² ≤ (16 k² L²)^ℓ
  have hM2 : M * M ≤ (16 * (k * k) * (L * L)) ^ ℓ := by
    have : M ≤ (4 * k * L) ^ ℓ := hM.trans (Nat.pow_le_pow_left (pl_le hk1) ℓ)
    calc M * M ≤ (4 * k * L) ^ ℓ * (4 * k * L) ^ ℓ := Nat.mul_le_mul this this
      _ = (16 * (k * k) * (L * L)) ^ ℓ := by rw [← mul_pow]; ring_nf
  have hn' : n ^ c ≤ 16 ^ c * k ^ (4 * c) := by
    calc n ^ c ≤ (16 * k ^ 4) ^ c := Nat.pow_le_pow_left hn2.le c
      _ = 16 ^ c * k ^ (4 * c) := by rw [mul_pow, ← pow_mul]
  -- k^(4(ℓ+1)) ≤ 2^(ℓ+1) (n - ℓ - 1)^(ℓ+1)
  have h4 : k ^ 4 ≤ 2 * (n - (ℓ + 1)) := by
    have : 2 * (ℓ + 1) ≤ k ^ 4 := by
      have h1 : 4 ≤ k ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left (show 2 ≤ k by omega) 3)
      have h44 : 4 * k ≤ k ^ 4 := by
        calc 4 * k ≤ k ^ 3 * k := Nat.mul_le_mul_right _ h1
          _ = k ^ 4 := by ring
      omega
    omega
  have hstep1 : k ^ (4 * (ℓ + 1)) ≤
      2 ^ (ℓ + 1) * (16 ^ c * k ^ (4 * c)) * (16 * (k * k) * (L * L)) ^ ℓ * k ^ (ℓ + 1) := by
    calc k ^ (4 * (ℓ + 1)) = (k ^ 4) ^ (ℓ + 1) := by rw [← pow_mul]
      _ ≤ (2 * (n - (ℓ + 1))) ^ (ℓ + 1) := Nat.pow_le_pow_left h4 _
      _ = 2 ^ (ℓ + 1) * (n - (ℓ + 1)) ^ (ℓ + 1) := by rw [mul_pow]
      _ ≤ 2 ^ (ℓ + 1) * (s * (M * M) * k ^ (ℓ + 1)) := Nat.mul_le_mul_left _ hA
      _ ≤ 2 ^ (ℓ + 1) * ((16 ^ c * k ^ (4 * c)) * (16 * (k * k) * (L * L)) ^ ℓ * k ^ (ℓ + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul (hs.trans hn') hM2))
      _ = _ := by ring
  -- rearrange: k^(ℓ+4) * k^(3ℓ) ≤ (2 * 16^c * k^(4c+1) * (32 L²)^ℓ) * k^(3ℓ)
  have hre : k ^ (ℓ + 4) * k ^ (3 * ℓ) ≤
      (2 * 16 ^ c * k ^ (4 * c + 1) * (32 * (L * L)) ^ ℓ) * k ^ (3 * ℓ) := by
    have e1 : k ^ (4 * (ℓ + 1)) = k ^ (ℓ + 4) * k ^ (3 * ℓ) := by rw [← pow_add]; ring_nf
    have e2 : 2 ^ (ℓ + 1) * (16 ^ c * k ^ (4 * c)) * (16 * (k * k) * (L * L)) ^ ℓ * k ^ (ℓ + 1) =
        (2 * 16 ^ c * k ^ (4 * c + 1) * (32 * (L * L)) ^ ℓ) * k ^ (3 * ℓ) := by
      have : (16 * (k * k) * (L * L)) ^ ℓ = 16 ^ ℓ * (k ^ ℓ * k ^ ℓ) * (L * L) ^ ℓ := by
        rw [mul_pow, mul_pow, mul_pow]
      rw [this, show (32 * (L * L)) ^ ℓ = 2 ^ ℓ * 16 ^ ℓ * (L * L) ^ ℓ by
        rw [show (32 : ℕ) = 2 * 16 by norm_num, mul_pow, mul_pow]]
      rw [show 3 * ℓ = ℓ + ℓ + ℓ by ring, pow_add, pow_add, pow_succ, pow_succ]
      ring
    rw [← e1, ← e2]; exact hstep1
  have hcan := Nat.le_of_mul_le_mul_right hre (Nat.pow_pos hkpos)
  -- square and use (32 L²)² ≤ k
  have hsq := Nat.pow_le_pow_left hcan 2
  have hD : (32 * (L * L)) ^ 2 ≤ k := by nlinarith
  have hD' : ((32 * (L * L)) ^ ℓ) ^ 2 ≤ k ^ ℓ := by
    rw [← pow_mul, mul_comm ℓ 2, pow_mul]; exact Nat.pow_le_pow_left hD ℓ
  have hfin : k ^ ℓ * k ^ (ℓ + 8) ≤ k ^ ℓ * (4 * 256 ^ c * k ^ (8 * c + 2)) := by
    have e3 : (k ^ (ℓ + 4)) ^ 2 = k ^ ℓ * k ^ (ℓ + 8) := by rw [← pow_mul, ← pow_add]; ring_nf
    have e4 : (2 * 16 ^ c * k ^ (4 * c + 1) * (32 * (L * L)) ^ ℓ) ^ 2 =
        ((32 * (L * L)) ^ ℓ) ^ 2 * (4 * 256 ^ c * k ^ (8 * c + 2)) := by
      have h256 : (16 : ℕ) ^ (c * 2) = 256 ^ c := by rw [mul_comm, pow_mul]; norm_num
      ring_nf
      rw [h256]
      ring
    rw [e3, e4] at hsq
    calc k ^ ℓ * k ^ (ℓ + 8) ≤ ((32 * (L * L)) ^ ℓ) ^ 2 * (4 * 256 ^ c * k ^ (8 * c + 2)) := hsq
      _ ≤ k ^ ℓ * (4 * 256 ^ c * k ^ (8 * c + 2)) := Nat.mul_le_mul_right _ hD'
  have hfin2 := Nat.le_of_mul_le_mul_left hfin (Nat.pow_pos hkpos)
  have hbig : 4 * 256 ^ c * k ^ (8 * c + 2) < k ^ (ℓ + 8) := by
    have h1 : k ^ (8 * c + 2) * k ^ 6 ≤ k ^ (ℓ + 8) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right hkpos (by omega)
    have h2 : 4 * 256 ^ c < k ^ 6 := by
      have : k ≤ k ^ 6 := Nat.le_self_pow (by norm_num) k
      omega
    calc 4 * 256 ^ c * k ^ (8 * c + 2) < k ^ 6 * k ^ (8 * c + 2) :=
          Nat.mul_lt_mul_of_pos_right h2 (Nat.pow_pos hkpos)
      _ = k ^ (8 * c + 2) * k ^ 6 := by ring
      _ ≤ _ := h1
  omega

end SATurday.ProofComplexity
