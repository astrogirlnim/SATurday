import Theory.ProofComplexity.C1Params
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Candidate C1: the real-number chain (isolated)

`kappa p q = (p-1) ln (cLam q)` is the explicit constant of this formalization (it differs from the
`kappa` of `docs/ladder/rungs/r4-phase23-c1.md`: no translation to degree `3(p-1)ρ`, and the constants
of the formalized Pang layers).  The per-`n` inequality `real_chain` shows, for `1 ≤ ρ ≤ ε ln n`,

* `cN0R p q ((p-1) ρ) ≤ n`, and
* `exp (n^(1-(κ+1)ε)) ≤ 2^(n / cCR p q ((p-1) ρ))`,

provided the two explicit `n`-conditions `hE1`, `hE2` hold; `eventually_conditions` shows that they
hold for all large `n`.
-/

open Real Filter

namespace C1

noncomputable section

/-- The explicit constant `κ = (p-1) ln (cLam q)`. -/
def kappa (p q : ℕ) : ℝ := ((p : ℝ) - 1) * Real.log (Pang.cLam q)

def A0 (q : ℕ) : ℕ := 2 + 1312 * (q * (q + 3) + (q - 1) * (2 * q + 1400))
def B0 (p q : ℕ) : ℕ := 1312 * (q - 1) * (24 + 8 * (p - 1))

lemma cN0R_eq (p q d : ℕ) : cN0R p q d = A0 q + B0 p q * d := by
  unfold cN0R cDminR A0 B0; ring


open Pang in
theorem real_chain (p q ρ n : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (ε : ℝ) (hε : 0 < ε)
    (hεκ : (kappa p q + 1) * ε < 1) (hρ1 : 1 ≤ ρ) (hρ : (ρ : ℝ) ≤ ε * Real.log n) (hn : 2 ≤ n)
    (hE1 : (A0 q : ℝ) + B0 p q * (((p : ℝ) - 1) * (ε * Real.log n)) ≤ n)
    (hE2 : 64 * (cA q : ℝ) * ((p : ℝ) - 1) ^ 2 * ε * Real.log n ≤ Real.log 2 * (n : ℝ) ^ ε) :
    cN0R p q ((p - 1) * ρ) ≤ n ∧
      Real.exp ((n : ℝ) ^ (1 - (kappa p q + 1) * ε)) ≤ (2 : ℝ) ^ (n / cCR p q ((p - 1) * ρ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  set L := Real.log n with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hn1
  set d : ℕ := (p - 1) * ρ with hd
  have he : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hdR : (d : ℝ) = ((p : ℝ) - 1) * ρ := by
    rw [hd]; push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
  have hdle : (d : ℝ) ≤ ((p : ℝ) - 1) * (ε * L) := by
    rw [hdR]; exact mul_le_mul_of_nonneg_left hρ he
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  constructor
  · have : (cN0R p q d : ℝ) ≤ n := by
      rw [cN0R_eq]; push_cast
      calc (A0 q : ℝ) + B0 p q * d ≤ A0 q + B0 p q * (((p : ℝ) - 1) * (ε * L)) := by
            have : (0 : ℝ) ≤ B0 p q := Nat.cast_nonneg _
            nlinarith
        _ ≤ n := hE1
    exact_mod_cast this
  · -- real part
    set Λ : ℝ := (cLam q : ℝ) with hΛ
    have hΛ1 : 1 ≤ Λ := by
      rw [hΛ]; unfold cLam cA
      exact_mod_cast (by nlinarith : 1 ≤ 18 * q * (2624 * q + 1313))
    have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ1
    have hκ : 0 ≤ kappa p q := mul_nonneg he hlogΛ
    set κ := kappa p q with hκdef
    have hpowΛ : Λ ^ d ≤ (n : ℝ) ^ (κ * ε) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos hn0]
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left hdle hlogΛ
      rw [hκdef, kappa]
      nlinarith
    have hΛd : 1 ≤ Λ ^ d := one_le_pow₀ hΛ1
    have hnκ : 0 < (n : ℝ) ^ (κ * ε) := Real.rpow_pos_of_pos hn0 _
    -- the constant
    have hc : (0 : ℝ) < cA q := by unfold cA; positivity
    have hcCR : (cCR p q d : ℝ) = cA q * (8 * (((p - 1 : ℕ) : ℝ) * d)) * (2 * (1 + Λ ^ d)) := by
      unfold cCR cSR; push_cast; rw [hΛ]
    have hpe : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ p)]; ring
    rw [hpe] at hcCR
    have hcCR_pos : (0 : ℝ) < cCR p q d := by
      rw [hcCR]
      have : (0 : ℝ) < (p : ℝ) - 1 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp
        linarith
      have hd1 : (0 : ℝ) < d := by
        have : 1 ≤ d := by rw [hd]; exact Nat.mul_pos (by omega) hρ1
        exact_mod_cast this
      positivity
    have hcCR_le : (cCR p q d : ℝ) ≤ 32 * cA q * ((p : ℝ) - 1) * (((p : ℝ) - 1) * (ε * L)) *
        (n : ℝ) ^ (κ * ε) := by
      rw [hcCR]
      have h1 : (1 + Λ ^ d) ≤ 2 * (n : ℝ) ^ (κ * ε) := by linarith
      have h2 : (0 : ℝ) ≤ cA q * (8 * (((p : ℝ) - 1) * d)) := by positivity
      calc (cA q : ℝ) * (8 * (((p : ℝ) - 1) * d)) * (2 * (1 + Λ ^ d))
          ≤ cA q * (8 * (((p : ℝ) - 1) * d)) * (2 * (2 * (n : ℝ) ^ (κ * ε))) :=
            mul_le_mul_of_nonneg_left (by linarith) h2
        _ = 32 * cA q * (((p : ℝ) - 1) * d) * (n : ℝ) ^ (κ * ε) := by ring
        _ ≤ 32 * cA q * ((p : ℝ) - 1) * (((p : ℝ) - 1) * (ε * L)) * (n : ℝ) ^ (κ * ε) := by
            have h3 : (p : ℝ) - 1 ≥ 0 := he
            have h4 : (0 : ℝ) ≤ 32 * cA q * (n : ℝ) ^ (κ * ε) := by positivity
            have h5 := mul_le_mul_of_nonneg_left hdle h3
            nlinarith [mul_le_mul_of_nonneg_left h5 h4]
    have hP : 2 * (cCR p q d : ℝ) ≤ Real.log 2 * (n : ℝ) ^ ((κ + 1) * ε) := by
      have e1 : (n : ℝ) ^ ((κ + 1) * ε) = (n : ℝ) ^ (κ * ε) * (n : ℝ) ^ ε := by
        rw [add_mul, one_mul, Real.rpow_add hn0]
      rw [e1]
      have := mul_le_mul_of_nonneg_right hE2 hnκ.le
      nlinarith [this, hcCR_le]
    have hQ1 : (n : ℝ) ^ ((κ + 1) * ε) ≤ n := by
      calc (n : ℝ) ^ ((κ + 1) * ε) ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1 hεκ.le
        _ = n := Real.rpow_one _
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hlog2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2c : 2 * (cCR p q d : ℝ) ≤ n := by
      have hQ0 : 0 ≤ (n : ℝ) ^ ((κ + 1) * ε) := Real.rpow_nonneg hn0.le _
      have : Real.log 2 * (n : ℝ) ^ ((κ + 1) * ε) ≤ 1 * (n : ℝ) ^ ((κ + 1) * ε) :=
        mul_le_mul_of_nonneg_right hlog2 hQ0
      linarith
    -- natural number division
    set x : ℕ := n / cCR p q d with hx
    have hcpos : 0 < cCR p q d := by exact_mod_cast hcCR_pos
    have hxlt : (n : ℝ) < cCR p q d * x + cCR p q d := by
      have := Nat.lt_mul_div_succ n hcpos
      have h' : (n : ℝ) < cCR p q d * (x + 1) := by exact_mod_cast this
      linarith
    have hxge : (n : ℝ) / (2 * cCR p q d) ≤ x := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hpow2 : (2 : ℝ) ^ x = Real.exp (x * Real.log 2) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]; ring_nf
    rw [hpow2]
    apply Real.exp_le_exp.2
    have hQpos : 0 < (n : ℝ) ^ ((κ + 1) * ε) := Real.rpow_pos_of_pos hn0 _
    have e2 : (n : ℝ) ^ (1 - (κ + 1) * ε) = n / (n : ℝ) ^ ((κ + 1) * ε) := by
      rw [Real.rpow_sub hn0, Real.rpow_one]
    rw [e2]
    calc (n : ℝ) / (n : ℝ) ^ ((κ + 1) * ε) ≤ n * Real.log 2 / (2 * cCR p q d) := by
          rw [div_le_div_iff₀ hQpos (by positivity)]
          have := mul_le_mul_of_nonneg_left hP hn0.le
          linarith
      _ = (n / (2 * cCR p q d)) * Real.log 2 := by ring
      _ ≤ x * Real.log 2 := mul_le_mul_of_nonneg_right hxge hlog2p.le


open Pang in
theorem eventually_conditions (p q : ℕ) (hp : 2 ≤ p) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → 2 ≤ n ∧
      ((A0 q : ℝ) + B0 p q * (((p : ℝ) - 1) * (ε * Real.log n)) ≤ n) ∧
      (64 * (cA q : ℝ) * ((p : ℝ) - 1) ^ 2 * ε * Real.log n ≤ Real.log 2 * (n : ℝ) ^ ε) := by
  have he : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hlog2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set a : ℝ := (B0 p q : ℝ) * ((p : ℝ) - 1) * ε with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  set K : ℝ := 128 * (cA q : ℝ) * ((p : ℝ) - 1) ^ 2 / Real.log 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  set T : ℝ := max (max 2 (2 * (A0 q : ℝ))) (max ((4 * a) ^ 2) (K ^ (2 / ε))) with hT
  refine ⟨⌈T⌉₊, fun n hn => ?_⟩
  have hnT : T ≤ n := (Nat.le_ceil T).trans (by exact_mod_cast hn)
  have h2 : (2 : ℝ) ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hnT)
  have hA : 2 * (A0 q : ℝ) ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hnT)
  have hu : (4 * a) ^ 2 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hnT)
  have hw : K ^ (2 / ε) ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hnT)
  have hn0 : (0 : ℝ) < n := by linarith
  refine ⟨by exact_mod_cast h2, ?_, ?_⟩
  · -- E1
    have hL := Real.log_le_rpow_div hn0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at hL
    set u := Real.sqrt n with hu'
    have hu2 : u ^ 2 = n := Real.sq_sqrt hn0.le
    have h4a : 4 * a ≤ u := by
      have := Real.sqrt_le_sqrt hu
      rwa [Real.sqrt_sq (by positivity)] at this
    have hL' : Real.log n ≤ 2 * u := by linarith [show u / (1 / 2) = 2 * u by ring]
    have : (B0 p q : ℝ) * (((p : ℝ) - 1) * (ε * Real.log n)) = a * Real.log n := by rw [ha]; ring
    rw [this]
    have hL0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have h5 : a * Real.log n ≤ a * (2 * u) := mul_le_mul_of_nonneg_left hL' ha0
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    nlinarith
  · -- E2
    have hL := Real.log_le_rpow_div hn0.le (by positivity : (0 : ℝ) < ε / 2)
    set w := (n : ℝ) ^ (ε / 2) with hwdef
    have hw0 : 0 < w := Real.rpow_pos_of_pos hn0 _
    have hKw : K ≤ w := by
      have h1 : (K ^ (2 / ε)) ^ (ε / 2) ≤ (n : ℝ) ^ (ε / 2) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hK0 _) hw (by positivity)
      rwa [← Real.rpow_mul hK0, show 2 / ε * (ε / 2) = 1 by field_simp, Real.rpow_one] at h1
    have hnε : (n : ℝ) ^ ε = w * w := by
      rw [hwdef, ← Real.rpow_add hn0]; congr 1; ring
    rw [hnε]
    have hL' : Real.log n ≤ 2 * w / ε := by
      have : w / (ε / 2) = 2 * w / ε := by field_simp
      linarith
    have hKw' : 128 * (cA q : ℝ) * ((p : ℝ) - 1) ^ 2 ≤ Real.log 2 * w := by
      have := mul_le_mul_of_nonneg_left hKw hlog2p.le
      rw [hK, mul_div_cancel₀ _ hlog2p.ne'] at this
      exact this
    have hpos : 0 ≤ 64 * (cA q : ℝ) * ((p : ℝ) - 1) ^ 2 * ε := by positivity
    calc 64 * (cA q : ℝ) * ((p : ℝ) - 1) ^ 2 * ε * Real.log n
        ≤ 64 * (cA q : ℝ) * ((p : ℝ) - 1) ^ 2 * ε * (2 * w / ε) :=
          mul_le_mul_of_nonneg_left hL' hpos
      _ = (128 * (cA q : ℝ) * ((p : ℝ) - 1) ^ 2) * w := by field_simp; ring
      _ ≤ (Real.log 2 * w) * w := mul_le_mul_of_nonneg_right hKw' hw0.le
      _ = Real.log 2 * (w * w) := by ring

end

end C1
