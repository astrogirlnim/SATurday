import Theory.ProofComplexity.MGG.GG.YoungAssembly
import Mathlib.Tactic

/-!
Factor-2 Gabber-Galil numerical radius.

The adjacency form is the eight labeled steps
`(x ± 2y, y)`, `(x ± (2y+1), y)`, `(x, y ± 2x)`, `(x, y ± (2x+1))`.
`young_assembly` and `corr_pair1` / `corr_pair2` supply the Fourier bound.
This is the Jimbo-Maruoka constant `5 * sqrt 2`, not a bound for `mggNeighbor`.

LOG: R2 manual port, factor-2 Rayleigh glue
-/

set_option maxHeartbeats 3200000

namespace SATurday.ProofComplexity.MGGGabberGalil

open Complex Finset Real BigOperators

variable {n : ℕ}

/-- Adding `c` and then subtracting `c % n` returns the start coordinate. -/
theorem gg_mod_inv_fwd (a c n : ℕ) (hn : 0 < n) (ha : a < n) :
    (((a + n - c % n) % n + c) % n) = a := by
  have hr : c % n < n := Nat.mod_lt c hn
  have hdiv : c - c % n = n * (c / n) := by
    have h := Nat.div_add_mod c n
    omega
  rcases Nat.lt_or_ge a (c % n) with hlt | hle
  · have ht : a + n - c % n < n := by omega
    rw [Nat.mod_eq_of_lt ht]
    exact mod_sub_add_round a c n hn ha
  · have ht : a + n - c % n = a - c % n + n := by omega
    rw [ht, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : a - c % n < n)]
    have h1 : a - c % n + c = a + c - c % n := (Nat.sub_add_comm hle).symm
    have h2 : a + c - c % n = a + (c - c % n) := Nat.add_sub_assoc (Nat.mod_le c n) _
    rw [h1, h2, hdiv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

/-- Horizontal factor-2 step and its inverse, as a coordinate bijection. -/
def ggShearX (n : ℕ) (hn : 0 < n) (s : Fin n → ℕ) : (Fin n × Fin n) ≃ (Fin n × Fin n) where
  toFun p := (⟨(p.1.val + s p.2) % n, Nat.mod_lt _ hn⟩, p.2)
  invFun p := (⟨(p.1.val + n - s p.2 % n) % n, Nat.mod_lt _ hn⟩, p.2)
  left_inv p := by
    ext
    · exact mod_add_sub_round p.1.val (s p.2) n hn p.1.isLt
    · rfl
  right_inv p := by
    ext
    · exact gg_mod_inv_fwd p.1.val (s p.2) n hn p.1.isLt
    · rfl

/-- Vertical factor-2 step and its inverse. -/
def ggShearY (n : ℕ) (hn : 0 < n) (s : Fin n → ℕ) : (Fin n × Fin n) ≃ (Fin n × Fin n) where
  toFun p := (p.1, ⟨(p.2.val + s p.1) % n, Nat.mod_lt _ hn⟩)
  invFun p := (p.1, ⟨(p.2.val + n - s p.1 % n) % n, Nat.mod_lt _ hn⟩)
  left_inv p := by
    ext
    · rfl
    · exact mod_add_sub_round p.2.val (s p.1) n hn p.2.isLt
  right_inv p := by
    ext
    · rfl
    · exact gg_mod_inv_fwd p.2.val (s p.1) n hn p.2.isLt

theorem sum_prod (body : Fin n × Fin n → ℝ) :
    (∑ p : Fin n × Fin n, body p) = ∑ x : Fin n, ∑ y : Fin n, body (x, y) :=
  Fintype.sum_prod_type body

/-- The inverse horizontal step has the same correlation sum as the forward step. -/
theorem gg_x_inv_sum_eq (hn : 0 < n) (s : Fin n → ℕ) (g : Fin n → Fin n → ℝ) :
    (∑ x : Fin n, ∑ y : Fin n,
        g x y * g ⟨(x.val + n - s y % n) % n, Nat.mod_lt _ hn⟩ y) =
      ∑ x : Fin n, ∑ y : Fin n,
        g x y * g ⟨(x.val + s y) % n, Nat.mod_lt _ hn⟩ y := by
  let e := ggShearX n hn s
  let f : Fin n × Fin n → ℝ := fun p =>
    g p.1 p.2 * g ⟨(p.1.val + n - s p.2 % n) % n, Nat.mod_lt _ hn⟩ p.2
  have h := e.sum_comp f
  rw [sum_prod f, sum_prod (fun i => f (e i))] at h
  refine h.symm.trans ?_
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hback := e.left_inv (x, y)
  simp only [f, e, ggShearX, Equiv.coe_fn_mk] at hback ⊢
  rw [mul_comm]
  have hx :
      (⟨((x.val + s y) % n + n - s y % n) % n, Nat.mod_lt _ hn⟩ : Fin n) = x := by
    simpa using congrArg Prod.fst hback
  rw [hx]

/-- The inverse vertical step has the same correlation sum as the forward step. -/
theorem gg_y_inv_sum_eq (hn : 0 < n) (s : Fin n → ℕ) (g : Fin n → Fin n → ℝ) :
    (∑ x : Fin n, ∑ y : Fin n,
        g x y * g x ⟨(y.val + n - s x % n) % n, Nat.mod_lt _ hn⟩) =
      ∑ x : Fin n, ∑ y : Fin n,
        g x y * g x ⟨(y.val + s x) % n, Nat.mod_lt _ hn⟩ := by
  let e := ggShearY n hn s
  let f : Fin n × Fin n → ℝ := fun p =>
    g p.1 p.2 * g p.1 ⟨(p.2.val + n - s p.1 % n) % n, Nat.mod_lt _ hn⟩
  have h := e.sum_comp f
  rw [sum_prod f, sum_prod (fun i => f (e i))] at h
  refine h.symm.trans ?_
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hback := e.left_inv (x, y)
  simp only [f, e, ggShearY, Equiv.coe_fn_mk] at hback ⊢
  rw [mul_comm]
  have hy :
      (⟨((y.val + s x) % n + n - s x % n) % n, Nat.mod_lt _ hn⟩ : Fin n) = y := by
    simpa using congrArg Prod.snd hback
  rw [hy]

/-- Horizontal correlation for one additive shift of `x`. -/
noncomputable def ggShiftX (hn : 0 < n) (s : Fin n → ℕ) (g : Fin n → Fin n → ℝ) : ℝ :=
  ∑ x : Fin n, ∑ y : Fin n, g x y * g ⟨(x.val + s y) % n, Nat.mod_lt _ hn⟩ y

/-- Vertical correlation for one additive shift of `y`. -/
noncomputable def ggShiftY (hn : 0 < n) (s : Fin n → ℕ) (g : Fin n → Fin n → ℝ) : ℝ :=
  ∑ x : Fin n, ∑ y : Fin n, g x y * g x ⟨(y.val + s x) % n, Nat.mod_lt _ hn⟩

/-- Two forward horizontal Gabber-Galil steps: `(x+2y, y)` and `(x+2y+1, y)`. -/
noncomputable def ggC1 (hn : 0 < n) (g : Fin n → Fin n → ℝ) : ℝ :=
  ggShiftX hn (fun y => 2 * y.val) g + ggShiftX hn (fun y => 2 * y.val + 1) g

/-- Two forward vertical Gabber-Galil steps: `(x, y+2x)` and `(x, y+2x+1)`. -/
noncomputable def ggC2 (hn : 0 < n) (g : Fin n → Fin n → ℝ) : ℝ :=
  ggShiftY hn (fun x => 2 * x.val) g + ggShiftY hn (fun x => 2 * x.val + 1) g

/-- Labeled 8-step adjacency form. Inverses use the shear bijections above. -/
noncomputable def ggAdj (hn : 0 < n) (g : Fin n → Fin n → ℝ) : ℝ :=
  (∑ x : Fin n, ∑ y : Fin n,
      g x y * g ⟨(x.val + n - (2 * y.val) % n) % n, Nat.mod_lt _ hn⟩ y) +
    (∑ x : Fin n, ∑ y : Fin n,
      g x y * g ⟨(x.val + n - (2 * y.val + 1) % n) % n, Nat.mod_lt _ hn⟩ y) +
    (∑ x : Fin n, ∑ y : Fin n,
      g x y * g x ⟨(y.val + n - (2 * x.val) % n) % n, Nat.mod_lt _ hn⟩) +
    (∑ x : Fin n, ∑ y : Fin n,
      g x y * g x ⟨(y.val + n - (2 * x.val + 1) % n) % n, Nat.mod_lt _ hn⟩) +
    ggC1 hn g + ggC2 hn g

theorem ggAdj_eq_two_corr (hn : 0 < n) (g : Fin n → Fin n → ℝ) :
    ggAdj hn g = 2 * (ggC1 hn g + ggC2 hn g) := by
  unfold ggAdj ggC1 ggC2 ggShiftX ggShiftY
  rw [gg_x_inv_sum_eq hn (fun y => 2 * y.val) g,
    gg_x_inv_sum_eq hn (fun y => 2 * y.val + 1) g,
    gg_y_inv_sum_eq hn (fun x => 2 * x.val) g,
    gg_y_inv_sum_eq hn (fun x => 2 * x.val + 1) g]
  ring

/-- `|C₁ + C₂| * n² / 2` is at most the cosine bilinear form of `|dft|`. -/
theorem gg_corr_bound (hn : 3 ≤ n) (g : Fin n → Fin n → ℝ) :
    let hn0 : 0 < n := by omega
    |ggC1 hn0 g + ggC2 hn0 g| * (n : ℝ) ^ 2 / 2 ≤
      ∑ α₁ : Fin n, ∑ α₂ : Fin n,
        ‖dft2d n g α₁ α₂‖ *
          (‖dft2d n g (shearS2Fin n hn0 (α₁, α₂)).1 (shearS2Fin n hn0 (α₁, α₂)).2‖ *
              |Real.cos (↑π * ↑α₁.val / ↑n)| +
            ‖dft2d n g (shearS1Fin n hn0 (α₁, α₂)).1 (shearS1Fin n hn0 (α₁, α₂)).2‖ *
              |Real.cos (↑π * ↑α₂.val / ↑n)|) := by
  intro hn0
  have hn' : n ≠ 0 := by omega
  set C₁ := ggC1 hn0 g
  set C₂ := ggC2 hn0 g
  have hF₁ := corr_pair1 n hn' g hn
  have hF₂ := corr_pair2 n hn' g hn
  set F₁ := ∑ α₁ : Fin n, ∑ α₂ : Fin n,
    dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g α₁
      ⟨(α₂.val + n - (2 * α₁.val) % n) % n, Nat.mod_lt _ hn0⟩) *
    (1 + ω n ^ (-(α₁.val : ℤ)))
  set F₂ := ∑ α₁ : Fin n, ∑ α₂ : Fin n,
    dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g
      ⟨(α₁.val + n - (2 * α₂.val) % n) % n, Nat.mod_lt _ hn0⟩ α₂) *
    (1 + ω n ^ (-(α₂.val : ℤ)))
  have hC₁ : (↑n : ℂ) ^ 2 * ↑C₁ = F₁ := by
    simpa [C₁, ggC1, ggShiftX, mul_add, sum_add_distrib] using hF₁
  have hC₂ : (↑n : ℂ) ^ 2 * ↑C₂ = F₂ := by
    have hord :
        C₂ = ∑ x : Fin n, ∑ y : Fin n,
          g x y * (g x ⟨(2 * x.val + y.val) % n, Nat.mod_lt _ hn0⟩ +
            g x ⟨(2 * x.val + y.val + 1) % n, Nat.mod_lt _ hn0⟩) := by
      unfold C₂ ggC2 ggShiftY
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [mul_add]
      congr 1
      · have hv : (y.val + 2 * x.val) % n = (2 * x.val + y.val) % n :=
          congrArg (fun t => t % n) (Nat.add_comm _ _)
        exact congrArg (fun z => g x y * g x z) (Fin.ext hv)
      · have hv : (y.val + (2 * x.val + 1)) % n = (2 * x.val + y.val + 1) % n :=
          congrArg (fun t => t % n) (by omega)
        exact congrArg (fun z => g x y * g x z) (Fin.ext hv)
    simpa [hord, mul_add, sum_add_distrib] using hF₂
  have h_re_cast : ((↑n : ℂ) ^ 2).re = (↑n : ℝ) ^ 2 := by norm_cast
  have h_C₁_re : (↑n : ℝ) ^ 2 * C₁ = F₁.re := by
    have := congr_arg Complex.re hC₁
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at this
    rw [h_re_cast] at this
    exact this
  have h_C₂_re : (↑n : ℝ) ^ 2 * C₂ = F₂.re := by
    have := congr_arg Complex.re hC₂
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at this
    rw [h_re_cast] at this
    exact this
  have h_sum : |C₁ + C₂| * (↑n : ℝ) ^ 2 = |F₁.re + F₂.re| := by
    have hnn : (0 : ℝ) ≤ (↑n : ℝ) ^ 2 := by positivity
    rw [mul_comm, ← abs_of_nonneg hnn, ← abs_mul, mul_add, h_C₁_re, h_C₂_re]
  have hre_le : |F₁.re + F₂.re| / 2 ≤ (‖F₁‖ + ‖F₂‖) / 2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
    calc |F₁.re + F₂.re| ≤ |F₁.re| + |F₂.re| := abs_add_le _ _
      _ ≤ ‖F₁‖ + ‖F₂‖ := add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
  have hF₁_tri : ‖F₁‖ ≤ ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      ‖dft2d n g α₁ α₂‖ *
        ‖dft2d n g α₁ ⟨(α₂.val + n - (2 * α₁.val) % n) % n, Nat.mod_lt _ hn0⟩‖ *
        ‖(1 : ℂ) + ω n ^ (-(α₁.val : ℤ))‖ := by
    calc ‖F₁‖ ≤ ∑ α₁ : Fin n, ‖∑ α₂ : Fin n,
        dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g α₁
          ⟨(α₂.val + n - (2 * α₁.val) % n) % n, _⟩) *
        (1 + ω n ^ (-(α₁.val : ℤ)))‖ := norm_sum_le _ _
      _ ≤ ∑ α₁ : Fin n, ∑ α₂ : Fin n,
        ‖dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g α₁
          ⟨(α₂.val + n - (2 * α₁.val) % n) % n, _⟩) *
        (1 + ω n ^ (-(α₁.val : ℤ)))‖ := by
        gcongr with α₁
        exact norm_sum_le _ _
      _ = _ := by
        congr 1
        ext α₁
        congr 1
        ext α₂
        rw [norm_mul, norm_mul, Complex.norm_conj, mul_assoc]
  have hF₂_tri : ‖F₂‖ ≤ ∑ α₁ : Fin n, ∑ α₂ : Fin n,
      ‖dft2d n g α₁ α₂‖ *
        ‖dft2d n g ⟨(α₁.val + n - (2 * α₂.val) % n) % n, Nat.mod_lt _ hn0⟩ α₂‖ *
        ‖(1 : ℂ) + ω n ^ (-(α₂.val : ℤ))‖ := by
    calc ‖F₂‖ ≤ ∑ α₁ : Fin n, ‖∑ α₂ : Fin n,
        dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g
          ⟨(α₁.val + n - (2 * α₂.val) % n) % n, _⟩ α₂) *
        (1 + ω n ^ (-(α₂.val : ℤ)))‖ := norm_sum_le _ _
      _ ≤ ∑ α₁ : Fin n, ∑ α₂ : Fin n,
        ‖dft2d n g α₁ α₂ * starRingEnd ℂ (dft2d n g
          ⟨(α₁.val + n - (2 * α₂.val) % n) % n, _⟩ α₂) *
        (1 + ω n ^ (-(α₂.val : ℤ)))‖ := by
        gcongr with α₁
        exact norm_sum_le _ _
      _ = _ := by
        congr 1
        ext α₁
        congr 1
        ext α₂
        rw [norm_mul, norm_mul, Complex.norm_conj, mul_assoc]
  simp_rw [norm_one_add_ω_inv n hn'] at hF₁_tri hF₂_tri
  have hhalf : |C₁ + C₂| * (↑n : ℝ) ^ 2 / 2 = |F₁.re + F₂.re| / 2 := by
    rw [h_sum]
  rw [hhalf]
  calc |F₁.re + F₂.re| / 2
      ≤ (‖F₁‖ + ‖F₂‖) / 2 := hre_le
    _ ≤ ((∑ α₁, ∑ α₂, ‖dft2d n g α₁ α₂‖ *
            ‖dft2d n g α₁ ⟨(α₂.val + n - (2 * α₁.val) % n) % n, Nat.mod_lt _ hn0⟩‖ *
            (2 * |Real.cos (↑π * ↑α₁.val / ↑n)|)) +
         (∑ α₁, ∑ α₂, ‖dft2d n g α₁ α₂‖ *
            ‖dft2d n g ⟨(α₁.val + n - (2 * α₂.val) % n) % n, Nat.mod_lt _ hn0⟩ α₂‖ *
            (2 * |Real.cos (↑π * ↑α₂.val / ↑n)|))) / 2 := by
        gcongr
    _ = ∑ α₁, ∑ α₂, ‖dft2d n g α₁ α₂‖ *
          (‖dft2d n g (shearS2Fin n hn0 (α₁, α₂)).1 (shearS2Fin n hn0 (α₁, α₂)).2‖ *
              |Real.cos (↑π * ↑α₁.val / ↑n)| +
            ‖dft2d n g (shearS1Fin n hn0 (α₁, α₂)).1 (shearS1Fin n hn0 (α₁, α₂)).2‖ *
              |Real.cos (↑π * ↑α₂.val / ↑n)|) := by
      rw [div_eq_iff (show (2 : ℝ) ≠ 0 by norm_num)]
      rw [← Finset.sum_add_distrib]
      simp_rw [← Finset.sum_add_distrib]
      conv_rhs => rw [Finset.sum_mul]; arg 2; ext; rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro α₁ _
      apply Finset.sum_congr rfl
      intro α₂ _
      simp only [shearS2Fin, shearS1Fin]
      ring

/-- Factor-2 adjacency form of a mean-zero function is at most `5√2` times its square norm. -/
theorem gg_numerical_radius (hn : 3 ≤ n) (g : Fin n → Fin n → ℝ)
    (hmean : ∑ x : Fin n, ∑ y : Fin n, g x y = 0) :
    |ggAdj (by omega : 0 < n) g| ≤
      5 * Real.sqrt 2 * ∑ x : Fin n, ∑ y : Fin n, (g x y) ^ 2 := by
  have hn0 : 0 < n := by omega
  let G : Fin n → Fin n → ℝ := fun α₁ α₂ => ‖dft2d n g α₁ α₂‖
  have hG0 : G ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 := by
    rw [norm_eq_zero, dft2d_zero n g hn0]
    exact_mod_cast hmean
  have hbridge := gg_corr_bound hn g
  have hyoung := young_assembly n hn G hG0
  have hchain :
      |ggC1 hn0 g + ggC2 hn0 g| * (↑n : ℝ) ^ 2 / 2 ≤
        5 * √2 / 4 * ∑ α₁ : Fin n, ∑ α₂ : Fin n, G α₁ α₂ ^ 2 :=
    hbridge.trans (by simpa [G] using hyoung)
  have hG2 :
      (∑ α₁ : Fin n, ∑ α₂ : Fin n, G α₁ α₂ ^ 2) =
        ∑ α₁ : Fin n, ∑ α₂ : Fin n, Complex.normSq (dft2d n g α₁ α₂) := by
    congr 1
    ext α₁
    congr 1
    ext α₂
    exact Complex.sq_norm (dft2d n g α₁ α₂)
  rw [hG2, parseval_2d n (by omega : n ≠ 0) g] at hchain
  have harith :
      |ggC1 hn0 g + ggC2 hn0 g| ≤ 5 * √2 / 2 * ∑ x, ∑ y, (g x y) ^ 2 := by
    have hpos : (0 : ℝ) < (↑n : ℝ) ^ 2 / 2 := by positivity
    have hrewrite :
        5 * √2 / 4 * ((↑n : ℝ) ^ 2 * ∑ x, ∑ y, (g x y) ^ 2) =
          (5 * √2 / 2 * ∑ x, ∑ y, (g x y) ^ 2) * ((↑n : ℝ) ^ 2 / 2) := by
      ring
    rw [hrewrite] at hchain
    have hassoc :
        |ggC1 hn0 g + ggC2 hn0 g| * (↑n : ℝ) ^ 2 / 2 =
          |ggC1 hn0 g + ggC2 hn0 g| * ((↑n : ℝ) ^ 2 / 2) := by
      ring
    rw [hassoc] at hchain
    exact le_of_mul_le_mul_right hchain hpos
  have htwo := ggAdj_eq_two_corr hn0 g
  rw [htwo, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

end SATurday.ProofComplexity.MGGGabberGalil
