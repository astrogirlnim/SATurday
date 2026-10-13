import Theory.ProofComplexity.ExpanderMixing
import Theory.ProofComplexity.MGG.Factor2Spectral

/-!
# Expander mixing for powers of the factor-2 Gabber-Galil graph (Ladder Rung R4, layer E2a)

The eight factor-2 shears on the torus `(Z/m)^2` form a `StepSys` (inverse labelling
`mggF2InvGen`). The Gabber-Galil numerical radius `5√2` (`gg_numerical_radius`) gives the Rayleigh
hypothesis of `Expander.StepSys.mixing`, so the `k`-th power (degree `8^k`) mixes with
`λ^k = (5√2)^k`.

LOG: R4 expander layer E2a (GG instance)
-/

set_option linter.unusedSectionVars false

namespace SATurday.ProofComplexity.Expander

open Finset StepSys

/-- The factor-2 Gabber-Galil step system on the torus `(Z/m)^2`, `m ≥ 3`. -/
noncomputable def ggSys (m : ℕ) (hm : 3 ≤ m) : StepSys (MggTorus m) 8 where
  step s := mggF2TorusStep (lt_of_lt_of_le (by decide : 0 < 3) hm) s
  inv := mggF2InvGen
  inv_inv := mggF2InvGen_invGen
  step_inv s p := mggF2TorusStep_inv (lt_of_lt_of_le (by decide : 0 < 3) hm) s p

/-- Rayleigh hypothesis for the Gabber-Galil step system with `λ = 5√2`. -/
theorem ggSys_rayleigh (m : ℕ) (hm : 3 ≤ m) (f : MggTorus m → ℝ) (hf : ∑ p, f p = 0) :
    |ip f ((ggSys m hm).adj f)| ≤ 5 * Real.sqrt 2 * ip f f := by
  classical
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < 3) hm
  letI : NeZero m := ⟨ne_of_gt hm0⟩
  let g : Fin m → Fin m → ℝ := fun x y => f (x, y)
  have hmean : ∑ x : Fin m, ∑ y : Fin m, g x y = 0 := by
    rw [← Fintype.sum_prod_type]
    simpa [g] using hf
  have h := MGGGabberGalil.gg_numerical_radius hm g hmean
  have e1 : ip f ((ggSys m hm).adj f) = mggF2MultiRayleigh hm0 f := by
    unfold ip StepSys.adj mggF2MultiRayleigh
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.mul_sum]
    rfl
  have e2 : ip f f = ∑ x : Fin m, ∑ y : Fin m, (g x y) ^ 2 := by
    rw [ip_self_eq, Fintype.sum_prod_type]
  rw [e1, e2, mggF2MultiRayleigh_eq_ggAdj hm0 f]
  exact h

/-- Mixing for walks of length `k` on the factor-2 Gabber-Galil graph on `(Z/m)^2`. -/
theorem gg_mixing (m : ℕ) (hm : 3 ≤ m) (A B : Finset (MggTorus m)) (k : ℕ) :
    (ip (ind A) (((ggSys m hm).adjL ^ k) (ind B)) - (8 : ℝ) ^ k * A.card * B.card / (m * m : ℕ))
        ^ 2 ≤ ((5 * Real.sqrt 2) ^ 2) ^ k * A.card * B.card := by
  have hV : 0 < Fintype.card (MggTorus m) := by
    simp only [MggTorus, Fintype.card_prod, Fintype.card_fin]
    have := lt_of_lt_of_le (by decide : 0 < 3) hm
    positivity
  have := (ggSys m hm).mixing (5 * Real.sqrt 2) (ggSys_rayleigh m hm) (by positivity) hV A B k
  simpa [MggTorus, Fintype.card_prod, Fintype.card_fin] using this

/-! ## The bipartite walk multigraph and its edge boundary

Left copy and right copy of the torus; one edge for every pair `(u, w)` with `u` a left vertex and
`w : Fin k → Fin 8` a step sequence, from `u` to the right vertex `walkEnd k u w`. It is
`8^k`-regular on both sides. For `IL`, `IR` sets of left and right vertices, the edge boundary of
`IL ∪ IR` consists of the edges with exactly one endpoint inside. -/

/-- Edge boundary of `(IL, IR)` in the walk multigraph `GGW m k`. -/
noncomputable def ggwBoundary (m : ℕ) (hm : 3 ≤ m) (k : ℕ) (IL IR : Finset (MggTorus m)) :
    Finset (MggTorus m × (Fin k → Fin 8)) := by
  classical
  exact Finset.univ.filter fun e => (e.1 ∈ IL) ≠ ((ggSys m hm).walkEnd k e.1 e.2 ∈ IR)

open Classical in
/-- Number of edges between `IL` and `IR` is the mixing quantity. -/
theorem ggw_cross_eq (m : ℕ) (hm : 3 ≤ m) (k : ℕ) (IL IR : Finset (MggTorus m)) :
    (((Finset.univ : Finset (MggTorus m × (Fin k → Fin 8))).filter fun e =>
        e.1 ∈ IL ∧ (ggSys m hm).walkEnd k e.1 e.2 ∈ IR).card : ℝ) =
      ip (ind IL) (((ggSys m hm).adjL ^ k) (ind IR)) := by
  rw [Finset.card_filter, Nat.cast_sum, Fintype.sum_prod_type]
  unfold ip
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [(ggSys m hm).pow_apply_eq_sum_walks, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [ind]
  split_ifs <;> simp_all

open Classical in
theorem ggw_left_count (m : ℕ) (_hm : 3 ≤ m) (k : ℕ) (IL : Finset (MggTorus m)) :
    (((Finset.univ : Finset (MggTorus m × (Fin k → Fin 8))).filter fun e => e.1 ∈ IL).card : ℝ) =
      (8 : ℝ) ^ k * IL.card := by
  rw [Finset.card_filter, Nat.cast_sum, Fintype.sum_prod_type]
  have : ∀ u : MggTorus m, ∑ w : Fin k → Fin 8, ((if u ∈ IL then 1 else 0 : ℕ) : ℝ)
      = (8 : ℝ) ^ k * ind IL u := by
    intro u
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ind]
    split_ifs <;> simp
  simp only [this, ← Finset.mul_sum, sum_ind]

open Classical in
theorem ggw_right_count (m : ℕ) (hm : 3 ≤ m) (k : ℕ) (IR : Finset (MggTorus m)) :
    (((Finset.univ : Finset (MggTorus m × (Fin k → Fin 8))).filter fun e =>
        (ggSys m hm).walkEnd k e.1 e.2 ∈ IR).card : ℝ) = (8 : ℝ) ^ k * IR.card := by
  rw [Finset.card_filter, Nat.cast_sum, Fintype.sum_prod_type]
  have h1 : ∀ u : MggTorus m, ∑ w : Fin k → Fin 8,
      ((if (ggSys m hm).walkEnd k u w ∈ IR then 1 else 0 : ℕ) : ℝ)
      = ((ggSys m hm).adjL ^ k) (ind IR) u := by
    intro u
    rw [(ggSys m hm).pow_apply_eq_sum_walks]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [ind]
    split_ifs <;> simp
  simp only [h1]
  rw [(ggSys m hm).sum_pow, sum_ind]
  rfl

open Classical in
/-- The boundary count: `|∂(IL,IR)| = 8^k(|IL| + |IR|) - 2 · cross`. -/
theorem ggw_boundary_card (m : ℕ) (hm : 3 ≤ m) (k : ℕ) (IL IR : Finset (MggTorus m)) :
    ((ggwBoundary m hm k IL IR).card : ℝ) =
      (8 : ℝ) ^ k * (IL.card + IR.card) -
        2 * ip (ind IL) (((ggSys m hm).adjL ^ k) (ind IR)) := by
  rw [← ggw_cross_eq m hm k IL IR]
  have key : ∀ e : MggTorus m × (Fin k → Fin 8),
      ((if (e.1 ∈ IL) ≠ ((ggSys m hm).walkEnd k e.1 e.2 ∈ IR) then 1 else 0 : ℕ) : ℝ) =
        ((if e.1 ∈ IL then 1 else 0 : ℕ) : ℝ) + ((if (ggSys m hm).walkEnd k e.1 e.2 ∈ IR then 1 else 0 : ℕ) : ℝ)
        - 2 * ((if e.1 ∈ IL ∧ (ggSys m hm).walkEnd k e.1 e.2 ∈ IR then 1 else 0 : ℕ) : ℝ) := by
    intro e
    by_cases h1 : e.1 ∈ IL <;> by_cases h2 : (ggSys m hm).walkEnd k e.1 e.2 ∈ IR <;> (simp [h1, h2]; try norm_num)
  have e1 := ggw_left_count m hm k IL
  have e2 := ggw_right_count m hm k IR
  rw [Finset.card_filter] at e1 e2
  rw [ggwBoundary, Finset.card_filter, Nat.cast_sum]
  simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Nat.cast_sum] at e1 e2
  rw [e1, e2, Finset.card_filter, Nat.cast_sum]
  ring

/-- Edge expansion of the walk multigraph (the Alekhnovich-Razborov `(r, s, c)`-expander property):
the boundary of `IL ∪ IR` with `t = |IL| + |IR|` has at least `t (8^k (1 - t / (2 m²)) - (5√2)^k)`
edges. -/
theorem ggw_expansion (m : ℕ) (hm : 3 ≤ m) (k : ℕ) (IL IR : Finset (MggTorus m)) :
    ((IL.card + IR.card : ℕ) : ℝ) *
        ((8 : ℝ) ^ k * (1 - ((IL.card + IR.card : ℕ) : ℝ) / (2 * (m * m : ℕ))) -
          (5 * Real.sqrt 2) ^ k) ≤ (ggwBoundary m hm k IL IR).card := by
  have hN : (0 : ℝ) < (m * m : ℕ) := by
    have := lt_of_lt_of_le (by decide : 0 < 3) hm
    positivity
  rw [ggw_boundary_card]
  set N : ℝ := ((m * m : ℕ) : ℝ) with hNdef
  set cross := ip (ind IL) (((ggSys m hm).adjL ^ k) (ind IR)) with hc
  set a : ℝ := (IL.card : ℝ)
  set b : ℝ := (IR.card : ℝ)
  have ha : 0 ≤ a := Nat.cast_nonneg _
  have hb : 0 ≤ b := Nat.cast_nonneg _
  have mix := gg_mixing m hm IL IR k
  rw [← hc, ← hNdef] at mix
  set μ : ℝ := (5 * Real.sqrt 2) ^ k with hμ
  have hμ0 : 0 ≤ μ := by positivity
  have hμsq : ((5 * Real.sqrt 2) ^ 2) ^ k = μ ^ 2 := by rw [hμ, ← pow_mul, ← pow_mul, mul_comm 2 k]
  rw [hμsq] at mix
  have hab : a * b ≤ ((a + b) / 2) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have h1 : (cross - (8 : ℝ) ^ k * a * b / N) ^ 2 ≤ (μ * ((a + b) / 2)) ^ 2 := by
    calc _ ≤ μ ^ 2 * a * b := mix
      _ = μ ^ 2 * (a * b) := by ring
      _ ≤ μ ^ 2 * ((a + b) / 2) ^ 2 := by gcongr
      _ = _ := by ring
  have h2 := (abs_le_of_sq_le_sq' h1 (by positivity)).2
  have h3 : (8 : ℝ) ^ k * a * b / N ≤ (8 : ℝ) ^ k * ((a + b) / 2) ^ 2 / N := by
    apply div_le_div_of_nonneg_right _ hN.le
    calc (8 : ℝ) ^ k * a * b = (8 : ℝ) ^ k * (a * b) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hab (by positivity)
  push_cast
  have h4 : (8 : ℝ) ^ k * ((a + b) / 2) ^ 2 / N = (8 : ℝ) ^ k * (a + b) ^ 2 / (4 * N) := by
    field_simp; ring
  have h5 : (a + b) * ((8 : ℝ) ^ k * (1 - (a + b) / (2 * N)) - μ)
      = (8 : ℝ) ^ k * (a + b) - 2 * ((8 : ℝ) ^ k * (a + b) ^ 2 / (4 * N)) - μ * (a + b) := by
    field_simp; ring
  rw [h5]
  rw [h4] at h3
  nlinarith

end SATurday.ProofComplexity.Expander
