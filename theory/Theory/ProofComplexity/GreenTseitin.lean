import Theory.ProofComplexity.GreenImmunity
import Theory.ProofComplexity.TseitinEdgeCNF

/-!
# AR-B for the walk multigraph: the immunity hypothesis of D1 is discharged (Ladder Rung R4)

Every vertex of `GGW m k` has all its incident edges oriented the same way (left vertices only
emit, right vertices only receive), so its root set is `{a | |a ∩ J v| ≡ ε σ(v) (mod q)}` with
`ε = ±1` (`OGraph.Z_eq`).  `green_immune` then gives `⌊(8^k + 1)/q⌋`-immunity (`ggw_himm`), which
exceeds Alekhnovich-Razborov's `⌊8^k/(4(q-1))⌋` (`ar_thm44_ggw`).  The numerical side conditions of
`ggw_tseitin_no_refutation` are discharged for `16 q ≤ m` and `k ≥ k0 q`, giving the polynomial
calculus degree lower bound `m² 8^k / (256 q²)` (`ggw_tseitin_pc_degree`).

LOG: R4 AR-B GreenTseitin
-/

namespace SATurday.ProofComplexity.TseitinEdge

open Finset SATurday.ProofComplexity SATurday.ProofComplexity.PCL
open SATurday.ProofComplexity.Green (ZA fl mem_fl green_immune)

noncomputable section
open Classical

section Generic

variable {V E : Type} [Fintype V] [Fintype E] (G : OGraph V E)

theorem OGraph.lsum_uniform {q : ℕ} {v : V} {ε : ZMod q} (h : ∀ e ∈ G.inc v, G.coef q v e = ε)
    (b : E → Bool) :
    G.lsum q v b = ε * (((G.inc v).filter fun e => b e = true).card : ZMod q) := by
  unfold OGraph.lsum
  rw [← Finset.sum_subset (Finset.subset_univ (G.inc v)) (fun e _ he => by
    rw [G.coef_eq_zero he]; simp)]
  rw [Finset.sum_congr rfl (fun e he => by rw [h e he]), ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_boole]

theorem OGraph.Z_eq {q : ℕ} (σ : V → ZMod q) {v : V} {ε : ZMod q} (hε : ε * ε = 1)
    (h : ∀ e ∈ G.inc v, G.coef q v e = ε) : G.Z q σ v = ZA q (G.J v) (ε * σ v) := by
  ext a
  unfold OGraph.Z ZA
  simp only [Set.mem_setOf_eq]
  have hfl : fl (G.J v) a = ((G.inc v).filter fun e => G.asg a e = true).image G.col := by
    ext x
    rw [mem_fl]
    simp only [OGraph.J, Finset.mem_image, Finset.mem_filter, OGraph.asg, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hx⟩; exact ⟨e, ⟨he, hx⟩, rfl⟩
    · rintro ⟨e, ⟨he, hx⟩, rfl⟩; exact ⟨⟨e, he, rfl⟩, hx⟩
  rw [hfl, Finset.card_image_of_injective _ G.col_inj, G.lsum_uniform h]
  constructor
  · intro h1; rw [← h1, ← mul_assoc, hε, one_mul]
  · intro h1; rw [h1, ← mul_assoc, hε, one_mul]

end Generic

section GGW

open SATurday.ProofComplexity.Expander

theorem ggw_sign (m : ℕ) (hm : 3 ≤ m) (k q : ℕ) (v : MggTorus m ⊕ MggTorus m) :
    ∃ ε : ZMod q, ε * ε = 1 ∧
      ∀ e ∈ (ggwGraph m hm k).inc v, (ggwGraph m hm k).coef q v e = ε := by
  rcases v with u | w
  · refine ⟨-1, by ring, fun e he => ?_⟩
    simp only [OGraph.inc, ggwGraph, Finset.mem_filter, Finset.mem_univ, true_and, reduceCtorEq,
      or_false, Sum.inl.injEq] at he
    simp [OGraph.coef, ggwGraph, he]
  · refine ⟨1, by ring, fun e he => ?_⟩
    simp only [OGraph.inc, ggwGraph, Finset.mem_filter, Finset.mem_univ, true_and, reduceCtorEq,
      false_or, Sum.inr.injEq] at he
    simp [OGraph.coef, ggwGraph, he]

theorem ggw_J_card (m : ℕ) (hm : 3 ≤ m) (k : ℕ) (v : MggTorus m ⊕ MggTorus m) :
    ((ggwGraph m hm k).J v).card = 8 ^ k := by
  have h : (((ggwGraph m hm k).inc v).card : ℝ) = (8 : ℝ) ^ k := ggwGraph_inc_card m hm k v
  have h2 : ((ggwGraph m hm k).inc v).card = 8 ^ k := by exact_mod_cast h
  rw [OGraph.J, Finset.card_image_of_injective _ (ggwGraph m hm k).col_inj, h2]

/-- **AR Theorem 4.4 for the walk multigraph** (stronger constant): the vertex root sets are
`⌊(8^k + 1)/q⌋`-immune over every field in which `q` is invertible. -/
theorem ggw_himm {F : Type} [Field F] {q : ℕ} (hq2 : 2 ≤ q) (hqF : (q : F) ≠ 0) (m : ℕ)
    (hm : 3 ≤ m) (k : ℕ) (σ : MggTorus m ⊕ MggTorus m → ZMod q) :
    ∀ v, ∀ g : ML F, g ≠ 0 → (∀ a ∈ (ggwGraph m hm k).Z q σ v, ev a g = 0) →
      (8 ^ k + 1) / q ≤ deg g := by
  haveI : NeZero q := ⟨by omega⟩
  intro v g hg hv
  obtain ⟨ε, hε, hc⟩ := ggw_sign m hm k q v
  rw [OGraph.Z_eq _ σ hε hc] at hv
  have := green_immune hq2 hqF ((ggwGraph m hm k).J v) (ε * σ v) hg hv
  rwa [ggw_J_card] at this

/-- The constant `⌊d/(4(q-1))⌋` of Alekhnovich-Razborov Theorem 4.4 is at most ours. -/
theorem ar_const_le {q d : ℕ} (hq2 : 2 ≤ q) : d / (4 * (q - 1)) ≤ (d + 1) / q := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  have h1 : d / (4 * (q - 1)) * (4 * (q - 1)) ≤ d := Nat.div_mul_le_self _ _
  have h2 : q ≤ 4 * (q - 1) := by omega
  calc d / (4 * (q - 1)) * q ≤ d / (4 * (q - 1)) * (4 * (q - 1)) := Nat.mul_le_mul_left _ h2
    _ ≤ d + 1 := by omega

/-- Alekhnovich-Razborov Theorem 4.4 (uniform signs), `⌊d/(4(q-1))⌋`-immunity with `d = 8^k`. -/
theorem ar_thm44_ggw {F : Type} [Field F] {q : ℕ} (hq2 : 2 ≤ q) (hqF : (q : F) ≠ 0) (m : ℕ)
    (hm : 3 ≤ m) (k : ℕ) (σ : MggTorus m ⊕ MggTorus m → ZMod q) :
    ∀ v, ∀ g : ML F, g ≠ 0 → (∀ a ∈ (ggwGraph m hm k).Z q σ v, ev a g = 0) →
      8 ^ k / (4 * (q - 1)) ≤ deg g := fun v g hg hv =>
  (ar_const_le hq2).trans (ggw_himm hq2 hqF m hm k σ v g hg hv)

end GGW

section Numerics

open SATurday.ProofComplexity.Expander

theorem four_q_le_pow (q : ℕ) {k : ℕ} (hk : k0 q ≤ k) : 4 * q ≤ 8 ^ k := by
  have h1 : 32 * q ≤ 2 ^ Nat.clog 2 (32 * q) := Nat.le_pow_clog (by norm_num) _
  have h2 : Nat.clog 2 (32 * q) ≤ k := by unfold k0 at hk; omega
  calc 4 * q ≤ 32 * q := by omega
    _ ≤ 2 ^ Nat.clog 2 (32 * q) := h1
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h2
    _ ≤ 8 ^ k := Nat.pow_le_pow_left (by norm_num) k

/-- The numerical side conditions of `ggw_tseitin_no_refutation` with `ℓ = ⌊(D+1)/q⌋`,
`r = ⌊m²/(16 q)⌋`, `s = D`, `s - c = D/(16 q)`. -/
theorem num_bounds {q D m : ℕ} (hq2 : 2 ≤ q) (hD : 4 * q ≤ D) (hm : 16 * q ≤ m) :
    1 ≤ (D + 1) / q ∧ 1 ≤ m * m / (16 * q) ∧
    4 * ((D : ℝ) - D * (1 - 1 / (16 * q))) < (((D + 1) / q : ℕ) : ℝ) ∧
    ((m : ℝ) * m * D) / (256 * (q : ℝ) ^ 2) ≤
      Dbd ((D + 1) / q) (m * m / (16 * q)) (D : ℝ) (D * (1 - 1 / (16 * q))) ∧
    (D : ℝ) ≤ ((m : ℝ) * m * D) / (256 * (q : ℝ) ^ 2) := by
  have hq0 : 0 < q := by omega
  have hl : 1 ≤ (D + 1) / q := Nat.div_pos (by omega) hq0
  have hmm : 16 * q ≤ m * m := by nlinarith
  have hr : 1 ≤ m * m / (16 * q) := Nat.div_pos hmm (by omega)
  refine ⟨hl, hr, ?_⟩
  -- the floors
  have hL : D + 2 ≤ q * ((D + 1) / q) + q := by
    have h1 := Nat.div_add_mod (D + 1) q
    have h2 := Nat.mod_lt (D + 1) hq0
    generalize q * ((D + 1) / q) = P at h1 ⊢
    omega
  have hR : m * m ≤ 16 * q * (m * m / (16 * q)) + 16 * q := by
    have h1 := Nat.div_add_mod (m * m) (16 * q)
    have h2 := Nat.mod_lt (m * m) (show 0 < 16 * q by omega)
    generalize 16 * q * (m * m / (16 * q)) = P at h1 ⊢
    omega
  generalize hl' : (D + 1) / q = ℓ at *
  generalize hr' : m * m / (16 * q) = r at *
  have hQ : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  have hX : (4 : ℝ) * q ≤ D := by exact_mod_cast hD
  have hM : (16 : ℝ) * q ≤ m := by exact_mod_cast hm
  have hLr : (D : ℝ) + 2 ≤ q * ℓ + q := by exact_mod_cast hL
  have hRr : (m : ℝ) * m ≤ 16 * q * r + 16 * q := by exact_mod_cast hR
  have hQ0 : (0 : ℝ) < q := by linarith
  have hscE : (D : ℝ) - D * (1 - 1 / (16 * q)) = D / (16 * q) := by field_simp; ring
  have hMM : (32 : ℝ) * q ≤ m * m := by nlinarith
  have hMM2 : (256 : ℝ) * q ^ 2 ≤ m * m := by nlinarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hX0 : (0 : ℝ) ≤ D := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hscE, show (4 : ℝ) * (D / (16 * q)) = D / (4 * q) by field_simp; ring,
      div_lt_iff₀ (by positivity)]
    nlinarith
  · unfold Dbd
    rw [hscE]
    have h1 : (D : ℝ) / (8 * q) ≤ (ℓ : ℝ) / 4 - D / (16 * q) := by
      have : (ℓ : ℝ) / 4 - D / (16 * q) - D / (8 * q) = (4 * q * ℓ - 3 * D) / (16 * q) := by
        field_simp; ring
      have h3 : (0 : ℝ) ≤ (4 * q * ℓ - 3 * D) / (16 * q) := by
        refine div_nonneg ?_ (by positivity)
        nlinarith
      linarith
    have h2 : (m : ℝ) * m / (32 * q) ≤ r := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc (m : ℝ) * m * D / (256 * (q : ℝ) ^ 2)
        = ((m : ℝ) * m / (32 * q)) * ((D : ℝ) / (8 * q)) := by field_simp; ring
      _ ≤ r * ((ℓ : ℝ) / 4 - D / (16 * q)) :=
        mul_le_mul h2 h1 (by positivity) hr0
  · rw [le_div_iff₀ (by positivity)]
    nlinarith

end Numerics

open SATurday.ProofComplexity.Expander in
/-- **Polynomial calculus degree lower bound for the Boolean-edge Tseitin mod `q` formula on the
walk multigraph `GGW m k`** (Alekhnovich-Razborov Corollary 4.5 shape): for `q ≥ 2`, every field
`F` with `(q : F) ≠ 0`, `16 q ≤ m`, `k ≥ k0 q`, every `σ`, no PC refutation of degree
`≤ m² 8^k / (256 q²)` exists.  Here `8^k` is the degree and `2 m²` the number of vertices, so the
bound is `Ω(d n / q²)`. -/
theorem ggw_tseitin_pc_degree {F : Type} [Field F] {q : ℕ} (hq2 : 2 ≤ q) (hqF : (q : F) ≠ 0)
    {m : ℕ} (hm : 16 * q ≤ m) {k : ℕ} (hk : k0 q ≤ k) (σ : MggTorus m ⊕ MggTorus m → ZMod q)
    {d : ℕ} (hd : (d : ℝ) ≤ (m : ℝ) * m * (8 : ℝ) ^ k / (256 * (q : ℝ) ^ 2)) :
    ¬ PCD ((ggwGraph m (by omega) k).Ax F q σ) d 1 := by
  have hm3 : 3 ≤ m := by omega
  obtain ⟨hl, hr, hsc, hDbd, hDle⟩ := num_bounds (D := 8 ^ k) hq2 (four_q_le_pow q hk) hm
  push_cast at hsc hDbd hDle
  exact ggw_tseitin_no_refutation m hm3 (by omega) hk σ (ggw_himm hq2 hqF m hm3 k σ) hr hl hsc
    (hDle.trans hDbd) (hd.trans hDbd)

end

end SATurday.ProofComplexity.TseitinEdge
