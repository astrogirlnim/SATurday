import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Expander mixing for powers of a symmetric step system (Ladder Rung R4, expander layer E1)

A *step system* on a finite type `V` is `D` bijections `step s` with an involutive relabelling
`inv` such that `step (inv s)` undoes `step s`. Its adjacency operator is
`adj f p = ∑ s, f (step s p)`; it is symmetric. If the quadratic form of `adj` is bounded by
`lam * ‖f‖²` on mean-zero functions, then `adj^k` has norm at most `lam^k` on mean-zero functions,
and the number of `k`-step walks from `S` ending in `T` is within `lam^k √(|S||T|)` of
`D^k |S||T| / |V|` (expander mixing lemma for the `k`-th power).

LOG: R4 expander layer E1 (generic mixing lemma)
-/

set_option linter.unusedSectionVars false

namespace SATurday.ProofComplexity.Expander

open Finset

/-- Inner product on real functions. -/
def ip {V : Type} [Fintype V] (f g : V → ℝ) : ℝ := ∑ p, f p * g p

structure StepSys (V : Type) (D : ℕ) where
  step : Fin D → V → V
  inv : Fin D → Fin D
  inv_inv : ∀ s, inv (inv s) = s
  step_inv : ∀ s p, step (inv s) (step s p) = p

namespace StepSys

variable {V : Type} [Fintype V] {D : ℕ} (S : StepSys V D)

/-- Each step is a bijection. -/
def stepEquiv (s : Fin D) : V ≃ V where
  toFun := S.step s
  invFun := S.step (S.inv s)
  left_inv := fun p => S.step_inv s p
  right_inv := fun p => by
    have := S.step_inv (S.inv s) p
    rwa [S.inv_inv] at this

def invEquiv : Fin D ≃ Fin D where
  toFun := S.inv
  invFun := S.inv
  left_inv := S.inv_inv
  right_inv := S.inv_inv

/-- Adjacency operator. -/
def adj (f : V → ℝ) (p : V) : ℝ := ∑ s, f (S.step s p)

theorem sum_comp_step (s : Fin D) (f : V → ℝ) : ∑ p, f (S.step s p) = ∑ p, f p :=
  Equiv.sum_comp (S.stepEquiv s) f

theorem sum_adj (f : V → ℝ) : ∑ p, S.adj f p = D * ∑ p, f p := by
  unfold adj
  rw [Finset.sum_comm]
  simp [S.sum_comp_step]

theorem sum_step_swap (s : Fin D) (f g : V → ℝ) :
    ∑ p, f p * g (S.step s p) = ∑ q, f (S.step (S.inv s) q) * g q := by
  rw [← Equiv.sum_comp (S.stepEquiv s) (fun q => f (S.step (S.inv s) q) * g q)]
  refine Finset.sum_congr rfl fun p _ => ?_
  show _ = f (S.step (S.inv s) (S.step s p)) * g (S.step s p)
  rw [S.step_inv]

theorem adj_symm (f g : V → ℝ) : ip f (S.adj g) = ip (S.adj f) g := by
  unfold ip adj
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h1 : ∀ s : Fin D, ∑ p, f p * g (S.step s p) = ∑ q, f (S.step (S.inv s) q) * g q :=
    fun s => S.sum_step_swap s f g
  simp only [h1]
  rw [← Equiv.sum_comp S.invEquiv (fun s => ∑ q, f (S.step (S.inv s) q) * g q)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun s _ => ?_
  show f (S.step (S.inv (S.inv s)) q) * g q = _
  rw [S.inv_inv]

/-- Adjacency as a linear map. -/
def adjL : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun := S.adj
  map_add' f g := by
    funext p
    simp [adj, Finset.sum_add_distrib]
  map_smul' c f := by
    funext p
    simp [adj, Finset.mul_sum]

theorem ip_comm (f g : V → ℝ) : ip f g = ip g f := by
  unfold ip; exact Finset.sum_congr rfl fun p _ => mul_comm _ _

theorem ip_add_left (f g h : V → ℝ) : ip (f + g) h = ip f h + ip g h := by
  simp [ip, add_mul, Finset.sum_add_distrib]

theorem ip_sub_left (f g h : V → ℝ) : ip (f - g) h = ip f h - ip g h := by
  simp [ip, sub_mul, Finset.sum_sub_distrib]

theorem ip_add_right (f g h : V → ℝ) : ip f (g + h) = ip f g + ip f h := by
  simp [ip, mul_add, Finset.sum_add_distrib]

theorem ip_sub_right (f g h : V → ℝ) : ip f (g - h) = ip f g - ip f h := by
  simp [ip, mul_sub, Finset.sum_sub_distrib]

theorem ip_smul_left (c : ℝ) (f g : V → ℝ) : ip (c • f) g = c * ip f g := by
  simp [ip, Finset.mul_sum, mul_assoc]

theorem ip_smul_right (c : ℝ) (f g : V → ℝ) : ip f (c • g) = c * ip f g := by
  simp [ip, Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring

theorem ip_self_eq (f : V → ℝ) : ip f f = ∑ p, f p ^ 2 := by
  simp [ip, sq]

theorem ip_self_nonneg (f : V → ℝ) : 0 ≤ ip f f := by
  rw [ip_self_eq]; exact Finset.sum_nonneg fun p _ => sq_nonneg _

section Spectral

variable (lam : ℝ) (H : ∀ f : V → ℝ, ∑ p, f p = 0 → |ip f (S.adj f)| ≤ lam * ip f f)

include H

theorem polar (f g : V → ℝ) (hf : ∑ p, f p = 0) (hg : ∑ p, g p = 0) :
    4 * ip f (S.adj g) ≤ 2 * lam * (ip f f + ip g g) := by
  have hfg : ∑ p, (f + g) p = 0 := by simp [Finset.sum_add_distrib, hf, hg]
  have hfg' : ∑ p, (f - g) p = 0 := by simp [Finset.sum_sub_distrib, hf, hg]
  have h1 := H _ hfg
  have h2 := H _ hfg'
  have adj_add : S.adj (f + g) = S.adj f + S.adj g := (S.adjL).map_add f g
  have adj_sub : S.adj (f - g) = S.adj f - S.adj g := (S.adjL).map_sub f g
  have sym : ip g (S.adj f) = ip f (S.adj g) := by
    rw [ip_comm, ← S.adj_symm]
  have e1 : ip (f + g) (S.adj (f + g)) =
      ip f (S.adj f) + ip f (S.adj g) + ip f (S.adj g) + ip g (S.adj g) := by
    rw [adj_add, ip_add_left, ip_add_right, ip_add_right, sym]; ring
  have e2 : ip (f - g) (S.adj (f - g)) =
      ip f (S.adj f) - ip f (S.adj g) - ip f (S.adj g) + ip g (S.adj g) := by
    rw [adj_sub, ip_sub_left, ip_sub_right, ip_sub_right, sym]; ring
  have p1 : ip (f + g) (f + g) = ip f f + 2 * ip f g + ip g g := by
    rw [ip_add_left, ip_add_right, ip_add_right, ip_comm g f]; ring
  have p2 : ip (f - g) (f - g) = ip f f - 2 * ip f g + ip g g := by
    rw [ip_sub_left, ip_sub_right, ip_sub_right, ip_comm g f]; ring
  have a1 := (abs_le.1 h1).2
  have a2 := (abs_le.1 h2).1
  rw [e1, p1] at a1
  rw [e2, p2] at a2
  linarith

theorem norm_adj_le (hlam : 0 ≤ lam) (f : V → ℝ) (hf : ∑ p, f p = 0) :
    ip (S.adj f) (S.adj f) ≤ lam ^ 2 * ip f f := by
  set h := S.adj f with hh
  have hh0 : ∑ p, h p = 0 := by rw [hh, S.sum_adj, hf, mul_zero]
  have hX : ip h (S.adj f) = ip h h := rfl
  rcases hlam.eq_or_lt with h0 | hpos
  · have := S.polar lam H h f hh0 hf
    rw [← h0] at this ⊢
    have := ip_self_nonneg h
    nlinarith [ip_self_nonneg f]
  · have hc : ∑ p, ((1 / lam) • h) p = 0 := by
      simp [← Finset.mul_sum, hh0]
    have := S.polar lam H ((1 / lam) • h) f hc hf
    rw [ip_smul_left, ip_smul_left, ip_smul_right, hX] at this
    have hX0 := ip_self_nonneg h
    have key : ip h h ≤ lam ^ 2 * ip f f := by
      have e : (1 / lam) * ip h h * 4 ≤ 2 * lam * (1 / lam * (1 / lam * ip h h) + ip f f) := by
        linarith
      have e2 : 2 * lam * (1 / lam * (1 / lam * ip h h) + ip f f)
          = 2 * (ip h h / lam) + 2 * lam * ip f f := by field_simp
      have e3 : (1 / lam) * ip h h * 4 = 4 * (ip h h / lam) := by ring
      have e4 : ip h h / lam ≤ lam * ip f f := by linarith
      rw [div_le_iff₀ hpos] at e4
      nlinarith
    exact key

theorem norm_pow_le (hlam : 0 ≤ lam) (k : ℕ) (f : V → ℝ) (hf : ∑ p, f p = 0) :
    ip ((S.adjL ^ k) f) ((S.adjL ^ k) f) ≤ (lam ^ 2) ^ k * ip f f := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hg : ∑ p, ((S.adjL ^ k) f) p = 0 := by
      clear ih
      induction k with
      | zero => simpa using hf
      | succ j ihj =>
        rw [pow_succ', Module.End.mul_apply]
        show ∑ p, S.adj ((S.adjL ^ j) f) p = 0
        rw [S.sum_adj, ihj, mul_zero]
    have := S.norm_adj_le lam H hlam _ hg
    rw [pow_succ', Module.End.mul_apply]
    show ip (S.adj ((S.adjL ^ k) f)) (S.adj ((S.adjL ^ k) f)) ≤ _
    calc _ ≤ lam ^ 2 * ip ((S.adjL ^ k) f) ((S.adjL ^ k) f) := this
      _ ≤ lam ^ 2 * ((lam ^ 2) ^ k * ip f f) := by gcongr
      _ = _ := by rw [pow_succ']; ring

end Spectral

theorem sum_pow (k : ℕ) (f : V → ℝ) : ∑ p, ((S.adjL ^ k) f) p = (D : ℝ) ^ k * ∑ p, f p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    show ∑ p, S.adj ((S.adjL ^ k) f) p = _
    rw [S.sum_adj, ih, pow_succ']; ring

theorem pow_const (k : ℕ) (c : ℝ) : (S.adjL ^ k) (fun _ => c) = fun _ => (D : ℝ) ^ k * c := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    funext p
    show ∑ s : Fin D, (D : ℝ) ^ k * c = _
    simp [pow_succ']; ring

/-- Endpoint of the walk from `u` along the step labels `w`. -/
def walkEnd : (k : ℕ) → V → (Fin k → Fin D) → V
  | 0, u, _ => u
  | k + 1, u, w => walkEnd k (S.step (w 0) u) (fun i => w i.succ)

theorem pow_apply_eq_sum_walks (k : ℕ) (f : V → ℝ) (u : V) :
    (S.adjL ^ k) f u = ∑ w : Fin k → Fin D, f (S.walkEnd k u w) := by
  induction k generalizing u with
  | zero => simp [walkEnd]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    show ∑ s : Fin D, ((S.adjL ^ k) f) (S.step s u) = _
    simp only [ih]
    rw [← Fintype.sum_prod_type'
      (f := fun (s : Fin D) (w : Fin k → Fin D) => f (S.walkEnd k (S.step s u) w))]
    refine Fintype.sum_equiv (Fin.consEquiv (fun _ => Fin D)) _ _ fun x => ?_
    simp [walkEnd, Fin.consEquiv]

open Classical in
/-- Indicator of a finite set. -/
noncomputable def ind (A : Finset V) : V → ℝ := fun p => if p ∈ A then 1 else 0

theorem sum_ind (A : Finset V) : ∑ p, ind A p = A.card := by
  classical
  simp [ind]

theorem ip_const_right (f : V → ℝ) (c : ℝ) : ip f (fun _ => c) = c * ∑ p, f p := by
  simp [ip, Finset.mul_sum, mul_comm]

theorem ip_const_left (f : V → ℝ) (c : ℝ) : ip (fun _ => c) f = c * ∑ p, f p := by
  simp [ip, Finset.mul_sum]

theorem ip_const_const (c d : ℝ) :
    ip (fun _ : V => c) (fun _ => d) = (Fintype.card V : ℝ) * (c * d) := by
  simp [ip]

theorem ip_centered_le (A : Finset V) (hV : 0 < Fintype.card V) :
    ip (ind A - fun _ => (A.card : ℝ) / Fintype.card V)
      (ind A - fun _ => (A.card : ℝ) / Fintype.card V) ≤ A.card := by
  classical
  set N : ℝ := (Fintype.card V : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast hV
  set a : ℝ := (A.card : ℝ) / N with ha
  have hNa : N * a = A.card := by rw [ha]; field_simp
  have ha0 : 0 ≤ a := by positivity
  rw [ip_self_eq]
  have : ∀ p, ((ind A - fun _ => a : V → ℝ) p) ^ 2 = ind A p * (1 - 2 * a) + a ^ 2 := by
    intro p
    simp only [Pi.sub_apply, ind]
    split_ifs <;> ring
  simp only [this, Finset.sum_add_distrib, ← Finset.sum_mul, sum_ind]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← hN]
  nlinarith [mul_nonneg ha0 (Nat.cast_nonneg (α := ℝ) A.card)]

section Mixing

variable (lam : ℝ) (H : ∀ f : V → ℝ, ∑ p, f p = 0 → |ip f (S.adj f)| ≤ lam * ip f f)

include H

/-- Expander mixing lemma for the `k`-th power: with `E` the number of `k`-walks from `A` that
end in `B` (as `ip (ind A) (adjL^k (ind B))`), `(E - D^k |A||B|/|V|)² ≤ lam^{2k} |A||B|`. -/
theorem mixing (hlam : 0 ≤ lam) (hV : 0 < Fintype.card V) (A B : Finset V) (k : ℕ) :
    (ip (ind A) ((S.adjL ^ k) (ind B)) - (D : ℝ) ^ k * A.card * B.card / Fintype.card V) ^ 2
      ≤ (lam ^ 2) ^ k * A.card * B.card := by
  classical
  set N : ℝ := (Fintype.card V : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast hV
  set a : ℝ := (A.card : ℝ) / N with ha
  set b : ℝ := (B.card : ℝ) / N with hb
  have hNa : N * a = A.card := by rw [ha]; field_simp
  have hNb : N * b = B.card := by rw [hb]; field_simp
  obtain ⟨f, hf⟩ : ∃ f : V → ℝ, f = ind A - fun _ => a := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : V → ℝ, g = ind B - fun _ => b := ⟨_, rfl⟩
  have hf0 : ∑ p, f p = 0 := by
    rw [hf]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_ind]
    simp [← hN, hNa]
  have hg0 : ∑ p, g p = 0 := by
    rw [hg]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_ind]
    simp [← hN, hNb]
  have decA : ind A = f + fun _ => a := by rw [hf]; funext p; simp
  have decB : ind B = g + fun _ => b := by rw [hg]; funext p; simp
  have hmain : ip (ind A) ((S.adjL ^ k) (ind B)) =
      ip f ((S.adjL ^ k) g) + (D : ℝ) ^ k * A.card * B.card / N := by
    rw [decB, map_add, S.pow_const, decA, ip_add_left, ip_add_right, ip_add_right,
      ip_const_right, hf0, ip_const_left, S.sum_pow, hg0, ip_const_const]
    have : (D : ℝ) ^ k * A.card * B.card / N = N * (a * ((D : ℝ) ^ k * b)) := by
      rw [div_eq_iff hNpos.ne', ← hNa, ← hNb]; ring
    rw [this]; ring
  rw [hmain, add_sub_cancel_right]
  have cs : (ip f ((S.adjL ^ k) g)) ^ 2 ≤ ip f f * ip ((S.adjL ^ k) g) ((S.adjL ^ k) g) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f ((S.adjL ^ k) g)
    rw [ip_self_eq, ip_self_eq]
    exact this
  have n1 := S.norm_pow_le lam H hlam k g hg0
  have f1 : ip f f ≤ A.card := by rw [hf]; exact ip_centered_le A hV
  have g1 : ip g g ≤ B.card := by rw [hg]; exact ip_centered_le B hV
  refine cs.trans ?_
  calc ip f f * ip ((S.adjL ^ k) g) ((S.adjL ^ k) g)
      ≤ (A.card : ℝ) * ((lam ^ 2) ^ k * (B.card : ℝ)) := by
        apply mul_le_mul f1 (n1.trans (by gcongr)) (ip_self_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by ring

end Mixing

end StepSys

end SATurday.ProofComplexity.Expander
