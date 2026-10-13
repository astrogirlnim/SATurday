import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Binomial rank lemma (Ladder Rung R4, AR-B, layer 1)

Beck-Li Lemma 5.1 in an arbitrary field in which `q` is a unit: if
`c₀, …, c_e ∈ F` satisfy `∑_k c_k * C(a + i q, k) = 0` for `i = 0, …, e`, then all `c_k = 0`.

Elementary proof by the `q`-step difference operator, without the closed form of the determinant
(whose `1/k!` factors are not available in small characteristic): the Pascal operator
`pS c = c_v + c_{v+1}` realizes the shift `w ↦ w + 1` on binomial expansions, `(pS^q - 1) c` has
degree one less and top coefficient `q * c_top`.

LOG: R4 AR-B GreenBinom
-/

namespace SATurday.ProofComplexity.Green

open Finset

variable {F : Type} [Field F]

/-- Pascal step on coefficient vectors. -/
def pS (c : ℕ → F) : ℕ → F := fun v => c v + c (v + 1)

/-- The binomial expansion `∑_{k<N} c_k * C(w, k)`. -/
def phi (N : ℕ) (c : ℕ → F) (w : ℕ) : F := ∑ k ∈ range N, c k * (w.choose k : F)

theorem phi_sub (N : ℕ) (c d : ℕ → F) (w : ℕ) :
    phi N (fun v => c v - d v) w = phi N c w - phi N d w := by
  unfold phi
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem phi_succ_eq (N : ℕ) (c : ℕ → F) (h : c N = 0) (w : ℕ) : phi (N + 1) c w = phi N c w := by
  unfold phi; rw [Finset.sum_range_succ, h]; simp

theorem pS_zero {N : ℕ} {c : ℕ → F} (hc : ∀ k, N ≤ k → c k = 0) : ∀ k, N ≤ k → pS c k = 0 := by
  intro k hk
  simp [pS, hc k hk, hc (k + 1) (by omega)]

theorem phi_pS (N : ℕ) (c : ℕ → F) (hc : ∀ k, N ≤ k → c k = 0) (w : ℕ) :
    phi N (pS c) w = phi N c (w + 1) := by
  rcases N with _ | M
  · simp [phi]
  · unfold phi pS
    have e1 : ∑ k ∈ range (M + 1), (c k + c (k + 1)) * (w.choose k : F)
        = ∑ k ∈ range (M + 1), c k * (w.choose k : F)
          + ∑ k ∈ range (M + 1), c (k + 1) * (w.choose k : F) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∑ k ∈ range (M + 1), c (k + 1) * (w.choose k : F)
        = ∑ k ∈ range M, c (k + 1) * (w.choose k : F) := by
      rw [Finset.sum_range_succ, hc (M + 1) le_rfl]; simp
    have e3 : ∑ k ∈ range (M + 1), c k * (w.choose k : F)
        = c 0 + ∑ k ∈ range M, c (k + 1) * (w.choose (k + 1) : F) := by
      rw [Finset.sum_range_succ']; simp [add_comm]
    have e4 : ∑ k ∈ range (M + 1), c k * ((w + 1).choose k : F)
        = c 0 + ∑ k ∈ range M, c (k + 1) * ((w + 1).choose (k + 1) : F) := by
      rw [Finset.sum_range_succ']; simp [add_comm]
    rw [e1, e2, e3, e4]
    have : ∀ k, ((w + 1).choose (k + 1) : F) = (w.choose k : F) + (w.choose (k + 1) : F) := by
      intro k; rw [Nat.choose_succ_succ]; push_cast; ring
    simp only [this, mul_add, Finset.sum_add_distrib]
    ring

theorem iter_zero {N : ℕ} {c : ℕ → F} (hc : ∀ k, N ≤ k → c k = 0) (j : ℕ) :
    ∀ k, N ≤ k → (pS^[j] c) k = 0 := by
  induction j generalizing c with
  | zero => simpa using hc
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    exact ih (pS_zero hc)

theorem phi_iter (N : ℕ) (c : ℕ → F) (hc : ∀ k, N ≤ k → c k = 0) (j w : ℕ) :
    phi N (pS^[j] c) w = phi N c (w + j) := by
  induction j generalizing c with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih _ (pS_zero hc), phi_pS N c hc]
    congr 1

/-- Top coefficients of the iterated Pascal step. -/
theorem iter_top (M : ℕ) (c : ℕ → F) (hc : ∀ k, M + 2 ≤ k → c k = 0) (j : ℕ) :
    (pS^[j] c) M = c M + j * c (M + 1) ∧ (pS^[j] c) (M + 1) = c (M + 1) ∧
      ∀ k, M + 2 ≤ k → (pS^[j] c) k = 0 := by
  induction j with
  | zero => exact ⟨by simp, by simp, by simpa using hc⟩
  | succ j ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨?_, ?_, ?_⟩
    · simp only [pS, h1, h2]; push_cast; ring
    · simp only [pS, h2, h3 (M + 2) le_rfl]; ring
    · intro k hk; simp only [pS, h3 k hk, h3 (k + 1) (by omega)]; ring

/-- **Rank lemma** (Beck-Li 5.1, any field with `q` invertible). -/
theorem rank_lemma {q : ℕ} (hq : (q : F) ≠ 0) :
    ∀ (N : ℕ) (c : ℕ → F) (a : ℕ), (∀ k, N ≤ k → c k = 0) →
      (∀ i < N, phi N c (a + i * q) = 0) → ∀ k, c k = 0 := by
  intro N
  induction N with
  | zero => intro c a hc _ k; exact hc k (Nat.zero_le _)
  | succ N ih =>
    intro c a hc hz
    rcases N with _ | M
    · have h0 := hz 0 (by omega)
      simp [phi] at h0
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact h0
      · exact hc k hk
    · obtain ⟨t1, t2, t3⟩ := iter_top M c hc q
      set c' : ℕ → F := fun v => (pS^[q] c) v - c v with hc'
      have hc'zero : ∀ k, M + 1 ≤ k → c' k = 0 := by
        intro k hk
        rcases Nat.eq_or_lt_of_le hk with h | h
        · subst h; simp [hc', t2]
        · simp [hc', t3 k (by omega), hc k (by omega)]
      have hphi : ∀ i < M + 1, phi (M + 1) c' (a + i * q) = 0 := by
        intro i hi
        rw [← phi_succ_eq (M + 1) c' (hc'zero _ le_rfl), hc', phi_sub, phi_iter _ c hc,
          hz i (by omega)]
        have : a + i * q + q = a + (i + 1) * q := by ring
        rw [this, hz (i + 1) (by omega)]; simp
      have hall := ih c' a hc'zero hphi
      have hM : c (M + 1) = 0 := by
        have := hall M
        simp only [hc', t1] at this
        have h2 : (q : F) * c (M + 1) = 0 := by linear_combination this
        exact (mul_eq_zero.1 h2).resolve_left hq
      refine ih c a (fun k hk => ?_) (fun i hi => ?_)
      · rcases Nat.eq_or_lt_of_le hk with h | h
        · subst h; exact hM
        · exact hc k (by omega)
      · rw [← phi_succ_eq (M + 1) c hM]; exact hz i (by omega)

end SATurday.ProofComplexity.Green
