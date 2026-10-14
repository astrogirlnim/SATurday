import Theory.ProofComplexity.PangHilbert

/-!
# Pang route, layer H: parameter arithmetic

* `exp_bound` : `M = θ + a`, `θ ≤ s a`, `M^t ≤ S θ^t` give `2^(t / s) ≤ S`.
* `Nn_ratio` : for `2d < K` and `n ≤ λ (K - 2d)`, `N_n(K) ≤ (1 + λ^d) N_n(K - d)`.
-/

namespace Pang

lemma two_mul_pow_le {θ a s : ℕ} (hs : θ ≤ s * a) (hs0 : 0 < s) : 2 * θ ^ s ≤ (θ + a) ^ s := by
  have key : ∀ s' : ℕ, θ ^ (s' + 1) + (s' + 1) * a * θ ^ s' ≤ (θ + a) ^ (s' + 1) := by
    intro s'
    induction s' with
    | zero => simp
    | succ s' ih =>
      calc θ ^ (s' + 1 + 1) + (s' + 1 + 1) * a * θ ^ (s' + 1)
          ≤ (θ + a) * (θ ^ (s' + 1) + (s' + 1) * a * θ ^ s') := by
            have : (θ + a) * (θ ^ (s' + 1) + (s' + 1) * a * θ ^ s') =
                θ ^ (s' + 1 + 1) + (s' + 1 + 1) * a * θ ^ (s' + 1) + (s' + 1) * a * a * θ ^ s' := by
              ring
            rw [this]; exact Nat.le_add_right _ _
        _ ≤ (θ + a) * (θ + a) ^ (s' + 1) := Nat.mul_le_mul_left _ ih
        _ = (θ + a) ^ (s' + 1 + 1) := by ring
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have h1 := key s'
  have h2 : θ ^ (s' + 1) ≤ (s' + 1) * a * θ ^ s' := by
    calc θ ^ (s' + 1) = θ * θ ^ s' := by ring
      _ ≤ ((s' + 1) * a) * θ ^ s' := Nat.mul_le_mul_right _ hs
  omega

theorem exp_bound {M θ a S t s : ℕ} (hMθ : M = θ + a) (hθ : 0 < θ) (hs : θ ≤ s * a)
    (hpow : M ^ t ≤ S * θ ^ t) : 2 ^ (t / s) ≤ S := by
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp at hs; omega
    · exact h
  have h2 := two_mul_pow_le hs hs0
  rw [← hMθ] at h2
  have hk : ∀ k : ℕ, 2 ^ k * θ ^ (s * k) ≤ M ^ (s * k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc 2 ^ (k + 1) * θ ^ (s * (k + 1)) = 2 ^ k * θ ^ (s * k) * (2 * θ ^ s) := by ring
        _ ≤ M ^ (s * k) * M ^ s := Nat.mul_le_mul ih h2
        _ = M ^ (s * (k + 1)) := by ring
  have hMθ' : θ ≤ M := by omega
  have ht : t = s * (t / s) + t % s := (Nat.div_add_mod t s).symm
  have h3 : 2 ^ (t / s) * θ ^ t ≤ M ^ t := by
    calc 2 ^ (t / s) * θ ^ t = (2 ^ (t / s) * θ ^ (s * (t / s))) * θ ^ (t % s) := by
          rw [mul_assoc, ← pow_add, ← ht]
      _ ≤ M ^ (s * (t / s)) * M ^ (t % s) :=
          Nat.mul_le_mul (hk _) (Nat.pow_le_pow_left hMθ' _)
      _ = M ^ t := by rw [← pow_add, ← ht]
  have h4 : 2 ^ (t / s) * θ ^ t ≤ S * θ ^ t := h3.trans hpow
  exact Nat.le_of_mul_le_mul_right h4 (pow_pos hθ t)

/-- `m^d C(n, j+d) ≤ n^d C(n, j)` whenever `m ≤ j + 1`. -/
lemma choose_ratio (n m : ℕ) : ∀ d j : ℕ, m ≤ j + 1 → m ^ d * n.choose (j + d) ≤ n ^ d * n.choose j := by
  intro d
  induction d with
  | zero => intro j _; simp
  | succ d ih =>
    intro j hj
    have h1 := ih j hj
    have h2 : m * n.choose (j + d + 1) ≤ n * n.choose (j + d) := by
      have e := Nat.choose_succ_right_eq n (j + d)
      have : m ≤ j + d + 1 := by omega
      calc m * n.choose (j + d + 1) ≤ (j + d + 1) * n.choose (j + d + 1) :=
            Nat.mul_le_mul_right _ this
        _ = n.choose (j + d) * (n - (j + d)) := by rw [mul_comm, e]
        _ ≤ n.choose (j + d) * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = n * n.choose (j + d) := mul_comm _ _
    calc m ^ (d + 1) * n.choose (j + (d + 1)) = m ^ d * (m * n.choose (j + d + 1)) := by ring
      _ ≤ m ^ d * (n * n.choose (j + d)) := Nat.mul_le_mul_left _ h2
      _ = n * (m ^ d * n.choose (j + d)) := by ring
      _ ≤ n * (n ^ d * n.choose j) := Nat.mul_le_mul_left _ h1
      _ = n ^ (d + 1) * n.choose j := by ring


theorem Nn_ratio {n K d lam : ℕ} (hK : 2 * d < K) (hlam : n ≤ lam * (K - 2 * d)) :
    Nn n K ≤ (1 + lam ^ d) * Nn n (K - d) := by
  set m := K - 2 * d with hm
  have hm0 : 0 < m := by omega
  have hsplit : K + 1 = (K - d + 1) + d := by omega
  have hsplit2 : K - d + 1 = (K - 2 * d + 1) + d := by omega
  have hN : Nn n K = Nn n (K - d) + ∑ i ∈ Finset.range d, n.choose (K - d + 1 + i) := by
    unfold Nn; rw [hsplit, Finset.sum_range_add]
  have hN' : Nn n (K - d) = ∑ j ∈ Finset.range (K - 2 * d + 1), n.choose j +
      ∑ i ∈ Finset.range d, n.choose (K - 2 * d + 1 + i) := by
    unfold Nn; rw [hsplit2, Finset.sum_range_add]
  have hT : m ^ d * ∑ i ∈ Finset.range d, n.choose (K - d + 1 + i) ≤ n ^ d * Nn n (K - d) := by
    rw [Finset.mul_sum]
    calc ∑ i ∈ Finset.range d, m ^ d * n.choose (K - d + 1 + i)
        ≤ ∑ i ∈ Finset.range d, n ^ d * n.choose (K - 2 * d + 1 + i) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          have := choose_ratio n m d (K - 2 * d + 1 + i) (by omega)
          have e : K - 2 * d + 1 + i + d = K - d + 1 + i := by omega
          rw [e] at this; exact this
      _ = n ^ d * ∑ i ∈ Finset.range d, n.choose (K - 2 * d + 1 + i) := by rw [Finset.mul_sum]
      _ ≤ n ^ d * Nn n (K - d) := Nat.mul_le_mul_left _ (by rw [hN']; exact Nat.le_add_left _ _)
  have hnd : n ^ d ≤ (lam * m) ^ d := Nat.pow_le_pow_left hlam _
  have h2 : m ^ d * ∑ i ∈ Finset.range d, n.choose (K - d + 1 + i) ≤ m ^ d * (lam ^ d * Nn n (K - d)) := by
    calc _ ≤ n ^ d * Nn n (K - d) := hT
      _ ≤ (lam * m) ^ d * Nn n (K - d) := Nat.mul_le_mul_right _ hnd
      _ = m ^ d * (lam ^ d * Nn n (K - d)) := by rw [mul_pow]; ring
  have h3 := Nat.le_of_mul_le_mul_left h2 (pow_pos hm0 d)
  rw [hN]; nlinarith [h3]

end Pang
