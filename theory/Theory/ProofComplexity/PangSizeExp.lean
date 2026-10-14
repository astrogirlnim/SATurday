import Theory.ProofComplexity.PangDegSize
import Theory.ProofComplexity.PangExp

/-!
# Pang route, layers F-H combined: an exponential size bound from a degree bound
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.PCL MvPolynomial

namespace Pang

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime]

/-- **Degree-size relation, exponential form** (Pang Theorem 1.1 for `r = 1`, up to constants):
if `1 ∉ C_D(Q(Φ))` then every dag-like `Res(lin F_p)` refutation of `Φ` over the variables `V`
has at least `2^(t / (2 (1 + λ^(p-1))))` nodes, for parameters satisfying the stated budgets. -/
theorem size_exp {Φ : CNF} {V : Finset ℕ} (R : Refutation Φ V p) {D K t w lam : ℕ}
    (hD : 2 ≤ D) (h1 : (1 : PP p) ∉ CD (cnfAx Φ) D) (ht : 1 ≤ t)
    (hw : ∀ C ∈ Φ, C.card ≤ w) (hdK : p - 1 ≤ K) (hKn : K ≤ V.card)
    (hb1 : K + 2 * (t * ((p - 1) * (p - 1))) + 2 * (p - 1) ≤ D)
    (hb2 : K + t * ((p - 1) * (p - 1)) + w ≤ D)
    (h2d : 2 * (p - 1) < K) (hlam : V.card ≤ lam * (K - 2 * (p - 1))) :
    2 ^ (t / (2 * (1 + lam ^ (p - 1)))) ≤ R.S := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hds := degree_size R hD h1 ht hw hdK hKn hb1 hb2
  set N := Nn V.card K with hN
  set N' := Nn V.card (K - (p - 1)) with hN'
  have hNN' : N' ≤ N := Nn_mono (Nat.sub_le _ _)
  have hNpos : 0 < N := Nn_pos V K
  have hratio : N ≤ (1 + lam ^ (p - 1)) * N' := Nn_ratio h2d hlam
  have hle : (p - 1) * N' ≤ p * N := by
    calc (p - 1) * N' ≤ p * N' := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ ≤ p * N := Nat.mul_le_mul_left _ hNN'
  have hθpos : 0 < p * N - (p - 1) * N' := by
    have : (p - 1) * N' ≤ (p - 1) * N := Nat.mul_le_mul_left _ hNN'
    have h3 : p * N = (p - 1) * N + N := by
      rw [← Nat.succ_mul]; congr 1; omega
    omega
  refine exp_bound (M := p * N) (θ := p * N - (p - 1) * N') (a := (p - 1) * N')
    (s := 2 * (1 + lam ^ (p - 1))) (by omega) hθpos ?_ hds
  calc p * N - (p - 1) * N' ≤ p * N := Nat.sub_le _ _
    _ ≤ 2 * ((p - 1) * N) := by
        have : p ≤ 2 * (p - 1) := by omega
        calc p * N ≤ (2 * (p - 1)) * N := Nat.mul_le_mul_right _ this
          _ = 2 * ((p - 1) * N) := by ring
    _ ≤ 2 * ((p - 1) * ((1 + lam ^ (p - 1)) * N')) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hratio)
    _ = 2 * (1 + lam ^ (p - 1)) * ((p - 1) * N') := by ring

end

end Pang
