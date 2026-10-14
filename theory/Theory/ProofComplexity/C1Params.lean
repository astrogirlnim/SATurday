import Theory.ProofComplexity.C1DegSize
import Theory.ProofComplexity.PangParams

/-!
# Candidate C1: parameter arithmetic (natural number form)

For a CNF on `nv` variables obtained from a degree bound
`D = ((n - 2) / 1312 - q (q + 3)) / (q - 1)`, choose `K = D / 4`, `t = D / (8 (p-1) d)`, where
`d = (p-1) ρ`, and get `2^(n / C) ≤ S` with `C = cCR p q d = cA q · 8 (p-1) d · 2 (1 + cLam q ^ d)`.
For `ρ = 1` this is `Pang.cC` up to the replacement `(p-1) → d` in two places.
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.PCL MvPolynomial

namespace C1

noncomputable section
open Classical Pang

variable {p : ℕ} [Fact p.Prime]

def cDminR (p q d : ℕ) : ℕ := 24 * d + 8 * ((p - 1) * d) + 2 * q + 1400
def cN0R (p q d : ℕ) : ℕ := 2 + 1312 * (q * (q + 3) + (q - 1) * cDminR p q d)
def cSR (q d : ℕ) : ℕ := 2 * (1 + cLam q ^ d)
def cCR (p q d : ℕ) : ℕ := cA q * (8 * ((p - 1) * d)) * cSR q d

theorem exp_of_degree_R {Φ : CNF} {V : Finset ℕ} {ρ : ℕ} (R : RRefutation Φ V ρ p) {q n d : ℕ}
    (hd : d = (p - 1) * ρ) (hρ : 1 ≤ ρ) (hq : 2 ≤ q)
    (hn : cN0R p q d ≤ n) (h1n : n ≤ 2 * V.card) (h2n : V.card ≤ 3 * n * q)
    (hw : ∀ C ∈ Φ, C.card ≤ q + 3)
    (h1 : (1 : PP p) ∉ CD (cnfAx Φ) (((n - 2) / 1312 - q * (q + 3)) / (q - 1))) :
    2 ^ (n / cCR p q d) ≤ R.S := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hd1 : 1 ≤ d := by rw [hd]; exact Nat.mul_pos (by omega) hρ
  obtain ⟨E, hE⟩ : ∃ E, E = (p - 1) * d := ⟨_, rfl⟩
  have hEd : d ≤ E := by rw [hE]; exact Nat.le_mul_of_pos_left d (by omega)
  have hE1 : 1 ≤ E := by omega
  set X := (n - 2) / 1312 with hX
  set D := (X - q * (q + 3)) / (q - 1) with hDdef
  have hq1 : 0 < q - 1 := by omega
  have hXge : q * (q + 3) + (q - 1) * cDminR p q d ≤ X := by
    rw [hX, Nat.le_div_iff_mul_le (by norm_num)]
    unfold cN0R at hn; omega
  have hDmin : cDminR p q d ≤ D := by
    rw [hDdef, Nat.le_div_iff_mul_le hq1]
    have e : cDminR p q d * (q - 1) = (q - 1) * cDminR p q d := mul_comm _ _
    omega
  have hnX : n ≤ 1312 * X + 1313 := by
    have h1 := Nat.div_add_mod (n - 2) 1312
    have h2 := Nat.mod_lt (n - 2) (show 0 < 1312 by norm_num)
    rw [← hX] at h1
    omega
  have hXD : X < (q - 1) * (D + 1) + q * (q + 3) := by
    have h1 := Nat.div_add_mod (X - q * (q + 3)) (q - 1)
    have h2 := Nat.mod_lt (X - q * (q + 3)) hq1
    rw [← hDdef] at h1
    have hXq : q * (q + 3) ≤ X := by
      have : 0 ≤ (q - 1) * cDminR p q d := Nat.zero_le _
      omega
    have e : (q - 1) * (D + 1) = (q - 1) * D + (q - 1) := by ring
    omega
  unfold cDminR at hDmin
  rw [← hE] at hDmin
  have hnD : n ≤ cA q * D := by
    unfold cA
    have e1 : (q - 1) * (D + 1) ≤ q * D + q := by
      have : (q - 1) * (D + 1) = (q - 1) * D + (q - 1) := by ring
      have h6 : (q - 1) * D ≤ q * D := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      omega
    have e2 : q * (q + 3) ≤ q * D := Nat.mul_le_mul_left _ (by omega)
    have e3 : q ≤ D := by omega
    have e4 : X ≤ (2 * q + 1) * D := by nlinarith [e1, e2, e3, hXD]
    have e5 : 1312 * X ≤ 1312 * ((2 * q + 1) * D) := Nat.mul_le_mul_left _ e4
    nlinarith [e5, hnX, hDmin]
  set K := D / 4 with hK
  set t := D / (8 * E) with ht
  have hK4 : 4 * K ≤ D := Nat.mul_div_le D 4
  have hK4' : D ≤ 4 * K + 3 := by omega
  have ht8 : 8 * E * t ≤ D := Nat.mul_div_le D _
  have hT : 8 * (t * E) ≤ D := by nlinarith [ht8]
  have ht1 : 1 ≤ t := Nat.div_pos (by omega) (by omega)
  have hDX : D ≤ X := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hXn : 1312 * X ≤ n := by
    rw [hX]; exact (Nat.mul_div_le (n - 2) 1312).trans (Nat.sub_le _ _)
  have hKV : K ≤ V.card := by omega
  have hD6 : D ≤ 6 * (K - 2 * d) := by omega
  have hlamb : V.card ≤ cLam q * (K - 2 * d) := by
    calc V.card ≤ 3 * n * q := h2n
      _ ≤ 3 * (cA q * D) * q := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hnD)
      _ ≤ 3 * (cA q * (6 * (K - 2 * d))) * q :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hD6))
      _ = cLam q * (K - 2 * d) := by unfold cLam; ring
  have hsz := c1_size_exp (Φ := Φ) (V := V) R (D := D) (K := K) (t := t) (w := q + 3)
    (lam := cLam q) (d := d) hd hρ
    (by omega) h1 ht1 hw (by omega) hKV (by rw [← hE]; omega) (by rw [← hE]; omega) (by omega)
    hlamb
  refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) hsz
  have e : cCR p q d = cA q * (8 * E) * cSR q d := by unfold cCR; rw [hE]
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  have h1' : n / cA q ≤ D := Nat.div_le_of_le_mul hnD
  have h2' : n / cA q / (8 * E) ≤ t := Nat.div_le_div_right h1'
  exact Nat.div_le_div_right h2'

end

end C1
