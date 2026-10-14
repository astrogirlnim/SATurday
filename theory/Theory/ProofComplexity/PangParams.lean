import Theory.ProofComplexity.PangSizeExp

/-!
# Pang route, layer I (arithmetic part): parameters for a CNF with a linear degree bound

For a CNF on `nv` variables obtained from a degree bound `D = ((n - 2) / 1312 - q (q + 3)) / (q - 1)`
(`n` the number of vertices, `n ≤ 2 nv`, `nv ≤ 3 n q`), choose `K = D / 4`, `t = D / (8 d²)`,
`d = p - 1`, and get `2^(n / C) ≤` the number of nodes, with `C` explicit.
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.PCL MvPolynomial

namespace Pang

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime]

/-- Explicit constants. -/
def cA (q : ℕ) : ℕ := 2624 * q + 1313
def cLam (q : ℕ) : ℕ := 18 * q * cA q
def cS (p q : ℕ) : ℕ := 2 * (1 + cLam q ^ (p - 1))
def cC (p q : ℕ) : ℕ := cA q * (8 * ((p - 1) * (p - 1))) * cS p q
def cDmin (p q : ℕ) : ℕ := 24 * (p - 1) + 8 * ((p - 1) * (p - 1)) + 2 * q + 1400
def cN0 (p q : ℕ) : ℕ := 2 + 1312 * (q * (q + 3) + (q - 1) * cDmin p q)

theorem exp_of_degree {Φ : CNF} {V : Finset ℕ} (R : Refutation Φ V p) {q n : ℕ} (hq : 2 ≤ q)
    (hn : cN0 p q ≤ n) (h1n : n ≤ 2 * V.card) (h2n : V.card ≤ 3 * n * q)
    (hw : ∀ C ∈ Φ, C.card ≤ q + 3)
    (h1 : (1 : PP p) ∉ CD (cnfAx Φ) (((n - 2) / 1312 - q * (q + 3)) / (q - 1))) :
    2 ^ (n / cC p q) ≤ R.S := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  set d := p - 1 with hd
  have hd1 : 1 ≤ d := by omega
  set X := (n - 2) / 1312 with hX
  set D := (X - q * (q + 3)) / (q - 1) with hDdef
  have hq1 : 0 < q - 1 := by omega
  have hXge : q * (q + 3) + (q - 1) * cDmin p q ≤ X := by
    rw [hX, Nat.le_div_iff_mul_le (by norm_num)]
    unfold cN0 at hn; omega
  have hDmin : cDmin p q ≤ D := by
    rw [hDdef, Nat.le_div_iff_mul_le hq1]
    have e : cDmin p q * (q - 1) = (q - 1) * cDmin p q := mul_comm _ _
    omega
  have hdd : 1 ≤ d * d := Nat.one_le_iff_ne_zero.2 (by positivity)
  -- n ≤ cA * D
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
      have : 0 ≤ (q - 1) * cDmin p q := Nat.zero_le _
      omega
    have e : (q - 1) * (D + 1) = (q - 1) * D + (q - 1) := by ring
    omega
  unfold cDmin at hDmin
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
  -- parameters
  set K := D / 4 with hK
  set t := D / (8 * (d * d)) with ht
  have hK4 : 4 * K ≤ D := Nat.mul_div_le D 4
  have hK4' : D ≤ 4 * K + 3 := by omega
  have ht8 : 8 * (d * d) * t ≤ D := Nat.mul_div_le D _
  have hT : 8 * (t * (d * d)) ≤ D := by nlinarith [ht8]
  have hT' : 8 * (t * ((p - 1) * (p - 1))) ≤ D := hT
  have ht1 : 1 ≤ t := Nat.div_pos (by nlinarith [hDmin]) (by omega)
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
  have hsz := size_exp (Φ := Φ) (V := V) R (D := D) (K := K) (t := t) (w := q + 3) (lam := cLam q)
    (by omega) h1 ht1 hw (by omega) hKV (by omega) (by omega) (by omega) hlamb
  refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) hsz
  have e : cC p q = cA q * (8 * (d * d)) * cS p q := rfl
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  have h1' : n / cA q ≤ D := Nat.div_le_of_le_mul hnD
  have h2' : n / cA q / (8 * (d * d)) ≤ t := Nat.div_le_div_right h1'
  exact Nat.div_le_div_right h2'

end

end Pang
