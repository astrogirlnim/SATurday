import Theory.ProofComplexity.CuttingPlanesStar
import Theory.ProofComplexity.CliqueFinal

/-!
# R3: cutting planes with polynomially bounded coefficients need super polynomial size
# to refute clique coloring

`cpstar_cliqueColoring_superpoly`: for every `d` and `c`, for `n` large, every CP refutation
of `ccCNF n k (k - 1)` (`k = ⌊n^{1/4}⌋`) whose coefficients and right hand sides are at most
`n^d` in absolute value has more than `n^c` lines (Bonet, Pitassi and Raz 1997; Pudlák 1997).
Cutting planes with polynomial coefficients p-simulates resolution and has polynomial size
proofs of the pigeonhole principle, so this is a lower bound strictly above resolution.

Proof: monotone Boolean interpolation for CP* (`cpstar_interpolation`) and the monotone
Boolean clique lower bound (`mono_bool_clique_lb`).

LOG: R3 CuttingPlanesFinal module (R3 theorem)
-/

namespace SATurday.ProofComplexity

/-- R3 target: CP* refutations of clique coloring need super polynomial size. -/
def CPStarCliqueColoringSuperpoly : Prop :=
  ∀ d c : ℕ, ∃ N, ∀ n ≥ N, ∀ L : List Ineq,
    CPStarRefutes (n ^ d) (ccCNF n (ccK n) (ccK n - 1)) L → n ^ c < L.length

theorem cpstar_cliqueColoring_superpoly : CPStarCliqueColoringSuperpoly := by
  obtain ⟨q, hq⟩ := cpstar_interpolation
  intro d c
  -- the interpolation polynomial is bounded by `D (t+1)^e`
  obtain ⟨D, e, hD⟩ := poly_le_pow' q
  set c' := e * (c + d + 3) + 1 with hc'
  obtain ⟨N1, hN1⟩ := mono_bool_clique_lb c'
  refine ⟨max N1 (D * 6 ^ e + 2), fun n hn L hLr => ?_⟩
  have hn1 : N1 ≤ n := le_of_max_le_left hn
  have hn2 : D * 6 ^ e + 2 ≤ n := le_of_max_le_right hn
  have hnpos : 1 ≤ n := by omega
  by_contra hlt
  rw [not_lt] at hlt
  set k := ccK n
  obtain ⟨C, hBool, hin, hsize, hsep⟩ := hq (cliqueCNF n k) (colorCNF n k (k - 1)) (edgeVars n)
    (qVars n k) (rVars n k (k - 1)) L (n ^ d) clique_lits color_lits (disj_PQ n k)
    (disj_PR n k (k - 1)) (disj_QR n k (k - 1)) hLr
  have hlb := hN1 n hn1 C hBool hin hsep
  -- size bound
  have hkn : k ≤ n := ccK_le n
  have hcard := card_vars_le n k (k - 1)
  have hkn2 : k * n ≤ n * n := Nat.mul_le_mul_right _ hkn
  have hmn2 : n * (k - 1) ≤ n * n := Nat.mul_le_mul_left _ (by omega)
  set E := c + d + 2
  have hpc : n ^ c ≤ n ^ E := Nat.pow_le_pow_right hnpos (by omega)
  have hpd : n ^ d ≤ n ^ E := Nat.pow_le_pow_right hnpos (by omega)
  have hn2' : n * n ≤ n ^ E := by
    rw [← pow_two]; exact Nat.pow_le_pow_right hnpos (by omega)
  have h1 : 1 ≤ n ^ E := Nat.one_le_pow _ _ hnpos
  have ht : L.length + (edgeVars n ∪ qVars n k ∪ rVars n k (k - 1)).card + n ^ d + 1 ≤
      6 * n ^ E := by omega
  have hpow := Nat.pow_le_pow_left ht e
  have hsz : C.length ≤ D * 6 ^ e * n ^ (E * e) := by
    calc C.length ≤ q.eval (L.length + (edgeVars n ∪ qVars n k ∪ rVars n k (k - 1)).card +
          n ^ d) := hsize
      _ ≤ D * (L.length + (edgeVars n ∪ qVars n k ∪ rVars n k (k - 1)).card + n ^ d + 1) ^ e :=
          hD _
      _ ≤ D * (6 * n ^ E) ^ e := Nat.mul_le_mul_left _ hpow
      _ = D * 6 ^ e * n ^ (E * e) := by rw [mul_pow, ← pow_mul]; ring
  have hfin : D * 6 ^ e * n ^ (E * e) ≤ n ^ c' := by
    rw [hc', pow_succ, show e * (c + d + 3) = E * e + e by rw [show E = c + d + 2 from rfl]; ring]
    rw [pow_add]
    have : D * 6 ^ e ≤ n := by omega
    have h6 : 1 ≤ n ^ e := Nat.one_le_pow _ _ hnpos
    calc D * 6 ^ e * n ^ (E * e) ≤ n * n ^ (E * e) := Nat.mul_le_mul_right _ this
      _ = n ^ (E * e) * 1 * n := by ring
      _ ≤ n ^ (E * e) * n ^ e * n := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h6)
  omega

end SATurday.ProofComplexity
