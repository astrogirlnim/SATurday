import Theory.ProofComplexity.CliqueBound
import Theory.ProofComplexity.CliqueArith

/-!
# Monotone Boolean circuits separating cliques from colorings are large (R3)

`mono_bool_clique_lb : MonoBoolCliqueLB`: any monotone Boolean circuit on the edge
variables that is `1` on assignments satisfying `cliqueCNF n k` and `0` on assignments
satisfying `colorCNF n k (k - 1)`, `k = ⌊n^{1/4}⌋`, has more than `n ^ c` gates for `n`
large (Razborov; Alon and Boppana; Boppana and Sipser).

LOG: R3 CliqueFinal module (monotone Boolean clique lower bound)
-/

namespace SATurday.ProofComplexity

open Finset

/-- Monotone Boolean circuits separating cliques from colorings need super polynomial size. -/
def MonoBoolCliqueLB : Prop :=
  ∀ c : ℕ, ∃ N, ∀ n ≥ N, ∀ C : List MGate, MCBool C → MCInputsIn (edgeVars n) C →
    (∀ a, (cnfSat a (cliqueCNF n (ccK n)) → mcEval a C = 1) ∧
      (cnfSat a (colorCNF n (ccK n) (ccK n - 1)) → mcEval a C = 0)) →
    n ^ c < C.length

theorem ccK_bounds {n K0 : ℕ} (h : K0 ^ 4 ≤ n) :
    K0 ≤ ccK n ∧ ccK n ^ 4 ≤ n ∧ n < (ccK n + 1) ^ 4 := by
  unfold ccK
  set r := Nat.sqrt n
  set k := Nat.sqrt r
  have hr1 : r * r ≤ n := Nat.sqrt_le n
  have hr2 : n < (r + 1) * (r + 1) := Nat.lt_succ_sqrt n
  have hk1 : k * k ≤ r := Nat.sqrt_le r
  have hk2 : r < (k + 1) * (k + 1) := Nat.lt_succ_sqrt r
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.le_sqrt, Nat.le_sqrt]
    calc K0 * K0 * (K0 * K0) = K0 ^ 4 := by ring
      _ ≤ n := h
  · calc k ^ 4 = (k * k) * (k * k) := by ring
      _ ≤ r * r := Nat.mul_le_mul hk1 hk1
      _ ≤ n := hr1
  · have : r + 1 ≤ (k + 1) * (k + 1) := hk2
    calc n < (r + 1) * (r + 1) := hr2
      _ ≤ ((k + 1) * (k + 1)) * ((k + 1) * (k + 1)) := Nat.mul_le_mul this this
      _ = (k + 1) ^ 4 := by ring

theorem mono_bool_clique_lb : MonoBoolCliqueLB := by
  intro c
  obtain ⟨KA, hKA⟩ := arith_A c
  obtain ⟨KB, hKB⟩ := arith_B c
  set K0 := KA + KB + 20
  refine ⟨K0 ^ 4, fun n hn C hBool hIn hsep => ?_⟩
  obtain ⟨hK0, hk4, hk4'⟩ := ccK_bounds hn
  set k := ccK n with hkdef
  have hk20 : 20 ≤ k := by omega
  have hkn : k ≤ n := by
    have : k ≤ k ^ 4 := Nat.le_self_pow (by norm_num) k
    omega
  have h16 : n < 16 * k ^ 4 := by
    have : (k + 1) ^ 4 ≤ (2 * k) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have e : (2 * k) ^ 4 = 16 * k ^ 4 := by ring
    omega
  set ℓ := cℓ k
  set p := cp k
  have hℓ3 : 3 ≤ ℓ := le_cℓ (by omega)
  have hℓsq : 2 * (ℓ * ℓ) ≤ k - 1 := cℓ_sq k
  have hℓk : ℓ + 1 ≤ k := by
    have : ℓ ≤ ℓ * ℓ := Nat.le_mul_self ℓ
    omega
  have hp : 2 ≤ p := by
    show 2 ≤ 8 * cℓ k * cL k
    have : 1 ≤ cL k := by unfold cL; omega
    have : 1 ≤ cℓ k := by omega
    nlinarith
  -- the circuit as a gate function
  set s := C.length
  let gt : ℕ → MGate := fun m => C.getD m (.cst 0)
  have hCeq : (List.range s).map gt = C := by
    apply List.ext_getElem
    · simp [s]
    · intro i h1 h2
      simp [gt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  have hB : ∀ m, BoolGate (gt m) := by
    intro m
    by_cases hm : m < s
    · have : gt m = C[m] := by simp [gt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
      rw [this]; exact hBool _ (List.getElem_mem hm)
    · have : gt m = .cst 0 := by
        simp only [gt, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]; rfl
      rw [this]; exact Or.inr (Or.inl rfl)
  have hI : ∀ m v, gt m = .inp v → v ∈ edgeVars n := by
    intro m v hv
    by_cases hm : m < s
    · have : gt m = C[m] := by simp [gt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
      rw [this] at hv
      exact hIn v (hv ▸ List.getElem_mem hm)
    · have : gt m = .cst 0 := by
        simp only [gt, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]; rfl
      rw [this] at hv; cases hv
  -- a positive test exists, so the circuit is nonempty
  obtain ⟨K1, hK1⟩ : ∃ K : Finset (Fin n), K.card = k :=
    Finset.exists_subset_card_eq (s := Finset.univ) (by simpa using hkn) |>.imp fun _ h => h.2
  have hs : 1 ≤ s := by
    by_contra h0
    have hC0 : C = [] := List.eq_nil_of_length_eq_zero (by omega)
    have := (hsep (posAssign n k K1 hK1)).1 (posAssign_sat K1 hK1)
    rw [hC0] at this
    simp [mcEval, mcVals] at this
  have hEval : ∀ a, mcEval a C = gateValue a gt (s - 1) := by
    intro a
    rw [← hCeq, show s = (s - 1) + 1 by omega, mcEval_range, Nat.add_sub_cancel]
  have hpos : ∀ K : Finset (Fin n), K.card = k → ∃ a : Assignment,
      (∀ u w : Fin n, u ≠ w → (a (eVar n u w) = true ↔ u ∈ K ∧ w ∈ K)) ∧
        gateValue a gt (s - 1) = 1 := by
    intro K hK
    refine ⟨posAssign n k K hK, fun u w h => posAssign_edge K hK h, ?_⟩
    rw [← hEval]; exact (hsep _).1 (posAssign_sat K hK)
  have hneg : ∀ c' : Fin n → Fin (k - 1), ∃ a : Assignment,
      (∀ u w : Fin n, u ≠ w → (a (eVar n u w) = true ↔ c' u ≠ c' w)) ∧
        gateValue a gt (s - 1) = 0 := by
    intro c'
    refine ⟨negAssign n k c', fun u w h => negAssign_edge c' h, ?_⟩
    rw [← hEval]; exact (hsep _).2 (negAssign_sat c')
  have hKc : 1 ≤ k - 1 := by omega
  have hM := sfBound_le p ℓ
  rcases approx_lb (n := n) (ℓ := ℓ) (p := p) (gt := gt) (k := k) (Kc := k - 1) (s := s)
      hp (by omega) hℓk hkn hKc hs hB hI hpos hneg with hA | hBc
  · -- case A
    have hcm := choose_mul_pow n k (ℓ + 1) hℓk hkn
    have hCpos : 0 < (n - (ℓ + 1)).choose (k - (ℓ + 1)) := Nat.choose_pos (by omega)
    have : (n - (ℓ + 1)) ^ (ℓ + 1) * (n - (ℓ + 1)).choose (k - (ℓ + 1)) ≤
        (s * (sfBound p ℓ * sfBound p ℓ) * k ^ (ℓ + 1)) *
          (n - (ℓ + 1)).choose (k - (ℓ + 1)) := by
      calc _ ≤ n.choose k * k ^ (ℓ + 1) := hcm
        _ ≤ s * (sfBound p ℓ * sfBound p ℓ * (n - (ℓ + 1)).choose (k - (ℓ + 1))) *
              k ^ (ℓ + 1) := Nat.mul_le_mul_right _ hA
        _ = _ := by ring
    have hA' := Nat.le_of_mul_le_mul_right this hCpos
    exact hKA k (by omega) n hk4 h16 s (sfBound p ℓ) hM hA'
  · -- case B
    set Kc := k - 1
    set M := sfBound p ℓ
    set E := sunE n Kc ℓ p
    set X := s * (M * M * E)
    have hKcn : 0 < Kc ^ n := Nat.pow_pos (by omega)
    have h1 : 2 * (ℓ * ℓ) * Kc ^ n ≤ Kc * Kc ^ n := Nat.mul_le_mul_right _ hℓsq
    have h2 : Kc ^ n * Kc ≤ 2 * X * Kc := by
      have e1 : 2 * (ℓ * ℓ) * Kc ^ n = 2 * (ℓ * ℓ * Kc ^ n) := by ring
      have e2 : Kc * Kc ^ n = Kc ^ n * Kc := by ring
      have e3 : 2 * X * Kc = 2 * (X * Kc) := by ring
      omega
    have h3 : Kc ^ n ≤ 2 * X := Nat.le_of_mul_le_mul_right h2 (by omega)
    have hE : E * Kc ^ p ≤ (ℓ * ℓ) ^ p * Kc ^ n := Nat.div_mul_le_self _ _
    have h4 : Kc ^ n * Kc ^ p ≤ (2 * s * (M * M) * (ℓ * ℓ) ^ p) * Kc ^ n := by
      calc Kc ^ n * Kc ^ p ≤ 2 * X * Kc ^ p := Nat.mul_le_mul_right _ h3
        _ = 2 * s * (M * M) * (E * Kc ^ p) := by ring
        _ ≤ 2 * s * (M * M) * ((ℓ * ℓ) ^ p * Kc ^ n) := Nat.mul_le_mul_left _ hE
        _ = _ := by ring
    rw [mul_comm (Kc ^ n)] at h4
    have h5 : Kc ^ p ≤ 2 * s * (M * M) * (ℓ * ℓ) ^ p := Nat.le_of_mul_le_mul_right h4 hKcn
    have h6 : 2 ^ p * (ℓ * ℓ) ^ p ≤ Kc ^ p := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) p
    have hlpos : 0 < (ℓ * ℓ) ^ p := Nat.pow_pos (by positivity)
    have h7 : 2 ^ p ≤ 2 * s * (M * M) :=
      Nat.le_of_mul_le_mul_right (h6.trans h5) hlpos
    exact hKB k (by omega) n h16 s M hM h7

end SATurday.ProofComplexity
