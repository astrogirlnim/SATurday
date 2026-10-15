import Theory.ProofComplexity.C1Sim
import Theory.ProofComplexity.PangCommon
import Theory.ProofComplexity.PangPrefix
import Theory.ProofComplexity.PangSizeExp

/-!
# Candidate C1: the degree-size relation and exponential size for `R_ρ^p`

With `d = (p-1) ρ` (the degree of the indicator `g_T` of a term of rank `≤ ρ`), the argument of
`Pang.degree_size` / `Pang.size_exp` goes through unchanged for `R_ρ^p` (same abstract layers
`common_multiplier`, `prefix_identity`, `Nn_ratio`, `exp_bound`; the simulation is `C1.c1_simulation`).
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.PCL MvPolynomial

namespace C1

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime]

lemma sum_equivFin' {ι : Type*} {M : Type*} [AddCommMonoid M] (L : Finset ι) (F : ι → M) :
    ∑ k : Fin L.card, F ((L.equivFin.symm k : L) : ι) = ∑ h ∈ L, F h := by
  rw [Equiv.sum_comp L.equivFin.symm (fun x : L => F x)]
  exact Finset.sum_coe_sort L F

open Pang in
theorem c1_degree_size {Φ : CNF} {V : Finset ℕ} {ρ : ℕ} (R : RRefutation Φ V ρ p) {D K t w d : ℕ}
    (hd : d = (p - 1) * ρ) (hρ : 1 ≤ ρ)
    (hD : 2 ≤ D) (h1 : (1 : PP p) ∉ CD (cnfAx Φ) D) (ht : 1 ≤ t)
    (hw : ∀ C ∈ Φ, C.card ≤ w) (hdK : d ≤ K) (hKn : K ≤ V.card)
    (hb1 : K + 2 * (t * ((p - 1) * d)) + 2 * d ≤ D)
    (hb2 : K + t * ((p - 1) * d) + w ≤ D) :
    (p * Nn V.card K) ^ t ≤
      R.S * (p * Nn V.card K - (p - 1) * Nn V.card (K - d)) ^ t := by
  by_contra hlt
  push Not at hlt
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdΔ : d ≤ t * ((p - 1) * d) := by
    have : d ≤ (p - 1) * d := Nat.le_mul_of_pos_left d (by omega)
    nlinarith
  let m : Fin R.S → ℕ := fun ν => (R.line ν).card
  let g : ∀ ν : Fin R.S, Fin (m ν) → PP p := fun ν k => gT ((R.line ν).equivFin.symm k : Term p)
  have hgd : ∀ ν k, (g ν k).totalDegree ≤ d := fun ν k => by
    rw [hd]; exact totalDegree_gT (R.bdd ν ν.2 _ (R.line ν |>.equivFin.symm k).2)
  have hgV : ∀ ν k, ∀ v ∈ (g ν k).vars, v ∈ V := fun ν k =>
    vars_gT (R.bdd ν ν.2 _ (R.line ν |>.equivFin.symm k).2)
      (R.supp ν ν.2 _ (R.line ν |>.equivFin.symm k).2)
  obtain ⟨c, f, hfV, hfn, hdeg, herr⟩ := common_multiplier (Ax := cnfAx Φ) hD h1 hdK hKn
    (by omega) m g hgd hgV hlt
  set Pn : ∀ ν : Fin R.S, PP p := fun ν =>
    ∏ j ∈ Finset.range t, (1 - (∑ k, c ν j k • g ν k) ^ (p - 1)) with hPn
  let P : ℕ → PP p := fun i => if hi : i < R.S then Pn ⟨i, hi⟩ else 1
  have hPi : ∀ i (hi : i < R.S), P i = Pn ⟨i, hi⟩ := fun i hi => by simp [P, hi]
  have hf : (polyOf f).totalDegree ≤ K :=
    (totalDegree_polyOf_le f).trans (deg_le_of_mem_Vk V hfV)
  refine hfn (c1_simulation_final R hD hd hρ hdΔ hw hb1 hb2 hf P ?_ ?_ ?_)
  · intro i hi
    rw [hPi i hi]; exact hdeg ⟨i, hi⟩
  · intro i hi
    let ν : Fin R.S := ⟨i, hi⟩
    let L := R.line i
    let c' : ℕ → Term p → ZMod p := fun j h => if hh : h ∈ L then c ν j (L.equivFin ⟨h, hh⟩) else 0
    have hsumeq : ∀ j, ∑ k, c ν j k • g ν k = ∑ h ∈ L, c' j h • gT h := by
      intro j
      rw [← sum_equivFin' L (fun h => c' j h • gT h)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [c', g]
      rw [dif_pos (L.equivFin.symm k).2]
      simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
      rfl
    obtain ⟨U, hU, hid⟩ := prefix_identity L gT c' (t := t) (d := d) ht
      (fun h hh => by rw [hd]; exact totalDegree_gT (R.bdd i hi h hh))
    refine ⟨U, hU, ?_⟩
    rw [hPi i hi]
    show 1 - (∏ j ∈ Finset.range t, (1 - (∑ k, c ν j k • g ν k) ^ (p - 1))) =
      ∑ h ∈ R.line i, U h * gT h
    simp_rw [hsumeq]
    exact hid
  · intro i hi h hh
    rw [hPi i hi]
    have := herr ⟨i, hi⟩ (R.line i |>.equivFin ⟨h, hh⟩)
    simpa [g, Pn] using this

open Pang in
/-- **Exponential form** of the degree-size relation for `R_ρ^p` (`d = (p-1) ρ`). -/
theorem c1_size_exp {Φ : CNF} {V : Finset ℕ} {ρ : ℕ} (R : RRefutation Φ V ρ p) {D K t w lam d : ℕ}
    (hd : d = (p - 1) * ρ) (hρ : 1 ≤ ρ)
    (hD : 2 ≤ D) (h1 : (1 : PP p) ∉ CD (cnfAx Φ) D) (ht : 1 ≤ t)
    (hw : ∀ C ∈ Φ, C.card ≤ w) (hdK : d ≤ K) (hKn : K ≤ V.card)
    (hb1 : K + 2 * (t * ((p - 1) * d)) + 2 * d ≤ D)
    (hb2 : K + t * ((p - 1) * d) + w ≤ D)
    (h2d : 2 * d < K) (hlam : V.card ≤ lam * (K - 2 * d)) :
    2 ^ (t / (2 * (1 + lam ^ d))) ≤ R.S := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hds := c1_degree_size R hd hρ hD h1 ht hw hdK hKn hb1 hb2
  set N := Nn V.card K with hN
  set N' := Nn V.card (K - d) with hN'
  have hNN' : N' ≤ N := Nn_mono (Nat.sub_le _ _)
  have hNpos : 0 < N := Nn_pos V K
  have hratio : N ≤ (1 + lam ^ d) * N' := Nn_ratio h2d hlam
  have hθpos : 0 < p * N - (p - 1) * N' := by
    have : (p - 1) * N' ≤ (p - 1) * N := Nat.mul_le_mul_left _ hNN'
    have h3 : p * N = (p - 1) * N + N := by
      rw [← Nat.succ_mul]; congr 1; omega
    omega
  have hle : (p - 1) * N' ≤ p * N := by
    calc (p - 1) * N' ≤ p * N' := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ ≤ p * N := Nat.mul_le_mul_left _ hNN'
  refine exp_bound (M := p * N) (θ := p * N - (p - 1) * N') (a := (p - 1) * N')
    (s := 2 * (1 + lam ^ d)) (by omega) hθpos ?_ hds
  calc p * N - (p - 1) * N' ≤ p * N := Nat.sub_le _ _
    _ ≤ 2 * ((p - 1) * N) := by
        have : p ≤ 2 * (p - 1) := by omega
        calc p * N ≤ (2 * (p - 1)) * N := Nat.mul_le_mul_right _ this
          _ = 2 * ((p - 1) * N) := by ring
    _ ≤ 2 * ((p - 1) * ((1 + lam ^ d) * N')) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hratio)
    _ = 2 * (1 + lam ^ d) * ((p - 1) * N') := by ring

end

end C1
