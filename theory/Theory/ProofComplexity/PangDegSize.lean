import Theory.ProofComplexity.PangSim
import Theory.ProofComplexity.PangCommon

/-!
# Pang route: the degree-size relation for dag-like `Res(lin F_p)` (core of Theorem 1.1, `r = 1`)
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.PCL MvPolynomial

namespace Pang

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime]

/-- Reindexing a sum over the elements of a finset by `Fin`. -/
lemma sum_equivFin {M : Type*} [AddCommMonoid M] (L : Finset (PP p)) (F : PP p → M) :
    ∑ k : Fin L.card, F ((L.equivFin.symm k : L) : PP p) = ∑ h ∈ L, F h := by
  rw [Equiv.sum_comp L.equivFin.symm (fun x : L => F x)]
  exact Finset.sum_coe_sort L F

theorem degree_size {Φ : CNF} {V : Finset ℕ} (R : Refutation Φ V p) {D K t w : ℕ}
    (hD : 2 ≤ D) (h1 : (1 : PP p) ∉ CD (cnfAx Φ) D) (ht : 1 ≤ t)
    (hw : ∀ C ∈ Φ, C.card ≤ w) (hdK : p - 1 ≤ K) (hKn : K ≤ V.card)
    (hb1 : K + 2 * (t * ((p - 1) * (p - 1))) + 2 * (p - 1) ≤ D)
    (hb2 : K + t * ((p - 1) * (p - 1)) + w ≤ D) :
    (p * Nn V.card K) ^ t ≤
      R.S * (p * Nn V.card K - (p - 1) * Nn V.card (K - (p - 1))) ^ t := by
  by_contra hlt
  push Not at hlt
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  set d := p - 1 with hd
  -- the families indexed by the nodes
  let m : Fin R.S → ℕ := fun ν => (R.line ν).card
  let g : ∀ ν : Fin R.S, Fin (m ν) → PP p := fun ν k => gInd ((R.line ν).equivFin.symm k : PP p)
  have hg : ∀ ν k, (g ν k).totalDegree ≤ d := fun ν k =>
    totalDegree_gInd ((R.wf ν ν.2) _ (R.line ν |>.equivFin.symm k).2).1
  have hgV : ∀ ν k, ∀ v ∈ (g ν k).vars, v ∈ V := fun ν k =>
    vars_gInd ((R.wf ν ν.2) _ (R.line ν |>.equivFin.symm k).2).1
      ((R.wf ν ν.2) _ (R.line ν |>.equivFin.symm k).2).2
  obtain ⟨c, f, hfV, hfn, hdeg, herr⟩ := common_multiplier (Ax := cnfAx Φ) hD h1 hdK hKn
    (by rw [show (p - 1) * d = d * d from rfl]; omega) m g hg hgV hlt
  set Pn : ∀ ν : Fin R.S, PP p := fun ν =>
    ∏ j ∈ Finset.range t, (1 - (∑ k, c ν j k • g ν k) ^ (p - 1)) with hPn
  let P : ℕ → PP p := fun i => if hi : i < R.S then Pn ⟨i, hi⟩ else 1
  have hPi : ∀ i (hi : i < R.S), P i = Pn ⟨i, hi⟩ := fun i hi => by simp [P, hi]
  have hf : (polyOf f).totalDegree ≤ K :=
    (totalDegree_polyOf_le f).trans (deg_le_of_mem_Vk V hfV)
  refine hfn (simulation_final R hD ht hw hb1 hb2 hf P ?_ ?_ ?_)
  · intro i hi
    rw [hPi i hi]; exact hdeg ⟨i, hi⟩
  · intro i hi
    -- coefficients indexed by the equations of the line
    let ν : Fin R.S := ⟨i, hi⟩
    let L := R.line i
    let c' : ℕ → PP p → ZMod p := fun j h => if hh : h ∈ L then c ν j (L.equivFin ⟨h, hh⟩) else 0
    have hsumeq : ∀ j, ∑ k, c ν j k • g ν k = ∑ h ∈ L, c' j h • gInd h := by
      intro j
      rw [← sum_equivFin L (fun h => c' j h • gInd h)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [c', g]
      rw [dif_pos (L.equivFin.symm k).2]
      simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
      rfl
    obtain ⟨U, hU, hid⟩ := prefix_identity L gInd c' (t := t) (d := d) ht
      (fun h hh => totalDegree_gInd ((R.wf i hi) h hh).1)
    refine ⟨U, fun h hh => ?_, ?_⟩
    · have := hU h hh; simpa [hd] using this
    · rw [hPi i hi]
      show 1 - (∏ j ∈ Finset.range t, (1 - (∑ k, c ν j k • g ν k) ^ (p - 1))) =
        ∑ h ∈ R.line i, U h * gInd h
      simp_rw [hsumeq]
      exact hid
  · intro i hi h hh
    rw [hPi i hi]
    have := herr ⟨i, hi⟩ (R.line i |>.equivFin ⟨h, hh⟩)
    simpa [g, Pn] using this

end

end Pang
