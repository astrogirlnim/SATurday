import Theory.ProofComplexity.MGG.Fourier
import Theory.ProofComplexity.MGG
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# MGG adjacency Rayleigh form

Real quadratic form of the 8 labeled Gabber–Galil generators. Vertex transport
uses accepted `mggEncode`, `mggDecode`, `mggEncode_decode`, `mggDecode_encode`,
`mggNeighbor`, `mggInvGen`, and `mggNeighbor_invGen`. The cut identity uses
accepted `mggLeavingGens` and `mggLeavingGens_card_sum`.

LOG: R2 manual AFP port, spectral quadratic form
-/

namespace SATurday.ProofComplexity

open Classical Finset BigOperators

variable {m : ℕ} [NeZero m]

/-- One labeled MGG step on torus coordinates. -/
def mggTorusStep (hm : 0 < m) (s : Fin 8) (p : MggTorus m) : MggTorus m :=
  mggDecode hm (mggNeighbor hm (mggEncode hm p) s)

theorem mggTorusStep_inv (hm : 0 < m) (s : Fin 8) (p : MggTorus m) :
    mggTorusStep hm (mggInvGen s) (mggTorusStep hm s p) = p := by
  unfold mggTorusStep
  rw [mggEncode_decode hm]
  rw [mggNeighbor_invGen hm (mggEncode hm p) s]
  exact mggDecode_encode hm p

/-- Accepted roundtrips make `mggEncode` bijective. -/
theorem mggEncode_bijective (hm : 0 < m) : Function.Bijective (mggEncode hm) := by
  refine ⟨fun a b h => ?_, fun v => ⟨mggDecode hm v, mggEncode_decode hm v⟩⟩
  exact (mggDecode_encode hm a).symm.trans
    ((congrArg (mggDecode hm) h).trans (mggDecode_encode hm b))

theorem mggTorusStep_bijective (hm : 0 < m) (s : Fin 8) :
    Function.Bijective (mggTorusStep hm s) := by
  refine ⟨fun p q h => ?_, fun p => ⟨mggTorusStep hm (mggInvGen s) p, ?_⟩⟩
  · have hp := congrArg (mggTorusStep hm (mggInvGen s)) h
    simpa [mggTorusStep_inv hm] using hp
  · have h := mggTorusStep_inv hm (mggInvGen s) p
    simpa [mggInvGen_invGen] using h

theorem sum_mggTorusStep (hm : 0 < m) (s : Fin 8) (f : MggTorus m → ℝ) :
    (∑ p : MggTorus m, f (mggTorusStep hm s p)) = ∑ p : MggTorus m, f p :=
  Function.Bijective.sum_comp (mggTorusStep_bijective hm s) f

noncomputable def mggRealNormSq (f : MggTorus m → ℝ) : ℝ :=
  ∑ p : MggTorus m, (f p) ^ 2

noncomputable def mggMultiRayleigh (hm : 0 < m) (f : MggTorus m → ℝ) : ℝ :=
  ∑ p : MggTorus m, ∑ s : Fin 8, f p * f (mggTorusStep hm s p)

/-- Indicator of a vertex set, via accepted `mggEncode`. -/
noncomputable def mggSetIndicator (hm : 0 < m) (S : Finset (Fin (m * m)))
    (p : MggTorus m) : ℝ :=
  if mggEncode hm p ∈ S then 1 else 0

theorem sum_mggSetIndicator (hm : 0 < m) (S : Finset (Fin (m * m))) :
    (∑ p : MggTorus m, mggSetIndicator hm S p) = S.card := by
  classical
  unfold mggSetIndicator
  have hre :=
    Function.Bijective.sum_comp (mggEncode_bijective hm)
      (fun v => if v ∈ S then (1 : ℝ) else 0)
  simpa [mggDecode_encode hm, sum_ite_mem, sum_const, nsmul_eq_mul] using hre

/-- Staying labels at `v` are `8 - |mggLeavingGens|`. -/
theorem mgg_staySum_eq_eight_sub_leaving (hm : 0 < m) (S : Finset (Fin (m * m)))
    (v : Fin (m * m)) :
    (∑ s : Fin 8, if mggNeighbor hm v s ∈ S then (1 : ℝ) else 0) =
      (8 : ℝ) - (mggLeavingGens hm S v).card := by
  classical
  have hleave : (mggLeavingGens hm S v).card ≤ 8 := by
    have := card_le_card (filter_subset (fun s => mggNeighbor hm v s ∉ S) univ)
    simpa [mggLeavingGens, card_univ, Fintype.card_fin] using this
  have hsum :
      (∑ s : Fin 8, if mggNeighbor hm v s ∈ S then (1 : ℝ) else 0) =
        ((univ.filter fun s => mggNeighbor hm v s ∈ S).card : ℝ) := by
    simp [sum_ite, sum_const, nsmul_eq_mul]
  have hdisj :
      Disjoint (univ.filter fun s => mggNeighbor hm v s ∈ S) (mggLeavingGens hm S v) := by
    refine disjoint_left.mpr ?_
    intro s hs hL
    exact (mem_mggLeavingGens_iff hm S v s).mp hL (mem_filter.mp hs).2
  have huniv :
      (univ.filter fun s => mggNeighbor hm v s ∈ S) ∪ mggLeavingGens hm S v = univ := by
    ext s
    simp [mem_mggLeavingGens_iff]
    exact Classical.em _
  have hcards :
      (univ.filter fun s => mggNeighbor hm v s ∈ S).card +
          (mggLeavingGens hm S v).card = 8 := by
    have := card_union_of_disjoint hdisj
    simpa [huniv, card_univ, Fintype.card_fin] using this.symm
  have hnat :
      (univ.filter fun s => mggNeighbor hm v s ∈ S).card =
        8 - (mggLeavingGens hm S v).card := by
    omega
  rw [hsum, hnat, Nat.cast_sub hleave]
  norm_cast

/-- Labeled staying mass is `8|S| - mggMultiCutCard`. -/
theorem mggMultiRayleigh_setIndicator (hm : 0 < m) (S : Finset (Fin (m * m))) :
    mggMultiRayleigh hm (mggSetIndicator hm S) =
      (8 : ℝ) * S.card - mggMultiCutCard hm S := by
  classical
  unfold mggMultiRayleigh mggSetIndicator
  have hstep (s : Fin 8) (p : MggTorus m) :
      mggEncode hm (mggTorusStep hm s p) = mggNeighbor hm (mggEncode hm p) s := by
    simp [mggTorusStep, mggEncode_decode]
  simp_rw [hstep]
  have hre :=
    Function.Bijective.sum_comp (mggEncode_bijective hm)
      (fun v => ∑ s : Fin 8,
        (if v ∈ S then (1 : ℝ) else 0) *
          (if mggNeighbor hm v s ∈ S then (1 : ℝ) else 0))
  have hsum :
      (∑ v : Fin (m * m), ∑ s : Fin 8,
          (if v ∈ S then (1 : ℝ) else 0) *
            (if mggNeighbor hm v s ∈ S then (1 : ℝ) else 0)) =
        ∑ v ∈ S, ∑ s : Fin 8, if mggNeighbor hm v s ∈ S then (1 : ℝ) else 0 := by
    have hpull (v : Fin (m * m)) :
        (∑ s : Fin 8,
            (if v ∈ S then (1 : ℝ) else 0) *
              (if mggNeighbor hm v s ∈ S then (1 : ℝ) else 0)) =
          if v ∈ S then ∑ s : Fin 8, if mggNeighbor hm v s ∈ S then (1 : ℝ) else 0 else 0 := by
      by_cases hv : v ∈ S <;> simp [hv]
    simp_rw [hpull]
    simp [sum_ite_mem, univ_inter]
  have hstay :
      (∑ v ∈ S, ∑ s : Fin 8, if mggNeighbor hm v s ∈ S then (1 : ℝ) else 0) =
        ∑ v ∈ S, ((8 : ℝ) - (mggLeavingGens hm S v).card) := by
    refine sum_congr rfl fun v _ => ?_
    exact mgg_staySum_eq_eight_sub_leaving hm S v
  have hcut :
      (∑ v ∈ S, ((8 : ℝ) - (mggLeavingGens hm S v).card)) =
        (8 : ℝ) * S.card - mggMultiCutCard hm S := by
    have hsub :
        (∑ v ∈ S, ((8 : ℝ) - ((mggLeavingGens hm S v).card : ℝ))) =
          ∑ v ∈ S, (8 : ℝ) -
            ∑ v ∈ S, ((mggLeavingGens hm S v).card : ℝ) := by
      simp [sum_sub_distrib]
    rw [hsub]
    have hcast :
        (∑ v ∈ S, ((mggLeavingGens hm S v).card : ℝ)) = (mggMultiCutCard hm S : ℝ) := by
      simpa [mggLeavingGens_card_sum hm S] using
        (Nat.cast_sum (s := S) (f := fun v => (mggLeavingGens hm S v).card)).symm
    rw [hcast]
    simp [sum_const, nsmul_eq_mul]
    ring
  calc
    (∑ p, ∑ s,
        (if mggEncode hm p ∈ S then (1 : ℝ) else 0) *
          (if mggNeighbor hm (mggEncode hm p) s ∈ S then (1 : ℝ) else 0))
        = ∑ v, ∑ s,
            (if v ∈ S then (1 : ℝ) else 0) *
              (if mggNeighbor hm v s ∈ S then (1 : ℝ) else 0) := by
          simpa [mggDecode_encode hm] using hre
    _ = ∑ v ∈ S, ∑ s, if mggNeighbor hm v s ∈ S then (1 : ℝ) else 0 := hsum
    _ = ∑ v ∈ S, ((8 : ℝ) - (mggLeavingGens hm S v).card) := hstay
    _ = (8 : ℝ) * S.card - mggMultiCutCard hm S := hcut

/-- Centered indicator, mean `|S| / m²`, on accepted vertex indices. -/
noncomputable def mggCenteredIndicator (hm : 0 < m) (S : Finset (Fin (m * m)))
    (p : MggTorus m) : ℝ :=
  mggSetIndicator hm S p - (S.card : ℝ) / ((m * m : ℕ) : ℝ)

theorem sum_mggCenteredIndicator (hm : 0 < m) (S : Finset (Fin (m * m))) :
    (∑ p : MggTorus m, mggCenteredIndicator hm S p) = 0 := by
  classical
  unfold mggCenteredIndicator
  have hμ : ((m * m : ℕ) : ℝ) ≠ 0 := by
    have : m ≠ 0 := NeZero.out
    positivity
  rw [sum_sub_distrib, sum_mggSetIndicator hm]
  have hN : ((Fintype.card (MggTorus m) : ℕ) : ℝ) = (m * m : ℕ) := by
    simp [Fintype.card_prod, Fintype.card_fin]
  simp [sum_const, nsmul_eq_mul, hN]
  field_simp [hμ]
  ring

end SATurday.ProofComplexity
