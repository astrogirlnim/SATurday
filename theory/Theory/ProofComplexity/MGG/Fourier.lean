import Theory.ProofComplexity.MGG
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Complex.Circle
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# MGG torus Fourier surface (AFP Expander_Graphs_MGG port spine)

Discrete Fourier analysis on `(Z/mZ)²`. Torus points are the codomain of the
accepted `mggDecode`. Vertex indices move through accepted `mggEncode`.
Guide: AFP `ω_F`, `FT`.

LOG: R2 manual AFP port Phase B Fourier scaffold
-/

namespace SATurday.ProofComplexity

open Classical Complex Finset BigOperators
open scoped ComplexConjugate

variable {m : ℕ} [NeZero m]

/-- Torus point. Same type as `mggDecode _ _`. -/
abbrev MggTorus (m : ℕ) := Fin m × Fin m

/-- Lift a coordinate to `ZMod m` for character evaluation. -/
abbrev mggZMod (i : Fin m) : ZMod m := (i : ZMod m)

/-- AFP `ω_F`. -/
noncomputable def mggOmega (x : ZMod m) : ℂ :=
  ZMod.stdAddChar x

theorem mggOmega_zero : mggOmega (0 : ZMod m) = 1 := by
  simp [mggOmega, AddChar.map_zero_eq_one]

theorem mggOmega_add (x y : ZMod m) :
    mggOmega (x + y) = mggOmega x * mggOmega y := by
  simp [mggOmega, AddChar.map_add_eq_mul]

theorem mggOmega_neg (x : ZMod m) :
    mggOmega (-x) = conj (mggOmega x) := by
  simp only [mggOmega, ZMod.stdAddChar_apply]
  rw [← Circle.coe_inv_eq_conj,
    AddChar.map_neg_eq_inv (ZMod.toCircle (N := m)) x]

theorem mggOmega_conj (x : ZMod m) : conj (mggOmega x) = mggOmega (-x) :=
  (mggOmega_neg x).symm

/-- Discrete Fourier transform on `(Z/mZ)²`. -/
noncomputable def mggFT (f : MggTorus m → ℂ) (freq : MggTorus m) : ℂ :=
  ∑ pt : MggTorus m,
    mggOmega (-(mggZMod freq.1 * mggZMod pt.1 + mggZMod freq.2 * mggZMod pt.2)) * f pt

theorem mggFT_zero (f : MggTorus m → ℂ) :
    mggFT f (0 : MggTorus m) = ∑ pt : MggTorus m, f pt := by
  unfold mggFT
  refine sum_congr rfl fun pt _ => ?_
  have h0 : mggZMod (0 : Fin m) = 0 := by simp [mggZMod]
  simp [h0, mggOmega_zero]

theorem mggFT_add (f g : MggTorus m → ℂ) (freq : MggTorus m) :
    mggFT (fun v => f v + g v) freq = mggFT f freq + mggFT g freq := by
  simp [mggFT, mul_add, sum_add_distrib]

theorem mggFT_const_mul (c : ℂ) (f : MggTorus m → ℂ) (freq : MggTorus m) :
    mggFT (fun v => c * f v) freq = c * mggFT f freq := by
  unfold mggFT
  calc
    ∑ pt, mggOmega (-(mggZMod freq.1 * mggZMod pt.1 + mggZMod freq.2 * mggZMod pt.2)) *
        (c * f pt)
        = ∑ pt, c * (mggOmega (-(mggZMod freq.1 * mggZMod pt.1 + mggZMod freq.2 * mggZMod pt.2)) *
            f pt) := by
          refine sum_congr rfl fun pt _ => by ring
    _ = c * ∑ pt, mggOmega (-(mggZMod freq.1 * mggZMod pt.1 + mggZMod freq.2 * mggZMod pt.2)) *
          f pt := by
          rw [mul_sum]

/-- One-dimensional character sum. -/
theorem mggOmega_sum (a : ZMod m) :
    (∑ x : ZMod m, mggOmega (a * x)) = if a = 0 then (m : ℂ) else 0 := by
  classical
  have h :=
    AddChar.sum_mulShift (R := ZMod m) (R' := ℂ) a (ZMod.isPrimitive_stdAddChar m)
  have hcard : (Fintype.card (ZMod m) : ℂ) = m := by simp [ZMod.card]
  calc
    (∑ x : ZMod m, mggOmega (a * x))
        = ∑ x : ZMod m, ZMod.stdAddChar (x * a) := by
          simp [mggOmega, mul_comm]
    _ = ((if a = 0 then Fintype.card (ZMod m) else 0 : ℕ) : ℂ) := h
    _ = if a = 0 then (Fintype.card (ZMod m) : ℂ) else 0 := by
          split_ifs <;> simp
    _ = if a = 0 then (m : ℂ) else 0 := by rw [hcard]

theorem mggZMod_eq_zero_iff (i : Fin m) : mggZMod i = 0 ↔ i = 0 := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg ZMod.val h
    have hi : ZMod.val (i : ZMod m) = i.val := by
      simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]
    simp only [mggZMod] at hv
    exact hi.symm.trans (hv.trans (by simp))
  · intro h
    simp [mggZMod, h]

/-- `mggZMod : Fin m → ZMod m` hits every residue exactly once. -/
theorem mggZMod_bijective : Function.Bijective (mggZMod (m := m)) := by
  constructor
  · intro a b h
    apply Fin.ext
    have ha : ZMod.val (mggZMod a) = a.val := by
      simp [mggZMod, ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]
    have hb : ZMod.val (mggZMod b) = b.val := by
      simp [mggZMod, ZMod.val_natCast, Nat.mod_eq_of_lt b.isLt]
    exact ha.symm.trans ((congrArg ZMod.val h).trans hb)
  · intro t
    refine ⟨⟨t.val, t.val_lt⟩, ?_⟩
    simpa [mggZMod] using (ZMod.natCast_zmod_val t)

/-- Sums over the torus coordinate and over `ZMod m` agree. -/
theorem mggSum_fin_eq_zmod (g : ZMod m → ℂ) :
    (∑ x : Fin m, g (mggZMod x)) = ∑ t : ZMod m, g t :=
  Function.Bijective.sum_comp mggZMod_bijective g

/-- Product-torus character sum over Fin coordinates. -/
theorem mgg_character_sum (freq : MggTorus m) :
    (∑ pt : MggTorus m,
        mggOmega (mggZMod freq.1 * mggZMod pt.1 + mggZMod freq.2 * mggZMod pt.2)) =
      if freq = 0 then (m * m : ℂ) else 0 := by
  have hfactor :
      (∑ pt : MggTorus m,
          mggOmega (mggZMod freq.1 * mggZMod pt.1 + mggZMod freq.2 * mggZMod pt.2)) =
        (∑ x : Fin m, mggOmega (mggZMod freq.1 * mggZMod x)) *
          (∑ y : Fin m, mggOmega (mggZMod freq.2 * mggZMod y)) := by
    calc
      (∑ pt : MggTorus m,
          mggOmega (mggZMod freq.1 * mggZMod pt.1 + mggZMod freq.2 * mggZMod pt.2))
          = ∑ x : Fin m, ∑ y : Fin m,
              mggOmega (mggZMod freq.1 * mggZMod x + mggZMod freq.2 * mggZMod y) :=
            Fintype.sum_prod_type _
      _ = ∑ x : Fin m, ∑ y : Fin m,
              mggOmega (mggZMod freq.1 * mggZMod x) *
                mggOmega (mggZMod freq.2 * mggZMod y) := by
            simp only [mggOmega_add]
      _ = (∑ x : Fin m, mggOmega (mggZMod freq.1 * mggZMod x)) *
            (∑ y : Fin m, mggOmega (mggZMod freq.2 * mggZMod y)) := by
            simp [sum_mul_sum]
  have hsum (a : Fin m) :
      (∑ x : Fin m, mggOmega (mggZMod a * mggZMod x)) =
        if mggZMod a = 0 then (m : ℂ) else 0 := by
    rw [mggSum_fin_eq_zmod (fun t => mggOmega (mggZMod a * t)), mggOmega_sum]
  rw [hfactor, hsum freq.1, hsum freq.2]
  by_cases hu : freq.1 = 0
  · by_cases hv : freq.2 = 0
    · have hfreq : freq = 0 := Prod.ext hu hv
      simp [hfreq, mggZMod]
    · have hfreq : freq ≠ 0 := fun h => hv (Prod.ext_iff.mp h).2
      simp [hu, mggZMod_eq_zero_iff, hv, if_neg hfreq]
  · have hfreq : freq ≠ 0 := fun h => hu (Prod.ext_iff.mp h).1
    simp [mggZMod_eq_zero_iff, hu, if_neg hfreq]

theorem mggFT_zero_eq_zero_of_sum_zero (f : MggTorus m → ℂ)
    (h : ∑ pt : MggTorus m, f pt = 0) : mggFT f 0 = 0 := by
  simpa [mggFT_zero] using h

/-- AFP `MGG_bound = 5 √2 / 8`. -/
noncomputable def mggSpectralBound : ℝ :=
  5 * Real.sqrt 2 / 8

theorem mggSpectralBound_pos : 0 < mggSpectralBound := by
  unfold mggSpectralBound
  positivity

theorem mggSpectralBound_lt_one : mggSpectralBound < 1 := by
  unfold mggSpectralBound
  have hsq : Real.sqrt 2 < 8 / 5 := by
    have : (2 : ℝ) < (8 / 5) ^ 2 := by norm_num
    exact (Real.sqrt_lt' (by positivity)).2 this
  nlinarith

theorem mggSpectralBound_mul_eight :
    (8 : ℝ) * mggSpectralBound = 5 * Real.sqrt 2 := by
  simp [mggSpectralBound]
  ring

end SATurday.ProofComplexity
