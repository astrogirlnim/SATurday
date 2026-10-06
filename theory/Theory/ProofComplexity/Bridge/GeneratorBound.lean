import Theory.ProofComplexity.Bridge.GeneratorOk

/-!
# The generator runs in polynomial time (Ladder Rung R5)

The time loop keeps every register below `S + (W + 2) * Fr W`, so the static bound `top`
applies to its body at every iteration. Together with `top` on the straight line parts this gives
a polynomial bound on `FP.cost` of the whole generator.

LOG: R5 Bridge GeneratorBound module (cost of genProg)
-/

open SATurday.Bridge.SP
open scoped Polynomial

namespace SATurday.Bridge
namespace CL

/-! ## Costs as polynomials -/

noncomputable def _root_.SATurday.Bridge.SP.FP.cmP : FP → Polynomial ℕ
  | .skip => 1
  | .seq p q => p.cmP + q.cmP
  | .emit bs => Polynomial.C (bs.length + 1)
  | .emitVar _ o => Polynomial.C 5 * Polynomial.X + Polynomial.C (o + 8)
  | .addConst _ k => Polynomial.C (k + 1)
  | .subConst _ k => Polynomial.C (2 * k + 1)
  | .addReg _ _ => Polynomial.C 5 * Polynomial.X + Polynomial.C 2
  | .subReg _ _ => Polynomial.C 6 * Polynomial.X + Polynomial.C 2
  | .clr _ => Polynomial.C 2 * Polynomial.X + Polynomial.C 1
  | .forLoop _ b => Polynomial.C 6 * Polynomial.X + Polynomial.C 3 + Polynomial.X * b.cmP
  | .forBits pf pt => Polynomial.X * (pf.cmP + pt.cmP + 1) + 1
  | .countBits _ => Polynomial.C 9 * Polynomial.X + Polynomial.C 4

theorem costM_eq (M : ℕ) : ∀ p : FP, p.costM M = (p.cmP).eval M := by
  intro p
  induction p with
  | skip => simp [FP.costM, FP.cmP]
  | seq p q ihp ihq => simp [FP.costM, FP.cmP, ihp, ihq]
  | emit bs => simp [FP.costM, FP.cmP]
  | emitVar r o => simp [FP.costM, FP.cmP]; ring
  | addConst r k => simp [FP.costM, FP.cmP]
  | subConst r k => simp [FP.costM, FP.cmP]
  | addReg r s => simp [FP.costM, FP.cmP]
  | subReg r s => simp [FP.costM, FP.cmP]
  | clr r => simp [FP.costM, FP.cmP]
  | forLoop c b ih => simp [FP.costM, FP.cmP, ih]
  | forBits pf pt ihf iht => simp [FP.costM, FP.cmP, ihf, iht]
  | countBits m => simp [FP.costM, FP.cmP]; ring

theorem cost_le_cmP (p : FP) (M : ℕ) (a : AS) (h : FP.Within M p a) :
    p.cost a ≤ (p.cmP).eval M := by
  rw [← costM_eq]; exact cost_le_costM M p a h

/-! ## The time loop keeps registers bounded -/

namespace CM

variable (cm : CM)

theorem vA_le {W t k d : ℕ} (hk : k < cm.K) (hd : d ≤ W) :
    cm.vA W t k d 0 ≤ (t + 1) * cm.Fr W := by
  unfold vA Fr
  have h1 : k * W + d ≤ cm.K * W := by nlinarith
  have h2 : (k * W + d) * (cm.A + 1) ≤ cm.K * (W * (cm.A + 1)) := by
    calc (k * W + d) * (cm.A + 1) ≤ (cm.K * W) * (cm.A + 1) := Nat.mul_le_mul_right _ h1
      _ = cm.K * (W * (cm.A + 1)) := by ring
  have h3 : (t + 1) * (cm.Q + cm.K * (W * (cm.A + 1))) =
      t * (cm.Q + cm.K * (W * (cm.A + 1))) + cm.Q + cm.K * (W * (cm.A + 1)) := by ring
  omega

/-- Frame registers at time `t ≤ W` are at most `(W + 2) * Fr W`. -/
theorem frame_le {W t : ℕ} {b : AS} (hF : cm.FrameRegs W t b) (ht : t ≤ W) :
    ∀ r, r < 2 * cm.K + 2 → b.reg r ≤ (W + 2) * cm.Fr W := by
  obtain ⟨f0, f1, f2, f3⟩ := hF
  have hm : ∀ u, u ≤ W + 2 → u * cm.Fr W ≤ (W + 2) * cm.Fr W :=
    fun u hu => Nat.mul_le_mul_right _ hu
  intro r hr
  by_cases r0 : r = 0
  · subst r0; rw [f0]; exact hm _ (by omega)
  by_cases r1 : r ≤ cm.K
  · have := f1 (r - 1) (by omega)
    rw [show 1 + (r - 1) = r by omega] at this
    rw [this]
    exact (cm.vA_le (t := t) (k := r - 1) (d := 0) (by omega) (Nat.zero_le _)).trans
      (hm _ (by omega))
  by_cases r2 : r = cm.K + 1
  · subst r2; rw [f2]; exact hm _ (by omega)
  · have := f3 (r - cm.K - 2) (by omega)
    rw [show cm.K + 2 + (r - cm.K - 2) = r by omega] at this
    rw [this]
    exact (cm.vA_le (t := t + 1) (k := r - cm.K - 2) (d := 0) (by omega) (Nat.zero_le _)).trans
      (hm _ (by omega))

/-- Invariant of the time loop, with all registers kept below `Sx`. -/
def MainInv (W Sx : ℕ) (b0 : AS) (j : ℕ) (b' : AS) : Prop :=
  cm.FrameRegs W j b' ∧ b'.reg cm.rP = W ∧ b'.reg cm.rN2 = W - 2 * cm.c ∧
  b'.reg cm.rFR = cm.Fr W ∧ (∀ r, 2 * cm.K + 4 ≤ r → b'.reg r = b0.reg r) ∧
  b'.bits = b0.bits ∧ b'.inp = b0.inp ∧ b'.reg (2 * cm.K + 2) ≤ Sx ∧
  b'.reg (2 * cm.K + 3) ≤ Sx

theorem mainBody_inv {W j Sx : ℕ} (hc : 0 < cm.c) (hK : 0 < cm.K) (hj : j < W)
    (hSx : (W + 2) * cm.Fr W ≤ Sx) (b0 b' : AS) (h : cm.MainInv W Sx b0 j b') :
    cm.MainInv W Sx b0 (j + 1) (cm.mainBody.run b') := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := h
  have hP' : cm.rP ≠ 2 * cm.K + 2 := by unfold rP; omega
  have hN' : cm.rN2 ≠ 2 * cm.K + 2 := by unfold rN2; omega
  have hFr' : cm.rFR ≠ 2 * cm.K + 2 := by unfold rFR; omega
  obtain ⟨f1, f2, f3, f4⟩ := cm.run_frameBlockP b' g1 g2 g3
  set b₁ := cm.frameBlockP.run b' with hb₁
  have hF₁ : cm.FrameRegs W j b₁ := cm.FrameRegs_of_same g1 f4
  have hN₁ : b₁.reg cm.rN2 = W - 2 * cm.c := by rw [f4 _ hN']; exact g3
  obtain ⟨s1, s2, s3, s4, s5⟩ := cm.run_stepBlockP hc b₁ hF₁ hN₁
  set b₂ := cm.stepBlockP.run b₁ with hb₂
  have hF₂ : cm.FrameRegs W j b₂ :=
    cm.FrameRegs_of_lt hF₁ (fun r hr => s4 r (by omega) (by omega))
  have hFr₂ : b₂.reg cm.rFR = cm.Fr W := by
    rw [s4 _ (by unfold rFR; omega) (by unfold rFR; omega), f4 _ hFr']; exact g4
  obtain ⟨a1, a2, a3, a4, a5⟩ := cm.run_advanceP b₂ hF₂ hFr₂
  have hmain : cm.mainBody.run b' = cm.advanceP.run b₂ := rfl
  rw [hmain]
  obtain ⟨c2, c3⟩ := s5 hK
  have hm : ∀ u, u ≤ W + 2 → u * cm.Fr W ≤ Sx := fun u hu =>
    (Nat.mul_le_mul_right _ hu).trans hSx
  refine ⟨a1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a5 _ (by unfold rP; omega), s4 _ (by unfold rP; omega) (by unfold rP; omega),
      f4 _ hP']; exact g2
  · rw [a5 _ (by unfold rN2; omega), s4 _ (by unfold rN2; omega) (by unfold rN2; omega),
      f4 _ hN']; exact g3
  · rw [a5 _ (by unfold rFR; omega)]; exact hFr₂
  · intro r hr
    rw [a5 r (by omega), s4 r (by omega) (by omega), f4 r (by omega), g5 r hr]
  · rw [a4, s3, f3, g6]
  · rw [a3, s2, f2, g7]
  · rw [a5 _ (by omega), c2]
    exact (cm.vA_le (t := j) (k := cm.K - 1) (d := W - 2 * cm.c) (by omega) (by omega)).trans
      (hm _ (by omega))
  · rw [a5 _ (by omega), c3]
    exact (cm.vA_le (t := j + 1) (k := cm.K - 1) (d := W - 2 * cm.c) (by omega)
      (by omega)).trans (hm _ (by omega))

theorem mainLoop_inv {W Sx : ℕ} (hc : 0 < cm.c) (hK : 0 < cm.K)
    (hSx : (W + 2) * cm.Fr W ≤ Sx) (b0 : AS) (h0 : cm.MainInv W Sx b0 0 b0) :
    ∀ j ≤ W, cm.MainInv W Sx b0 j (cm.mainBody.run^[j] b0) := by
  intro j
  induction j with
  | zero => intro _; exact h0
  | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply']
      exact cm.mainBody_inv hc hK (by omega) hSx b0 _ (ih (by omega))

theorem MainInv.bd {W S1 : ℕ} {b0 b' : AS} {j : ℕ} (hj : j ≤ W) (hB : Bd S1 b0)
    (h : cm.MainInv W (S1 + (W + 2) * cm.Fr W) b0 j b') : Bd (S1 + (W + 2) * cm.Fr W) b' := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := h
  refine ⟨fun r => ?_, by rw [g6]; have := hB.2.1; omega, by rw [g7]; have := hB.2.2; omega⟩
  by_cases hr : r < 2 * cm.K + 2
  · have := cm.frame_le g1 hj r hr; omega
  by_cases hr2 : r = 2 * cm.K + 2
  · subst hr2; exact g8
  by_cases hr3 : r = 2 * cm.K + 3
  · subst hr3; exact g9
  · rw [g5 r (by omega)]; have := hB.1 r; omega


/-- `P = C * (n + 1)^e` as a polynomial. -/
noncomputable def Ppoly (C e : ℕ) : Polynomial ℕ :=
  Polynomial.C C * (Polynomial.X + 1) ^ e

/-- `Sx = S1 + (P + 2) * Fr P` as a polynomial in `n`. -/
noncomputable def Sxpoly (C e : ℕ) : Polynomial ℕ :=
  (cm.preP C e).bd + (Ppoly C e + Polynomial.C 2) *
    (Polynomial.C cm.Q + Polynomial.C cm.K * (Ppoly C e * Polynomial.C (cm.A + 1)))

noncomputable def genCostPoly (C e : ℕ) : Polynomial ℕ :=
  (cm.preP C e).cmP.comp (cm.preP C e).bd +
  (FP.forLoop cm.rP cm.mainBody).cmP.comp (cm.mainBody.bd.comp (cm.Sxpoly C e)) +
  cm.frameBlockP.cmP.comp (cm.frameBlockP.bd.comp (cm.Sxpoly C e)) +
  cm.accP.cmP.comp (cm.accP.bd.comp (cm.frameBlockP.bd.comp (cm.Sxpoly C e))) +
  Polynomial.C ((encodeFormula tautSeed).length + 1)

theorem cost_genProg_le (hc : 0 < cm.c) (hkin : cm.kin < cm.K) (hkout : cm.kout < cm.K)
    (C e : ℕ) (x : List Bool) :
    (cm.genProg C e).cost (AS0 x) ≤ (cm.genCostPoly C e).eval x.length := by
  have hK : 0 < cm.K := by omega
  set n := x.length with hn
  set a0 := AS0 x with ha0
  have hB0 : Bd n a0 := ⟨fun r => Nat.zero_le _, by simp [ha0, AS0], by simp [ha0, AS0, hn]⟩
  obtain ⟨w1, b1⟩ := top (cm.preP C e) (cm.preP_LinOK C e) n a0 hB0
  obtain ⟨hF6, a6P, a6N2, a6F, -⟩ := cm.run_preP hc hkin hkout C e x
  set a6 := (cm.preP C e).run a0 with ha6
  set M1 := ((cm.preP C e).bd).eval n with hM1
  set P := C * (n + 1) ^ e with hP
  set Sx := M1 + (P + 2) * cm.Fr P with hSx
  have h0 : cm.MainInv P Sx a6 0 a6 :=
    ⟨hF6, a6P, a6N2, a6F, fun _ _ => rfl, rfl, rfl,
      (b1.1 _).trans (by omega), (b1.1 _).trans (by omega)⟩
  have hloop := cm.mainLoop_inv hc hK (by omega) a6 h0
  have hBd : ∀ j ≤ P, Bd Sx (cm.mainBody.run^[j] a6) := fun j hj =>
    CM.MainInv.bd cm hj b1 (hloop j hj)
  set M2 := (cm.mainBody.bd).eval Sx with hM2
  have hwl : FP.Within M2 (FP.forLoop cm.rP cm.mainBody) a6 := by
    refine .forLoop _ _ _ ?_ (fun j hj => ?_)
    · rw [a6P]
      have := b1.1 cm.rP
      rw [a6P] at this
      have := le_bd cm.mainBody Sx
      omega
    · rw [a6P] at hj
      exact (top cm.mainBody cm.mainBody_LinOK Sx _ (hBd j hj.le)).1
  have hL : (FP.forLoop cm.rP cm.mainBody).run a6 = cm.mainBody.run^[P] a6 := by
    show cm.mainBody.run^[a6.reg cm.rP] a6 = _
    rw [a6P]
  have hBL : Bd Sx ((FP.forLoop cm.rP cm.mainBody).run a6) := by
    rw [hL]; exact hBd P le_rfl
  obtain ⟨w3, b3⟩ := top cm.frameBlockP cm.frameBlockP_LinOK Sx _ hBL
  obtain ⟨w4, b4⟩ := top cm.accP cm.accP_LinOK _ _ b3
  have c1 := cost_le_cmP _ _ _ w1
  have c2 := cost_le_cmP _ _ _ hwl
  have c3 := cost_le_cmP _ _ _ w3
  have c4 := cost_le_cmP _ _ _ w4
  have hcost : (cm.genProg C e).cost a0 = (cm.preP C e).cost a0 +
      ((FP.forLoop cm.rP cm.mainBody).cost a6 +
        cm.frameBlockP.cost ((FP.forLoop cm.rP cm.mainBody).run a6) +
        (cm.accP.cost (cm.mainP.run a6) + ((encodeFormula tautSeed).length + 1))) := by
    show _ = _
    simp only [genProg, mainP, FP.cost, Nat.add_assoc]
    rfl
  have hSxe : (cm.Sxpoly C e).eval n = Sx := by
    simp [Sxpoly, Ppoly, hSx, hM1, hP, Fr]
  have hT : (cm.genCostPoly C e).eval n =
      (cm.preP C e).cmP.eval M1 + (FP.forLoop cm.rP cm.mainBody).cmP.eval M2 +
      cm.frameBlockP.cmP.eval ((cm.frameBlockP.bd).eval Sx) +
      cm.accP.cmP.eval ((cm.accP.bd).eval ((cm.frameBlockP.bd).eval Sx)) +
      ((encodeFormula tautSeed).length + 1) := by
    simp [genCostPoly, Polynomial.eval_comp, hSxe, hM1, hM2]
  rw [hcost, hT]
  have e7 : cm.mainP.run a6 = cm.frameBlockP.run ((FP.forLoop cm.rP cm.mainBody).run a6) := rfl
  rw [e7] at *
  omega

end CM

end CL
end SATurday.Bridge
