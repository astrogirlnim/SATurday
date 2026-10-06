import Theory.ProofComplexity.Bridge.FProg
import Theory.ProofComplexity.Bridge.Tableau

/-!
# The tableau generator as a register program (Ladder Rung R5)

Emission of templates, and (below) the families of constraints, as `FP` programs
whose abstract run is proved to output the bits of the tableau formula.

LOG: R5 Bridge Generator module (emission of templates, families)
-/

open SATurday.Bridge.SP

namespace SATurday.Bridge
namespace CL

/-! ## Emitting templates -/

/-- Emit the bits of an instantiated template, reading variable numbers from registers. -/
def emitTF : TF → FP
  | .leaf r o => .emitVar r o
  | .not a => .seq (.emit [false, true]) (emitTF a)
  | .and a b => .seq (.emit [true, false]) (.seq (emitTF a) (emitTF b))
  | .or a b => .seq (.emit [true, true]) (.seq (emitTF a) (emitTF b))

/-- Registers used by a template are below `M`. -/
def TF.regsLt (M : ℕ) : TF → Prop
  | .leaf r _ => r < M
  | .not a => a.regsLt M
  | .and a b => a.regsLt M ∧ b.regsLt M
  | .or a b => a.regsLt M ∧ b.regsLt M

theorem TF.inst_congr {V V' : ℕ → ℕ → ℕ} {M : ℕ} (h : ∀ r < M, ∀ o, V r o = V' r o) :
    ∀ φ : TF, φ.regsLt M → φ.inst V = φ.inst V' := by
  intro φ
  induction φ with
  | leaf r o => intro hr; simp [TF.inst, h r hr o]
  | not a ih => intro hr; simp [TF.inst, ih hr]
  | and a b iha ihb => intro hr; simp [TF.inst, iha hr.1, ihb hr.2]
  | or a b iha ihb => intro hr; simp [TF.inst, iha hr.1, ihb hr.2]

theorem emitTF_run (φ : TF) (a : AS) :
    (emitTF φ).run a =
      { a with out := a.out ++ encodeFormula (φ.inst (fun r o => a.reg r + o)) } := by
  induction φ generalizing a with
  | leaf r o =>
      simp [emitTF, FP.run, TF.inst, encodeFormula, encodeNat, List.append_assoc]
  | not x ih =>
      simp only [emitTF, FP.run, ih, TF.inst, encodeFormula]
      simp
  | and x y ihx ihy =>
      simp only [emitTF, FP.run, ihx, ihy, TF.inst, encodeFormula]
      simp [List.append_assoc]
  | or x y ihx ihy =>
      simp only [emitTF, FP.run, ihx, ihy, TF.inst, encodeFormula]
      simp [List.append_assoc]

theorem run_seq' (p q : FP) (a : AS) : (FP.seq p q).run a = q.run (p.run a) := rfl
theorem run_emit' (bs : List Bool) (a : AS) :
    (FP.emit bs).run a = { a with out := a.out ++ bs } := rfl
theorem run_addConst' (r k : ℕ) (a : AS) :
    (FP.addConst r k).run a = { a with reg := Function.update a.reg r (a.reg r + k) } := rfl
theorem run_subConst' (r k : ℕ) (a : AS) :
    (FP.subConst r k).run a = { a with reg := Function.update a.reg r (a.reg r - k) } := rfl
theorem run_addReg' (r s : ℕ) (a : AS) :
    (FP.addReg r s).run a = { a with reg := Function.update a.reg r (a.reg r + a.reg s) } := rfl
theorem run_clr' (r : ℕ) (a : AS) :
    (FP.clr r).run a = { a with reg := Function.update a.reg r 0 } := rfl
theorem run_countBits' (m : ℕ) (a : AS) :
    (FP.countBits m).run a =
      { a with reg := Function.update a.reg m a.inp.length, bits := a.inp.reverse, inp := [] } :=
  rfl
theorem run_forLoop' (cnt : ℕ) (body : FP) (a : AS) :
    (FP.forLoop cnt body).run a = body.run^[a.reg cnt] a := rfl

/-- Bits of a list of instantiated templates, each preceded by the `and` tag. -/
def tmplBits (V : ℕ → ℕ → ℕ) (l : List TF) : List Bool :=
  l.flatMap fun φ => [true, false] ++ encodeFormula (φ.inst V)

/-- Emit a list of templates as conjuncts. -/
def emitTL : List TF → FP
  | [] => .skip
  | φ :: l => .seq (.emit [true, false]) (.seq (emitTF φ) (emitTL l))

theorem emitTL_run (l : List TF) (a : AS) :
    (emitTL l).run a = { a with out := a.out ++ tmplBits (fun r o => a.reg r + o) l } := by
  induction l generalizing a with
  | nil => simp [emitTL, FP.run, tmplBits]
  | cons φ l ih =>
      simp only [emitTL, FP.run, emitTF_run, ih, tmplBits, List.flatMap_cons]
      simp [List.append_assoc]

theorem tmplBits_append (V : ℕ → ℕ → ℕ) (l l' : List TF) :
    tmplBits V (l ++ l') = tmplBits V l ++ tmplBits V l' := by
  simp [tmplBits, List.flatMap_append]

theorem tmplBits_instL (V : ℕ → ℕ → ℕ) (l : List TF) :
    (instL V l).flatMap (fun φ => [true, false] ++ encodeFormula φ) = tmplBits V l := by
  simp [instL, tmplBits, List.flatMap_map]

/-- Repeat a program. -/
def repeatFP : ℕ → FP → FP
  | 0, _ => .skip
  | n + 1, p => .seq p (repeatFP n p)

theorem run_repeat (p : FP) (n : ℕ) (a : AS) : (repeatFP n p).run a = p.run^[n] a := by
  induction n generalizing a with
  | zero => simp [repeatFP, FP.run]
  | succ n ih => simp [repeatFP, FP.run, ih, Function.iterate_succ_apply]

/-- `r := n`. -/
def setConst (r n : ℕ) : FP := .seq (.clr r) (.addConst r n)

/-- `r := s` (`r ≠ s`). -/
def setReg (r s : ℕ) : FP := .seq (.clr r) (.addReg r s)

/-- `r := n * s` (`r ≠ s`). -/
def mulConstTo (r s n : ℕ) : FP := .seq (.clr r) (repeatFP n (.addReg r s))

theorem run_setConst (r n : ℕ) (a : AS) :
    (setConst r n).run a = { a with reg := Function.update a.reg r n } := by
  simp [setConst, FP.run]

theorem run_setReg {r s : ℕ} (h : r ≠ s) (a : AS) :
    (setReg r s).run a = { a with reg := Function.update a.reg r (a.reg s) } := by
  simp [setReg, FP.run, Function.update_of_ne (Ne.symm h)]

theorem run_mulConstTo {r s : ℕ} (h : r ≠ s) (n : ℕ) (a : AS) :
    (mulConstTo r s n).run a = { a with reg := Function.update a.reg r (n * a.reg s) } := by
  have key : ∀ j (b : AS), b.reg r = 0 →
      (FP.addReg r s).run^[j] b = { b with reg := Function.update b.reg r (j * b.reg s) } := by
    intro j
    induction j with
    | zero =>
        intro b hb
        simp only [Function.iterate_zero, id]
        cases b; simp_all
    | succ j ih =>
        intro b hb
        rw [Function.iterate_succ_apply', ih b hb]
        simp [FP.run, Function.update_of_ne (Ne.symm h), Nat.succ_mul]
  have e : (mulConstTo r s n).run a =
      (repeatFP n (.addReg r s)).run ((FP.clr r).run a) := rfl
  rw [e, run_repeat, key n _ (by simp [FP.run])]
  simp [FP.run, Function.update_of_ne (Ne.symm h)]

/-! ## Registers written by a program -/

/-- Register `r` may be changed by the program. -/
def _root_.SATurday.Bridge.SP.FP.writes (r : ℕ) : FP → Prop
  | .skip => False
  | .seq p q => p.writes r ∨ q.writes r
  | .emit _ => False
  | .emitVar _ _ => False
  | .addConst r' _ => r' = r
  | .subConst r' _ => r' = r
  | .addReg r' _ => r' = r
  | .subReg r' _ => r' = r
  | .clr r' => r' = r
  | .forLoop _ body => body.writes r
  | .forBits pf pt => pf.writes r ∨ pt.writes r
  | .countBits m => m = r

theorem _root_.SATurday.Bridge.SP.FP.run_reg_of_not_writes (r : ℕ) : ∀ (p : FP), ¬ p.writes r → ∀ a : AS,
    (p.run a).reg r = a.reg r := by
  intro p
  induction p with
  | skip => intros; rfl
  | seq p q ihp ihq =>
      intro h a
      simp only [FP.writes, not_or] at h
      simp only [FP.run, ihq h.2, ihp h.1]
  | emit _ => intros; rfl
  | emitVar _ _ => intros; rfl
  | addConst r' k =>
      intro h a; simp only [FP.writes] at h; simp [FP.run, Function.update_of_ne (Ne.symm h)]
  | subConst r' k =>
      intro h a; simp only [FP.writes] at h; simp [FP.run, Function.update_of_ne (Ne.symm h)]
  | addReg r' s =>
      intro h a; simp only [FP.writes] at h; simp [FP.run, Function.update_of_ne (Ne.symm h)]
  | subReg r' s =>
      intro h a; simp only [FP.writes] at h; simp [FP.run, Function.update_of_ne (Ne.symm h)]
  | clr r' =>
      intro h a; simp only [FP.writes] at h; simp [FP.run, Function.update_of_ne (Ne.symm h)]
  | forLoop cnt body ih =>
      intro h a
      have key : ∀ j (b : AS), (body.run^[j] b).reg r = b.reg r := by
        intro j
        induction j with
        | zero => intro b; rfl
        | succ j ihj => intro b; rw [Function.iterate_succ_apply, ihj, ih h]
      simp only [FP.run]; exact key _ a
  | forBits pf pt ihf iht =>
      intro h a
      simp only [FP.writes, not_or] at h
      simp only [FP.run]
      have key : ∀ k (b : AS), (forBitsAux (fun bit => if bit then pt.run else pf.run) k b).reg r =
          b.reg r := by
        intro k
        induction k with
        | zero => intro b; rfl
        | succ k ihk =>
            intro b
            simp only [forBitsAux]
            cases hb : b.bits with
            | nil => rfl
            | cons bit rest =>
                simp only
                rw [ihk]
                cases bit
                · simp only [Bool.false_eq_true, if_false]; exact ihf h.1 _
                · simp only [if_true]; exact iht h.2 _
      exact key _ a
  | countBits m =>
      intro h a; simp only [FP.writes] at h; simp [FP.run, Function.update_of_ne (Ne.symm h)]

theorem TF.regsLt_mono {M M' : ℕ} (hMM : M ≤ M') : ∀ φ : TF, φ.regsLt M → φ.regsLt M' := by
  intro φ
  induction φ with
  | leaf r o => intro h; simp only [TF.regsLt] at *; omega
  | not a ih => intro h; exact ih h
  | and a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
  | or a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩

/-! ## Register layout of the generator -/

namespace CM

variable (cm : CM)

/-- `|x|`. -/
def rM : ℕ := 2 * cm.K + 4
/-- The common width and time bound `P`. -/
def rP : ℕ := 2 * cm.K + 5
/-- Frame size. -/
def rFR : ℕ := 2 * cm.K + 6
/-- Stack block size `P * (A + 1)`. -/
def rL : ℕ := 2 * cm.K + 7
/-- Scratch. -/
def rN1 : ℕ := 2 * cm.K + 8
/-- Deep loop count `P - 2c`. -/
def rN2 : ℕ := 2 * cm.K + 9
/-- Scratch. -/
def rT : ℕ := 2 * cm.K + 10
/-- Scratch. -/
def rU : ℕ := 2 * cm.K + 11
/-- Init count `P - (2m+1)`. -/
def rN3 : ℕ := 2 * cm.K + 12
/-- Init count `P - (2m+2)`. -/
def rN4 : ℕ := 2 * cm.K + 13
/-- Number of registers. -/
def nR : ℕ := 2 * cm.K + 14

/-- The frame registers hold the values for time `t`. -/
def FrameRegs (W t : ℕ) (a : AS) : Prop :=
  a.reg 0 = t * cm.Fr W ∧ (∀ k < cm.K, a.reg (1 + k) = cm.vA W t k 0 0) ∧
  a.reg (cm.K + 1) = (t + 1) * cm.Fr W ∧
  (∀ k < cm.K, a.reg (cm.K + 2 + k) = cm.vA W (t + 1) k 0 0)

/-- The template valuation agrees with the registers below `M`. -/
def RegsAgree (W t k dOff M : ℕ) (a : AS) : Prop :=
  ∀ r < M, a.reg r = cm.valF W t k dOff r

theorem agree_frame {W t : ℕ} {a : AS} (h : cm.FrameRegs W t a) (k dOff : ℕ) :
    cm.RegsAgree W t k dOff (2 * cm.K + 2) a := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  intro r hr
  by_cases r0 : r = 0
  · subst r0; simp [valF, h0]
  by_cases r1 : r ≤ cm.K
  · have := h1 (r - 1) (by omega)
    have e : 1 + (r - 1) = r := by omega
    rw [e] at this
    simp [valF, r0, r1, this]
  by_cases r2 : r = cm.K + 1
  · subst r2; simp [valF, h2]
  · have := h3 (r - cm.K - 2) (by omega)
    have e : cm.K + 2 + (r - cm.K - 2) = r := by omega
    rw [e] at this
    have r3 : r ≤ 2 * cm.K + 1 := by omega
    simp [valF, r0, r1, r2, r3, this]

theorem agree_frame_D {W t : ℕ} {a : AS} (h : cm.FrameRegs W t a) {k dOff : ℕ}
    (hD : a.reg (2 * cm.K + 2) = cm.vA W t k dOff 0) :
    cm.RegsAgree W t k dOff (2 * cm.K + 3) a := by
  intro r hr
  by_cases r2 : r < 2 * cm.K + 2
  · exact cm.agree_frame h k dOff r r2
  · have : r = 2 * cm.K + 2 := by omega
    subst this
    have h1 : ¬ 2 * cm.K + 2 ≤ cm.K := by omega
    have h2 : 2 * cm.K + 2 ≠ cm.K + 1 := by omega
    have h3 : ¬ 2 * cm.K + 2 ≤ 2 * cm.K + 1 := by omega
    simp [valF, h1, h2, h3, hD]

theorem agree_frame_DD {W t : ℕ} {a : AS} (h : cm.FrameRegs W t a) {k dOff : ℕ}
    (hD : a.reg (2 * cm.K + 2) = cm.vA W t k dOff 0)
    (hD' : a.reg (2 * cm.K + 3) = cm.vA W (t + 1) k dOff 0) :
    cm.RegsAgree W t k dOff (2 * cm.K + 4) a := by
  intro r hr
  by_cases r2 : r < 2 * cm.K + 3
  · exact cm.agree_frame_D h hD r r2
  · have : r = 2 * cm.K + 3 := by omega
    subst this
    have h1 : ¬ 2 * cm.K + 3 ≤ cm.K := by omega
    have h2 : 2 * cm.K + 3 ≠ cm.K + 1 := by omega
    have h3 : ¬ 2 * cm.K + 3 ≤ 2 * cm.K + 1 := by omega
    have h4 : 2 * cm.K + 3 ≠ 2 * cm.K + 2 := by omega
    simp [valF, h1, h2, h3, h4, hD']

theorem tmplBits_agree {W t k dOff M : ℕ} {a : AS} (hA : cm.RegsAgree W t k dOff M a)
    (l : List TF) (hl : ∀ φ ∈ l, φ.regsLt M) :
    tmplBits (fun r o => a.reg r + o) l = tmplBits (cm.Vf W t k dOff) l := by
  unfold tmplBits
  apply List.flatMap_congr
  intro φ hφ
  rw [TF.inst_congr (V' := cm.Vf W t k dOff) (M := M) (fun r hr o => by simp [Vf, hA r hr]) φ (hl φ hφ)]

theorem emitTL_run_agree {W t k dOff M : ℕ} {a : AS} (hA : cm.RegsAgree W t k dOff M a)
    (l : List TF) (hl : ∀ φ ∈ l, φ.regsLt M) :
    (emitTL l).run a = { a with out := a.out ++ tmplBits (cm.Vf W t k dOff) l } := by
  rw [emitTL_run, tmplBits_agree cm hA l hl]

/-! ### Registers read by the templates -/

theorem regsLt_conjT {M : ℕ} (hM : 0 < M) (l : List TF) (h : ∀ φ ∈ l, φ.regsLt M) :
    (conjT l).regsLt M := by
  induction l with
  | nil => simp [conjT, TF.tt, TF.regsLt, hM]
  | cons φ l ih =>
      simp only [conjT, TF.regsLt]
      exact ⟨h φ (by simp), ih (fun ψ hψ => h ψ (by simp [hψ]))⟩

theorem regsLt_disjT {M : ℕ} (hM : 0 < M) (l : List TF) (h : ∀ φ ∈ l, φ.regsLt M) :
    (disjT l).regsLt M := by
  induction l with
  | nil => simp [disjT, TF.tt, TF.regsLt, hM]
  | cons φ l ih =>
      simp only [disjT, TF.regsLt]
      exact ⟨h φ (by simp), ih (fun ψ hψ => h ψ (by simp [hψ]))⟩

theorem regsLt_impT {M : ℕ} {a b : TF} (ha : a.regsLt M) (hb : b.regsLt M) :
    (impT a b).regsLt M := by
  simp only [impT, TF.regsLt]; exact ⟨ha, hb⟩

theorem regsLt_exactlyOne {M r : ℕ} (hr : r < M) (offs : List ℕ) :
    (exactlyOne r offs).regsLt M := by
  have hM : 0 < M := by omega
  unfold exactlyOne
  simp only [TF.regsLt]
  refine ⟨regsLt_disjT hM _ ?_, regsLt_conjT hM _ ?_⟩
  · intro φ hφ
    simp only [List.mem_map] at hφ
    obtain ⟨o, _, rfl⟩ := hφ
    exact hr
  · intro φ hφ
    simp only [List.mem_flatMap, List.mem_filterMap] at hφ
    obtain ⟨o, _, o', _, hφ⟩ := hφ
    split_ifs at hφ
    · simp only [Option.some.injEq] at hφ
      subst hφ
      simp [TF.regsLt, hr]

theorem guardT_regs (hc : 0 < cm.c) (q : ℕ) (p : List ℕ) :
    ∀ φ ∈ cm.guardT q p, φ.regsLt (cm.K + 1) := by
  intro φ hφ
  unfold guardT at hφ
  simp only [List.mem_cons, List.mem_map, List.mem_range] at hφ
  rcases hφ with rfl | ⟨i, hi, rfl⟩
  · simp [TF.regsLt]
  · simp only [TF.regsLt]
    have : i / cm.c < cm.K := by
      rw [Nat.div_lt_iff_lt_mul hc]; linarith
    omega

theorem stepCtlT_regs (hc : 0 < cm.c) : ∀ φ ∈ cm.stepCtlT, φ.regsLt (cm.K + 2) := by
  intro φ hφ
  unfold stepCtlT at hφ
  simp only [List.mem_map] at hφ
  obtain ⟨qp, _, rfl⟩ := hφ
  refine regsLt_impT (regsLt_conjT (by omega) _ ?_) ?_
  · intro ψ hψ
    have := cm.guardT_regs hc qp.1 qp.2 ψ hψ
    have e : ∀ {M M' : ℕ}, M ≤ M' → ∀ φ : TF, φ.regsLt M → φ.regsLt M' := by
      intro M M' hMM φ
      induction φ with
      | leaf r o => intro h; simp only [TF.regsLt] at *; omega
      | not a ih => intro h; exact ih h
      | and a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
      | or a b iha ihb => intro h; exact ⟨iha h.1, ihb h.2⟩
    exact e (by omega) ψ this
  · simp [TF.regsLt]

theorem topT_regs (hc : 0 < cm.c) {k : ℕ} (hk : k < cm.K) (d : ℕ) :
    ∀ φ ∈ cm.topT k d, φ.regsLt (2 * cm.K + 2) := by
  intro φ hφ
  unfold topT at hφ
  simp only [List.mem_flatMap] at hφ
  obtain ⟨qp, _, hφ⟩ := hφ
  have hg : ∀ ψ ∈ cm.guardT qp.1 qp.2, ψ.regsLt (2 * cm.K + 2) :=
    fun ψ hψ => TF.regsLt_mono (by omega) ψ (cm.guardT_regs hc _ _ ψ hψ)
  have hgc : (conjT (cm.guardT qp.1 qp.2)).regsLt (2 * cm.K + 2) :=
    regsLt_conjT (by omega) _ hg
  split_ifs at hφ
  · simp only [List.mem_singleton] at hφ
    subst hφ
    exact regsLt_impT hgc (by simp [TF.regsLt]; omega)
  · simp only [List.mem_map, List.mem_range] at hφ
    obtain ⟨a, _, rfl⟩ := hφ
    refine regsLt_impT (regsLt_conjT (by omega) _ ?_) (by simp [TF.regsLt]; omega)
    intro ψ hψ
    simp only [List.mem_append, List.mem_singleton] at hψ
    rcases hψ with hψ | rfl
    · exact hg ψ hψ
    · simp [TF.regsLt]; omega

theorem deepT_regs (hc : 0 < cm.c) (k : ℕ) :
    ∀ φ ∈ cm.deepT k, φ.regsLt (2 * cm.K + 4) := by
  intro φ hφ
  unfold deepT at hφ
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hφ
  obtain ⟨qp, _, a, _, rfl⟩ := hφ
  have hg : ∀ ψ ∈ cm.guardT qp.1 qp.2, ψ.regsLt (2 * cm.K + 4) :=
    fun ψ hψ => TF.regsLt_mono (by omega) ψ (cm.guardT_regs hc _ _ ψ hψ)
  refine regsLt_impT (regsLt_conjT (by omega) _ ?_) (by simp [TF.regsLt])
  intro ψ hψ
  simp only [List.mem_append, List.mem_singleton] at hψ
  rcases hψ with hψ | rfl
  · exact hg ψ hψ
  · simp [TF.regsLt]

/-! ### Generic loop lemmas -/

end CM

theorem run_forLoop_addReg {c r s : ℕ} (h : r ≠ s) (a : AS) :
    (FP.forLoop c (.addReg r s)).run a =
      { a with reg := Function.update a.reg r (a.reg r + a.reg c * a.reg s) } := by
  have key : ∀ j (b : AS), (FP.addReg r s).run^[j] b =
      { b with reg := Function.update b.reg r (b.reg r + j * b.reg s) } := by
    intro j
    induction j with
    | zero => intro b; cases b; simp
    | succ j ih =>
        intro b
        rw [Function.iterate_succ_apply', ih b]
        simp [FP.run, Function.update_of_ne (Ne.symm h), Nat.succ_mul, Nat.add_assoc]
  rw [show (FP.forLoop c (.addReg r s)).run a = (FP.addReg r s).run^[a.reg c] a from rfl, key]

theorem run_forLoop_addConst {c r : ℕ} (k : ℕ) (a : AS) :
    (FP.forLoop c (.addConst r k)).run a =
      { a with reg := Function.update a.reg r (a.reg r + a.reg c * k) } := by
  have key : ∀ j (b : AS), (FP.addConst r k).run^[j] b =
      { b with reg := Function.update b.reg r (b.reg r + j * k) } := by
    intro j
    induction j with
    | zero => intro b; cases b; simp
    | succ j ih =>
        intro b
        rw [Function.iterate_succ_apply', ih b]
        simp [FP.run, Nat.succ_mul, Nat.add_assoc]
  rw [show (FP.forLoop c (.addConst r k)).run a = (FP.addConst r k).run^[a.reg c] a from rfl, key]

theorem run_skip' (a : AS) : FP.skip.run a = a := rfl

theorem run_forLoop_subConst {c r : ℕ} (k : ℕ) (a : AS) :
    (FP.forLoop c (.subConst r k)).run a =
      { a with reg := Function.update a.reg r (a.reg r - a.reg c * k) } := by
  have key : ∀ j (b : AS), (FP.subConst r k).run^[j] b =
      { b with reg := Function.update b.reg r (b.reg r - j * k) } := by
    intro j
    induction j with
    | zero => intro b; cases b; simp
    | succ j ih =>
        intro b
        rw [Function.iterate_succ_apply', ih b]
        simp [FP.run, Nat.succ_mul, Nat.sub_sub]
  rw [show (FP.forLoop c (.subConst r k)).run a = (FP.subConst r k).run^[a.reg c] a from rfl, key]

namespace CM

variable (cm : CM)

/-- One multiplication by `m + 1`: `rT := rU * rT`. -/
def powStep : FP :=
  .seq (.clr cm.rN1) (.seq (.forLoop cm.rU (.addReg cm.rN1 cm.rT)) (setReg cm.rT cm.rN1))

theorem run_powStep (a : AS) :
    (cm.powStep.run a) = { a with reg := Function.update (Function.update a.reg cm.rN1
      (a.reg cm.rU * a.reg cm.rT)) cm.rT (a.reg cm.rU * a.reg cm.rT) } := by
  have h1 : cm.rN1 ≠ cm.rT := by unfold rN1 rT; omega
  have h2 : cm.rN1 ≠ cm.rU := by unfold rN1 rU; omega
  have h3 : cm.rT ≠ cm.rU := by unfold rT rU; omega
  have e1 : (FP.clr cm.rN1).run a = { a with reg := Function.update a.reg cm.rN1 0 } := rfl
  have e2 := run_forLoop_addReg (c := cm.rU) h1 ({ a with reg := Function.update a.reg cm.rN1 0 })
  have e3 := run_setReg (r := cm.rT) (s := cm.rN1) (Ne.symm h1)
  simp only [powStep, FP.run]
  rw [e1] at *
  show (setReg cm.rT cm.rN1).run ((FP.forLoop cm.rU (.addReg cm.rN1 cm.rT)).run
    { a with reg := Function.update a.reg cm.rN1 0 }) = _
  rw [e2, e3]
  congr 1
  funext x
  by_cases hT : x = cm.rT
  · subst hT; simp [Function.update_apply, h1, h1.symm, h2, h2.symm, h3, h3.symm]
  · by_cases hN : x = cm.rN1
    · subst hN; simp [Function.update_apply, h1, h1.symm, h2, h2.symm, h3, h3.symm]
    · simp [Function.update_apply, hT, hN, h1, h1.symm, h2, h2.symm, h3, h3.symm]

theorem iter_powStep (j : ℕ) (b : AS) :
    (cm.powStep.run^[j] b).reg cm.rU = b.reg cm.rU ∧
    (cm.powStep.run^[j] b).reg cm.rT = b.reg cm.rU ^ j * b.reg cm.rT ∧
    (∀ r, r ≠ cm.rN1 → r ≠ cm.rT → (cm.powStep.run^[j] b).reg r = b.reg r) ∧
    (cm.powStep.run^[j] b).out = b.out ∧ (cm.powStep.run^[j] b).inp = b.inp ∧
    (cm.powStep.run^[j] b).bits = b.bits := by
  have h1 : cm.rN1 ≠ cm.rT := by unfold rN1 rT; omega
  have h2 : cm.rN1 ≠ cm.rU := by unfold rN1 rU; omega
  have h3 : cm.rT ≠ cm.rU := by unfold rT rU; omega
  induction j generalizing b with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply]
      obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih (cm.powStep.run b)
      have hc := cm.run_powStep b
      have c1 : (cm.powStep.run b).reg cm.rU = b.reg cm.rU := by
        rw [hc]; simp [Function.update_apply, h2, h2.symm, h3, h3.symm, h1, h1.symm]
      have c2 : (cm.powStep.run b).reg cm.rT = b.reg cm.rU * b.reg cm.rT := by
        rw [hc]; simp [Function.update_apply, h2, h2.symm, h3, h3.symm, h1, h1.symm]
      have c3 : ∀ r, r ≠ cm.rN1 → r ≠ cm.rT → (cm.powStep.run b).reg r = b.reg r := by
        intro r hr1 hr2
        rw [hc]; simp [Function.update_apply, hr1, hr2]
      have c4 : (cm.powStep.run b).out = b.out := by rw [hc]
      have c5 : (cm.powStep.run b).inp = b.inp := by rw [hc]
      have c6 : (cm.powStep.run b).bits = b.bits := by rw [hc]
      refine ⟨by rw [i1, c1], ?_, fun r hr1 hr2 => by rw [i3 r hr1 hr2, c3 r hr1 hr2],
        by rw [i4, c4], by rw [i5, c5], by rw [i6, c6]⟩
      rw [i2, c1, c2, pow_succ]; ring

/-- Compute `P = C * (|x| + 1)^e` into `rP`. -/
def polyProg (C e : ℕ) : FP :=
  .seq (.countBits cm.rM) (.seq (setReg cm.rU cm.rM) (.seq (.addConst cm.rU 1)
    (.seq (setConst cm.rT 1) (.seq (repeatFP e cm.powStep) (mulConstTo cm.rP cm.rT C)))))

theorem run_polyProg (C e : ℕ) (a : AS) :
    ((cm.polyProg C e).run a).out = a.out ∧ ((cm.polyProg C e).run a).inp = [] ∧
    ((cm.polyProg C e).run a).bits = a.inp.reverse ∧
    ((cm.polyProg C e).run a).reg cm.rM = a.inp.length ∧
    ((cm.polyProg C e).run a).reg cm.rP = C * (a.inp.length + 1) ^ e ∧
    ∀ r, r ≠ cm.rM → r ≠ cm.rU → r ≠ cm.rT → r ≠ cm.rN1 → r ≠ cm.rP →
      ((cm.polyProg C e).run a).reg r = a.reg r := by
  have hMU : cm.rM ≠ cm.rU := by unfold rM rU; omega
  have hPT : cm.rP ≠ cm.rT := by unfold rP rT; omega
  have hTU : cm.rT ≠ cm.rU := by unfold rT rU; omega
  have hPU : cm.rP ≠ cm.rU := by unfold rP rU; omega
  have hMT : cm.rM ≠ cm.rT := by unfold rM rT; omega
  have hMP : cm.rM ≠ cm.rP := by unfold rM rP; omega
  have hMN1 : cm.rM ≠ cm.rN1 := by unfold rM rN1; omega
  have e0 : (cm.polyProg C e).run a =
      (mulConstTo cm.rP cm.rT C).run ((repeatFP e cm.powStep).run ((setConst cm.rT 1).run
        ((FP.addConst cm.rU 1).run ((setReg cm.rU cm.rM).run ((FP.countBits cm.rM).run a))))) := rfl
  have hPM : cm.rP ≠ cm.rM := hMP.symm
  have hUM : cm.rU ≠ cm.rM := hMU.symm
  have hTM : cm.rT ≠ cm.rM := hMT.symm
  have hTP : cm.rT ≠ cm.rP := hPT.symm
  have hUT : cm.rU ≠ cm.rT := hTU.symm
  have hUP : cm.rU ≠ cm.rP := hPU.symm
  rw [e0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_mulConstTo hPT, run_repeat]
    have := (cm.iter_powStep e ((setConst cm.rT 1).run ((FP.addConst cm.rU 1).run
      ((setReg cm.rU cm.rM).run ((FP.countBits cm.rM).run a))))).2.2.2.1
    simp only [] at this ⊢
    rw [this]
    simp [run_setConst, run_addConst', run_setReg hMU.symm, run_countBits']
  · rw [run_mulConstTo hPT, run_repeat]
    have := (cm.iter_powStep e ((setConst cm.rT 1).run ((FP.addConst cm.rU 1).run
      ((setReg cm.rU cm.rM).run ((FP.countBits cm.rM).run a))))).2.2.2.2.1
    simp only [] at this ⊢
    rw [this]
    simp [run_setConst, run_addConst', run_setReg hMU.symm, run_countBits']
  · rw [run_mulConstTo hPT, run_repeat]
    have := (cm.iter_powStep e ((setConst cm.rT 1).run ((FP.addConst cm.rU 1).run
      ((setReg cm.rU cm.rM).run ((FP.countBits cm.rM).run a))))).2.2.2.2.2
    simp only [] at this ⊢
    rw [this]
    simp [run_setConst, run_addConst', run_setReg hMU.symm, run_countBits']
  · rw [run_mulConstTo hPT, run_repeat]
    have := (cm.iter_powStep e ((setConst cm.rT 1).run ((FP.addConst cm.rU 1).run
      ((setReg cm.rU cm.rM).run ((FP.countBits cm.rM).run a))))).2.2.1 cm.rM hMN1 hMT
    dsimp only
    rw [Function.update_of_ne hMP, this]
    simp [run_setConst, run_addConst', run_setReg hMU.symm, run_countBits', hMT, hMU]
  · rw [run_mulConstTo hPT, run_repeat]
    have h1 := (cm.iter_powStep e ((setConst cm.rT 1).run ((FP.addConst cm.rU 1).run
      ((setReg cm.rU cm.rM).run ((FP.countBits cm.rM).run a))))).2.1
    have h2 := (cm.iter_powStep e ((setConst cm.rT 1).run ((FP.addConst cm.rU 1).run
      ((setReg cm.rU cm.rM).run ((FP.countBits cm.rM).run a))))).1
    dsimp only
    rw [Function.update_self, h1]
    simp [run_setConst, run_addConst', run_setReg hMU.symm, run_countBits', hUT, hUM]
  · intro r hrM hrU hrT hrN1 hrP
    rw [run_mulConstTo hPT, run_repeat]
    have := (cm.iter_powStep e ((setConst cm.rT 1).run ((FP.addConst cm.rU 1).run
      ((setReg cm.rU cm.rM).run ((FP.countBits cm.rM).run a))))).2.2.1 r hrN1 hrT
    dsimp only
    rw [Function.update_of_ne hrP, this]
    simp [run_setConst, run_addConst', run_setReg hMU.symm, run_countBits', hrT, hrU, hrM]

/-! ### Constants -/

/-- `rL := (A+1) * rP`, `rFR := Q + K * rL`. -/
def constProg : FP :=
  .seq (mulConstTo cm.rL cm.rP (cm.A + 1))
    (.seq (setConst cm.rFR cm.Q) (repeatFP cm.K (.addReg cm.rFR cm.rL)))

theorem run_constProg (a : AS) :
    ((cm.constProg).run a).reg cm.rL = (cm.A + 1) * a.reg cm.rP ∧
    ((cm.constProg).run a).reg cm.rFR = cm.Q + cm.K * ((cm.A + 1) * a.reg cm.rP) ∧
    ((cm.constProg).run a).out = a.out ∧ ((cm.constProg).run a).inp = a.inp ∧
    ((cm.constProg).run a).bits = a.bits ∧
    ∀ r, r ≠ cm.rL → r ≠ cm.rFR → ((cm.constProg).run a).reg r = a.reg r := by
  have h1 : cm.rL ≠ cm.rP := by unfold rL rP; omega
  have h2 : cm.rFR ≠ cm.rL := by unfold rFR rL; omega
  have h3 : cm.rFR ≠ cm.rP := by unfold rFR rP; omega
  have key : ∀ j (b : AS), (FP.addReg cm.rFR cm.rL).run^[j] b =
      { b with reg := Function.update b.reg cm.rFR (b.reg cm.rFR + j * b.reg cm.rL) } := by
    intro j
    induction j with
    | zero => intro b; cases b; simp
    | succ j ih =>
        intro b
        rw [Function.iterate_succ_apply', ih b]
        simp [run_addReg', Function.update_of_ne h2.symm, Nat.succ_mul, Nat.add_assoc]
  have e0 : (cm.constProg).run a =
      (repeatFP cm.K (.addReg cm.rFR cm.rL)).run ((setConst cm.rFR cm.Q).run
        ((mulConstTo cm.rL cm.rP (cm.A + 1)).run a)) := rfl
  rw [e0, run_repeat, key, run_setConst, run_mulConstTo h1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Function.update_of_ne h2.symm]
  · simp [Function.update_of_ne h2.symm, Function.update_of_ne h3, h1]
  · rfl
  · rfl
  · rfl
  · intro r hr1 hr2
    simp [Function.update_of_ne hr2, Function.update_of_ne hr1]

end CM

/-! ### Structural helpers for loops and unrolled sequences -/

/-- Programs that never touch the output or the input bits. -/
def _root_.SATurday.Bridge.SP.FP.pure : FP → Prop
  | .skip => True
  | .seq p q => p.pure ∧ q.pure
  | .emit _ => False
  | .emitVar _ _ => False
  | .addConst _ _ => True
  | .subConst _ _ => True
  | .addReg _ _ => True
  | .subReg _ _ => True
  | .clr _ => True
  | .forLoop _ body => body.pure
  | .forBits _ _ => False
  | .countBits _ => False

theorem _root_.SATurday.Bridge.SP.FP.run_pure : ∀ (p : FP), p.pure → ∀ a : AS,
    (p.run a).out = a.out ∧ (p.run a).inp = a.inp ∧ (p.run a).bits = a.bits := by
  intro p
  induction p with
  | skip => intros; exact ⟨rfl, rfl, rfl⟩
  | seq p q ihp ihq =>
      intro h a
      have h1 := ihp h.1 a
      have h2 := ihq h.2 (p.run a)
      exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩
  | emit _ => intro h; exact absurd h id
  | emitVar _ _ => intro h; exact absurd h id
  | addConst _ _ => intros; exact ⟨rfl, rfl, rfl⟩
  | subConst _ _ => intros; exact ⟨rfl, rfl, rfl⟩
  | addReg _ _ => intros; exact ⟨rfl, rfl, rfl⟩
  | subReg _ _ => intros; exact ⟨rfl, rfl, rfl⟩
  | clr _ => intros; exact ⟨rfl, rfl, rfl⟩
  | forLoop cnt body ih =>
      intro h a
      have key : ∀ j (b : AS), (body.run^[j] b).out = b.out ∧ (body.run^[j] b).inp = b.inp ∧
          (body.run^[j] b).bits = b.bits := by
        intro j
        induction j with
        | zero => intro b; exact ⟨rfl, rfl, rfl⟩
        | succ j ihj =>
            intro b
            rw [Function.iterate_succ_apply]
            have h1 := ihj (body.run b)
            have h2 := ih h b
            exact ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩
      exact key _ a
  | forBits _ _ _ _ => intro h; exact absurd h id
  | countBits _ => intro h; exact absurd h id

theorem forLoop_inv (cnt : ℕ) (body : FP) (a : AS) (Inv : ℕ → AS → Prop) (h0 : Inv 0 a)
    (hs : ∀ j < a.reg cnt, ∀ b, Inv j b → Inv (j + 1) (body.run b)) :
    Inv (a.reg cnt) ((FP.forLoop cnt body).run a) := by
  have key : ∀ j ≤ a.reg cnt, Inv j (body.run^[j] a) := by
    intro j
    induction j with
    | zero => intro _; exact h0
    | succ j ih =>
        intro hj
        rw [Function.iterate_succ_apply']
        exact hs j (by omega) _ (ih (by omega))
  exact key _ le_rfl

/-- Sequence of a list of programs. -/
def seqL : List FP → FP
  | [] => .skip
  | p :: l => .seq p (seqL l)

/-- `f 0; f 1; ...; f (n-1)`. -/
def forK : ℕ → (ℕ → FP) → FP
  | 0, _ => .skip
  | n + 1, f => .seq (forK n f) (f n)

theorem forK_inv (n : ℕ) (f : ℕ → FP) (a : AS) (Inv : ℕ → AS → Prop) (h0 : Inv 0 a)
    (hs : ∀ k < n, ∀ b, Inv k b → Inv (k + 1) ((f k).run b)) :
    Inv n ((forK n f).run a) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
      have := ih (fun k hk b hb => hs k (by omega) b hb)
      exact hs n (by omega) _ this

theorem forK_writes (n : ℕ) (f : ℕ → FP) (r : ℕ) :
    (forK n f).writes r ↔ ∃ k < n, (f k).writes r := by
  induction n with
  | zero => simp [forK, FP.writes]
  | succ n ih =>
      simp only [forK, FP.writes, ih]
      constructor
      · rintro (⟨k, hk, h⟩ | h)
        · exact ⟨k, by omega, h⟩
        · exact ⟨n, by omega, h⟩
      · rintro ⟨k, hk, h⟩
        by_cases hkn : k < n
        · exact Or.inl ⟨k, hkn, h⟩
        · have : k = n := by omega
          subst this; exact Or.inr h

theorem forK_pure (n : ℕ) (f : ℕ → FP) (h : ∀ k < n, (f k).pure) : (forK n f).pure := by
  induction n with
  | zero => simp [forK, FP.pure]
  | succ n ih =>
      simp only [forK, FP.pure]
      exact ⟨ih (fun k hk => h k (by omega)), h n (by omega)⟩

theorem repeatFP_writes (n : ℕ) (p : FP) (r : ℕ) :
    (repeatFP n p).writes r ↔ (0 < n ∧ p.writes r) := by
  induction n with
  | zero => simp [repeatFP, FP.writes]
  | succ n ih =>
      simp only [repeatFP, FP.writes, ih]
      constructor
      · rintro (h | ⟨_, h⟩)
        · exact ⟨by omega, h⟩
        · exact ⟨by omega, h⟩
      · rintro ⟨_, h⟩; exact Or.inl h

theorem repeatFP_pure (n : ℕ) (p : FP) (h : p.pure) : (repeatFP n p).pure := by
  induction n with
  | zero => simp [repeatFP, FP.pure]
  | succ n ih => simp only [repeatFP, FP.pure]; exact ⟨h, ih⟩

theorem iter_addReg_eq {r s : ℕ} (h : r ≠ s) (j : ℕ) (b : AS) :
    (FP.addReg r s).run^[j] b =
      { b with reg := Function.update b.reg r (b.reg r + j * b.reg s) } := by
  induction j generalizing b with
  | zero => cases b; simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih b]
      simp [run_addReg', Function.update_of_ne (Ne.symm h), Nat.succ_mul, Nat.add_assoc]

theorem run_setConst_repeat {r s : ℕ} (h : r ≠ s) (Q k : ℕ) (b : AS) :
    (FP.seq (setConst r Q) (repeatFP k (.addReg r s))).run b =
      { b with reg := Function.update b.reg r (Q + k * b.reg s) } := by
  rw [run_seq', run_repeat, iter_addReg_eq h, run_setConst]
  simp [Function.update_of_ne (Ne.symm h)]

theorem run_setReg_const_repeat {r s t : ℕ} (h : r ≠ s) (h' : r ≠ t) (Q k : ℕ) (b : AS) :
    (FP.seq (setReg r t) (FP.seq (.addConst r Q) (repeatFP k (.addReg r s)))).run b =
      { b with reg := Function.update b.reg r (b.reg t + Q + k * b.reg s) } := by
  rw [run_seq', run_seq', run_setReg h', run_addConst', run_repeat, iter_addReg_eq h]
  simp [Function.update_of_ne (Ne.symm h), Nat.add_assoc]

namespace CM

variable (cm : CM)

/-- Set the frame registers to time 0. -/
def frameInit : FP :=
  .seq (.clr 0)
    (.seq (forK cm.K fun k => .seq (setConst (1 + k) cm.Q) (repeatFP k (.addReg (1 + k) cm.rL)))
      (.seq (setReg (cm.K + 1) cm.rFR)
        (forK cm.K fun k => .seq (setReg (cm.K + 2 + k) cm.rFR)
          (.seq (.addConst (cm.K + 2 + k) cm.Q) (repeatFP k (.addReg (cm.K + 2 + k) cm.rL))))))

theorem frameInit_pure : cm.frameInit.pure := by
  unfold frameInit
  refine ⟨trivial, forK_pure _ _ ?_, ?_, forK_pure _ _ ?_⟩
  · intro k _
    simp only [setConst, FP.pure, true_and]
    exact repeatFP_pure _ _ trivial
  · simp [setReg, FP.pure]
  · intro k _
    simp only [setReg, FP.pure, true_and]
    exact repeatFP_pure _ _ trivial

theorem frameInit_writes (r : ℕ) (hr : cm.frameInit.writes r) :
    r = 0 ∨ (∃ k < cm.K, r = 1 + k) ∨ r = cm.K + 1 ∨ (∃ k < cm.K, r = cm.K + 2 + k) := by
  unfold frameInit at hr
  simp only [FP.writes, forK_writes, setConst, setReg, repeatFP_writes] at hr
  rcases hr with h | ⟨k, hk, h⟩ | h | ⟨k, hk, h⟩
  · exact Or.inl h.symm
  · right; left; refine ⟨k, hk, ?_⟩
    rcases h with (h | h) | ⟨_, h⟩ <;> omega
  · right; right; left
    rcases h with h | h <;> omega
  · right; right; right; refine ⟨k, hk, ?_⟩
    rcases h with (h | h) | ⟨_, h⟩ <;> omega

theorem run_frameInit (a : AS) :
    (cm.frameInit.run a).reg 0 = 0 ∧
    (∀ k < cm.K, (cm.frameInit.run a).reg (1 + k) = cm.Q + k * a.reg cm.rL) ∧
    (cm.frameInit.run a).reg (cm.K + 1) = a.reg cm.rFR ∧
    (∀ k < cm.K, (cm.frameInit.run a).reg (cm.K + 2 + k) =
      a.reg cm.rFR + cm.Q + k * a.reg cm.rL) ∧
    (cm.frameInit.run a).reg cm.rL = a.reg cm.rL ∧
    (cm.frameInit.run a).reg cm.rFR = a.reg cm.rFR := by
  have hL : cm.rL = 2 * cm.K + 7 := rfl
  have hF : cm.rFR = 2 * cm.K + 6 := rfl
  have e0 : cm.frameInit.run a = (forK cm.K fun k => FP.seq (setReg (cm.K + 2 + k) cm.rFR)
      (FP.seq (FP.addConst (cm.K + 2 + k) cm.Q) (repeatFP k (FP.addReg (cm.K + 2 + k) cm.rL)))).run
        ((setReg (cm.K + 1) cm.rFR).run ((forK cm.K fun k => FP.seq (setConst (1 + k) cm.Q)
          (repeatFP k (FP.addReg (1 + k) cm.rL))).run ((FP.clr 0).run a))) := rfl
  -- first loop
  have P1 := forK_inv cm.K (fun k => FP.seq (setConst (1 + k) cm.Q)
      (repeatFP k (FP.addReg (1 + k) cm.rL))) ((FP.clr 0).run a)
    (fun k b => b.reg cm.rL = a.reg cm.rL ∧ b.reg cm.rFR = a.reg cm.rFR ∧ b.reg 0 = 0 ∧
      ∀ k' < k, b.reg (1 + k') = cm.Q + k' * a.reg cm.rL)
    (by simp [run_clr', hL, hF])
    (by
      intro k hk b ⟨h1, h2, h3, h4⟩
      rw [run_setConst_repeat (by omega) cm.Q k b]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Function.update_of_ne (show cm.rL ≠ 1 + k by omega), h1]
      · simp [Function.update_of_ne (show cm.rFR ≠ 1 + k by omega), h2]
      · simp [Function.update_of_ne (show (0 : ℕ) ≠ 1 + k by omega), h3]
      · intro k' hk'
        by_cases hkk : k' = k
        · subst hkk; simp [h1]
        · simp [Function.update_of_ne (show 1 + k' ≠ 1 + k by omega), h4 k' (by omega)])
  obtain ⟨q1, q2, q3, q4⟩ := P1
  -- second loop
  rw [e0]
  have P2 := forK_inv cm.K (fun k => FP.seq (setReg (cm.K + 2 + k) cm.rFR)
      (FP.seq (FP.addConst (cm.K + 2 + k) cm.Q) (repeatFP k (FP.addReg (cm.K + 2 + k) cm.rL))))
    ((setReg (cm.K + 1) cm.rFR).run ((forK cm.K fun k => FP.seq (setConst (1 + k) cm.Q)
      (repeatFP k (FP.addReg (1 + k) cm.rL))).run ((FP.clr 0).run a)))
    (fun k b => b.reg cm.rL = a.reg cm.rL ∧ b.reg cm.rFR = a.reg cm.rFR ∧ b.reg 0 = 0 ∧
      (∀ k' < cm.K, b.reg (1 + k') = cm.Q + k' * a.reg cm.rL) ∧
      b.reg (cm.K + 1) = a.reg cm.rFR ∧
      ∀ k' < k, b.reg (cm.K + 2 + k') = a.reg cm.rFR + cm.Q + k' * a.reg cm.rL)
    (by
      rw [run_setReg (show cm.K + 1 ≠ cm.rFR by omega)]
      refine ⟨?_, ?_, ?_, ?_, ?_, fun k' hk' => absurd hk' (by omega)⟩
      · simp [Function.update_of_ne (show cm.rL ≠ cm.K + 1 by omega), q1]
      · simp [Function.update_of_ne (show cm.rFR ≠ cm.K + 1 by omega), q2]
      · simp [Function.update_of_ne (show (0 : ℕ) ≠ cm.K + 1 by omega), q3]
      · intro k' hk'
        simp [Function.update_of_ne (show 1 + k' ≠ cm.K + 1 by omega), q4 k' hk']
      · simp [q2])
    (by
      intro k hk b ⟨h1, h2, h3, h4, h5, h6⟩
      rw [run_setReg_const_repeat (show cm.K + 2 + k ≠ cm.rL by omega)
        (show cm.K + 2 + k ≠ cm.rFR by omega) cm.Q k b]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Function.update_of_ne (show cm.rL ≠ cm.K + 2 + k by omega), h1]
      · simp [Function.update_of_ne (show cm.rFR ≠ cm.K + 2 + k by omega), h2]
      · simp [Function.update_of_ne (show (0 : ℕ) ≠ cm.K + 2 + k by omega), h3]
      · intro k' hk'
        simp [Function.update_of_ne (show 1 + k' ≠ cm.K + 2 + k by omega), h4 k' hk']
      · simp [Function.update_of_ne (show cm.K + 1 ≠ cm.K + 2 + k by omega), h5]
      · intro k' hk'
        by_cases hkk : k' = k
        · subst hkk; simp [h2, h1]
        · simp [Function.update_of_ne (show cm.K + 2 + k' ≠ cm.K + 2 + k by omega),
            h6 k' (by omega)])
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := P2
  exact ⟨r3, r4, r5, r6, r1, r2⟩

end CM

/-! ## Bits of constraint lists -/

/-- Bits of a list of formulas as conjuncts (each preceded by the `and` tag). -/
def consBits (l : List PropFormula) : List Bool :=
  l.flatMap fun φ => [true, false] ++ encodeFormula φ

theorem consBits_append (l l' : List PropFormula) :
    consBits (l ++ l') = consBits l ++ consBits l' := by
  simp [consBits, List.flatMap_append]

theorem consBits_flatMap {α : Type} (l : List α) (f : α → List PropFormula) :
    consBits (l.flatMap f) = l.flatMap (fun a => consBits (f a)) := by
  simp [consBits, List.flatMap_assoc]

theorem consBits_instL (V : ℕ → ℕ → ℕ) (l : List TF) :
    consBits (instL V l) = tmplBits V l := by
  simp [consBits, instL, tmplBits, List.flatMap_map]

theorem encodeFormula_conjF (l : List PropFormula) :
    encodeFormula (conjF l) = consBits l ++ encodeFormula tautSeed := by
  induction l with
  | nil => simp [conjF, consBits]
  | cons φ l ih => simp [conjF, encodeFormula, consBits, ih]

theorem encodeFormula_tabFormula (cm : CM) (W B : ℕ) (x : List Bool) :
    encodeFormula (tabFormula cm W B x) =
      [false, true] ++ (consBits (cm.consL W B x) ++ encodeFormula tautSeed) := by
  simp [tabFormula, encodeFormula, encodeFormula_conjF]

/-! ## Emission loops over the depth register -/

namespace CM

variable (cm : CM)

/-- Loop `cnt` times: emit `l` at the depth register `D`, then advance `D`. -/
def dLoop (cnt : ℕ) (l : List TF) : FP :=
  .forLoop cnt (.seq (emitTL l) (.addConst (2 * cm.K + 2) (cm.A + 1)))

theorem run_dLoop {W t k d0 M : ℕ} (hM : M ≤ 2 * cm.K + 3) (cnt : ℕ) (l : List TF)
    (hl : ∀ φ ∈ l, φ.regsLt M) (b : AS) (hF : cm.FrameRegs W t b)
    (hD : b.reg (2 * cm.K + 2) = cm.vA W t k d0 0) (hcnt : cnt ≠ 2 * cm.K + 2) :
    ((cm.dLoop cnt l).run b).out = b.out ++
      (List.range (b.reg cnt)).flatMap (fun j => tmplBits (cm.Vf W t k (d0 + j)) l) ∧
    ((cm.dLoop cnt l).run b).reg (2 * cm.K + 2) = cm.vA W t k (d0 + b.reg cnt) 0 ∧
    ((cm.dLoop cnt l).run b).inp = b.inp ∧ ((cm.dLoop cnt l).run b).bits = b.bits ∧
    ∀ r, r ≠ 2 * cm.K + 2 → ((cm.dLoop cnt l).run b).reg r = b.reg r := by
  have hAg : ∀ b' : AS, cm.FrameRegs W t b' → b'.reg (2 * cm.K + 2) = cm.vA W t k d0 0 → False ∨
      True := fun _ _ _ => Or.inr trivial
  let Inv : ℕ → AS → Prop := fun j b' =>
    cm.FrameRegs W t b' ∧ b'.reg (2 * cm.K + 2) = cm.vA W t k (d0 + j) 0 ∧
    b'.out = b.out ++ (List.range j).flatMap (fun j' => tmplBits (cm.Vf W t k (d0 + j')) l) ∧
    b'.inp = b.inp ∧ b'.bits = b.bits ∧ (∀ r, r ≠ 2 * cm.K + 2 → b'.reg r = b.reg r)
  have key : Inv (b.reg cnt) ((cm.dLoop cnt l).run b) := by
    unfold dLoop
    apply forLoop_inv
    · refine ⟨hF, by simpa using hD, by simp, rfl, rfl, fun r _ => rfl⟩
    · intro j hj b' ⟨h1, h2, h3, h4, h5, h6⟩
      have hag : cm.RegsAgree W t k (d0 + j) (2 * cm.K + 3) b' :=
        cm.agree_frame_D h1 h2
      have hag' : cm.RegsAgree W t k (d0 + j) M b' := fun r hr => hag r (by omega)
      rw [run_seq', cm.emitTL_run_agree hag' l hl, run_addConst']
      refine ⟨?_, ?_, ?_, h4, h5, ?_⟩
      · obtain ⟨f0, f1, f2, f3⟩ := h1
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [Function.update_of_ne (show (0 : ℕ) ≠ 2 * cm.K + 2 by omega), f0]
        · intro k' hk'
          simp [Function.update_of_ne (show 1 + k' ≠ 2 * cm.K + 2 by omega), f1 k' hk']
        · simp [Function.update_of_ne (show cm.K + 1 ≠ 2 * cm.K + 2 by omega), f2]
        · intro k' hk'
          simp [Function.update_of_ne (show cm.K + 2 + k' ≠ 2 * cm.K + 2 by omega), f3 k' hk']
      · have e : d0 + (j + 1) = (d0 + j) + 1 := by omega
        simp only [Function.update_self, h2, e, cm.vA_shift W t k (d0 + j) 1 0]
        ring
      · simp only [h3, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      · intro r hr
        simp [Function.update_of_ne hr, h6 r hr]
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := key
  exact ⟨k3, by simpa using k2, k4, k5, k6⟩

/-- Exactly-one constraints for the cells of stack `k` at all depths. -/
def cellLoopP (k : ℕ) : FP :=
  .seq (setReg (2 * cm.K + 2) (1 + k))
    (cm.dLoop cm.rP [exactlyOne (2 * cm.K + 2) (List.range (cm.A + 1))])

/-- Margin constraints for stack `k`. -/
def marginP (k : ℕ) : FP :=
  .seq (setReg (2 * cm.K + 2) (1 + k))
    (.seq (.forLoop cm.rN2 (.addConst (2 * cm.K + 2) (cm.A + 1)))
      (emitTL ((List.range (2 * cm.c)).map fun i =>
        TF.leaf (2 * cm.K + 2) (i * (cm.A + 1) + cm.A))))

/-- All frame constraints at the current time. -/
def frameBlockP : FP :=
  .seq (emitTL [exactlyOne 0 (List.range cm.Q)])
    (.seq (forK cm.K cm.cellLoopP) (forK cm.K cm.marginP))

theorem consBits_frameBlock (W t : ℕ) :
    consBits (cm.frameBlock W t) =
      tmplBits (cm.Vf W t 0 0) [exactlyOne 0 (List.range cm.Q)] ++
      (List.range cm.K).flatMap (fun k => (List.range W).flatMap fun d =>
        tmplBits (cm.Vf W t k d) [exactlyOne (2 * cm.K + 2) (List.range (cm.A + 1))]) ++
      (List.range cm.K).flatMap (fun k =>
        tmplBits (cm.Vf W t k (W - 2 * cm.c))
          ((List.range (2 * cm.c)).map fun i =>
            TF.leaf (2 * cm.K + 2) (i * (cm.A + 1) + cm.A))) := by
  simp [frameBlock, consBits_append, consBits_flatMap, consBits_instL]

theorem run_cellLoopP {W t : ℕ} (k : ℕ) (hk : k < cm.K) (b : AS) (hF : cm.FrameRegs W t b)
    (hP : b.reg cm.rP = W) :
    ((cm.cellLoopP k).run b).out = b.out ++ (List.range W).flatMap (fun d =>
        tmplBits (cm.Vf W t k d) [exactlyOne (2 * cm.K + 2) (List.range (cm.A + 1))]) ∧
    ((cm.cellLoopP k).run b).inp = b.inp ∧ ((cm.cellLoopP k).run b).bits = b.bits ∧
    ∀ r, r ≠ 2 * cm.K + 2 → ((cm.cellLoopP k).run b).reg r = b.reg r := by
  have hne : cm.rP ≠ 2 * cm.K + 2 := by unfold rP; omega
  have hD : (setReg (2 * cm.K + 2) (1 + k)).run b =
      { b with reg := Function.update b.reg (2 * cm.K + 2) (b.reg (1 + k)) } :=
    run_setReg (by omega) b
  have hF' : cm.FrameRegs W t ((setReg (2 * cm.K + 2) (1 + k)).run b) := by
    rw [hD]
    obtain ⟨f0, f1, f2, f3⟩ := hF
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Function.update_of_ne (show (0 : ℕ) ≠ 2 * cm.K + 2 by omega), f0]
    · intro k' hk'
      simp [Function.update_of_ne (show 1 + k' ≠ 2 * cm.K + 2 by omega), f1 k' hk']
    · simp [Function.update_of_ne (show cm.K + 1 ≠ 2 * cm.K + 2 by omega), f2]
    · intro k' hk'
      simp [Function.update_of_ne (show cm.K + 2 + k' ≠ 2 * cm.K + 2 by omega), f3 k' hk']
  have hDv : ((setReg (2 * cm.K + 2) (1 + k)).run b).reg (2 * cm.K + 2) = cm.vA W t k 0 0 := by
    rw [hD]; simp [hF.2.1 k hk]
  have hPv : ((setReg (2 * cm.K + 2) (1 + k)).run b).reg cm.rP = W := by
    rw [hD]; simp [Function.update_of_ne hne, hP]
  obtain ⟨d1, d2, d3, d4, d5⟩ := cm.run_dLoop (W := W) (t := t) (k := k) (d0 := 0)
    (M := 2 * cm.K + 3) le_rfl cm.rP [exactlyOne (2 * cm.K + 2) (List.range (cm.A + 1))]
    (by intro φ hφ; simp only [List.mem_singleton] at hφ; subst hφ
        exact regsLt_exactlyOne (by omega) _)
    ((setReg (2 * cm.K + 2) (1 + k)).run b) hF' hDv hne
  rw [hPv] at d1
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cellLoopP
    rw [run_seq', d1, hD]
    simp only [Nat.zero_add]
  · unfold cellLoopP; rw [run_seq', d3, hD]
  · unfold cellLoopP; rw [run_seq', d4, hD]
  · intro r hr
    unfold cellLoopP; rw [run_seq', d5 r hr, hD]
    simp [Function.update_of_ne hr]

theorem run_marginP {W t : ℕ} (k : ℕ) (hk : k < cm.K) (b : AS) (hF : cm.FrameRegs W t b)
    (hN : b.reg cm.rN2 = W - 2 * cm.c) :
    ((cm.marginP k).run b).out = b.out ++ tmplBits (cm.Vf W t k (W - 2 * cm.c))
        ((List.range (2 * cm.c)).map fun i =>
          TF.leaf (2 * cm.K + 2) (i * (cm.A + 1) + cm.A)) ∧
    ((cm.marginP k).run b).inp = b.inp ∧ ((cm.marginP k).run b).bits = b.bits ∧
    ∀ r, r ≠ 2 * cm.K + 2 → ((cm.marginP k).run b).reg r = b.reg r := by
  have hne : cm.rN2 ≠ 2 * cm.K + 2 := by unfold rN2; omega
  have hD : (setReg (2 * cm.K + 2) (1 + k)).run b =
      { b with reg := Function.update b.reg (2 * cm.K + 2) (b.reg (1 + k)) } :=
    run_setReg (by omega) b
  have hF' : cm.FrameRegs W t ((FP.forLoop cm.rN2 (.addConst (2 * cm.K + 2) (cm.A + 1))).run
      ((setReg (2 * cm.K + 2) (1 + k)).run b)) := by
    rw [hD, run_forLoop_addConst]
    obtain ⟨f0, f1, f2, f3⟩ := hF
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Function.update_of_ne (show (0 : ℕ) ≠ 2 * cm.K + 2 by omega), f0]
    · intro k' hk'
      simp [Function.update_of_ne (show 1 + k' ≠ 2 * cm.K + 2 by omega), f1 k' hk']
    · simp [Function.update_of_ne (show cm.K + 1 ≠ 2 * cm.K + 2 by omega), f2]
    · intro k' hk'
      simp [Function.update_of_ne (show cm.K + 2 + k' ≠ 2 * cm.K + 2 by omega), f3 k' hk']
  have hDv : ((FP.forLoop cm.rN2 (.addConst (2 * cm.K + 2) (cm.A + 1))).run
      ((setReg (2 * cm.K + 2) (1 + k)).run b)).reg (2 * cm.K + 2) =
      cm.vA W t k (W - 2 * cm.c) 0 := by
    rw [hD, run_forLoop_addConst]
    simp only [Function.update_self]
    simp [Function.update_of_ne hne, hN, hF.2.1 k hk]
    have := cm.vA_shift W t k 0 (W - 2 * cm.c) 0
    simp only [Nat.zero_add] at this
    rw [this]; ring
  have hag : cm.RegsAgree W t k (W - 2 * cm.c) (2 * cm.K + 3)
      ((FP.forLoop cm.rN2 (.addConst (2 * cm.K + 2) (cm.A + 1))).run
        ((setReg (2 * cm.K + 2) (1 + k)).run b)) := cm.agree_frame_D hF' hDv
  unfold marginP
  rw [run_seq', run_seq', cm.emitTL_run_agree hag _ ?_]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hD, run_forLoop_addConst]
    · rw [hD, run_forLoop_addConst]
    · rw [hD, run_forLoop_addConst]
    · intro r hr
      rw [hD, run_forLoop_addConst]
      simp [Function.update_of_ne hr]
  · intro φ hφ
    simp only [List.mem_map, List.mem_range] at hφ
    obtain ⟨i, _, rfl⟩ := hφ
    simp [TF.regsLt]

theorem FrameRegs_of_same {W t : ℕ} {b b' : AS} (hF : cm.FrameRegs W t b)
    (h : ∀ r, r ≠ 2 * cm.K + 2 → b'.reg r = b.reg r) : cm.FrameRegs W t b' := by
  obtain ⟨f0, f1, f2, f3⟩ := hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h 0 (by omega), f0]
  · intro k hk; rw [h _ (by omega), f1 k hk]
  · rw [h _ (by omega), f2]
  · intro k hk; rw [h _ (by omega), f3 k hk]

theorem run_frameBlockP {W t : ℕ} (b : AS) (hF : cm.FrameRegs W t b) (hP : b.reg cm.rP = W)
    (hN : b.reg cm.rN2 = W - 2 * cm.c) :
    (cm.frameBlockP.run b).out = b.out ++ consBits (cm.frameBlock W t) ∧
    (cm.frameBlockP.run b).inp = b.inp ∧ (cm.frameBlockP.run b).bits = b.bits ∧
    ∀ r, r ≠ 2 * cm.K + 2 → (cm.frameBlockP.run b).reg r = b.reg r := by
  have hP' : cm.rP ≠ 2 * cm.K + 2 := by unfold rP; omega
  have hN' : cm.rN2 ≠ 2 * cm.K + 2 := by unfold rN2; omega
  -- step 1: control exactly-one
  have hag := cm.agree_frame hF 0 0
  have e1 := cm.emitTL_run_agree hag [exactlyOne 0 (List.range cm.Q)]
    (by intro φ hφ; simp only [List.mem_singleton] at hφ; subst hφ
        exact regsLt_exactlyOne (by omega) _)
  set b₁ := (emitTL [exactlyOne 0 (List.range cm.Q)]).run b with hb₁
  have hF₁ : cm.FrameRegs W t b₁ := cm.FrameRegs_of_same hF (by intro r _; rw [e1])
  have hP₁ : b₁.reg cm.rP = W := by rw [e1]; exact hP
  have hN₁ : b₁.reg cm.rN2 = W - 2 * cm.c := by rw [e1]; exact hN
  -- step 2: the cell loops
  have P2 := forK_inv cm.K cm.cellLoopP b₁
    (fun k b' => cm.FrameRegs W t b' ∧ b'.reg cm.rP = W ∧ b'.reg cm.rN2 = W - 2 * cm.c ∧
      b'.out = b₁.out ++ (List.range k).flatMap (fun k' => (List.range W).flatMap fun d =>
        tmplBits (cm.Vf W t k' d) [exactlyOne (2 * cm.K + 2) (List.range (cm.A + 1))]) ∧
      b'.inp = b₁.inp ∧ b'.bits = b₁.bits ∧ ∀ r, r ≠ 2 * cm.K + 2 → b'.reg r = b₁.reg r)
    ⟨hF₁, hP₁, hN₁, by simp, rfl, rfl, fun r _ => rfl⟩
    (by
      intro k hk b' ⟨g1, g2, g3, g4, g5, g6, g7⟩
      obtain ⟨c1, c2, c3, c4⟩ := cm.run_cellLoopP k hk b' g1 g2
      refine ⟨cm.FrameRegs_of_same g1 c4, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [c4 _ hP', g2]
      · rw [c4 _ hN', g3]
      · rw [c1, g4]
        simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      · rw [c2, g5]
      · rw [c3, g6]
      · intro r hr; rw [c4 r hr, g7 r hr])
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := P2
  -- step 3: the margins
  have P3 := forK_inv cm.K cm.marginP ((forK cm.K cm.cellLoopP).run b₁)
    (fun k b' => cm.FrameRegs W t b' ∧ b'.reg cm.rP = W ∧ b'.reg cm.rN2 = W - 2 * cm.c ∧
      b'.out = ((forK cm.K cm.cellLoopP).run b₁).out ++ (List.range k).flatMap (fun k' =>
        tmplBits (cm.Vf W t k' (W - 2 * cm.c))
          ((List.range (2 * cm.c)).map fun i => TF.leaf (2 * cm.K + 2) (i * (cm.A + 1) + cm.A))) ∧
      b'.inp = ((forK cm.K cm.cellLoopP).run b₁).inp ∧
      b'.bits = ((forK cm.K cm.cellLoopP).run b₁).bits ∧
      ∀ r, r ≠ 2 * cm.K + 2 → b'.reg r = ((forK cm.K cm.cellLoopP).run b₁).reg r)
    ⟨q1, q2, q3, by simp, rfl, rfl, fun r _ => rfl⟩
    (by
      intro k hk b' ⟨g1, g2, g3, g4, g5, g6, g7⟩
      obtain ⟨c1, c2, c3, c4⟩ := cm.run_marginP k hk b' g1 g3
      refine ⟨cm.FrameRegs_of_same g1 c4, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [c4 _ hP', g2]
      · rw [c4 _ hN', g3]
      · rw [c1, g4]
        simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      · rw [c2, g5]
      · rw [c3, g6]
      · intro r hr; rw [c4 r hr, g7 r hr])
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := P3
  have hfin : cm.frameBlockP.run b = (forK cm.K cm.marginP).run ((forK cm.K cm.cellLoopP).run b₁) :=
    rfl
  rw [hfin]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [m4, q4, e1, consBits_frameBlock]
    simp [List.append_assoc]
  · rw [m5, q5, e1]
  · rw [m6, q6, e1]
  · intro r hr; rw [m7 r hr, q7 r hr, e1]

theorem FrameRegs_of_lt {W t : ℕ} {b b' : AS} (hF : cm.FrameRegs W t b)
    (h : ∀ r, r < 2 * cm.K + 2 → b'.reg r = b.reg r) : cm.FrameRegs W t b' := by
  obtain ⟨f0, f1, f2, f3⟩ := hF
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h 0 (by omega), f0]
  · intro k hk; rw [h _ (by omega), f1 k hk]
  · rw [h _ (by omega), f2]
  · intro k hk; rw [h _ (by omega), f3 k hk]

/-- Control update and cell update constraints of the current step. -/
def topP (k : ℕ) : FP := forK cm.c (fun d => emitTL (cm.topT k d))

/-- Deep cell update constraints for stack `k`. -/
def deepLoopP (k : ℕ) : FP :=
  .seq (setReg (2 * cm.K + 2) (1 + k)) (.seq (setReg (2 * cm.K + 3) (cm.K + 2 + k))
    (.forLoop cm.rN2 (.seq (emitTL (cm.deepT k))
      (.seq (.addConst (2 * cm.K + 2) (cm.A + 1)) (.addConst (2 * cm.K + 3) (cm.A + 1))))))

/-- All step constraints of the current time. -/
def stepBlockP : FP :=
  .seq (emitTL cm.stepCtlT) (forK cm.K (fun k => .seq (cm.topP k) (cm.deepLoopP k)))

theorem consBits_stepBlock (W t : ℕ) :
    consBits (cm.stepBlock W t) =
      tmplBits (cm.Vf W t 0 0) cm.stepCtlT ++
      (List.range cm.K).flatMap (fun k =>
        (List.range cm.c).flatMap (fun d => tmplBits (cm.Vf W t k 0) (cm.topT k d)) ++
        (List.range (W - 2 * cm.c)).flatMap (fun e => tmplBits (cm.Vf W t k e) (cm.deepT k))) := by
  simp [stepBlock, consBits_append, consBits_flatMap, consBits_instL]

theorem run_topP {W t : ℕ} (hc : 0 < cm.c) {k : ℕ} (hk : k < cm.K) (b : AS)
    (hF : cm.FrameRegs W t b) :
    ((cm.topP k).run b).out = b.out ++
      (List.range cm.c).flatMap (fun d => tmplBits (cm.Vf W t k 0) (cm.topT k d)) ∧
    ((cm.topP k).run b).reg = b.reg ∧ ((cm.topP k).run b).inp = b.inp ∧
    ((cm.topP k).run b).bits = b.bits := by
  have P := forK_inv cm.c (fun d => emitTL (cm.topT k d)) b
    (fun j b' => b'.reg = b.reg ∧ b'.inp = b.inp ∧ b'.bits = b.bits ∧
      b'.out = b.out ++ (List.range j).flatMap (fun d => tmplBits (cm.Vf W t k 0) (cm.topT k d)))
    ⟨rfl, rfl, rfl, by simp⟩
    (by
      intro j hj b' ⟨g1, g2, g3, g4⟩
      have hag : cm.RegsAgree W t k 0 (2 * cm.K + 2) b' := by
        have := cm.agree_frame hF k 0
        intro r hr; rw [g1]; exact this r hr
      rw [cm.emitTL_run_agree hag _ (cm.topT_regs hc hk j)]
      refine ⟨g1, g2, g3, ?_⟩
      simp only [g4, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc])
  obtain ⟨p1, p2, p3, p4⟩ := P
  exact ⟨p4, p1, p2, p3⟩

theorem run_deepLoopP {W t : ℕ} (hc : 0 < cm.c) {k : ℕ} (hk : k < cm.K) (b : AS)
    (hF : cm.FrameRegs W t b) (hN : b.reg cm.rN2 = W - 2 * cm.c) :
    ((cm.deepLoopP k).run b).out = b.out ++
      (List.range (W - 2 * cm.c)).flatMap (fun e => tmplBits (cm.Vf W t k e) (cm.deepT k)) ∧
    ((cm.deepLoopP k).run b).inp = b.inp ∧ ((cm.deepLoopP k).run b).bits = b.bits ∧
    ∀ r, r ≠ 2 * cm.K + 2 → r ≠ 2 * cm.K + 3 → ((cm.deepLoopP k).run b).reg r = b.reg r := by
  have hne : cm.rN2 ≠ 2 * cm.K + 2 := by unfold rN2; omega
  have hne' : cm.rN2 ≠ 2 * cm.K + 3 := by unfold rN2; omega
  have e1 : (setReg (2 * cm.K + 2) (1 + k)).run b =
      { b with reg := Function.update b.reg (2 * cm.K + 2) (b.reg (1 + k)) } :=
    run_setReg (by omega) b
  set b₁ := (setReg (2 * cm.K + 2) (1 + k)).run b with hb₁
  have e2 : (setReg (2 * cm.K + 3) (cm.K + 2 + k)).run b₁ =
      { b₁ with reg := Function.update b₁.reg (2 * cm.K + 3) (b₁.reg (cm.K + 2 + k)) } :=
    run_setReg (by omega) b₁
  set b₂ := (setReg (2 * cm.K + 3) (cm.K + 2 + k)).run b₁ with hb₂
  have hb₂reg : ∀ r, r ≠ 2 * cm.K + 2 → r ≠ 2 * cm.K + 3 → b₂.reg r = b.reg r := by
    intro r h1 h2
    rw [e2, e1]; simp [Function.update_of_ne h1, Function.update_of_ne h2]
  have hb₂out : b₂.out = b.out := by rw [e2, e1]
  have hb₂inp : b₂.inp = b.inp := by rw [e2, e1]
  have hb₂bits : b₂.bits = b.bits := by rw [e2, e1]
  have hF₂ : cm.FrameRegs W t b₂ := cm.FrameRegs_of_lt hF (fun r hr => hb₂reg r (by omega) (by omega))
  have hD₂ : b₂.reg (2 * cm.K + 2) = cm.vA W t k 0 0 := by
    rw [e2, e1]
    simp [Function.update_of_ne (show 2 * cm.K + 2 ≠ 2 * cm.K + 3 by omega), hF.2.1 k hk]
  have hD'₂ : b₂.reg (2 * cm.K + 3) = cm.vA W (t + 1) k 0 0 := by
    rw [e2, e1]
    simp [Function.update_of_ne (show cm.K + 2 + k ≠ 2 * cm.K + 2 by omega), hF.2.2.2 k hk]
  have hN₂ : b₂.reg cm.rN2 = W - 2 * cm.c := by rw [hb₂reg _ hne hne']; exact hN
  have P := forLoop_inv cm.rN2 (FP.seq (emitTL (cm.deepT k))
      (FP.seq (FP.addConst (2 * cm.K + 2) (cm.A + 1)) (FP.addConst (2 * cm.K + 3) (cm.A + 1))))
    b₂
    (fun j b' => cm.FrameRegs W t b' ∧ b'.reg (2 * cm.K + 2) = cm.vA W t k j 0 ∧
      b'.reg (2 * cm.K + 3) = cm.vA W (t + 1) k j 0 ∧
      b'.out = b.out ++ (List.range j).flatMap (fun e => tmplBits (cm.Vf W t k e) (cm.deepT k)) ∧
      b'.inp = b.inp ∧ b'.bits = b.bits ∧
      ∀ r, r ≠ 2 * cm.K + 2 → r ≠ 2 * cm.K + 3 → b'.reg r = b.reg r)
    ⟨hF₂, by simpa using hD₂, by simpa using hD'₂, by rw [hb₂out]; simp, hb₂inp, hb₂bits, hb₂reg⟩
    (by
      intro j hj b' ⟨h1, h2, h3, h4, h5, h6, h7⟩
      have hag := cm.agree_frame_DD h1 h2 h3
      rw [run_seq', cm.emitTL_run_agree hag _ (cm.deepT_regs hc k), run_seq', run_addConst',
        run_addConst']
      refine ⟨?_, ?_, ?_, ?_, h5, h6, ?_⟩
      · refine cm.FrameRegs_of_lt h1 (fun r hr => ?_)
        simp [Function.update_of_ne (show r ≠ 2 * cm.K + 3 by omega),
          Function.update_of_ne (show r ≠ 2 * cm.K + 2 by omega)]
      · simp [Function.update_of_ne (show 2 * cm.K + 2 ≠ 2 * cm.K + 3 by omega), h2,
          cm.vA_shift W t k j 1 0]
      · simp [h3, cm.vA_shift W (t + 1) k j 1 0]
      · simp only [h4, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      · intro r hr1 hr2
        simp [Function.update_of_ne hr1, Function.update_of_ne hr2, h7 r hr1 hr2])
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := P
  rw [hN₂] at p4 p2 p3
  unfold deepLoopP
  rw [run_seq', run_seq']
  refine ⟨?_, p5, p6, p7⟩
  rw [← hb₁, ← hb₂]
  exact p4

theorem run_stepBlockP {W t : ℕ} (hc : 0 < cm.c) (b : AS) (hF : cm.FrameRegs W t b)
    (hN : b.reg cm.rN2 = W - 2 * cm.c) :
    (cm.stepBlockP.run b).out = b.out ++ consBits (cm.stepBlock W t) ∧
    (cm.stepBlockP.run b).inp = b.inp ∧ (cm.stepBlockP.run b).bits = b.bits ∧
    ∀ r, r ≠ 2 * cm.K + 2 → r ≠ 2 * cm.K + 3 → (cm.stepBlockP.run b).reg r = b.reg r := by
  have hne : cm.rN2 ≠ 2 * cm.K + 2 := by unfold rN2; omega
  have hne' : cm.rN2 ≠ 2 * cm.K + 3 := by unfold rN2; omega
  have hag := cm.agree_frame hF 0 0
  have e1 := cm.emitTL_run_agree hag cm.stepCtlT
    (fun φ hφ => TF.regsLt_mono (by omega) φ (cm.stepCtlT_regs hc φ hφ))
  set b₁ := (emitTL cm.stepCtlT).run b with hb₁
  have hF₁ : cm.FrameRegs W t b₁ := cm.FrameRegs_of_lt hF (by intro r _; rw [e1])
  have hN₁ : b₁.reg cm.rN2 = W - 2 * cm.c := by rw [e1]; exact hN
  have P := forK_inv cm.K (fun k => FP.seq (cm.topP k) (cm.deepLoopP k)) b₁
    (fun k b' => cm.FrameRegs W t b' ∧ b'.reg cm.rN2 = W - 2 * cm.c ∧
      b'.out = b₁.out ++ (List.range k).flatMap (fun k' =>
        (List.range cm.c).flatMap (fun d => tmplBits (cm.Vf W t k' 0) (cm.topT k' d)) ++
        (List.range (W - 2 * cm.c)).flatMap (fun e => tmplBits (cm.Vf W t k' e) (cm.deepT k'))) ∧
      b'.inp = b₁.inp ∧ b'.bits = b₁.bits ∧
      ∀ r, r ≠ 2 * cm.K + 2 → r ≠ 2 * cm.K + 3 → b'.reg r = b₁.reg r)
    ⟨hF₁, hN₁, by simp, rfl, rfl, fun r _ _ => rfl⟩
    (by
      intro k hk b' ⟨g1, g2, g3, g4, g5, g6⟩
      obtain ⟨t1, t2, t3, t4⟩ := cm.run_topP hc hk b' g1
      set b'' := (cm.topP k).run b' with hb''
      have hF'' : cm.FrameRegs W t b'' := by
        refine cm.FrameRegs_of_lt g1 (fun r _ => ?_); rw [t2]
      have hN'' : b''.reg cm.rN2 = W - 2 * cm.c := by rw [t2]; exact g2
      obtain ⟨d1, d2, d3, d4⟩ := cm.run_deepLoopP hc hk b'' hF'' hN''
      rw [run_seq']
      refine ⟨cm.FrameRegs_of_lt hF'' (fun r hr => d4 r (by omega) (by omega)), ?_, ?_, ?_, ?_, ?_⟩
      · rw [d4 _ hne hne', t2]; exact g2
      · rw [d1, t1, g3]
        simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      · rw [d2, t3, g4]
      · rw [d3, t4, g5]
      · intro r hr1 hr2; rw [d4 r hr1 hr2, t2, g6 r hr1 hr2])
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := P
  have hfin : cm.stepBlockP.run b = (forK cm.K (fun k => FP.seq (cm.topP k) (cm.deepLoopP k))).run b₁ :=
    rfl
  rw [hfin]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [q3, e1, consBits_stepBlock]
    simp [List.append_assoc]
  · rw [q4, e1]
  · rw [q5, e1]
  · intro r hr1 hr2; rw [q6 r hr1 hr2, e1]

/-- Advance all frame registers by one frame. -/
def advanceP : FP :=
  seqL ((List.range (2 * cm.K + 2)).map fun r => FP.addReg r cm.rFR)

theorem run_addRegs (F : ℕ) (l : List ℕ) (hnd : l.Nodup) (hF : ∀ r ∈ l, r ≠ F) (b : AS) :
    ((seqL (l.map fun r => FP.addReg r F)).run b).out = b.out ∧
    ((seqL (l.map fun r => FP.addReg r F)).run b).inp = b.inp ∧
    ((seqL (l.map fun r => FP.addReg r F)).run b).bits = b.bits ∧
    ∀ x, ((seqL (l.map fun r => FP.addReg r F)).run b).reg x =
      b.reg x + (if x ∈ l then b.reg F else 0) := by
  induction l generalizing b with
  | nil => simp [seqL, FP.run]
  | cons r l ih =>
      have hr : r ≠ F := hF r (by simp)
      have hrl : r ∉ l := (List.nodup_cons.1 hnd).1
      have hl : l.Nodup := (List.nodup_cons.1 hnd).2
      obtain ⟨i1, i2, i3, i4⟩ := ih hl (fun x hx => hF x (by simp [hx]))
        ((FP.addReg r F).run b)
      simp only [List.map_cons, seqL, run_seq']
      refine ⟨i1, i2, i3, ?_⟩
      intro x
      rw [i4 x]
      by_cases hxr : x = r
      · subst hxr; simp [run_addReg', hrl, Function.update_of_ne (Ne.symm hr)]
      · by_cases hxl : x ∈ l
        · simp [run_addReg', hxl, hxr, Function.update_of_ne (Ne.symm hr), Function.update_of_ne hxr]
        · simp [run_addReg', hxl, hxr, Function.update_of_ne hxr]

theorem run_advanceP {W t : ℕ} (b : AS) (hF : cm.FrameRegs W t b)
    (hFr : b.reg cm.rFR = cm.Fr W) :
    cm.FrameRegs W (t + 1) (cm.advanceP.run b) ∧
    (cm.advanceP.run b).out = b.out ∧ (cm.advanceP.run b).inp = b.inp ∧
    (cm.advanceP.run b).bits = b.bits ∧
    ∀ r, 2 * cm.K + 2 ≤ r → (cm.advanceP.run b).reg r = b.reg r := by
  have hnd : (List.range (2 * cm.K + 2)).Nodup := List.nodup_range
  have hne : ∀ r ∈ List.range (2 * cm.K + 2), r ≠ cm.rFR := by
    intro r hr; simp only [List.mem_range] at hr; unfold rFR; omega
  obtain ⟨a1, a2, a3, a4⟩ := run_addRegs cm.rFR _ hnd hne b
  unfold advanceP
  refine ⟨?_, a1, a2, a3, ?_⟩
  · obtain ⟨f0, f1, f2, f3⟩ := hF
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [a4]; simp [f0, hFr]; ring
    · intro k hk
      rw [a4]
      have : 1 + k < 2 * cm.K + 2 := by omega
      simp [this, f1 k hk, hFr, vA]; ring
    · rw [a4]
      have : cm.K + 1 < 2 * cm.K + 2 := by omega
      simp [this, f2, hFr]; ring
    · intro k hk
      rw [a4]
      have : cm.K + 2 + k < 2 * cm.K + 2 := by omega
      simp [this, f3 k hk, hFr, vA]; ring
  · intro r hr
    rw [a4]; simp [show ¬ r < 2 * cm.K + 2 by omega]

/-- One iteration of the time loop. -/
def mainBody : FP := .seq cm.frameBlockP (.seq cm.stepBlockP cm.advanceP)

/-- The time loop and the last frame block. -/
def mainP : FP := .seq (.forLoop cm.rP cm.mainBody) cm.frameBlockP

theorem run_mainP {W : ℕ} (hc : 0 < cm.c) (b : AS) (hF : cm.FrameRegs W 0 b)
    (hP : b.reg cm.rP = W) (hN : b.reg cm.rN2 = W - 2 * cm.c) (hFr : b.reg cm.rFR = cm.Fr W) :
    (cm.mainP.run b).out = b.out ++ consBits (cm.mainL W W) ∧
    (cm.mainP.run b).inp = b.inp ∧ (cm.mainP.run b).bits = b.bits ∧
    cm.FrameRegs W W (cm.mainP.run b) ∧
    ∀ r, 2 * cm.K + 4 ≤ r → (cm.mainP.run b).reg r = b.reg r := by
  have hP' : cm.rP ≠ 2 * cm.K + 2 := by unfold rP; omega
  have hN' : cm.rN2 ≠ 2 * cm.K + 2 := by unfold rN2; omega
  have hFr' : cm.rFR ≠ 2 * cm.K + 2 := by unfold rFR; omega
  have P := forLoop_inv cm.rP cm.mainBody b
    (fun j b' => cm.FrameRegs W j b' ∧ b'.reg cm.rP = W ∧ b'.reg cm.rN2 = W - 2 * cm.c ∧
      b'.reg cm.rFR = cm.Fr W ∧
      b'.out = b.out ++ consBits ((List.range j).flatMap fun t =>
        cm.frameBlock W t ++ cm.stepBlock W t) ∧
      b'.inp = b.inp ∧ b'.bits = b.bits ∧ ∀ r, 2 * cm.K + 4 ≤ r → b'.reg r = b.reg r)
    ⟨hF, hP, hN, hFr, by simp [consBits], rfl, rfl, fun r _ => rfl⟩
    (by
      intro j hj b' ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩
      obtain ⟨f1, f2, f3, f4⟩ := cm.run_frameBlockP b' g1 g2 g3
      set b₁ := cm.frameBlockP.run b' with hb₁
      have hF₁ : cm.FrameRegs W j b₁ := cm.FrameRegs_of_same g1 f4
      have hN₁ : b₁.reg cm.rN2 = W - 2 * cm.c := by rw [f4 _ hN']; exact g3
      obtain ⟨s1, s2, s3, s4⟩ := cm.run_stepBlockP hc b₁ hF₁ hN₁
      set b₂ := cm.stepBlockP.run b₁ with hb₂
      have hF₂ : cm.FrameRegs W j b₂ := cm.FrameRegs_of_lt hF₁ (fun r hr => s4 r (by omega) (by omega))
      have hFr₂ : b₂.reg cm.rFR = cm.Fr W := by
        rw [s4 _ (by unfold rFR; omega) (by unfold rFR; omega), f4 _ hFr']; exact g4
      obtain ⟨a1, a2, a3, a4, a5⟩ := cm.run_advanceP b₂ hF₂ hFr₂
      have hmain : cm.mainBody.run b' = cm.advanceP.run b₂ := rfl
      rw [hmain]
      refine ⟨a1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [a5 _ (by unfold rP; omega), s4 _ (by unfold rP; omega) (by unfold rP; omega),
          f4 _ hP']; exact g2
      · rw [a5 _ (by unfold rN2; omega), s4 _ (by unfold rN2; omega) (by unfold rN2; omega),
          f4 _ hN']; exact g3
      · rw [a5 _ (by unfold rFR; omega)]; exact hFr₂
      · rw [a2, s1, f1, g5, List.range_succ, List.flatMap_append, consBits_append]
        simp [consBits_append, List.append_assoc]
      · rw [a3, s2, f2, g6]
      · rw [a4, s3, f3, g7]
      · intro r hr
        rw [a5 r (by omega), s4 r (by omega) (by omega), f4 r (by omega), g8 r hr])
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := P
  rw [hP] at p1 p5
  have hfinal := cm.run_frameBlockP ((FP.forLoop cm.rP cm.mainBody).run b) p1 p2 p3
  obtain ⟨z1, z2, z3, z4⟩ := hfinal
  have hmp : cm.mainP.run b = cm.frameBlockP.run ((FP.forLoop cm.rP cm.mainBody).run b) := rfl
  rw [hmp]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [z1, p5]
    simp only [mainL, consBits_append]
    simp [List.append_assoc]
  · rw [z2, p6]
  · rw [z3, p7]
  · exact cm.FrameRegs_of_same p1 z4
  · intro r hr; rw [z4 r (by omega), p8 r hr]

/-! ### The initial constraints -/

/-- Loop body for one input bit (the input is processed from its last bit down). -/
def xBody (bit : Bool) : FP :=
  .seq (.subConst (2 * cm.K + 2) (2 * (cm.A + 1)))
    (emitTL [TF.leaf (2 * cm.K + 2) (cm.inSym true),
             TF.leaf (2 * cm.K + 2) ((cm.A + 1) + cm.inSym bit)])

/-- Bits of the input cell constraints for the remaining bit list `l`. -/
def blocksOf (W : ℕ) : List Bool → List Bool
  | [] => []
  | b :: r =>
      tmplBits (cm.Vf W 0 cm.kin (2 * r.length))
        [TF.leaf (2 * cm.K + 2) (cm.inSym true),
         TF.leaf (2 * cm.K + 2) ((cm.A + 1) + cm.inSym b)] ++ blocksOf W r

theorem blocksOf_eq (W : ℕ) (l : List Bool) :
    cm.blocksOf W l = (List.range l.length).reverse.flatMap (fun i =>
      tmplBits (cm.Vf W 0 cm.kin (2 * i))
        [TF.leaf (2 * cm.K + 2) (cm.inSym true),
         TF.leaf (2 * cm.K + 2) ((cm.A + 1) + cm.inSym (l.reverse.getD i false))]) := by
  induction l with
  | nil => simp [blocksOf]
  | cons b r ih =>
      simp only [blocksOf, ih, List.length_cons, List.range_succ, List.reverse_append,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
        List.flatMap_cons]
      congr 1
      · simp [List.getD_eq_getElem?_getD]
      · apply List.flatMap_congr
        intro i hi
        simp only [List.mem_reverse, List.mem_range] at hi
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hi]

theorem run_xBody {W : ℕ} (hkin : cm.kin < cm.K) (bit : Bool) (n : ℕ) (b : AS)
    (hF : cm.FrameRegs W 0 b) (hD : b.reg (2 * cm.K + 2) = cm.vA W 0 cm.kin (2 * (n + 1)) 0) :
    ((cm.xBody bit).run b).out = b.out ++ tmplBits (cm.Vf W 0 cm.kin (2 * n))
        [TF.leaf (2 * cm.K + 2) (cm.inSym true),
         TF.leaf (2 * cm.K + 2) ((cm.A + 1) + cm.inSym bit)] ∧
    ((cm.xBody bit).run b).inp = b.inp ∧ ((cm.xBody bit).run b).bits = b.bits ∧
    ((cm.xBody bit).run b).reg (2 * cm.K + 2) = cm.vA W 0 cm.kin (2 * n) 0 ∧
    ∀ r, r ≠ 2 * cm.K + 2 → ((cm.xBody bit).run b).reg r = b.reg r := by
  have hD1 := run_subConst' (2 * cm.K + 2) (2 * (cm.A + 1)) b
  set b₁ := (FP.subConst (2 * cm.K + 2) (2 * (cm.A + 1))).run b with hb₁
  have hDv : b₁.reg (2 * cm.K + 2) = cm.vA W 0 cm.kin (2 * n) 0 := by
    rw [hD1]
    simp only [Function.update_self, hD]
    have := cm.vA_shift W 0 cm.kin (2 * n) 2 0
    have e : 2 * (n + 1) = 2 * n + 2 := by ring
    rw [e, this]
    omega
  have hF₁ : cm.FrameRegs W 0 b₁ := cm.FrameRegs_of_lt hF (by
    intro r hr; rw [hD1]; simp [Function.update_of_ne (show r ≠ 2 * cm.K + 2 by omega)])
  have hag : cm.RegsAgree W 0 cm.kin (2 * n) (2 * cm.K + 3) b₁ := cm.agree_frame_D hF₁ hDv
  have e2 := cm.emitTL_run_agree hag
    [TF.leaf (2 * cm.K + 2) (cm.inSym true), TF.leaf (2 * cm.K + 2) ((cm.A + 1) + cm.inSym bit)]
    (by intro φ hφ
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hφ
        rcases hφ with rfl | rfl <;> simp [TF.regsLt])
  unfold xBody
  rw [run_seq', e2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hD1]
  · rw [hD1]
  · rw [hD1]
  · exact hDv
  · intro r hr; rw [hD1]; simp [Function.update_of_ne hr]

theorem run_xLoop {W : ℕ} (hkin : cm.kin < cm.K) :
    ∀ (l : List Bool) (b : AS), cm.FrameRegs W 0 b → b.bits = l →
      b.reg (2 * cm.K + 2) = cm.vA W 0 cm.kin (2 * l.length) 0 →
      (forBitsAux (fun bit => if bit then (cm.xBody true).run else (cm.xBody false).run)
          l.length b).out = b.out ++ cm.blocksOf W l ∧
      (forBitsAux (fun bit => if bit then (cm.xBody true).run else (cm.xBody false).run)
          l.length b).bits = [] ∧
      (forBitsAux (fun bit => if bit then (cm.xBody true).run else (cm.xBody false).run)
          l.length b).inp = b.inp ∧
      (forBitsAux (fun bit => if bit then (cm.xBody true).run else (cm.xBody false).run)
          l.length b).reg (2 * cm.K + 2) = cm.vA W 0 cm.kin 0 0 ∧
      ∀ r, r ≠ 2 * cm.K + 2 → (forBitsAux (fun bit => if bit then (cm.xBody true).run
          else (cm.xBody false).run) l.length b).reg r = b.reg r := by
  intro l
  induction l with
  | nil =>
      intro b hF hb hD
      refine ⟨by simp [forBitsAux, blocksOf], by simpa [forBitsAux] using hb,
        by simp [forBitsAux], by simpa [forBitsAux] using hD, fun r _ => by simp [forBitsAux]⟩
  | cons bit r ih =>
      intro b hF hb hD
      simp only [List.length_cons, forBitsAux, hb]
      have hbody : ∀ bt : Bool, (if bt then (cm.xBody true).run else (cm.xBody false).run) =
          (cm.xBody bt).run := by intro bt; cases bt <;> rfl
      rw [hbody bit]
      set b₀ : AS := { b with bits := r } with hb₀
      have hF₀ : cm.FrameRegs W 0 b₀ := hF
      have hD₀ : b₀.reg (2 * cm.K + 2) = cm.vA W 0 cm.kin (2 * (r.length + 1)) 0 := by
        rw [hb₀]; simpa using hD
      obtain ⟨x1, x2, x3, x4, x5⟩ := cm.run_xBody hkin bit r.length b₀ hF₀ hD₀
      set b₁ := (cm.xBody bit).run b₀ with hb₁
      have hF₁ : cm.FrameRegs W 0 b₁ := cm.FrameRegs_of_lt hF₀ (fun r' hr' => x5 r' (by omega))
      have hbits₁ : b₁.bits = r := by rw [x3]
      obtain ⟨y1, y2, y3, y4, y5⟩ := ih b₁ hF₁ hbits₁ x4
      refine ⟨?_, y2, ?_, y4, ?_⟩
      · rw [y1, x1]; simp [blocksOf, hb₀, List.append_assoc]
      · rw [y3, x2]
      · intro r' hr'; rw [y5 r' hr', x5 r' hr']

/-- The depth register holds `vA t k dOff 0` and the frame registers are right. -/
def DAt (W t k dOff : ℕ) (b : AS) : Prop :=
  cm.FrameRegs W t b ∧ b.reg (2 * cm.K + 2) = cm.vA W t k dOff 0

theorem DAt_setD {W t : ℕ} {k : ℕ} (hk : k < cm.K) (b : AS) (hF : cm.FrameRegs W t b) :
    cm.DAt W t k 0 ((setReg (2 * cm.K + 2) (1 + k)).run b) ∧
    ((setReg (2 * cm.K + 2) (1 + k)).run b).out = b.out ∧
    ((setReg (2 * cm.K + 2) (1 + k)).run b).inp = b.inp ∧
    ((setReg (2 * cm.K + 2) (1 + k)).run b).bits = b.bits ∧
    ∀ r, r ≠ 2 * cm.K + 2 → ((setReg (2 * cm.K + 2) (1 + k)).run b).reg r = b.reg r := by
  have hD : (setReg (2 * cm.K + 2) (1 + k)).run b =
      { b with reg := Function.update b.reg (2 * cm.K + 2) (b.reg (1 + k)) } :=
    run_setReg (by omega) b
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact cm.FrameRegs_of_lt hF (by
      intro r hr; rw [hD]; simp [Function.update_of_ne (show r ≠ 2 * cm.K + 2 by omega)])
  · rw [hD]; simp [hF.2.1 k hk]
  · rw [hD]
  · rw [hD]
  · rw [hD]
  · intro r hr; rw [hD]; simp [Function.update_of_ne hr]

theorem DAt_addConst {W t k d0 : ℕ} (b : AS) (h : cm.DAt W t k d0 b) :
    cm.DAt W t k (d0 + 1) ((FP.addConst (2 * cm.K + 2) (cm.A + 1)).run b) ∧
    ((FP.addConst (2 * cm.K + 2) (cm.A + 1)).run b).out = b.out ∧
    ((FP.addConst (2 * cm.K + 2) (cm.A + 1)).run b).inp = b.inp ∧
    ((FP.addConst (2 * cm.K + 2) (cm.A + 1)).run b).bits = b.bits ∧
    ∀ r, r ≠ 2 * cm.K + 2 → ((FP.addConst (2 * cm.K + 2) (cm.A + 1)).run b).reg r = b.reg r := by
  obtain ⟨hF, hD⟩ := h
  rw [run_addConst']
  refine ⟨⟨?_, ?_⟩, rfl, rfl, rfl, ?_⟩
  · exact cm.FrameRegs_of_lt hF (by
      intro r hr; simp [Function.update_of_ne (show r ≠ 2 * cm.K + 2 by omega)])
  · simp only [Function.update_self, hD]
    rw [cm.vA_shift W t k d0 1 0]; ring
  · intro r hr; simp [Function.update_of_ne hr]

theorem DAt_forAdd {W t k d0 : ℕ} (c n e : ℕ) (b : AS) (h : cm.DAt W t k d0 b)
    (hc : b.reg c = n) :
    cm.DAt W t k (d0 + n * e) ((FP.forLoop c (.addConst (2 * cm.K + 2) (e * (cm.A + 1)))).run b) ∧
    ((FP.forLoop c (.addConst (2 * cm.K + 2) (e * (cm.A + 1)))).run b).out = b.out ∧
    ((FP.forLoop c (.addConst (2 * cm.K + 2) (e * (cm.A + 1)))).run b).inp = b.inp ∧
    ((FP.forLoop c (.addConst (2 * cm.K + 2) (e * (cm.A + 1)))).run b).bits = b.bits ∧
    ∀ r, r ≠ 2 * cm.K + 2 →
      ((FP.forLoop c (.addConst (2 * cm.K + 2) (e * (cm.A + 1)))).run b).reg r = b.reg r := by
  obtain ⟨hF, hD⟩ := h
  rw [run_forLoop_addConst]
  refine ⟨⟨?_, ?_⟩, rfl, rfl, rfl, ?_⟩
  · exact cm.FrameRegs_of_lt hF (by
      intro r hr; simp [Function.update_of_ne (show r ≠ 2 * cm.K + 2 by omega)])
  · simp only [Function.update_self, hD, hc]
    rw [cm.vA_shift W t k d0 (n * e) 0]; ring
  · intro r hr; simp [Function.update_of_ne hr]

/-- Cell value alternatives for the witness region. -/
def orT : TF :=
  .or (.leaf (2 * cm.K + 2) (cm.inSym false))
    (.or (.leaf (2 * cm.K + 2) (cm.inSym true)) (.leaf (2 * cm.K + 2) cm.A))

/-- Contiguity of blanks. -/
def contigT : TF :=
  impT (.leaf (2 * cm.K + 2) cm.A) (.leaf (2 * cm.K + 2) ((cm.A + 1) + cm.A))

/-- All initial constraints. -/
def initP : FP :=
  seqL [
    emitTL [TF.leaf 0 cm.q0],
    setReg (2 * cm.K + 2) (1 + cm.kin),
    .forLoop cm.rM (.addConst (2 * cm.K + 2) (2 * (cm.A + 1))),
    .forBits (cm.xBody false) (cm.xBody true),
    .forLoop cm.rM (.addConst (2 * cm.K + 2) (2 * (cm.A + 1))),
    emitTL [TF.leaf (2 * cm.K + 2) (cm.inSym false)],
    .addConst (2 * cm.K + 2) (cm.A + 1),
    cm.dLoop cm.rN3 [cm.orT],
    setReg (2 * cm.K + 2) (1 + cm.kin),
    .forLoop cm.rM (.addConst (2 * cm.K + 2) (2 * (cm.A + 1))),
    .addConst (2 * cm.K + 2) (cm.A + 1),
    cm.dLoop cm.rN4 [cm.contigT],
    forK cm.K (fun k => if k = cm.kin then FP.skip else
      FP.seq (setReg (2 * cm.K + 2) (1 + k))
        (cm.dLoop cm.rP [TF.leaf (2 * cm.K + 2) cm.A]))]
theorem consBits_initL (W : ℕ) (x : List Bool) :
    consBits (cm.initL W x) =
      tmplBits (cm.Vf W 0 0 0) [TF.leaf 0 cm.q0] ++
      (List.range x.length).reverse.flatMap (fun i =>
        tmplBits (cm.Vf W 0 cm.kin (2 * i))
          [TF.leaf (2 * cm.K + 2) (cm.inSym true),
           TF.leaf (2 * cm.K + 2) ((cm.A + 1) + cm.inSym (x.getD i false))]) ++
      tmplBits (cm.Vf W 0 cm.kin (2 * x.length)) [TF.leaf (2 * cm.K + 2) (cm.inSym false)] ++
      (List.range (W - (2 * x.length + 1))).flatMap (fun e =>
        tmplBits (cm.Vf W 0 cm.kin (2 * x.length + 1 + e)) [cm.orT]) ++
      (List.range (W - (2 * x.length + 2))).flatMap (fun e =>
        tmplBits (cm.Vf W 0 cm.kin (2 * x.length + 1 + e)) [cm.contigT]) ++
      (List.range cm.K).flatMap (fun k =>
        if k = cm.kin then [] else (List.range W).flatMap fun d =>
          tmplBits (cm.Vf W 0 k d) [TF.leaf (2 * cm.K + 2) cm.A]) := by
  have hif : ∀ (k : ℕ) (l : List PropFormula), consBits (if k = cm.kin then [] else l) =
      if k = cm.kin then [] else consBits l := by
    intro k l; split_ifs <;> simp [consBits]
  simp only [initL, consBits_append, consBits_flatMap, consBits_instL, hif, orT, contigT]

theorem DAt_congr {W t k d d' : ℕ} {b : AS} (h : d = d') (hb : cm.DAt W t k d b) :
    cm.DAt W t k d' b := h ▸ hb

theorem run_initP {W : ℕ} (x : List Bool) (hkin : cm.kin < cm.K) (b : AS)
    (hF : cm.FrameRegs W 0 b) (hP : b.reg cm.rP = W) (hM : b.reg cm.rM = x.length)
    (hbits : b.bits = x.reverse) (hN3 : b.reg cm.rN3 = W - (2 * x.length + 1))
    (hN4 : b.reg cm.rN4 = W - (2 * x.length + 2)) :
    (cm.initP.run b).out = b.out ++ consBits (cm.initL W x) ∧
    (cm.initP.run b).inp = b.inp ∧ (cm.initP.run b).bits = [] ∧
    ∀ r, r ≠ 2 * cm.K + 2 → (cm.initP.run b).reg r = b.reg r := by
  have hM' : cm.rM ≠ 2 * cm.K + 2 := by unfold rM; omega
  have hP' : cm.rP ≠ 2 * cm.K + 2 := by unfold rP; omega
  have hN3' : cm.rN3 ≠ 2 * cm.K + 2 := by unfold rN3; omega
  have hN4' : cm.rN4 ≠ 2 * cm.K + 2 := by unfold rN4; omega
  have hDk : 2 * cm.K + 2 ≠ 2 * cm.K + 2 → False := fun h => h rfl
  -- stage 1
  have hag := cm.agree_frame hF 0 0
  have e1 := cm.emitTL_run_agree hag [TF.leaf 0 cm.q0]
    (by intro φ hφ; simp only [List.mem_singleton] at hφ; subst hφ; simp [TF.regsLt])
  set b1 := (emitTL [TF.leaf 0 cm.q0]).run b with hb1
  have hF1 : cm.FrameRegs W 0 b1 := cm.FrameRegs_of_lt hF (by intro r _; rw [e1])
  -- stage 2
  obtain ⟨s2d, s2o, s2i, s2b, s2r⟩ := cm.DAt_setD hkin b1 hF1
  set b2 := (setReg (2 * cm.K + 2) (1 + cm.kin)).run b1 with hb2
  -- stage 3
  have hM2 : b2.reg cm.rM = x.length := by rw [s2r _ hM', e1]; exact hM
  obtain ⟨s3d, s3o, s3i, s3b, s3r⟩ := cm.DAt_forAdd cm.rM x.length 2 b2 s2d hM2
  set b3 := (FP.forLoop cm.rM (.addConst (2 * cm.K + 2) (2 * (cm.A + 1)))).run b2 with hb3
  have hb3bits : b3.bits = x.reverse := by rw [s3b, s2b, e1]; exact hbits
  -- stage 4
  have hD3 : b3.reg (2 * cm.K + 2) = cm.vA W 0 cm.kin (2 * x.reverse.length) 0 := by
    have := s3d.2
    rw [this]
    simp [List.length_reverse]; ring_nf
  obtain ⟨x1, x2, x3, x4, x5⟩ := cm.run_xLoop hkin x.reverse b3 s3d.1 hb3bits hD3
  have hfb : (FP.forBits (cm.xBody false) (cm.xBody true)).run b3 =
      forBitsAux (fun bit => if bit then (cm.xBody true).run else (cm.xBody false).run)
        x.reverse.length b3 := by
    show forBitsAux _ b3.bits.length b3 = _
    rw [hb3bits]
  have x1' : ((FP.forBits (cm.xBody false) (cm.xBody true)).run b3).out =
      b3.out ++ cm.blocksOf W x.reverse := by rw [hfb]; exact x1
  have x2' : ((FP.forBits (cm.xBody false) (cm.xBody true)).run b3).bits = [] := by
    rw [hfb]; exact x2
  have x3' : ((FP.forBits (cm.xBody false) (cm.xBody true)).run b3).inp = b3.inp := by
    rw [hfb]; exact x3
  have x4' : ((FP.forBits (cm.xBody false) (cm.xBody true)).run b3).reg (2 * cm.K + 2) =
      cm.vA W 0 cm.kin 0 0 := by rw [hfb]; exact x4
  have x5' : ∀ r, r ≠ 2 * cm.K + 2 →
      ((FP.forBits (cm.xBody false) (cm.xBody true)).run b3).reg r = b3.reg r := by
    intro r hr; rw [hfb]; exact x5 r hr
  set b4 := (FP.forBits (cm.xBody false) (cm.xBody true)).run b3 with hb4
  have hF4 : cm.FrameRegs W 0 b4 := cm.FrameRegs_of_lt s3d.1 (fun r hr => x5' r (by omega))
  have hD4 : cm.DAt W 0 cm.kin 0 b4 := ⟨hF4, x4'⟩
  -- stage 5
  have hM4 : b4.reg cm.rM = x.length := by rw [x5' _ hM', s3r _ hM']; exact hM2
  obtain ⟨s5d, s5o, s5i, s5b, s5r⟩ := cm.DAt_forAdd cm.rM x.length 2 b4 hD4 hM4
  set b5 := (FP.forLoop cm.rM (.addConst (2 * cm.K + 2) (2 * (cm.A + 1)))).run b4 with hb5
  have s5d' : cm.DAt W 0 cm.kin (2 * x.length) b5 :=
    cm.DAt_congr (by ring) s5d
  -- stage 6
  have hag6 := cm.agree_frame_D s5d'.1 s5d'.2
  have e6 := cm.emitTL_run_agree hag6 [TF.leaf (2 * cm.K + 2) (cm.inSym false)]
    (by intro φ hφ; simp only [List.mem_singleton] at hφ; subst hφ; simp [TF.regsLt])
  set b6 := (emitTL [TF.leaf (2 * cm.K + 2) (cm.inSym false)]).run b5 with hb6
  have s6d : cm.DAt W 0 cm.kin (2 * x.length) b6 :=
    ⟨cm.FrameRegs_of_lt s5d'.1 (by intro r _; rw [e6]), by rw [e6]; exact s5d'.2⟩
  -- stage 7
  obtain ⟨s7d, s7o, s7i, s7b, s7r⟩ := cm.DAt_addConst b6 s6d
  set b7 := (FP.addConst (2 * cm.K + 2) (cm.A + 1)).run b6 with hb7
  -- stage 8
  have hreg7 : ∀ r, r ≠ 2 * cm.K + 2 → b7.reg r = b.reg r := by
    intro r hr
    rw [s7r r hr, e6, s5r r hr, x5' r hr, s3r r hr, s2r r hr, e1]
  have hN3_7 : b7.reg cm.rN3 = W - (2 * x.length + 1) := by rw [hreg7 _ hN3']; exact hN3
  obtain ⟨d1, d2, d3, d4, d5⟩ := cm.run_dLoop (W := W) (t := 0) (k := cm.kin)
    (d0 := 2 * x.length + 1) (M := 2 * cm.K + 3) le_rfl cm.rN3 [cm.orT]
    (by intro φ hφ; simp only [List.mem_singleton] at hφ; subst hφ
        simp [orT, TF.regsLt])
    b7 s7d.1 s7d.2 hN3'
  set b8 := (cm.dLoop cm.rN3 [cm.orT]).run b7 with hb8
  have hF8 : cm.FrameRegs W 0 b8 := cm.FrameRegs_of_lt s7d.1 (fun r hr => d5 r (by omega))
  -- stage 9
  obtain ⟨s9d, s9o, s9i, s9b, s9r⟩ := cm.DAt_setD hkin b8 hF8
  set b9 := (setReg (2 * cm.K + 2) (1 + cm.kin)).run b8 with hb9
  have hM9 : b9.reg cm.rM = x.length := by
    rw [s9r _ hM', d5 _ hM', hreg7 _ hM']; exact hM
  -- stage 10
  obtain ⟨s10d, s10o, s10i, s10b, s10r⟩ := cm.DAt_forAdd cm.rM x.length 2 b9 s9d hM9
  set b10 := (FP.forLoop cm.rM (.addConst (2 * cm.K + 2) (2 * (cm.A + 1)))).run b9 with hb10
  -- stage 11
  obtain ⟨s11d, s11o, s11i, s11b, s11r⟩ := cm.DAt_addConst b10 s10d
  set b11 := (FP.addConst (2 * cm.K + 2) (cm.A + 1)).run b10 with hb11
  have s11d' : cm.DAt W 0 cm.kin (2 * x.length + 1) b11 := cm.DAt_congr (by ring) s11d
  -- stage 12
  have hreg11 : ∀ r, r ≠ 2 * cm.K + 2 → b11.reg r = b.reg r := by
    intro r hr
    rw [s11r r hr, s10r r hr, s9r r hr, d5 r hr, hreg7 r hr]
  have hN4_11 : b11.reg cm.rN4 = W - (2 * x.length + 2) := by rw [hreg11 _ hN4']; exact hN4
  obtain ⟨c1, c2, c3, c4, c5⟩ := cm.run_dLoop (W := W) (t := 0) (k := cm.kin)
    (d0 := 2 * x.length + 1) (M := 2 * cm.K + 3) le_rfl cm.rN4 [cm.contigT]
    (by intro φ hφ; simp only [List.mem_singleton] at hφ; subst hφ
        simp [contigT, impT, TF.regsLt])
    b11 s11d'.1 s11d'.2 hN4'
  set b12 := (cm.dLoop cm.rN4 [cm.contigT]).run b11 with hb12
  have hF12 : cm.FrameRegs W 0 b12 := cm.FrameRegs_of_lt s11d'.1 (fun r hr => c5 r (by omega))
  have hreg12 : ∀ r, r ≠ 2 * cm.K + 2 → b12.reg r = b.reg r := by
    intro r hr; rw [c5 r hr, hreg11 r hr]
  -- stage 13
  have P13 := forK_inv cm.K (fun k => if k = cm.kin then FP.skip else
      FP.seq (setReg (2 * cm.K + 2) (1 + k)) (cm.dLoop cm.rP [TF.leaf (2 * cm.K + 2) cm.A])) b12
    (fun k b' => cm.FrameRegs W 0 b' ∧ (∀ r, r ≠ 2 * cm.K + 2 → b'.reg r = b.reg r) ∧
      b'.out = b12.out ++ (List.range k).flatMap (fun k' =>
        if k' = cm.kin then [] else (List.range W).flatMap fun d =>
          tmplBits (cm.Vf W 0 k' d) [TF.leaf (2 * cm.K + 2) cm.A]) ∧
      b'.inp = b12.inp ∧ b'.bits = b12.bits)
    ⟨hF12, hreg12, by simp, rfl, rfl⟩
    (by
      intro k hk b' ⟨g1, g2, g3, g4, g5⟩
      by_cases hkk : k = cm.kin
      · subst hkk
        simp only [if_true, FP.run, List.range_succ, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.append_assoc]
        exact ⟨g1, g2, g3, g4, g5⟩
      · simp only [hkk, if_false]
        obtain ⟨t1, t2, t3, t4, t5⟩ := cm.DAt_setD hk b' g1
        have hP9 : ((setReg (2 * cm.K + 2) (1 + k)).run b').reg cm.rP = W := by
          rw [t5 _ hP', g2 _ hP']; exact hP
        obtain ⟨u1, u2, u3, u4, u5⟩ := cm.run_dLoop (W := W) (t := 0) (k := k) (d0 := 0)
          (M := 2 * cm.K + 3) le_rfl cm.rP [TF.leaf (2 * cm.K + 2) cm.A]
          (by intro φ hφ; simp only [List.mem_singleton] at hφ; subst hφ; simp [TF.regsLt])
          _ t1.1 t1.2 hP'
        rw [run_seq']
        refine ⟨cm.FrameRegs_of_lt t1.1 (fun r hr => u5 r (by omega)), ?_, ?_, ?_, ?_⟩
        · intro r hr; rw [u5 r hr, t5 r hr, g2 r hr]
        · rw [u1, t2, g3, hP9]
          simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.append_assoc, hkk, if_false, Nat.zero_add]
        · rw [u3, t3, g4]
        · rw [u4, t4, g5])
  obtain ⟨o1, o2, o3, o4, o5⟩ := P13
  -- assemble
  have hfin : cm.initP.run b = (forK cm.K (fun k => if k = cm.kin then FP.skip else
      FP.seq (setReg (2 * cm.K + 2) (1 + k)) (cm.dLoop cm.rP [TF.leaf (2 * cm.K + 2) cm.A]))).run b12 :=
    rfl
  rw [hfin]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [o3, consBits_initL]
    have hb12o : b12.out = b11.out ++ (List.range (b11.reg cm.rN4)).flatMap (fun j =>
        tmplBits (cm.Vf W 0 cm.kin (2 * x.length + 1 + j)) [cm.contigT]) := c1
    have hb8o : b8.out = b7.out ++ (List.range (b7.reg cm.rN3)).flatMap (fun j =>
        tmplBits (cm.Vf W 0 cm.kin (2 * x.length + 1 + j)) [cm.orT]) := d1
    rw [hb12o, hN4_11, s11o, s10o, s9o, hb8o, hN3_7, s7o, e6, s5o]
    rw [x1', blocksOf_eq]
    simp only [s3o, s2o, e1, List.length_reverse, List.reverse_reverse, List.append_assoc]
  · rw [o4, c3, s11i, s10i, s9i, d3, s7i, e6, s5i, x3', s3i, s2i, e1]
  · rw [o5, c4, s11b, s10b, s9b, d4, s7b, e6, s5b, x2']
  · intro r hr
    rw [o2 r hr]


/-- Loop counts: `rN2 = P - 2c`, `rN3 = P - (2m+1)`, `rN4 = P - (2m+2)`. -/
def cntInit : FP :=
  seqL [setReg cm.rN2 cm.rP, .subConst cm.rN2 (2 * cm.c),
    setReg cm.rN3 cm.rP, .forLoop cm.rM (.subConst cm.rN3 2), .subConst cm.rN3 1,
    setReg cm.rN4 cm.rN3, .subConst cm.rN4 1]

theorem run_cntInit (a : AS) :
    ((cm.cntInit).run a).reg cm.rN2 = a.reg cm.rP - 2 * cm.c ∧
    ((cm.cntInit).run a).reg cm.rN3 = a.reg cm.rP - (2 * a.reg cm.rM + 1) ∧
    ((cm.cntInit).run a).reg cm.rN4 = a.reg cm.rP - (2 * a.reg cm.rM + 2) ∧
    ((cm.cntInit).run a).out = a.out ∧ ((cm.cntInit).run a).inp = a.inp ∧
    ((cm.cntInit).run a).bits = a.bits ∧
    ∀ r, r ≠ cm.rN2 → r ≠ cm.rN3 → r ≠ cm.rN4 → ((cm.cntInit).run a).reg r = a.reg r := by
  have h23 : cm.rN2 ≠ cm.rN3 := by unfold rN2 rN3; omega
  have h24 : cm.rN2 ≠ cm.rN4 := by unfold rN2 rN4; omega
  have h34 : cm.rN3 ≠ cm.rN4 := by unfold rN3 rN4; omega
  have h2P : cm.rN2 ≠ cm.rP := by unfold rN2 rP; omega
  have h3P : cm.rN3 ≠ cm.rP := by unfold rN3 rP; omega
  have h3M : cm.rN3 ≠ cm.rM := by unfold rN3 rM; omega
  have h4P : cm.rN4 ≠ cm.rP := by unfold rN4 rP; omega
  have h4M : cm.rN4 ≠ cm.rM := by unfold rN4 rM; omega
  have h2M : cm.rN2 ≠ cm.rM := by unfold rN2 rM; omega
  simp only [cntInit, seqL, run_seq', run_setReg h2P, run_setReg h3P, run_setReg h34.symm,
    run_forLoop_subConst, run_subConst', run_skip']
  have e2 := h2P.symm
  refine ⟨?_, ?_, ?_, trivial, trivial, trivial, ?_⟩
  · simp [Function.update_apply, h23, h23.symm, h24, h24.symm, h34, h34.symm, h2P, h3P, h3M, h4P,
      h4M, h2M, h2P.symm, h3P.symm, h3M.symm, h4P.symm, h4M.symm, h2M.symm]
  · simp [Function.update_apply, h23, h23.symm, h24, h24.symm, h34, h34.symm, h2P, h3P, h3M, h4P,
      h4M, h2M, h2P.symm, h3P.symm, h3M.symm, h4P.symm, h4M.symm, h2M.symm]
    omega
  · simp [Function.update_apply, h23, h23.symm, h24, h24.symm, h34, h34.symm, h2P, h3P, h3M, h4P,
      h4M, h2M, h2P.symm, h3P.symm, h3M.symm, h4P.symm, h4M.symm, h2M.symm]
    omega
  · intro r h2 h3 h4
    simp [Function.update_apply, h2, h3, h4]

/-- The acceptance templates. -/
def accTL : List TF :=
  [disjT (((List.range cm.Q).filter fun q => cm.halt q).map fun q => TF.leaf 0 q),
   TF.leaf (1 + cm.kout) cm.outTrue, TF.leaf (1 + cm.kout) ((cm.A + 1) + cm.A)]

theorem accL_eq (W B : ℕ) : cm.accL W B = instL (cm.Vf W B cm.kout 0) cm.accTL := rfl

/-- Emit the acceptance constraints. -/
def accP : FP := emitTL cm.accTL

theorem run_accP {W : ℕ} (hk : cm.kout < cm.K) (b : AS) (hF : cm.FrameRegs W W b) :
    (cm.accP.run b).out = b.out ++ consBits (cm.accL W W) ∧
    (cm.accP.run b).inp = b.inp ∧ (cm.accP.run b).bits = b.bits ∧
    (cm.accP.run b).reg = b.reg := by
  have hag := cm.agree_frame hF cm.kout 0
  have e := cm.emitTL_run_agree hag cm.accTL (by
    intro φ hφ
    simp only [accTL, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hφ
    rcases hφ with rfl | rfl | rfl
    · refine regsLt_disjT (by omega) _ ?_
      intro ψ hψ
      simp only [List.mem_map] at hψ
      obtain ⟨q, _, rfl⟩ := hψ
      simp [TF.regsLt]
    · simp [TF.regsLt]; omega
    · simp [TF.regsLt]; omega)
  unfold accP
  rw [e, accL_eq, consBits_instL]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The whole generator. -/
def genProg (C e : ℕ) : FP :=
  seqL [cm.polyProg C e, cm.constProg, cm.cntInit, cm.frameInit, .emit [false, true], cm.initP,
    cm.mainP, cm.accP, .emit (encodeFormula tautSeed)]

theorem run_genProg (hc : 0 < cm.c) (hkin : cm.kin < cm.K) (hkout : cm.kout < cm.K)
    (C e : ℕ) (x : List Bool) :
    ((cm.genProg C e).run (AS0 x)).out =
      encodeFormula (tabFormula cm (C * (x.length + 1) ^ e) (C * (x.length + 1) ^ e) x) := by
  set P := C * (x.length + 1) ^ e with hP
  have rMne : cm.rM ≠ 2 * cm.K + 2 := by unfold rM; omega
  have rPne : cm.rP ≠ 2 * cm.K + 2 := by unfold rP; omega
  have rLne : cm.rL ≠ 2 * cm.K + 2 := by unfold rL; omega
  have rFne : cm.rFR ≠ 2 * cm.K + 2 := by unfold rFR; omega
  have rN2ne : cm.rN2 ≠ 2 * cm.K + 2 := by unfold rN2; omega
  have rN3ne : cm.rN3 ≠ 2 * cm.K + 2 := by unfold rN3; omega
  have rN4ne : cm.rN4 ≠ 2 * cm.K + 2 := by unfold rN4; omega
  simp only [genProg, seqL, run_seq']
  -- stage 1: P
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := cm.run_polyProg C e (AS0 x)
  set a1 := (cm.polyProg C e).run (AS0 x) with ha1
  have a1M : a1.reg cm.rM = x.length := by rw [p4]; rfl
  have a1P : a1.reg cm.rP = P := by rw [p5]; rfl
  have a1bits : a1.bits = x.reverse := by rw [p3]; rfl
  have a1out : a1.out = [] := by rw [p1]; rfl
  have a1inp : a1.inp = [] := p2
  have a1reg : ∀ r, r ≠ cm.rM → r ≠ cm.rU → r ≠ cm.rT → r ≠ cm.rN1 → r ≠ cm.rP → a1.reg r = 0 :=
    fun r h1 h2 h3 h4 h5 => by rw [p6 r h1 h2 h3 h4 h5]; rfl
  -- stage 2: constants
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := cm.run_constProg a1
  set a2 := (cm.constProg).run a1 with ha2
  have hrLP : cm.rL ≠ cm.rP := by unfold rL rP; omega
  have hrFP : cm.rFR ≠ cm.rP := by unfold rFR rP; omega
  have hrLM : cm.rL ≠ cm.rM := by unfold rL rM; omega
  have hrFM : cm.rFR ≠ cm.rM := by unfold rFR rM; omega
  have a2P : a2.reg cm.rP = P := by rw [q6 _ hrLP.symm hrFP.symm]; exact a1P
  have a2M : a2.reg cm.rM = x.length := by rw [q6 _ hrLM.symm hrFM.symm]; exact a1M
  have a2L : a2.reg cm.rL = (cm.A + 1) * P := by rw [q1, a1P]
  have a2F : a2.reg cm.rFR = cm.Fr P := by
    rw [q2, a1P]; unfold Fr; ring_nf
  -- stage 3: counts
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := cm.run_cntInit a2
  set a3 := (cm.cntInit).run a2 with ha3
  have hLN2 : cm.rL ≠ cm.rN2 := by unfold rL rN2; omega
  have hLN3 : cm.rL ≠ cm.rN3 := by unfold rL rN3; omega
  have hLN4 : cm.rL ≠ cm.rN4 := by unfold rL rN4; omega
  have hFN2 : cm.rFR ≠ cm.rN2 := by unfold rFR rN2; omega
  have hFN3 : cm.rFR ≠ cm.rN3 := by unfold rFR rN3; omega
  have hFN4 : cm.rFR ≠ cm.rN4 := by unfold rFR rN4; omega
  have hPN2 : cm.rP ≠ cm.rN2 := by unfold rP rN2; omega
  have hPN3 : cm.rP ≠ cm.rN3 := by unfold rP rN3; omega
  have hPN4 : cm.rP ≠ cm.rN4 := by unfold rP rN4; omega
  have hMN2 : cm.rM ≠ cm.rN2 := by unfold rM rN2; omega
  have hMN3 : cm.rM ≠ cm.rN3 := by unfold rM rN3; omega
  have hMN4 : cm.rM ≠ cm.rN4 := by unfold rM rN4; omega
  have a3L : a3.reg cm.rL = (cm.A + 1) * P := by rw [n7 _ hLN2 hLN3 hLN4]; exact a2L
  have a3F : a3.reg cm.rFR = cm.Fr P := by rw [n7 _ hFN2 hFN3 hFN4]; exact a2F
  have a3P : a3.reg cm.rP = P := by rw [n7 _ hPN2 hPN3 hPN4]; exact a2P
  have a3M : a3.reg cm.rM = x.length := by rw [n7 _ hMN2 hMN3 hMN4]; exact a2M
  have a3N2 : a3.reg cm.rN2 = P - 2 * cm.c := by rw [n1, a2P]
  have a3N3 : a3.reg cm.rN3 = P - (2 * x.length + 1) := by rw [n2, a2P, a2M]
  have a3N4 : a3.reg cm.rN4 = P - (2 * x.length + 2) := by rw [n3, a2P, a2M]
  have a3out : a3.out = [] := by rw [n4, q3, a1out]
  have a3bits : a3.bits = x.reverse := by rw [n6, q5, a1bits]
  -- stage 4: frame registers
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := cm.run_frameInit a3
  set a4 := (cm.frameInit).run a3 with ha4
  obtain ⟨u1, u2, u3⟩ := FP.run_pure cm.frameInit cm.frameInit_pure a3
  have a4reg : ∀ r, 2 * cm.K + 2 ≤ r → a4.reg r = a3.reg r := by
    intro r hr
    apply FP.run_reg_of_not_writes
    intro hw
    have := cm.frameInit_writes r hw
    rcases this with h | ⟨k, hk, h⟩ | h | ⟨k, hk, h⟩ <;> omega
  have hF4 : cm.FrameRegs P 0 a4 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [f1]; simp
    · intro k hk
      rw [f2 k hk, a3L]; unfold vA; ring
    · rw [f3, a3F]; simp
    · intro k hk
      rw [f4 k hk, a3F, a3L]; unfold vA; ring
  have a4P : a4.reg cm.rP = P := by rw [a4reg _ (by unfold rP; omega)]; exact a3P
  have a4M : a4.reg cm.rM = x.length := by rw [a4reg _ (by unfold rM; omega)]; exact a3M
  have a4N2 : a4.reg cm.rN2 = P - 2 * cm.c := by rw [a4reg _ (by unfold rN2; omega)]; exact a3N2
  have a4N3 : a4.reg cm.rN3 = P - (2 * x.length + 1) := by
    rw [a4reg _ (by unfold rN3; omega)]; exact a3N3
  have a4N4 : a4.reg cm.rN4 = P - (2 * x.length + 2) := by
    rw [a4reg _ (by unfold rN4; omega)]; exact a3N4
  have a4F : a4.reg cm.rFR = cm.Fr P := by rw [f6]; exact a3F
  -- stage 5: the outer negation
  rw [run_emit' [false, true] a4]
  set a5 : AS := { a4 with out := a4.out ++ [false, true] } with ha5
  have hF5 : cm.FrameRegs P 0 a5 := hF4
  -- stage 6: the initial constraints
  obtain ⟨i1, i2, i3, i4⟩ := cm.run_initP (W := P) x hkin a5 hF5 a4P a4M
    (by show a4.bits = _; rw [u3, a3bits]) a4N3 a4N4
  set a6 := (cm.initP).run a5 with ha6
  have hF6 : cm.FrameRegs P 0 a6 := cm.FrameRegs_of_same hF5 i4
  have a6P : a6.reg cm.rP = P := by rw [i4 _ rPne]; exact a4P
  have a6N2 : a6.reg cm.rN2 = P - 2 * cm.c := by rw [i4 _ rN2ne]; exact a4N2
  have a6F : a6.reg cm.rFR = cm.Fr P := by rw [i4 _ rFne]; exact a4F
  -- stage 7: the time loop
  obtain ⟨m1, m2, m3, m4, m5⟩ := cm.run_mainP (W := P) hc a6 hF6 a6P a6N2 a6F
  set a7 := (cm.mainP).run a6 with ha7
  -- stage 8: acceptance
  obtain ⟨c1, c2, c3, c4⟩ := cm.run_accP (W := P) hkout a7 m4
  set a8 := (cm.accP).run a7 with ha8
  rw [run_emit' (encodeFormula tautSeed) a8]
  show a8.out ++ encodeFormula tautSeed = _
  have a5out : a5.out = [false, true] := by
    show a4.out ++ [false, true] = _
    rw [u1, a3out]; simp
  rw [c1, m1, i1, a5out, encodeFormula_tabFormula]
  simp [consL, consBits_append, List.append_assoc]


end CM

end CL
end SATurday.Bridge
