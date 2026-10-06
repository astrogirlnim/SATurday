import Theory.ProofComplexity.Bridge.GeneratorCost

/-!
# Well-formedness of the generator program (Ladder Rung R5)

`FP.Ok` (registers in range, loop depth, distinct addends) and `FP.LinOK` (linear loops) for
every block of the generator, so that `fp_computes` and the static bound `top` apply.

LOG: R5 Bridge GeneratorOk module (Ok and LinOK of genProg)
-/

open SATurday.Bridge.SP

namespace SATurday.Bridge
namespace CL

/-! ## Generic combinators -/

theorem Ok_seqL (NR d : ℕ) : ∀ (l : List FP), (∀ p ∈ l, p.Ok NR d) → (seqL l).Ok NR d := by
  intro l
  induction l with
  | nil => intro _; simp [seqL, FP.Ok]
  | cons p l ih =>
      intro h
      show FP.Ok NR d (.seq p (seqL l))
      exact ⟨h p (by simp), ih (fun q hq => h q (by simp [hq]))⟩

theorem Ok_forK (NR d n : ℕ) (f : ℕ → FP) (h : ∀ k < n, (f k).Ok NR d) :
    (forK n f).Ok NR d := by
  induction n with
  | zero => simp [forK, FP.Ok]
  | succ n ih =>
      exact ⟨ih (fun k hk => h k (by omega)), h n (by omega)⟩

theorem Ok_repeat (NR d n : ℕ) (p : FP) (h : p.Ok NR d) : (repeatFP n p).Ok NR d := by
  induction n with
  | zero => simp [repeatFP, FP.Ok]
  | succ n ih => exact ⟨h, ih⟩

theorem Ok_setReg {NR d r s : ℕ} (hr : r < NR) (hs : s < NR) (hne : r ≠ s) :
    (setReg r s).Ok NR d := ⟨hr, hr, hs, hne⟩

theorem Ok_setConst {NR d r : ℕ} (n : ℕ) (hr : r < NR) : (setConst r n).Ok NR d := ⟨hr, hr⟩

theorem Ok_mulConstTo {NR d r s : ℕ} (n : ℕ) (hr : r < NR) (hs : s < NR) (hne : r ≠ s) :
    (mulConstTo r s n).Ok NR d :=
  ⟨hr, Ok_repeat NR d n (.addReg r s) ⟨hr, hs, hne⟩⟩

theorem Ok_emitTF (NR d : ℕ) : ∀ φ : TF, φ.regsLt NR → (emitTF φ).Ok NR d := by
  intro φ
  induction φ with
  | leaf r o => intro h; exact h
  | not a ih => intro h; exact ⟨trivial, ih h⟩
  | and a b iha ihb => intro h; exact ⟨trivial, iha h.1, ihb h.2⟩
  | or a b iha ihb => intro h; exact ⟨trivial, iha h.1, ihb h.2⟩

theorem Ok_emitTL (NR d : ℕ) : ∀ l : List TF, (∀ φ ∈ l, φ.regsLt NR) → (emitTL l).Ok NR d := by
  intro l
  induction l with
  | nil => intro _; simp [emitTL, FP.Ok]
  | cons φ l ih =>
      intro h
      exact ⟨trivial, Ok_emitTF NR d φ (h φ (by simp)),
        ih (fun ψ hψ => h ψ (by simp [hψ]))⟩

theorem LinOK_seqL : ∀ (l : List FP), (∀ p ∈ l, p.LinOK) → (seqL l).LinOK := by
  intro l
  induction l with
  | nil => intro _; simp [seqL, FP.LinOK]
  | cons p l ih =>
      intro h
      show FP.LinOK (.seq p (seqL l))
      exact ⟨h p (by simp), ih (fun q hq => h q (by simp [hq]))⟩

theorem LinOK_forK (n : ℕ) (f : ℕ → FP) (h : ∀ k < n, (f k).LinOK) : (forK n f).LinOK := by
  induction n with
  | zero => simp [forK, FP.LinOK]
  | succ n ih => exact ⟨ih (fun k hk => h k (by omega)), h n (by omega)⟩

theorem LinOK_repeat (n : ℕ) (p : FP) (h : p.LinOK) : (repeatFP n p).LinOK := by
  induction n with
  | zero => simp [repeatFP, FP.LinOK]
  | succ n ih => exact ⟨h, ih⟩

theorem LinOK_emitTF : ∀ φ : TF, (emitTF φ).LinOK := by
  intro φ
  induction φ with
  | leaf r o => trivial
  | not a ih => exact ⟨trivial, ih⟩
  | and a b iha ihb => exact ⟨trivial, iha, ihb⟩
  | or a b iha ihb => exact ⟨trivial, iha, ihb⟩

theorem LinOK_emitTL : ∀ l : List TF, (emitTL l).LinOK := by
  intro l
  induction l with
  | nil => simp [emitTL, FP.LinOK]
  | cons φ l ih => exact ⟨trivial, LinOK_emitTF φ, ih⟩

theorem LinW_emitTF (Wr : ℕ → Prop) : ∀ φ : TF, (emitTF φ).LinW Wr := by
  intro φ
  induction φ with
  | leaf r o => trivial
  | not a ih => exact ⟨trivial, ih⟩
  | and a b iha ihb => exact ⟨trivial, iha, ihb⟩
  | or a b iha ihb => exact ⟨trivial, iha, ihb⟩

theorem LinW_emitTL (Wr : ℕ → Prop) : ∀ l : List TF, (emitTL l).LinW Wr := by
  intro l
  induction l with
  | nil => simp [emitTL, FP.LinW]
  | cons φ l ih => exact ⟨trivial, LinW_emitTF Wr φ, ih⟩

theorem LinOK_setReg (r s : ℕ) : (setReg r s).LinOK := ⟨trivial, trivial⟩
theorem LinOK_setConst (r n : ℕ) : (setConst r n).LinOK := ⟨trivial, trivial⟩
theorem LinOK_mulConstTo (r s n : ℕ) : (mulConstTo r s n).LinOK :=
  ⟨trivial, LinOK_repeat n (.addReg r s) trivial⟩


namespace CM

variable (cm : CM)

section Pieces

variable {d : ℕ}

theorem powStep_Ok (hd : d < 3) : cm.powStep.Ok cm.nR d := by
  unfold powStep
  have h1 : cm.rN1 < cm.nR := by unfold rN1 nR; omega
  have h2 : cm.rT < cm.nR := by unfold rT nR; omega
  have h3 : cm.rU < cm.nR := by unfold rU nR; omega
  have h4 : cm.rN1 ≠ cm.rT := by unfold rN1 rT; omega
  exact ⟨h1, ⟨h3, hd, h1, h2, h4⟩, Ok_setReg h2 h1 (Ne.symm h4)⟩

theorem powStep_LinOK : cm.powStep.LinOK := by
  unfold powStep
  refine ⟨trivial, ?_, LinOK_setReg _ _⟩
  show FP.LinW (fun r => FP.writes r (FP.addReg cm.rN1 cm.rT)) (FP.addReg cm.rN1 cm.rT)
  show ¬ (FP.writes cm.rT (FP.addReg cm.rN1 cm.rT))
  show ¬ (cm.rN1 = cm.rT)
  unfold rT rN1; omega

theorem polyProg_Ok (C e : ℕ) (hd : d < 3) : (cm.polyProg C e).Ok cm.nR d := by
  unfold polyProg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show cm.rM < cm.nR; unfold rM nR; omega
  · exact Ok_setReg (by unfold rU nR; omega) (by unfold rM nR; omega) (by unfold rU rM; omega)
  · show cm.rU < cm.nR; unfold rU nR; omega
  · exact Ok_setConst _ (by unfold rT nR; omega)
  · exact Ok_repeat _ _ _ _ (cm.powStep_Ok hd)
  · exact Ok_mulConstTo _ (by unfold rP nR; omega) (by unfold rT nR; omega)
      (by unfold rP rT; omega)

theorem polyProg_LinOK (C e : ℕ) : (cm.polyProg C e).LinOK :=
  ⟨trivial, LinOK_setReg _ _, trivial, LinOK_setConst _ _,
    LinOK_repeat _ _ cm.powStep_LinOK, LinOK_mulConstTo _ _ _⟩

theorem constProg_Ok (hd : d < 3) : cm.constProg.Ok cm.nR d := by
  unfold constProg
  refine ⟨Ok_mulConstTo _ (by unfold rL nR; omega) (by unfold rP nR; omega)
    (by unfold rL rP; omega), Ok_setConst _ (by unfold rFR nR; omega),
    Ok_repeat _ _ _ (.addReg cm.rFR cm.rL) ⟨?_, ?_, ?_⟩⟩
  · unfold rFR nR; omega
  · unfold rL nR; omega
  · unfold rFR rL; omega

theorem constProg_LinOK : cm.constProg.LinOK :=
  ⟨LinOK_mulConstTo _ _ _, LinOK_setConst _ _, LinOK_repeat _ _ trivial⟩

theorem cntInit_Ok (hd : d < 3) : cm.cntInit.Ok cm.nR d := by
  unfold cntInit seqL
  have h1 : cm.rN2 < cm.nR := by unfold rN2 nR; omega
  have h2 : cm.rP < cm.nR := by unfold rP nR; omega
  have h3 : cm.rN3 < cm.nR := by unfold rN3 nR; omega
  have h4 : cm.rM < cm.nR := by unfold rM nR; omega
  have h5 : cm.rN4 < cm.nR := by unfold rN4 nR; omega
  refine ⟨Ok_setReg h1 h2 (by unfold rN2 rP; omega), h1, Ok_setReg h3 h2 (by unfold rN3 rP; omega),
    ⟨h4, hd, h3⟩, h3, Ok_setReg h5 h3 (by unfold rN4 rN3; omega), h5, trivial⟩

theorem cntInit_LinOK : cm.cntInit.LinOK := by
  unfold cntInit seqL
  exact ⟨LinOK_setReg _ _, trivial, LinOK_setReg _ _, trivial, trivial, LinOK_setReg _ _, trivial,
    trivial⟩

theorem frameInit_Ok (hd : d < 3) : cm.frameInit.Ok cm.nR d := by
  unfold frameInit
  have hL : cm.rL < cm.nR := by unfold rL nR; omega
  have hF : cm.rFR < cm.nR := by unfold rFR nR; omega
  refine ⟨(show 0 < cm.nR by unfold nR; omega), Ok_forK _ _ _ _ (fun k hk => ?_),
    Ok_setReg (r := cm.K + 1) (s := cm.rFR) (by unfold nR; omega) hF (by unfold rFR; omega),
    Ok_forK _ _ _ _ (fun k hk => ?_)⟩
  · have h1 : 1 + k < cm.nR := by unfold nR; omega
    have h2 : 1 + k ≠ cm.rL := by unfold rL; omega
    exact ⟨Ok_setConst (r := 1 + k) _ h1, Ok_repeat _ _ _ (.addReg (1 + k) cm.rL) ⟨h1, hL, h2⟩⟩
  · have h1 : cm.K + 2 + k < cm.nR := by unfold nR; omega
    have h2 : cm.K + 2 + k ≠ cm.rL := by unfold rL; omega
    have h3 : cm.K + 2 + k ≠ cm.rFR := by unfold rFR; omega
    exact ⟨Ok_setReg h1 hF h3, h1, Ok_repeat _ _ _ (.addReg (cm.K + 2 + k) cm.rL) ⟨h1, hL, h2⟩⟩

theorem frameInit_LinOK : cm.frameInit.LinOK := by
  unfold frameInit
  exact ⟨trivial, LinOK_forK _ _ (fun k _ => ⟨LinOK_setConst _ _, LinOK_repeat _ _ trivial⟩),
    LinOK_setReg _ _, LinOK_forK _ _ (fun k _ => ⟨LinOK_setReg _ _, trivial,
      LinOK_repeat _ _ trivial⟩)⟩



theorem okSet {r s : ℕ} (hr : r < cm.nR) (hs : s < cm.nR) (hne : r ≠ s) :
    (setReg r s).Ok cm.nR d := Ok_setReg hr hs hne

theorem noBits_emitTF : ∀ φ : TF, (emitTF φ).noBits := by
  intro φ
  induction φ with
  | leaf r o => trivial
  | not a ih => exact ⟨trivial, ih⟩
  | and a b iha ihb => exact ⟨trivial, iha, ihb⟩
  | or a b iha ihb => exact ⟨trivial, iha, ihb⟩

theorem noBits_emitTL : ∀ l : List TF, (emitTL l).noBits := by
  intro l
  induction l with
  | nil => simp [emitTL, FP.noBits]
  | cons φ l ih => exact ⟨trivial, noBits_emitTF φ, ih⟩

theorem dLoop_Ok (hd : d < 3) {cnt : ℕ} (hcnt : cnt < cm.nR) (l : List TF)
    (hl : ∀ φ ∈ l, φ.regsLt cm.nR) : (cm.dLoop cnt l).Ok cm.nR d :=
  ⟨hcnt, hd, Ok_emitTL _ _ l hl, (show 2 * cm.K + 2 < cm.nR by unfold nR; omega)⟩

theorem dLoop_LinOK (cnt : ℕ) (l : List TF) : (cm.dLoop cnt l).LinOK :=
  ⟨LinW_emitTL _ l, trivial⟩

theorem regsLt_nR {M : ℕ} (hM : M ≤ cm.nR) {φ : TF} (h : φ.regsLt M) : φ.regsLt cm.nR :=
  TF.regsLt_mono hM φ h

theorem cellLoopP_Ok (hd : d < 3) {k : ℕ} (hk : k < cm.K) : (cm.cellLoopP k).Ok cm.nR d := by
  unfold cellLoopP
  refine ⟨cm.okSet (r := 2 * cm.K + 2) (s := 1 + k) (by unfold nR; omega) (by unfold nR; omega)
    (by omega), cm.dLoop_Ok hd (by unfold rP nR; omega) _ ?_⟩
  intro φ hφ
  simp only [List.mem_singleton] at hφ; subst hφ
  exact regsLt_exactlyOne (by unfold nR; omega) _

theorem cellLoopP_LinOK (k : ℕ) : (cm.cellLoopP k).LinOK :=
  ⟨LinOK_setReg _ _, cm.dLoop_LinOK _ _⟩

theorem marginP_Ok (hd : d < 3) {k : ℕ} (hk : k < cm.K) : (cm.marginP k).Ok cm.nR d := by
  unfold marginP
  refine ⟨cm.okSet (r := 2 * cm.K + 2) (s := 1 + k) (by unfold nR; omega) (by unfold nR; omega)
    (by omega), ⟨by unfold rN2 nR; omega, hd, (show 2 * cm.K + 2 < cm.nR by unfold nR; omega)⟩, Ok_emitTL _ _ _ ?_⟩
  intro φ hφ
  simp only [List.mem_map] at hφ
  obtain ⟨i, _, rfl⟩ := hφ
  show 2 * cm.K + 2 < cm.nR
  unfold nR; omega

theorem marginP_LinOK (k : ℕ) : (cm.marginP k).LinOK :=
  ⟨LinOK_setReg _ _, trivial, LinOK_emitTL _⟩

theorem frameBlockP_Ok (hd : d < 3) : cm.frameBlockP.Ok cm.nR d := by
  unfold frameBlockP
  refine ⟨Ok_emitTL _ _ _ ?_, Ok_forK _ _ _ _ (fun k hk => cm.cellLoopP_Ok hd hk),
    Ok_forK _ _ _ _ (fun k hk => cm.marginP_Ok hd hk)⟩
  intro φ hφ
  simp only [List.mem_singleton] at hφ; subst hφ
  exact regsLt_exactlyOne (by unfold nR; omega) _

theorem frameBlockP_LinOK : cm.frameBlockP.LinOK :=
  ⟨LinOK_emitTL _, LinOK_forK _ _ (fun k _ => cm.cellLoopP_LinOK k),
    LinOK_forK _ _ (fun k _ => cm.marginP_LinOK k)⟩

theorem topP_Ok (hc : 0 < cm.c) {k : ℕ} (hk : k < cm.K) : (cm.topP k).Ok cm.nR d := by
  unfold topP
  refine Ok_forK _ _ _ _ (fun j _ => Ok_emitTL _ _ _ ?_)
  intro φ hφ
  exact cm.regsLt_nR (by unfold nR; omega) (cm.topT_regs hc hk j φ hφ)

theorem topP_LinOK (k : ℕ) : (cm.topP k).LinOK :=
  LinOK_forK _ _ (fun j _ => LinOK_emitTL _)

theorem deepLoopP_Ok (hc : 0 < cm.c) (hd : d < 3) {k : ℕ} (hk : k < cm.K) :
    (cm.deepLoopP k).Ok cm.nR d := by
  unfold deepLoopP
  refine ⟨cm.okSet (r := 2 * cm.K + 2) (s := 1 + k) (by unfold nR; omega) (by unfold nR; omega)
      (by omega),
    cm.okSet (r := 2 * cm.K + 3) (s := cm.K + 2 + k) (by unfold nR; omega) (by unfold nR; omega)
      (by omega),
    ⟨by unfold rN2 nR; omega, hd, Ok_emitTL _ _ _ ?_, (show 2 * cm.K + 2 < cm.nR by unfold nR; omega),
      (show 2 * cm.K + 3 < cm.nR by unfold nR; omega)⟩⟩
  intro φ hφ
  exact cm.regsLt_nR (by unfold nR; omega) (cm.deepT_regs hc k φ hφ)

theorem deepLoopP_LinOK (k : ℕ) : (cm.deepLoopP k).LinOK :=
  ⟨LinOK_setReg _ _, LinOK_setReg _ _, LinW_emitTL _ _, trivial, trivial⟩

theorem stepBlockP_Ok (hc : 0 < cm.c) (hd : d < 3) : cm.stepBlockP.Ok cm.nR d := by
  unfold stepBlockP
  refine ⟨Ok_emitTL _ _ _ ?_, Ok_forK _ _ _ _ (fun k hk => ⟨cm.topP_Ok hc hk,
    cm.deepLoopP_Ok hc hd hk⟩)⟩
  intro φ hφ
  exact cm.regsLt_nR (by unfold nR; omega) (cm.stepCtlT_regs hc φ hφ)

theorem stepBlockP_LinOK : cm.stepBlockP.LinOK :=
  ⟨LinOK_emitTL _, LinOK_forK _ _ (fun k _ => ⟨cm.topP_LinOK k, cm.deepLoopP_LinOK k⟩)⟩

theorem advanceP_Ok : cm.advanceP.Ok cm.nR d := by
  unfold advanceP
  apply Ok_seqL
  intro p hp
  simp only [List.mem_map, List.mem_range] at hp
  obtain ⟨r, hr, rfl⟩ := hp
  exact ⟨by unfold nR; omega, by unfold rFR nR; omega, by unfold rFR; omega⟩

theorem advanceP_LinOK : cm.advanceP.LinOK := by
  unfold advanceP
  apply LinOK_seqL
  intro p hp
  simp only [List.mem_map] at hp
  obtain ⟨r, _, rfl⟩ := hp
  trivial

theorem mainBody_Ok (hc : 0 < cm.c) (hd : d < 3) : cm.mainBody.Ok cm.nR d :=
  ⟨cm.frameBlockP_Ok hd, cm.stepBlockP_Ok hc hd, cm.advanceP_Ok⟩

theorem mainBody_LinOK : cm.mainBody.LinOK :=
  ⟨cm.frameBlockP_LinOK, cm.stepBlockP_LinOK, cm.advanceP_LinOK⟩

theorem mainP_Ok (hc : 0 < cm.c) (hd : d < 2) : cm.mainP.Ok cm.nR d :=
  ⟨⟨by unfold rP nR; omega, by omega, cm.mainBody_Ok hc (by omega)⟩, cm.frameBlockP_Ok (by omega)⟩

theorem xBody_Ok (bit : Bool) : (cm.xBody bit).Ok cm.nR d := by
  unfold xBody
  refine ⟨(show 2 * cm.K + 2 < cm.nR by unfold nR; omega), Ok_emitTL _ _ _ ?_⟩
  intro φ hφ
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl <;> (show 2 * cm.K + 2 < cm.nR; unfold nR; omega)

theorem xBody_noBits (bit : Bool) : (cm.xBody bit).noBits :=
  ⟨trivial, noBits_emitTL _⟩

theorem xBody_LinW (bit : Bool) (Wr : ℕ → Prop) : (cm.xBody bit).LinW Wr :=
  ⟨trivial, LinW_emitTL _ _⟩

theorem accP_Ok (hkout : cm.kout < cm.K) : cm.accP.Ok cm.nR d := by
  unfold accP
  apply Ok_emitTL
  intro φ hφ
  simp only [accTL, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hφ
  rcases hφ with rfl | rfl | rfl
  · refine regsLt_disjT (by unfold nR; omega) _ ?_
    intro ψ hψ
    simp only [List.mem_map] at hψ
    obtain ⟨q, _, rfl⟩ := hψ
    simp [TF.regsLt, nR]
  · simp only [TF.regsLt, nR]; omega
  · simp only [TF.regsLt, nR]; omega

theorem accP_LinOK : cm.accP.LinOK := LinOK_emitTL _

theorem initP_Ok (hd : d < 3) (hkin : cm.kin < cm.K) : cm.initP.Ok cm.nR d := by
  unfold initP seqL
  have hc2 : 2 * cm.K + 2 < cm.nR := by unfold nR; omega
  have hset : (setReg (2 * cm.K + 2) (1 + cm.kin)).Ok cm.nR d :=
    cm.okSet (r := 2 * cm.K + 2) (s := 1 + cm.kin) hc2 (by unfold nR; omega) (by omega)
  have hloopM : (FP.forLoop cm.rM (.addConst (2 * cm.K + 2) (2 * (cm.A + 1)))).Ok cm.nR d :=
    ⟨by unfold rM nR; omega, hd, hc2⟩
  have hleaf : ∀ o, (emitTL [TF.leaf (2 * cm.K + 2) o]).Ok cm.nR d := by
    intro o
    apply Ok_emitTL
    intro φ hφ
    simp only [List.mem_singleton] at hφ; subst hφ
    exact hc2
  refine ⟨Ok_emitTL _ _ _ ?_, hset, hloopM, ⟨cm.xBody_noBits false, cm.xBody_noBits true,
    cm.xBody_Ok false, cm.xBody_Ok true⟩, hloopM, hleaf _, hc2,
    cm.dLoop_Ok hd (by unfold rN3 nR; omega) _ ?_, hset, hloopM, hc2,
    cm.dLoop_Ok hd (by unfold rN4 nR; omega) _ ?_, Ok_forK _ _ _ _ (fun k hk => ?_), trivial⟩
  · intro φ hφ
    simp only [List.mem_singleton] at hφ; subst hφ
    show 0 < cm.nR
    unfold nR; omega
  · intro φ hφ
    simp only [List.mem_singleton] at hφ; subst hφ
    simp only [orT, TF.regsLt]
    exact ⟨hc2, hc2, hc2⟩
  · intro φ hφ
    simp only [List.mem_singleton] at hφ; subst hφ
    simp only [contigT, impT, TF.regsLt]
    exact ⟨hc2, hc2⟩
  · by_cases h : k = cm.kin
    · simp [h, FP.Ok]
    · simp only [h, if_false]
      refine ⟨cm.okSet (r := 2 * cm.K + 2) (s := 1 + k) hc2 (by unfold nR; omega) (by omega),
        cm.dLoop_Ok hd (by unfold rP nR; omega) _ ?_⟩
      intro φ hφ
      simp only [List.mem_singleton] at hφ; subst hφ
      exact hc2

theorem initP_LinOK : cm.initP.LinOK := by
  unfold initP seqL
  have hloopM : (FP.forLoop cm.rM (.addConst (2 * cm.K + 2) (2 * (cm.A + 1)))).LinOK := trivial
  refine ⟨LinOK_emitTL _, LinOK_setReg _ _, hloopM, ⟨cm.xBody_LinW false _, cm.xBody_LinW true _⟩,
    hloopM, LinOK_emitTL _, trivial, cm.dLoop_LinOK _ _, LinOK_setReg _ _, hloopM, trivial,
    cm.dLoop_LinOK _ _, LinOK_forK _ _ (fun k _ => ?_), trivial⟩
  by_cases h : k = cm.kin
  · simp [h, FP.LinOK]
  · simp only [h, if_false]
    exact ⟨LinOK_setReg _ _, cm.dLoop_LinOK _ _⟩

theorem preP_Ok (C e : ℕ) (hkin : cm.kin < cm.K) (hd : d < 3) : (cm.preP C e).Ok cm.nR d := by
  unfold preP seqL
  exact ⟨cm.polyProg_Ok C e hd, cm.constProg_Ok hd, cm.cntInit_Ok hd, cm.frameInit_Ok hd, trivial,
    cm.initP_Ok hd hkin, trivial⟩

theorem preP_LinOK (C e : ℕ) : (cm.preP C e).LinOK := by
  unfold preP seqL
  exact ⟨cm.polyProg_LinOK C e, cm.constProg_LinOK, cm.cntInit_LinOK, cm.frameInit_LinOK, trivial,
    cm.initP_LinOK, trivial⟩

theorem genProg_Ok (C e : ℕ) (hc : 0 < cm.c) (hkin : cm.kin < cm.K) (hkout : cm.kout < cm.K) :
    (cm.genProg C e).Ok cm.nR 0 :=
  ⟨cm.preP_Ok C e hkin (by omega), cm.mainP_Ok hc (by omega), cm.accP_Ok hkout, trivial⟩

end Pieces

end CM

end CL
end SATurday.Bridge
