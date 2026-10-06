import Theory.ProofComplexity.Bridge.Generator

/-!
# Cost bounds for register programs (Ladder Rung R5)

`FP.Within M p a` says every register that `p` reads, when started from `a`, is at most `M`.
Then `FP.cost p a ≤ FP.costM M p`, and `costM` is a polynomial in `M`.

LOG: R5 Bridge GeneratorCost module (Within, costM, costPoly)
-/

open SATurday.Bridge.SP
open scoped Polynomial

namespace SATurday.Bridge
namespace CL

/-- Every register read by the program is at most `M`, along the run from `a`. -/
inductive _root_.SATurday.Bridge.SP.FP.Within (M : ℕ) : FP → AS → Prop
  | skip (a : AS) : Within M .skip a
  | seq (p q : FP) (a : AS) : Within M p a → Within M q (p.run a) → Within M (.seq p q) a
  | emit (bs : List Bool) (a : AS) : Within M (.emit bs) a
  | emitVar (r o : ℕ) (a : AS) : a.reg r ≤ M → Within M (.emitVar r o) a
  | addConst (r k : ℕ) (a : AS) : Within M (.addConst r k) a
  | subConst (r k : ℕ) (a : AS) : Within M (.subConst r k) a
  | addReg (r s : ℕ) (a : AS) : a.reg s ≤ M → Within M (.addReg r s) a
  | subReg (r s : ℕ) (a : AS) : a.reg s ≤ M → Within M (.subReg r s) a
  | clr (r : ℕ) (a : AS) : a.reg r ≤ M → Within M (.clr r) a
  | forLoop (cnt : ℕ) (body : FP) (a : AS) : a.reg cnt ≤ M →
      (∀ j < a.reg cnt, Within M body (body.run^[j] a)) → Within M (.forLoop cnt body) a
  | forBits (pf pt : FP) (a : AS) : a.bits.length ≤ M →
      (∀ i < a.bits.length, ∀ b r,
        (forBitsAux (fun b => if b then pt.run else pf.run) i a).bits = b :: r →
        Within M (if b then pt else pf)
          { forBitsAux (fun b => if b then pt.run else pf.run) i a with bits := r }) →
      Within M (.forBits pf pt) a
  | countBits (m : ℕ) (a : AS) : a.reg m ≤ M → a.bits.length ≤ M → a.inp.length ≤ M →
      Within M (.countBits m) a

/-- State independent cost bound, for registers and counts at most `M`. -/
def _root_.SATurday.Bridge.SP.FP.costM (M : ℕ) : FP → ℕ
  | .skip => 1
  | .seq p q => p.costM M + q.costM M
  | .emit bs => bs.length + 1
  | .emitVar _ o => 5 * M + o + 8
  | .addConst _ k => k + 1
  | .subConst _ k => 2 * k + 1
  | .addReg _ _ => 5 * M + 2
  | .subReg _ _ => 6 * M + 2
  | .clr _ => 2 * M + 1
  | .forLoop _ body => 6 * M + 3 + M * body.costM M
  | .forBits pf pt => M * (pf.costM M + pt.costM M + 1) + 1
  | .countBits _ => 2 * M + 2 * M + 5 * M + 4

theorem forBitsCost_le (M : ℕ) (pf pt : FP)
    (hf : ∀ a, pf.Within M a → pf.cost a ≤ pf.costM M)
    (ht : ∀ a, pt.Within M a → pt.cost a ≤ pt.costM M) :
    ∀ (k : ℕ) (a : AS),
      (∀ i < k, ∀ b r, (forBitsAux (fun b => if b then pt.run else pf.run) i a).bits = b :: r →
        (if b then pt else pf).Within M
          { forBitsAux (fun b => if b then pt.run else pf.run) i a with bits := r }) →
      forBitsCost (fun b => if b then pt.run else pf.run) (fun b => if b then pt.cost else pf.cost)
        k a ≤ k * (pf.costM M + pt.costM M + 1) + 1 := by
  intro k
  induction k with
  | zero => intro a _; simp [forBitsCost]
  | succ k ih =>
      intro a h
      simp only [forBitsCost]
      cases hb : a.bits with
      | nil => simp
      | cons b r =>
          simp only []
          have h0 := h 0 (by omega) b r (by simp [forBitsAux, hb])
          simp only [forBitsAux] at h0
          have hcost : (if b then pt.cost else pf.cost) { a with bits := r } ≤
              pf.costM M + pt.costM M := by
            cases b
            · simp only [Bool.false_eq_true, if_false] at h0 ⊢
              have := hf _ h0
              omega
            · simp only [if_true] at h0 ⊢
              have := ht _ h0
              omega
          have hrest := ih ((if b then pt.run else pf.run) { a with bits := r }) (by
            intro i hi
            intro b' r' hb'
            have := h (i + 1) (by omega) b' r' (by simpa [forBitsAux, hb] using hb')
            simpa [forBitsAux, hb] using this)
          nlinarith

theorem cost_le_costM (M : ℕ) : ∀ (p : FP) (a : AS), p.Within M a → p.cost a ≤ p.costM M := by
  intro p
  induction p with
  | skip => intro a _; simp [FP.cost, FP.costM]
  | seq p q ihp ihq =>
      intro a h
      cases h with
      | seq _ _ _ h1 h2 =>
      simp only [FP.cost, FP.costM]
      exact Nat.add_le_add (ihp a h1) (ihq _ h2)
  | emit bs => intro a _; simp [FP.cost, FP.costM]
  | emitVar r o =>
      intro a h
      cases h with
      | emitVar _ _ _ h => simp only [FP.cost, FP.costM]; omega
  | addConst r k => intro a _; simp [FP.cost, FP.costM]
  | subConst r k => intro a _; simp [FP.cost, FP.costM]
  | addReg r s =>
      intro a h; cases h with
      | addReg _ _ _ h => simp only [FP.cost, FP.costM]; omega
  | subReg r s =>
      intro a h; cases h with
      | subReg _ _ _ h => simp only [FP.cost, FP.costM]; omega
  | clr r =>
      intro a h; cases h with
      | clr _ _ h => simp only [FP.cost, FP.costM]; omega
  | forLoop cnt body ih =>
      intro a h
      cases h with
      | forLoop _ _ _ hc hj =>
      simp only [FP.cost, FP.costM]
      have hsum : ∑ i ∈ Finset.range (a.reg cnt), body.cost (body.run^[i] a) ≤
          a.reg cnt * body.costM M := by
        calc ∑ i ∈ Finset.range (a.reg cnt), body.cost (body.run^[i] a)
            ≤ ∑ i ∈ Finset.range (a.reg cnt), body.costM M :=
              Finset.sum_le_sum fun i hi => ih _ (hj i (Finset.mem_range.1 hi))
          _ = a.reg cnt * body.costM M := by simp
      have := Nat.mul_le_mul_right (body.costM M) hc
      omega
  | forBits pf pt ihf iht =>
      intro a h
      cases h with
      | forBits _ _ _ hl hw =>
      simp only [FP.cost, FP.costM]
      have := forBitsCost_le M pf pt ihf iht a.bits.length a hw
      have h2 : a.bits.length * (pf.costM M + pt.costM M + 1) ≤ M * (pf.costM M + pt.costM M + 1) :=
        Nat.mul_le_mul_right _ hl
      omega
  | countBits m =>
      intro a h
      cases h with
      | countBits _ _ h1 h2 h3 =>
      simp only [FP.cost, FP.costM]; omega


theorem Within.mono {M M' : ℕ} (h : M ≤ M') {p : FP} {a : AS} (hw : FP.Within M p a) :
    FP.Within M' p a := by
  induction hw with
  | skip a => exact .skip a
  | seq p q a _ _ ih1 ih2 => exact .seq p q a ih1 ih2
  | emit bs a => exact .emit bs a
  | emitVar r o a h1 => exact .emitVar r o a (h1.trans h)
  | addConst r k a => exact .addConst r k a
  | subConst r k a => exact .subConst r k a
  | addReg r s a h1 => exact .addReg r s a (h1.trans h)
  | subReg r s a h1 => exact .subReg r s a (h1.trans h)
  | clr r a h1 => exact .clr r a (h1.trans h)
  | forLoop cnt body a h1 _ ih => exact .forLoop cnt body a (h1.trans h) ih
  | forBits pf pt a h1 _ ih => exact .forBits pf pt a (h1.trans h) ih
  | countBits m a h1 h2 h3 => exact .countBits m a (h1.trans h) (h2.trans h) (h3.trans h)

/-! ## Static bounds: register mass and the all register bound -/

/-- Everything (registers and the two bit lists) is at most `S`. -/
def Bd (S : ℕ) (a : AS) : Prop := (∀ r, a.reg r ≤ S) ∧ a.bits.length ≤ S ∧ a.inp.length ≤ S

/-- Total amount a program can add to registers, as a polynomial in the register bound. -/
noncomputable def _root_.SATurday.Bridge.SP.FP.ms : FP → Polynomial ℕ
  | .addConst _ k => Polynomial.C k
  | .addReg _ _ => Polynomial.X
  | .seq p q => p.ms + q.ms
  | .forLoop _ b => Polynomial.X * b.ms
  | .forBits pf pt => Polynomial.X * (pf.ms + pt.ms)
  | _ => 0

/-- Register bound after a program, from a bound `S` on entry. -/
noncomputable def _root_.SATurday.Bridge.SP.FP.bd : FP → Polynomial ℕ
  | .addConst _ k => Polynomial.X + Polynomial.C k
  | .addReg _ _ => Polynomial.C 2 * Polynomial.X
  | .seq p q => q.bd.comp p.bd
  | .forLoop _ b => Polynomial.X + Polynomial.X * b.ms
  | .forBits pf pt => Polynomial.X + Polynomial.X * (pf.ms + pt.ms)
  | _ => Polynomial.X

/-- Loop bodies in which every added register is untouched by the loop. -/
def _root_.SATurday.Bridge.SP.FP.LinW (Wr : ℕ → Prop) : FP → Prop
  | .seq p q => p.LinW Wr ∧ q.LinW Wr
  | .addReg _ s => ¬ Wr s
  | .forLoop cnt body => ¬ Wr cnt ∧ body.LinW Wr
  | .forBits _ _ => False
  | .countBits _ => False
  | _ => True

/-- Programs whose loops are all linear. -/
def _root_.SATurday.Bridge.SP.FP.LinOK : FP → Prop
  | .seq p q => p.LinOK ∧ q.LinOK
  | .forLoop _ body => body.LinW (fun r => body.writes r)
  | .forBits pf pt => pf.LinW (fun r => pf.writes r ∨ pt.writes r) ∧
      pt.LinW (fun r => pf.writes r ∨ pt.writes r)
  | _ => True

theorem LinW_keep (Wr : ℕ → Prop) : ∀ (p : FP), p.LinW Wr → ∀ a : AS,
    (p.run a).bits = a.bits ∧ (p.run a).inp = a.inp := by
  intro p
  induction p with
  | seq p q ihp ihq =>
      intro h a
      have h1 := ihp h.1 a
      have h2 := ihq h.2 (p.run a)
      exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
  | forLoop cnt body ih =>
      intro h a
      have key : ∀ j (b : AS), (body.run^[j] b).bits = b.bits ∧ (body.run^[j] b).inp = b.inp := by
        intro j
        induction j with
        | zero => intro b; exact ⟨rfl, rfl⟩
        | succ j ihj =>
            intro b
            rw [Function.iterate_succ_apply]
            have h1 := ihj (body.run b)
            have h2 := ih h.2 b
            exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
      exact key _ a
  | forBits _ _ _ _ => intro h; exact absurd h id
  | countBits _ => intro h; exact absurd h id
  | _ => intros; exact ⟨rfl, rfl⟩

theorem iter_reg_of_not_writes (body : FP) (r : ℕ) (h : ¬ body.writes r) :
    ∀ (j : ℕ) (b : AS), (body.run^[j] b).reg r = b.reg r := by
  intro j
  induction j with
  | zero => intro b; rfl
  | succ j ihj => intro b; rw [Function.iterate_succ_apply, ihj, FP.run_reg_of_not_writes r body h]

theorem loop_mass (body : FP) (Wr : ℕ → Prop) (hW : ∀ r, body.writes r → Wr r)
    (S T n m : ℕ) (a : AS) (hST : S ≤ T)
    (hmass : ∀ (T' : ℕ) (b : AS), S ≤ T' → (∀ r, ¬ Wr r → b.reg r ≤ S) → (∀ r, b.reg r ≤ T') →
      FP.Within (T' + m) body b ∧ ∀ r, (body.run b).reg r ≤ T' + m)
    (hsrc : ∀ r, ¬ Wr r → a.reg r ≤ S) (hall : ∀ r, a.reg r ≤ T) :
    (∀ j ≤ n, ∀ r, (body.run^[j] a).reg r ≤ T + j * m) ∧
    (∀ j < n, FP.Within (T + n * m) body (body.run^[j] a)) := by
  have hreg : ∀ j ≤ n, ∀ r, (body.run^[j] a).reg r ≤ T + j * m := by
    intro j
    induction j with
    | zero => intro _ r; simpa using hall r
    | succ j ih =>
        intro hj r
        rw [Function.iterate_succ_apply']
        have h1 := ih (by omega)
        have hs : ∀ r, ¬ Wr r → (body.run^[j] a).reg r ≤ S := by
          intro r hr
          rw [iter_reg_of_not_writes body r (fun h => hr (hW r h)) j a]
          exact hsrc r hr
        have := (hmass (T + j * m) _ (by omega) hs h1).2 r
        rw [Nat.succ_mul]; omega
  refine ⟨hreg, ?_⟩
  intro j hj
  have hs : ∀ r, ¬ Wr r → (body.run^[j] a).reg r ≤ S := by
    intro r hr
    rw [iter_reg_of_not_writes body r (fun h => hr (hW r h)) j a]
    exact hsrc r hr
  have := (hmass (T + j * m) _ (by omega) hs (hreg j (by omega))).1
  refine Within.mono ?_ this
  have : (j + 1) * m ≤ n * m := Nat.mul_le_mul_right _ hj
  rw [Nat.succ_mul] at this; omega

theorem mass (Wr : ℕ → Prop) : ∀ (p : FP), (∀ r, p.writes r → Wr r) → p.LinW Wr →
    ∀ (S T : ℕ) (a : AS), S ≤ T → (∀ r, ¬ Wr r → a.reg r ≤ S) → (∀ r, a.reg r ≤ T) →
      FP.Within (T + (p.ms).eval S) p a ∧ ∀ r, (p.run a).reg r ≤ T + (p.ms).eval S := by
  intro p
  induction p with
  | skip => intro _ _ S T a _ _ hall; exact ⟨.skip a, fun r => by simpa [FP.run, FP.ms] using hall r⟩
  | emit bs => intro _ _ S T a _ _ hall; exact ⟨.emit bs a, fun r => by simpa [FP.run, FP.ms] using hall r⟩
  | emitVar r o =>
      intro _ _ S T a _ _ hall
      exact ⟨.emitVar r o a (by have := hall r; simp [FP.ms]; omega),
        fun r => by simpa [FP.run, FP.ms] using hall r⟩
  | addConst r k =>
      intro _ _ S T a _ _ hall
      refine ⟨.addConst r k a, fun r' => ?_⟩
      simp only [FP.run, FP.ms, Polynomial.eval_C]
      by_cases h : r' = r
      · subst h; simp; have := hall r'; omega
      · simp [Function.update_of_ne h]; have := hall r'; omega
  | subConst r k =>
      intro _ _ S T a _ _ hall
      refine ⟨.subConst r k a, fun r' => ?_⟩
      simp only [FP.run, FP.ms, Polynomial.eval_zero]
      by_cases h : r' = r
      · subst h; simp; have := hall r'; omega
      · simp [Function.update_of_ne h]; have := hall r'; omega
  | addReg r s =>
      intro _ hl S T a hST hsrc hall
      have hs : a.reg s ≤ S := hsrc s hl
      refine ⟨.addReg r s a (by simp [FP.ms]; omega), fun r' => ?_⟩
      simp only [FP.run, FP.ms, Polynomial.eval_X]
      by_cases h : r' = r
      · subst h; simp; have := hall r'; omega
      · simp [Function.update_of_ne h]; have := hall r'; omega
  | subReg r s =>
      intro _ _ S T a _ _ hall
      refine ⟨.subReg r s a (by have := hall s; simp [FP.ms]; omega), fun r' => ?_⟩
      simp only [FP.run, FP.ms, Polynomial.eval_zero]
      by_cases h : r' = r
      · subst h; simp; have := hall r'; omega
      · simp [Function.update_of_ne h]; have := hall r'; omega
  | clr r =>
      intro _ _ S T a _ _ hall
      refine ⟨.clr r a (by have := hall r; simp [FP.ms]; omega), fun r' => ?_⟩
      simp only [FP.run, FP.ms, Polynomial.eval_zero]
      by_cases h : r' = r
      · subst h; simp
      · simp [Function.update_of_ne h]; have := hall r'; omega
  | seq p q ihp ihq =>
      intro hW hl S T a hST hsrc hall
      have hWp : ∀ r, p.writes r → Wr r := fun r h => hW r (Or.inl h)
      have hWq : ∀ r, q.writes r → Wr r := fun r h => hW r (Or.inr h)
      obtain ⟨w1, r1⟩ := ihp hWp hl.1 S T a hST hsrc hall
      have hsrc' : ∀ r, ¬ Wr r → (p.run a).reg r ≤ S := by
        intro r hr
        rw [FP.run_reg_of_not_writes r p (fun h => hr (hWp r h))]
        exact hsrc r hr
      obtain ⟨w2, r2⟩ := ihq hWq hl.2 S (T + (p.ms).eval S) (p.run a) (by omega) hsrc' r1
      simp only [FP.ms, FP.run, Polynomial.eval_add]
      refine ⟨.seq p q a (Within.mono (by omega) w1) ?_, fun r => ?_⟩
      · exact Within.mono (by omega) w2
      · have := r2 r; omega
  | forLoop cnt body ih =>
      intro hW hl S T a hST hsrc hall
      have hW' : ∀ r, body.writes r → Wr r := hW
      have hn : a.reg cnt ≤ S := hsrc cnt hl.1
      obtain ⟨l1, l2⟩ := loop_mass body Wr hW' S T (a.reg cnt) ((body.ms).eval S) a hST
        (fun T' b h1 h2 h3 => ih hW' hl.2 S T' b h1 h2 h3) hsrc hall
      have hmul : a.reg cnt * (body.ms).eval S ≤ S * (body.ms).eval S :=
        Nat.mul_le_mul_right _ hn
      simp only [FP.ms, FP.run, Polynomial.eval_mul, Polynomial.eval_X]
      refine ⟨.forLoop cnt body a (by omega) (fun j hj => ?_), fun r => ?_⟩
      · exact Within.mono (by omega) (l2 j hj)
      · have := l1 _ le_rfl r; omega
  | forBits pf pt _ _ => intro _ hl; exact absurd hl id
  | countBits m => intro _ hl; exact absurd hl id


theorem forBitsAux_nil (f : Bool → AS → AS) (a : AS) (h : a.bits = []) :
    ∀ i, forBitsAux f i a = a := by
  intro i; cases i <;> simp [forBitsAux, h]

theorem forBitsAux_cons (f : Bool → AS → AS) (a : AS) (b : Bool) (r : List Bool)
    (h : a.bits = b :: r) (i : ℕ) :
    forBitsAux f (i + 1) a = forBitsAux f i (f b { a with bits := r }) := by
  simp [forBitsAux, h]

theorem forBits_mass (pf pt : FP) (Wr : ℕ → Prop) (hWf : ∀ r, pf.writes r → Wr r)
    (hWt : ∀ r, pt.writes r → Wr r) (hlf : pf.LinW Wr) (hlt : pt.LinW Wr) (S : ℕ) :
    ∀ (k : ℕ) (a : AS) (T : ℕ), S ≤ T → (∀ r, ¬ Wr r → a.reg r ≤ S) → (∀ r, a.reg r ≤ T) →
      (∀ i < k, ∀ b r, (forBitsAux (fun b => if b then pt.run else pf.run) i a).bits = b :: r →
        FP.Within (T + k * ((pf.ms).eval S + (pt.ms).eval S)) (if b then pt else pf)
          { forBitsAux (fun b => if b then pt.run else pf.run) i a with bits := r }) ∧
      (∀ r, (forBitsAux (fun b => if b then pt.run else pf.run) k a).reg r ≤
          T + k * ((pf.ms).eval S + (pt.ms).eval S)) ∧
      (forBitsAux (fun b => if b then pt.run else pf.run) k a).bits.length ≤ a.bits.length ∧
      (forBitsAux (fun b => if b then pt.run else pf.run) k a).inp = a.inp := by
  intro k
  induction k with
  | zero =>
      intro a T _ _ hall
      exact ⟨fun i hi => absurd hi (by omega), fun r => by simpa [forBitsAux] using hall r,
        by simp [forBitsAux], by simp [forBitsAux]⟩
  | succ k ih =>
      intro a T hST hsrc hall
      cases hb : a.bits with
      | nil =>
          have hA := forBitsAux_nil (fun b => if b then pt.run else pf.run) a hb
          refine ⟨fun i hi b r h => ?_, fun r => ?_, ?_, ?_⟩
          · rw [hA] at h; rw [hb] at h; exact absurd h (by simp)
          · rw [hA]; have := hall r; omega
          · simp [hA, hb]
          · rw [hA]
      | cons b r =>
          set a0 : AS := { a with bits := r } with ha0
          set m' := (pf.ms).eval S + (pt.ms).eval S with hm'
          have hsrc0 : ∀ r', ¬ Wr r' → a0.reg r' ≤ S := hsrc
          have hall0 : ∀ r', a0.reg r' ≤ T := hall
          have hbody : FP.Within (T + (((if b then pt else pf)).ms).eval S)
              (if b then pt else pf) a0 ∧
              (∀ r', ((if b then pt else pf).run a0).reg r' ≤
                T + (((if b then pt else pf)).ms).eval S) ∧
              ((if b then pt else pf).run a0).bits = r ∧
              ((if b then pt else pf).run a0).inp = a.inp ∧
              (∀ r', ¬ Wr r' → ((if b then pt else pf).run a0).reg r' = a.reg r') := by
            cases b
            · simp only [Bool.false_eq_true, if_false]
              obtain ⟨w, rr⟩ := mass Wr pf hWf hlf S T a0 hST hsrc0 hall0
              obtain ⟨k1, k2⟩ := LinW_keep Wr pf hlf a0
              exact ⟨w, rr, k1, k2, fun r' hr' =>
                FP.run_reg_of_not_writes r' pf (fun h => hr' (hWf r' h)) a0⟩
            · simp only [if_true]
              obtain ⟨w, rr⟩ := mass Wr pt hWt hlt S T a0 hST hsrc0 hall0
              obtain ⟨k1, k2⟩ := LinW_keep Wr pt hlt a0
              exact ⟨w, rr, k1, k2, fun r' hr' =>
                FP.run_reg_of_not_writes r' pt (fun h => hr' (hWt r' h)) a0⟩
          obtain ⟨hw, hr, hbits, hinp, hun⟩ := hbody
          have hmb : (((if b then pt else pf)).ms).eval S ≤ m' := by
            cases b <;> simp [hm']
          set a' := (fun b => if b then pt.run else pf.run) b a0 with ha'
          have ha'eq : a' = (if b then pt else pf).run a0 := by cases b <;> rfl
          have hsrc' : ∀ r', ¬ Wr r' → a'.reg r' ≤ S := by
            intro r' hr'; rw [ha'eq, hun r' hr']; exact hsrc r' hr'
          have hall' : ∀ r', a'.reg r' ≤ T + m' := by
            intro r'; rw [ha'eq]; have := hr r'; omega
          obtain ⟨i1, i2, i3, i4⟩ := ih a' (T + m') (by omega) hsrc' hall'
          have hA := forBitsAux_cons (fun b => if b then pt.run else pf.run) a b r hb
          have hbits' : a'.bits = r := by rw [ha'eq]; exact hbits
          have hinp' : a'.inp = a.inp := by rw [ha'eq]; exact hinp
          have harith : T + m' + k * m' = T + (k + 1) * m' := by rw [Nat.succ_mul]; omega
          refine ⟨fun i hi b' r' h => ?_, fun r'' => ?_, ?_, ?_⟩
          · cases i with
            | zero =>
                simp only [forBitsAux] at h ⊢
                rw [hb] at h
                obtain ⟨rfl, rfl⟩ := List.cons.inj h
                refine Within.mono ?_ hw
                have : m' ≤ (k + 1) * m' := Nat.le_mul_of_pos_left _ (by omega)
                omega
            | succ i =>
                rw [hA] at h ⊢
                have := i1 i (by omega) b' r' h
                rw [harith] at this
                exact this
          · rw [hA]
            have := i2 r''
            rw [harith] at this; exact this
          · have h3 : (forBitsAux (fun b => if b then pt.run else pf.run) k a').bits.length ≤
                r.length := by
              have := i3; rw [hbits'] at this; exact this
            rw [hA]
            exact h3.trans (by simp)
          · rw [hA, i4, hinp']

theorem iter_keep (Wr : ℕ → Prop) (body : FP) (hl : body.LinW Wr) :
    ∀ (j : ℕ) (b : AS), (body.run^[j] b).bits = b.bits ∧ (body.run^[j] b).inp = b.inp := by
  intro j
  induction j with
  | zero => intro b; exact ⟨rfl, rfl⟩
  | succ j ihj =>
      intro b
      rw [Function.iterate_succ_apply]
      have h1 := ihj (body.run b)
      have h2 := LinW_keep Wr body hl b
      exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem le_bd : ∀ (p : FP) (S : ℕ), S ≤ (p.bd).eval S := by
  intro p
  induction p with
  | seq p q ihp ihq =>
      intro S
      simp only [FP.bd, Polynomial.eval_comp]
      exact (ihp S).trans (ihq _)
  | addConst r k => intro S; simp [FP.bd]
  | addReg r s => intro S; simp [FP.bd]; omega
  | forLoop c b ih => intro S; simp [FP.bd]
  | forBits pf pt ihf iht => intro S; simp [FP.bd]
  | _ => intro S; simp [FP.bd]

/-- The main static theorem: a program with linear loops, started below a bound, stays below the
polynomial bound `bd`, and every register it reads is below it. -/
theorem top : ∀ (p : FP), p.LinOK → ∀ (S : ℕ) (a : AS), Bd S a →
    FP.Within ((p.bd).eval S) p a ∧ Bd ((p.bd).eval S) (p.run a) := by
  intro p
  induction p with
  | skip =>
      intro _ S a hB
      exact ⟨.skip a, by simpa [FP.bd, FP.run] using hB⟩
  | emit bs =>
      intro _ S a hB
      exact ⟨.emit bs a, by simpa [FP.bd, FP.run] using hB⟩
  | emitVar r o =>
      intro _ S a hB
      exact ⟨.emitVar r o a (by simpa [FP.bd] using hB.1 r), by simpa [FP.bd, FP.run] using hB⟩
  | addConst r k =>
      intro _ S a hB
      refine ⟨.addConst r k a, ?_, ?_, ?_⟩
      · intro r'
        simp only [FP.run, FP.bd, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
        by_cases h : r' = r
        · subst h; simp; have := hB.1 r'; omega
        · simp [Function.update_of_ne h]; have := hB.1 r'; omega
      · simp only [FP.run, FP.bd, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
        have := hB.2.1; omega
      · simp only [FP.run, FP.bd, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
        have := hB.2.2; omega
  | subConst r k =>
      intro _ S a hB
      refine ⟨.subConst r k a, ?_, ?_, ?_⟩
      · intro r'
        simp only [FP.run, FP.bd, Polynomial.eval_X]
        by_cases h : r' = r
        · subst h; simp; have := hB.1 r'; omega
        · simp [Function.update_of_ne h]; exact hB.1 r'
      · simpa [FP.run, FP.bd] using hB.2.1
      · simpa [FP.run, FP.bd] using hB.2.2
  | addReg r s =>
      intro _ S a hB
      refine ⟨.addReg r s a (by simp [FP.bd]; have := hB.1 s; omega), ?_, ?_, ?_⟩
      · intro r'
        simp only [FP.run, FP.bd, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
        by_cases h : r' = r
        · subst h; simp; have := hB.1 r'; have := hB.1 s; omega
        · simp [Function.update_of_ne h]; have := hB.1 r'; omega
      · simp only [FP.run, FP.bd, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
        have := hB.2.1; omega
      · simp only [FP.run, FP.bd, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
        have := hB.2.2; omega
  | subReg r s =>
      intro _ S a hB
      refine ⟨.subReg r s a (by simpa [FP.bd] using hB.1 s), ?_, ?_, ?_⟩
      · intro r'
        simp only [FP.run, FP.bd, Polynomial.eval_X]
        by_cases h : r' = r
        · subst h; simp; have := hB.1 r'; omega
        · simp [Function.update_of_ne h]; exact hB.1 r'
      · simpa [FP.run, FP.bd] using hB.2.1
      · simpa [FP.run, FP.bd] using hB.2.2
  | clr r =>
      intro _ S a hB
      refine ⟨.clr r a (by simpa [FP.bd] using hB.1 r), ?_, ?_, ?_⟩
      · intro r'
        simp only [FP.run, FP.bd, Polynomial.eval_X]
        by_cases h : r' = r
        · subst h; simp
        · simp [Function.update_of_ne h]; exact hB.1 r'
      · simpa [FP.run, FP.bd] using hB.2.1
      · simpa [FP.run, FP.bd] using hB.2.2
  | countBits m =>
      intro _ S a hB
      refine ⟨.countBits m a (by simpa [FP.bd] using hB.1 m) (by simpa [FP.bd] using hB.2.1)
        (by simpa [FP.bd] using hB.2.2), ?_, ?_, ?_⟩
      · intro r'
        simp only [FP.run, FP.bd, Polynomial.eval_X]
        by_cases h : r' = m
        · subst h; simp; exact hB.2.2
        · simp [Function.update_of_ne h]; exact hB.1 r'
      · simpa [FP.run, FP.bd] using hB.2.2
      · simp [FP.run, FP.bd]
  | seq p q ihp ihq =>
      intro hl S a hB
      obtain ⟨w1, b1⟩ := ihp hl.1 S a hB
      obtain ⟨w2, b2⟩ := ihq hl.2 _ (p.run a) b1
      simp only [FP.bd, FP.run, Polynomial.eval_comp]
      exact ⟨.seq p q a (Within.mono (le_bd q _) w1) w2, b2⟩
  | forLoop cnt body ih =>
      intro hl S a hB
      have hn : a.reg cnt ≤ S := hB.1 cnt
      obtain ⟨l1, l2⟩ := loop_mass body (fun r => body.writes r) (fun r h => h) S S (a.reg cnt)
        ((body.ms).eval S) a le_rfl
        (fun T' b h1 h2 h3 => mass (fun r => body.writes r) body (fun r h => h) hl S T' b h1 h2 h3)
        (fun r _ => hB.1 r) hB.1
      have hmul : a.reg cnt * (body.ms).eval S ≤ S * (body.ms).eval S :=
        Nat.mul_le_mul_right _ hn
      obtain ⟨k1, k2⟩ := iter_keep (fun r => body.writes r) body hl (a.reg cnt) a
      simp only [FP.bd, FP.run, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      refine ⟨.forLoop cnt body a (by omega) (fun j hj => ?_), fun r => ?_, ?_, ?_⟩
      · exact Within.mono (by omega) (l2 j hj)
      · have := l1 _ le_rfl r; omega
      · rw [k1]; have := hB.2.1; omega
      · rw [k2]; have := hB.2.2; omega
  | forBits pf pt ihf iht =>
      intro hl S a hB
      obtain ⟨hlf, hlt⟩ := hl
      obtain ⟨f1, f2, f3, f4⟩ := forBits_mass pf pt (fun r => pf.writes r ∨ pt.writes r)
        (fun r h => Or.inl h) (fun r h => Or.inr h) hlf hlt S a.bits.length a S le_rfl
        (fun r _ => hB.1 r) hB.1
      have hmul : a.bits.length * ((pf.ms).eval S + (pt.ms).eval S) ≤
          S * ((pf.ms).eval S + (pt.ms).eval S) := Nat.mul_le_mul_right _ hB.2.1
      simp only [FP.bd, FP.run, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      refine ⟨.forBits pf pt a (by have := hB.2.1; omega) (fun i hi b r h => ?_), fun r => ?_, ?_, ?_⟩
      · exact Within.mono (by omega) (f1 i hi b r h)
      · have := f2 r; omega
      · have := hB.2.1; have := f3; omega
      · rw [f4]; have := hB.2.2; omega

end CL
end SATurday.Bridge
