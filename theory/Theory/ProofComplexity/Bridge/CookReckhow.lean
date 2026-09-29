import Theory.ProofComplexity.Bridge.ProofSystem
import Mathlib.Tactic

/-!
# Cook Reckhow bridge (Ladder Rung R5, Block C)

Bridge theorem 2 is the certified implication `ClassP = ClassNP → ClassNP = ClassCoNP`.
Bridge theorem 1 is the Cook Reckhow equivalence: a polynomially bounded
propositional proof system exists if and only if NP equals coNP.
The summit corollary is the contrapositive packaging used by the ladder:
if no propositional proof system is polynomially bounded, then P differs from NP.

LOG: R5 Block C CookReckhow (TAUT in coNP, proof system from NP, summit)
-/

open Turing
open TM2.Stmt
open StateTransition
open scoped Polynomial

namespace SATurday.Bridge

set_option maxHeartbeats 2000000

/-! ## Bridge theorem 2 -/

/-- Cook Reckhow bridge theorem 2: `P = NP` implies `NP = coNP`. -/
theorem bridge_theorem_2 (h : ClassP_eq_ClassNP) : ClassNP_eq_ClassCoNP :=
  classP_eq_classNP_implies_NP_eq_coNP h

/-! ## Falsifying assignments for `TAUT` -/

/-- Fixed non tautology used when a code is not a formula: variable `0`. -/
def var0Code : List Bool := encodeFormula (.var 0)

/-- Assignment that makes variable `0` false. -/
def dummyAssign : List Bool := [false]

/-- Pair the evaluator already knows how to run: `encodePair ([false], encodeFormula (var 0))`. -/
def dummyEvalInput : List Bool := encodePair (dummyAssign, var0Code)

theorem dummyEvalInput_eq :
    dummyEvalInput = [true, false, false, false, false, false] := by
  simp [dummyEvalInput, dummyAssign, var0Code, encodePair, encodeFormula, encodeNat,
    List.flatMap, List.replicate]

theorem var0_evalOn_false : (PropFormula.var 0).evalOn dummyAssign = false := by
  simp [PropFormula.evalOn, dummyAssign]

/-- Verifier for the complement of `TAUT`.
Malformed codes are accepted immediately. A decoded formula is accepted exactly
when `w` is a falsifying assignment (`evalOn` reads missing variables as false). -/
def tautComplV (x w : List Bool) : Bool :=
  match decodeFormula x with
  | none => true
  | some φ => !(φ.evalOn w)

/-- Input handed to `evalEncodedComputer`: a known false instance, or `(w, x)`. -/
def sanitizeInput (x w : List Bool) : List Bool :=
  match decodeFormula x with
  | none => dummyEvalInput
  | some _ => encodePair (w, x)

theorem sanitizeInput_none {x w : List Bool} (h : decodeFormula x = none) :
    sanitizeInput x w = dummyEvalInput := by
  simp [sanitizeInput, h]

theorem sanitizeInput_some {x w : List Bool} {φ : PropFormula}
    (h : decodeFormula x = some φ) : sanitizeInput x w = encodePair (w, x) := by
  simp [sanitizeInput, h]

/-- One false `evalOn` shows the formula is not a tautology. -/
theorem not_tautology_of_evalOn_false (φ : PropFormula) (w : List Bool)
    (h : φ.evalOn w = false) : ¬ φ.Tautology := by
  intro ht
  have := ht (fun i => w.getD i false)
  rw [← evalOn_eq_eval_getD] at this
  simp [h] at this

/-- `tautComplV` accepts a short witness exactly on the complement of `TAUT`. -/
theorem tautComplV_witness (x : List Bool) :
    (¬ TAUT x) ↔
      ∃ w, w.length ≤ (Polynomial.X + 1).eval x.length ∧ tautComplV x w = true := by
  constructor
  · intro hn
    cases hdec : decodeFormula x with
    | none =>
        refine ⟨[], ?_, ?_⟩
        · simp
        · simp [tautComplV, hdec]
    | some φ =>
        have hnot : ¬ φ.Tautology := by
          intro ht
          exact hn ⟨φ, hdec, ht⟩
        unfold PropFormula.Tautology at hnot
        push Not at hnot
        rcases hnot with ⟨σ, hσ⟩
        refine ⟨(List.range (φ.maxVar + 1)).map σ, ?_, ?_⟩
        · have hx : encodeFormula φ = x := encodeFormula_of_decodeFormula hdec
          have hmax := maxVar_le_encodeFormula_length φ
          have hmax' : φ.maxVar ≤ x.length := by simpa [hx] using hmax
          simp [List.length_map, List.length_range]
          omega
        · have hσ' : φ.eval σ = false := Bool.eq_false_iff.mpr (by simpa using hσ)
          have hfin : φ.evalOn ((List.range (φ.maxVar + 1)).map σ) = false := by
            rw [← eval_eq_evalOn]
            exact hσ'
          simp [tautComplV, hdec, hfin]
  · intro ⟨w, _, hV⟩ hT
    rcases hT with ⟨φ, hdec, htaut⟩
    have hbit : !(φ.evalOn w) = true := by simpa [tautComplV, hdec] using hV
    cases he : φ.evalOn w with
    | false => exact not_tautology_of_evalOn_false φ w he htaut
    | true => simp [he] at hbit

/-! ## Lifting a Bool stack machine onto extra stacks

`decodeFormulaResultComputer` must run while the witness bits stay on a side
stack. Halt of the inner machine is remapped to a host label so the outer
machine can still emit. -/

section Lift

variable {K E : Type} [DecidableEq K] [DecidableEq E]
variable {Γ : K → Type} {β Λ Λ' σ : Type}

/-- Extra stacks sit in the right summand and are not touched by the inner program. -/
def embedStk (extra : E → List β) (S : ∀ k, List (Γ k)) :
    ∀ k : K ⊕ E, List (Sum.elim Γ (fun _ : E => β) k)
  | Sum.inl k => S k
  | Sum.inr e => extra e

theorem embedStk_update (extra : E → List β) (S : ∀ k, List (Γ k)) (k : K)
    (xs : List (Γ k)) :
    embedStk extra (Function.update S k xs) =
      Function.update (embedStk extra S) (Sum.inl k) xs := by
  funext t
  cases t with
  | inl k' =>
      by_cases hk : k' = k
      · subst hk
        simp [embedStk, Function.update]
      · simp [embedStk, Function.update, hk]
  | inr e =>
      simp [embedStk, Function.update]

/-- Inner statement, with stack indices injected and `halt` replaced by `goto onHalt`. -/
def liftStmt (mapL : Λ → Λ') (onHalt : σ → Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt (Sum.elim Γ (fun _ : E => β)) Λ' σ
  | .push k f q => .push (Sum.inl k) f (liftStmt mapL onHalt q)
  | .peek k f q => .peek (Sum.inl k) f (liftStmt mapL onHalt q)
  | .pop k f q => .pop (Sum.inl k) f (liftStmt mapL onHalt q)
  | .load f q => .load f (liftStmt mapL onHalt q)
  | .branch p q₁ q₂ => .branch p (liftStmt mapL onHalt q₁) (liftStmt mapL onHalt q₂)
  | .goto f => .goto fun s => mapL (f s)
  | .halt => .goto onHalt

/-- Host view of an inner configuration. A halted inner label becomes `onHalt`. -/
def translateCfg (mapL : Λ → Λ') (onHalt : σ → Λ') (extra : E → List β)
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg (Sum.elim Γ (fun _ : E => β)) Λ' σ where
  l := match c.l with
    | some lab => some (mapL lab)
    | none => some (onHalt c.var)
  var := c.var
  stk := embedStk extra c.stk

theorem liftStmt_stepAux (mapL : Λ → Λ') (onHalt : σ → Λ')
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (extra : E → List β) :
    TM2.stepAux (liftStmt mapL onHalt q) v (embedStk extra S) =
      translateCfg mapL onHalt extra (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f next ih =>
      simp only [liftStmt, TM2.stepAux, embedStk, ← embedStk_update]
      exact ih v (Function.update S k (f v :: S k))
  | peek k f next ih =>
      have hhead : (embedStk extra S (Sum.inl k)).head? = (S k).head? := by
        simp [embedStk]
      simp only [liftStmt, TM2.stepAux, hhead]
      exact ih (f v (S k).head?) S
  | pop k f next ih =>
      have hhead : (embedStk extra S (Sum.inl k)).head? = (S k).head? := by
        simp [embedStk]
      have htail : (embedStk extra S (Sum.inl k)).tail = (S k).tail := by
        simp [embedStk]
      simp only [liftStmt, TM2.stepAux, ← embedStk_update, embedStk]
      exact ih (f v (S k).head?) (Function.update S k (S k).tail)
  | load f next ih =>
      simp only [liftStmt, TM2.stepAux]
      exact ih (f v) S
  | branch p q₁ q₂ ih₁ ih₂ =>
      simp only [liftStmt, TM2.stepAux]
      cases hpv : p v
      · exact ih₂ v S
      · exact ih₁ v S
  | goto f =>
      simp [liftStmt, TM2.stepAux, translateCfg]
  | halt =>
      simp [liftStmt, TM2.stepAux, translateCfg]

end Lift

/-! ## Host machine: sanitize `encodePair (x, w)` into an eval input -/

inductive HostExtra where
  | hold
  | out
  deriving DecidableEq, Repr, Fintype

abbrev HostK := DFRStack ⊕ HostExtra

inductive HostLabel where
  | parse
  | expect
  | takeW
  | revX
  | dfr : DFRLabel → HostLabel
  | after
  | revCode
  | flushX
  | flushW
  | dummy
  | clearHold
  deriving DecidableEq, Repr, Fintype

def hostΓ : HostK → Type :=
  Sum.elim (fun _ : DFRStack => Bool) (fun _ : HostExtra => Bool)

instance (k : HostK) : Fintype (hostΓ k) := by
  cases k with
  | inl _ => exact inferInstanceAs (Fintype Bool)
  | inr _ => exact inferInstanceAs (Fintype Bool)

/-- Side stacks during the inner decode: reversed witness, empty output. -/
def phase0Extra (wRev : List Bool) : HostExtra → List Bool
  | .hold => wRev
  | .out => []

def translateDFR (extra : HostExtra → List Bool) (c : decodeFormulaResultComputer.Cfg) :
    TM2.Cfg hostΓ HostLabel (Option Bool) :=
  translateCfg (Γ := fun _ : DFRStack => Bool) (β := Bool)
    HostLabel.dfr (fun _ => HostLabel.after) extra c

/-- Build `sanitizeInput x w` on the output stack.
Phase 0 parks `x` on the decode input and the reversed witness on `hold`.
The lifted decode machine then writes `decodeFormulaResult x`. Emit turns that
tag into either `dummyEvalInput` or `encodePair (w, x)`. -/
def sanitizeComputer : FinTM2 where
  K := HostK
  k₀ := Sum.inl .inp
  k₁ := Sum.inr .out
  Γ := hostΓ
  Λ := HostLabel
  main := .parse
  σ := Option Bool
  initialState := none
  m
    | .parse =>
        pop (Sum.inl .inp) (fun _ o => o) <|
          branch (fun s => decide (s = none))
            halt
            (branch (fun s => decide (s = some false))
              (goto fun _ => .takeW)
              (goto fun _ => .expect))
    | .expect =>
        pop (Sum.inl .inp) (fun _ o => o) <|
          branch (fun s => decide (s = none))
            halt
            (push (Sum.inl .work) (fun s => s.getD false) <|
              load (fun _ => none) <|
                goto fun _ => .parse)
    | .takeW =>
        pop (Sum.inl .inp) (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => .revX)
            (push (Sum.inr .hold) (fun s => s.getD false) <|
              load (fun _ => none) <|
                goto fun _ => .takeW)
    | .revX =>
        pop (Sum.inl .work) (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => .dfr .dupToAux)
            (push (Sum.inl .inp) (fun s => s.getD false) <|
              load (fun _ => none) <|
                goto fun _ => .revX)
    | .dfr lab =>
        liftStmt (E := HostExtra) (β := Bool) HostLabel.dfr (fun _ => HostLabel.after)
          (decodeFormulaResultComputer.m lab)
    | .after =>
        pop (Sum.inl .out) (fun _ o => o) <|
          branch (fun s => decide (s = none))
            halt
            (branch (fun s => decide (s = some false))
              (goto fun _ => .revCode)
              (goto fun _ => .dummy))
    | .dummy =>
        pop (Sum.inl .out) (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => .clearHold)
            halt
    | .clearHold =>
        pop (Sum.inr .hold) (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push (Sum.inr .out) (fun _ => false) <|
              push (Sum.inr .out) (fun _ => false) <|
                push (Sum.inr .out) (fun _ => false) <|
                  push (Sum.inr .out) (fun _ => false) <|
                    push (Sum.inr .out) (fun _ => false) <|
                      push (Sum.inr .out) (fun _ => true) <|
                        halt)
            (load (fun _ => none) <|
              goto fun _ => .clearHold)
    | .revCode =>
        pop (Sum.inl .out) (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => .flushX)
            (push (Sum.inl .aux) (fun s => s.getD false) <|
              load (fun _ => none) <|
                goto fun _ => .revCode)
    | .flushX =>
        pop (Sum.inl .aux) (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push (Sum.inr .out) (fun _ => false) <|
              goto fun _ => .flushW)
            (push (Sum.inr .out) (fun s => s.getD false) <|
              load (fun _ => none) <|
                goto fun _ => .flushX)
    | .flushW =>
        pop (Sum.inr .hold) (fun _ o => o) <|
          branch (fun s => decide (s = none))
            halt
            (push (Sum.inr .out) (fun s => s.getD false) <|
              push (Sum.inr .out) (fun _ => true) <|
                load (fun _ => none) <|
                  goto fun _ => .flushW)

def hostStk (inp work aux dout hold hout : List Bool) : (k : HostK) → List (hostΓ k)
  | .inl .inp => inp
  | .inl .work => work
  | .inl .aux => aux
  | .inl .out => dout
  | .inr .hold => hold
  | .inr .out => hout

def hostCfg (l : Option HostLabel) (v : Option Bool)
    (inp work aux dout hold hout : List Bool) : sanitizeComputer.Cfg :=
  ⟨l, v, hostStk inp work aux dout hold hout⟩

theorem sanitize_initList (s : List Bool) :
    initList sanitizeComputer s =
      hostCfg (some .parse) none s [] [] [] [] [] := by
  refine congrArg (fun stk =>
      (⟨some HostLabel.parse, none, stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s =>
      cases s <;> (simp [sanitizeComputer, hostStk, initList]; try rfl)
  | inr e =>
      cases e <;> (simp [sanitizeComputer, hostStk, initList]; try rfl)

theorem sanitize_haltList (s : List Bool) :
    haltList sanitizeComputer s =
      hostCfg none none [] [] [] [] [] s := by
  refine congrArg (fun stk =>
      (⟨(none : Option HostLabel), none, stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s =>
      cases s <;> (simp [sanitizeComputer, hostStk, haltList]; try rfl)
  | inr e =>
      cases e <;> (simp [sanitizeComputer, hostStk, haltList]; try rfl)

theorem host_step_parse_true (b : Bool) (rest work aux dout hold hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .parse) none (true :: b :: rest) work aux dout hold hout) =
      some (hostCfg (some .expect) (some true) (b :: rest) work aux dout hold hout) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some HostLabel.expect, some true, stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

theorem host_step_expect (b : Bool) (rest work aux dout hold hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .expect) (some true) (b :: rest) work aux dout hold hout) =
      some (hostCfg (some .parse) none rest (b :: work) aux dout hold hout) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some HostLabel.parse, (none : Option Bool), stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

theorem host_step_parse_false (rest work aux dout hold hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .parse) none (false :: rest) work aux dout hold hout) =
      some (hostCfg (some .takeW) (some false) rest work aux dout hold hout) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some HostLabel.takeW, some false, stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

theorem host_step_take_bit (v : Option Bool) (b : Bool)
    (rest work aux dout hold hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .takeW) v (b :: rest) work aux dout hold hout) =
      some (hostCfg (some .takeW) none rest work aux dout (b :: hold) hout) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some HostLabel.takeW, (none : Option Bool), stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

theorem host_step_take_nil (v : Option Bool) (work aux dout hold hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .takeW) v [] work aux dout hold hout) =
      some (hostCfg (some .revX) none [] work aux dout hold hout) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some HostLabel.revX, (none : Option Bool), stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

theorem host_step_rev_bit (b : Bool) (rest acc aux dout hold hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .revX) none acc (b :: rest) aux dout hold hout) =
      some (hostCfg (some .revX) none (b :: acc) rest aux dout hold hout) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some HostLabel.revX, (none : Option Bool), stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

theorem host_step_rev_nil (acc aux dout hold hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .revX) none acc [] aux dout hold hout) =
      some (hostCfg (some (.dfr .dupToAux)) none acc [] aux dout hold hout) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some (HostLabel.dfr .dupToAux), (none : Option Bool), stk⟩ :
        sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

def host_evals_step {a b : sanitizeComputer.Cfg}
    (h : TM2.step sanitizeComputer.m a = some b) :
    EvalsToInTime sanitizeComputer.step a (some b) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some a).bind sanitizeComputer.step = some b
    simpa [FinTM2.step] using h

def host_evals_one_bit (b : Bool) (rest work aux dout hold hout : List Bool) :
    EvalsToInTime sanitizeComputer.step
      (hostCfg (some .parse) none (true :: b :: rest) work aux dout hold hout)
      (some (hostCfg (some .parse) none rest (b :: work) aux dout hold hout))
      2 where
  steps := 2
  steps_le_m := by decide
  evals_in_steps := by
    change ((some (hostCfg (some .parse) none (true :: b :: rest) work aux dout hold hout)).bind
        sanitizeComputer.step).bind sanitizeComputer.step =
      some (hostCfg (some .parse) none rest (b :: work) aux dout hold hout)
    simp only [FinTM2.step]
    rw [Option.bind_some, host_step_parse_true, Option.bind_some]
    exact host_step_expect b rest work aux dout hold hout

noncomputable def host_evals_parse (x rest work aux dout hold hout : List Bool) :
    EvalsToInTime sanitizeComputer.step
      (hostCfg (some .parse) none
        ((x.flatMap fun b => [true, b]) ++ rest) work aux dout hold hout)
      (some (hostCfg (some .parse) none rest (x.reverse ++ work) aux dout hold hout))
      (2 * x.length) := by
  induction x generalizing work with
  | nil =>
      simpa using EvalsToInTime.refl sanitizeComputer.step
        (hostCfg (some .parse) none rest work aux dout hold hout)
  | cons b xs ih =>
      have h1 := host_evals_one_bit b ((xs.flatMap fun b => [true, b]) ++ rest)
        work aux dout hold hout
      have h2 := ih (b :: work)
      have h := EvalsToInTime.trans sanitizeComputer.step 2 (2 * xs.length)
        (hostCfg (some .parse) none
          ((b :: xs).flatMap (fun b => [true, b]) ++ rest) work aux dout hold hout)
        (hostCfg (some .parse) none
          ((xs.flatMap fun b => [true, b]) ++ rest) (b :: work) aux dout hold hout)
        (some (hostCfg (some .parse) none rest
          (xs.reverse ++ (b :: work)) aux dout hold hout))
        (by simpa [List.flatMap] using h1) h2
      simpa [List.flatMap, List.reverse_cons, List.append_assoc, Nat.mul_succ,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

def host_evals_sep (w work aux dout hold hout : List Bool) :
    EvalsToInTime sanitizeComputer.step
      (hostCfg (some .parse) none (false :: w) work aux dout hold hout)
      (some (hostCfg (some .takeW) (some false) w work aux dout hold hout))
      1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (hostCfg (some .parse) none (false :: w) work aux dout hold hout)).bind
        sanitizeComputer.step =
      some (hostCfg (some .takeW) (some false) w work aux dout hold hout)
    simpa [FinTM2.step] using host_step_parse_false w work aux dout hold hout

noncomputable def host_evals_take (v : Option Bool)
    (w work aux dout hold hout : List Bool) :
    EvalsToInTime sanitizeComputer.step
      (hostCfg (some .takeW) v w work aux dout hold hout)
      (some (hostCfg (some .revX) none [] work aux dout (w.reverse ++ hold) hout))
      (w.length + 1) := by
  induction w generalizing hold v with
  | nil =>
      exact host_evals_step (host_step_take_nil v work aux dout hold hout)
  | cons b bs ih =>
      have h1 := host_evals_step
        (host_step_take_bit v b bs work aux dout hold hout)
      have h2 := ih none (b :: hold)
      have h := EvalsToInTime.trans sanitizeComputer.step 1 (bs.length + 1)
        _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc, Nat.succ_eq_add_one] using h

noncomputable def host_evals_rev (rev acc aux dout hold hout : List Bool) :
    EvalsToInTime sanitizeComputer.step
      (hostCfg (some .revX) none acc rev aux dout hold hout)
      (some (hostCfg (some (.dfr .dupToAux)) none (rev.reverse ++ acc) [] aux dout hold hout))
      (rev.length + 1) := by
  induction rev generalizing acc with
  | nil =>
      exact host_evals_step (host_step_rev_nil acc aux dout hold hout)
  | cons b bs ih =>
      have h1 := host_evals_step (host_step_rev_bit b bs acc aux dout hold hout)
      have h2 := ih (b :: acc)
      have h := EvalsToInTime.trans sanitizeComputer.step 1 (bs.length + 1) _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

/-- Phase 0 lands on the lifted decode start state with witness bits reversed on `hold`. -/
noncomputable def host_evals_phase0 (x w : List Bool) :
    EvalsToInTime sanitizeComputer.step
      (initList sanitizeComputer (encodePair (x, w)))
      (some (hostCfg (some (.dfr .dupToAux)) none x [] [] [] w.reverse []))
      (3 * x.length + w.length + 3) := by
  have hparse := host_evals_parse x (false :: w) [] [] [] [] []
  have hsep := host_evals_sep w (x.reverse ++ []) [] [] [] []
  have h1 := EvalsToInTime.trans sanitizeComputer.step (2 * x.length) 1 _ _ _ hparse hsep
  have htake := host_evals_take (some false) w (x.reverse ++ []) [] [] [] []
  have h2 := EvalsToInTime.trans sanitizeComputer.step (1 + 2 * x.length) (w.length + 1)
    _ _ _ h1 htake
  have hrev := host_evals_rev (x.reverse ++ []) [] [] [] (w.reverse ++ []) []
  have h3 := EvalsToInTime.trans sanitizeComputer.step
    ((w.length + 1) + (1 + 2 * x.length)) ((x.reverse ++ []).length + 1) _ _ _ h2 hrev
  have h3s : EvalsToInTime sanitizeComputer.step
      (hostCfg (some .parse) none (encodePair (x, w)) [] [] [] [] [])
      (some (hostCfg (some (.dfr .dupToAux)) none x [] [] [] w.reverse []))
      (x.length + 1 + (w.length + 1 + (1 + 2 * x.length))) := by
    simpa [encodePair, List.append_nil, List.reverse_reverse, List.length_reverse] using h3
  have hm : x.length + 1 + (w.length + 1 + (1 + 2 * x.length)) ≤
      3 * x.length + w.length + 3 := by omega
  have h3' := evalsToInTime_le_mono h3s hm
  rw [sanitize_initList]
  exact h3'

/-! ## Inner decode simulates on the host -/

theorem iterate_bind_none {σ : Type*} (f : σ → Option σ) {a : Option σ} {n m : ℕ}
    (h : (flip bind f)^[n] a = none) (hm : n ≤ m) :
    (flip bind f)^[m] a = none := by
  induction hm with
  | refl => exact h
  | step _ ih =>
      rw [Function.iterate_succ_apply', ih]
      rfl

theorem dfr_step_none_of_label_none (v : Option Bool) (S : ∀ k : DFRStack, List Bool) :
    decodeFormulaResultComputer.step ⟨none, v, S⟩ = none := by
  simp [FinTM2.step, TM2.step]
  rfl

theorem prehalt_dfr_label {c halt : decodeFormulaResultComputer.Cfg} {N : ℕ}
    (hN : (flip bind decodeFormulaResultComputer.step)^[N] (some c) = some halt)
    (_hh : halt.l = none) {k : ℕ} (hk : k < N) {c' : decodeFormulaResultComputer.Cfg}
    (hk' : (flip bind decodeFormulaResultComputer.step)^[k] (some c) = some c') :
    c'.l ≠ none := by
  intro hnone
  cases c' with
  | mk l v S =>
      cases l with
      | none =>
          have h1 : (flip bind decodeFormulaResultComputer.step)^[k + 1] (some c) = none := by
            rw [Function.iterate_succ_apply', hk']
            exact dfr_step_none_of_label_none v S
          have hnone' := iterate_bind_none decodeFormulaResultComputer.step h1
            (Nat.succ_le_of_lt hk)
          have : some halt = none := by
            rw [← hN]
            exact hnone'
          cases this
      | some _ =>
          cases hnone

theorem host_step_translate {c : decodeFormulaResultComputer.Cfg}
    (hl : c.l ≠ none) (extra : HostExtra → List Bool) :
    sanitizeComputer.step (translateDFR extra c) =
      Option.map (translateDFR extra) (decodeFormulaResultComputer.step c) := by
  cases c with
  | mk l v S =>
      cases l with
      | none => exact (hl rfl).elim
      | some lab =>
          simp only [translateDFR, FinTM2.step, TM2.step, sanitizeComputer]
          exact congrArg some
            (liftStmt_stepAux HostLabel.dfr (fun _ => HostLabel.after)
              (decodeFormulaResultComputer.m lab) v S extra)

theorem iterate_translate (n : ℕ) (c : decodeFormulaResultComputer.Cfg)
    (extra : HostExtra → List Bool)
    (hpre : ∀ k < n, ∀ c',
      (flip bind decodeFormulaResultComputer.step)^[k] (some c) = some c' → c'.l ≠ none) :
    (flip bind sanitizeComputer.step)^[n] (some (translateDFR extra c)) =
      Option.map (translateDFR extra)
        ((flip bind decodeFormulaResultComputer.step)^[n] (some c)) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have hpre' : ∀ k < n, ∀ c',
          (flip bind decodeFormulaResultComputer.step)^[k] (some c) = some c' →
            c'.l ≠ none :=
        fun k hk c' hc => hpre k (Nat.lt_trans hk (Nat.lt_succ_self _)) c' hc
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih hpre']
      cases hiter : (flip bind decodeFormulaResultComputer.step)^[n] (some c) with
      | none =>
          rfl
      | some c' =>
          have hlab : c'.l ≠ none := hpre n (Nat.lt_succ_self _) c' hiter
          simp only [Option.map_some]
          exact host_step_translate hlab extra

theorem translate_initList (x wRev : List Bool) :
    translateDFR (phase0Extra wRev) (initList decodeFormulaResultComputer x) =
      hostCfg (some (.dfr .dupToAux)) none x [] [] [] wRev [] := by
  refine congrArg (fun stk =>
      (⟨some (HostLabel.dfr DFRLabel.dupToAux), none, stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s =>
      cases s with
      | inp =>
          simpa [translateDFR, translateCfg, embedStk, hostStk, phase0Extra] using
            initList_stk_k₀ decodeFormulaResultComputer x
      | work =>
          simpa [translateDFR, translateCfg, embedStk, hostStk, phase0Extra] using
            initList_stk_of_ne decodeFormulaResultComputer x DFRStack.work
              (by simp [decodeFormulaResultComputer])
      | aux =>
          simpa [translateDFR, translateCfg, embedStk, hostStk, phase0Extra] using
            initList_stk_of_ne decodeFormulaResultComputer x DFRStack.aux
              (by simp [decodeFormulaResultComputer])
      | out =>
          simpa [translateDFR, translateCfg, embedStk, hostStk, phase0Extra] using
            initList_stk_of_ne decodeFormulaResultComputer x DFRStack.out
              (by simp [decodeFormulaResultComputer])
  | inr e =>
      cases e <;> simp [translateDFR, translateCfg, embedStk, hostStk, phase0Extra]

theorem translate_haltList (out wRev : List Bool) :
    translateDFR (phase0Extra wRev) (haltList decodeFormulaResultComputer out) =
      hostCfg (some .after) none [] [] [] out wRev [] := by
  refine congrArg (fun stk =>
      (⟨some HostLabel.after, (none : Option Bool), stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s =>
      cases s with
      | out =>
          simpa [translateDFR, translateCfg, embedStk, hostStk, phase0Extra] using
            haltList_stk_k₁ decodeFormulaResultComputer out
      | inp =>
          simpa [translateDFR, translateCfg, embedStk, hostStk, phase0Extra] using
            haltList_stk_of_ne decodeFormulaResultComputer out DFRStack.inp
              (by simp [decodeFormulaResultComputer])
      | work =>
          simpa [translateDFR, translateCfg, embedStk, hostStk, phase0Extra] using
            haltList_stk_of_ne decodeFormulaResultComputer out DFRStack.work
              (by simp [decodeFormulaResultComputer])
      | aux =>
          simpa [translateDFR, translateCfg, embedStk, hostStk, phase0Extra] using
            haltList_stk_of_ne decodeFormulaResultComputer out DFRStack.aux
              (by simp [decodeFormulaResultComputer])
  | inr e =>
      cases e <;> simp [translateDFR, translateCfg, embedStk, hostStk, phase0Extra]

noncomputable def host_evals_dfr (x : List Bool) (wRev : List Bool) :
    EvalsToInTime sanitizeComputer.step
      (hostCfg (some (.dfr .dupToAux)) none x [] [] [] wRev [])
      (some (hostCfg (some .after) none [] [] [] (decodeFormulaResult x) wRev []))
      (10 * x.length + 10) := by
  have hrun : EvalsToInTime decodeFormulaResultComputer.step
      (initList decodeFormulaResultComputer x)
      (some (haltList decodeFormulaResultComputer (decodeFormulaResult x)))
      (10 * x.length + 10) := by
    have h := decodeFormulaResultComputableInPolyTime.outputsFun x
    change TM2OutputsInTime decodeFormulaResultComputer (List.map id (idBitEnc x))
        (some (List.map id (idBitEnc (decodeFormulaResult x))))
        (decodeFormulaResultTime.eval (idBitEnc x).length) at h
    simp only [idBitEnc, List.map_id, id_eq, decodeFormulaResultTime_eval] at h
    exact h
  have hpre : ∀ k < hrun.steps, ∀ c',
      (flip bind decodeFormulaResultComputer.step)^[k]
        (some (initList decodeFormulaResultComputer x)) = some c' → c'.l ≠ none := by
    intro k hk c' hc
    exact prehalt_dfr_label hrun.evals_in_steps rfl hk hc
  have hiter := iterate_translate hrun.steps
    (initList decodeFormulaResultComputer x) (phase0Extra wRev) hpre
  rw [hrun.evals_in_steps] at hiter
  have hiter' : (flip bind sanitizeComputer.step)^[hrun.steps]
      (some (hostCfg (some (.dfr .dupToAux)) none x [] [] [] wRev [])) =
      some (hostCfg (some .after) none [] [] [] (decodeFormulaResult x) wRev []) := by
    simpa [translate_initList, translate_haltList] using hiter
  exact ⟨⟨hrun.steps, hiter'⟩, hrun.steps_le_m⟩

-- The packaging above uses `steps_le_m` against `10 * |x| + 10`, which is
-- `decodeFormulaResultTime`. Rebuild the bound explicitly so the goal sees it.
theorem host_evals_dfr_bound (x : List Bool) :
    decodeFormulaResultTime.eval x.length = 10 * x.length + 10 :=
  decodeFormulaResultTime_eval x.length

/-! ## Emit `dummyEvalInput` or `encodePair (w, x)` -/

theorem host_step_after_false (x work aux hold hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .after) none [] work aux (false :: x) hold hout) =
      some (hostCfg (some .revCode) (some false) [] work aux x hold hout) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some HostLabel.revCode, some false, stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

theorem host_step_after_true (rest work aux hold hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .after) none [] work aux (true :: rest) hold hout) =
      some (hostCfg (some .dummy) (some true) [] work aux rest hold hout) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some HostLabel.dummy, some true, stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

theorem host_step_dummy_nil (v : Option Bool) (work aux hold hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .dummy) v [] work aux [] hold hout) =
      some (hostCfg (some .clearHold) none [] work aux [] hold hout) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some HostLabel.clearHold, (none : Option Bool), stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

theorem host_step_clear_bit (b : Bool) (rest work aux hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .clearHold) none [] work aux [] (b :: rest) hout) =
      some (hostCfg (some .clearHold) none [] work aux [] rest hout) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some HostLabel.clearHold, (none : Option Bool), stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

theorem host_step_clear_nil (work aux hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .clearHold) none [] work aux [] [] hout) =
      some (hostCfg none none [] work aux [] []
        (true :: false :: false :: false :: false :: false :: hout)) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option HostLabel), (none : Option Bool), stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

theorem host_step_revCode_bit (v : Option Bool) (b : Bool)
    (rest aux hold hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .revCode) v [] [] aux (b :: rest) hold hout) =
      some (hostCfg (some .revCode) none [] [] (b :: aux) rest hold hout) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some HostLabel.revCode, (none : Option Bool), stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

theorem host_step_revCode_nil (v : Option Bool) (aux hold hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .revCode) v [] [] aux [] hold hout) =
      some (hostCfg (some .flushX) none [] [] aux [] hold hout) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some HostLabel.flushX, (none : Option Bool), stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

theorem host_step_flush_bit (b : Bool) (rest hold hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .flushX) none [] [] (b :: rest) [] hold hout) =
      some (hostCfg (some .flushX) none [] [] rest [] hold (b :: hout)) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some HostLabel.flushX, (none : Option Bool), stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

theorem host_step_flush_nil (hold hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .flushX) none [] [] [] [] hold hout) =
      some (hostCfg (some .flushW) none [] [] [] [] hold (false :: hout)) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some HostLabel.flushW, (none : Option Bool), stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

theorem host_step_flushW_bit (b : Bool) (rest hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .flushW) none [] [] [] [] (b :: rest) hout) =
      some (hostCfg (some .flushW) none [] [] [] [] rest (true :: b :: hout)) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some HostLabel.flushW, (none : Option Bool), stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

theorem host_step_flushW_nil (hout : List Bool) :
    TM2.step sanitizeComputer.m
        (hostCfg (some .flushW) none [] [] [] [] [] hout) =
      some (hostCfg none none [] [] [] [] [] hout) := by
  simp [sanitizeComputer, hostCfg, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option HostLabel), (none : Option Bool), stk⟩ : sanitizeComputer.Cfg)) ?_
  funext k
  cases k with
  | inl s => cases s <;> (simp [hostStk, Function.update]; try rfl)
  | inr e => cases e <;> (simp [hostStk, Function.update]; try rfl)

/-- Pairs written in reverse, so the last popped witness bit ends up at the head. -/
def prependPairs (wRev hout : List Bool) : List Bool :=
  match wRev with
  | [] => hout
  | b :: bs => prependPairs bs (true :: b :: hout)

theorem prependPairs_append_singleton (ys : List Bool) (b : Bool) (hout : List Bool) :
    prependPairs (ys ++ [b]) hout = true :: b :: prependPairs ys hout := by
  induction ys generalizing hout with
  | nil => simp [prependPairs]
  | cons y ys ih =>
      simp [prependPairs, ih]

theorem prependPairs_encodePair (w x : List Bool) :
    prependPairs w.reverse (false :: x) = encodePair (w, x) := by
  induction w with
  | nil => simp [prependPairs, encodePair]
  | cons b bs ih =>
      rw [List.reverse_cons, prependPairs_append_singleton, ih]
      simp [encodePair, List.flatMap]

noncomputable def host_evals_revCode (v : Option Bool) (x acc hold hout : List Bool) :
    EvalsToInTime sanitizeComputer.step
      (hostCfg (some .revCode) v [] [] acc x hold hout)
      (some (hostCfg (some .flushX) none [] [] (x.reverse ++ acc) [] hold hout))
      (x.length + 1) := by
  induction x generalizing acc v with
  | nil =>
      exact host_evals_step (host_step_revCode_nil v acc hold hout)
  | cons b bs ih =>
      have h1 := host_evals_step (host_step_revCode_bit v b bs acc hold hout)
      have h2 := ih none (b :: acc)
      have h := EvalsToInTime.trans sanitizeComputer.step 1 (bs.length + 1) _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

noncomputable def host_evals_flush (rev hold hout : List Bool) :
    EvalsToInTime sanitizeComputer.step
      (hostCfg (some .flushX) none [] [] rev [] hold hout)
      (some (hostCfg (some .flushW) none [] [] [] [] hold (false :: rev.reverse ++ hout)))
      (rev.length + 1) := by
  induction rev generalizing hout with
  | nil =>
      exact host_evals_step (host_step_flush_nil hold hout)
  | cons b bs ih =>
      have h1 := host_evals_step (host_step_flush_bit b bs hold hout)
      have h2 := ih (b :: hout)
      have h := EvalsToInTime.trans sanitizeComputer.step 1 (bs.length + 1) _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

noncomputable def host_evals_flushW (wRev hout : List Bool) :
    EvalsToInTime sanitizeComputer.step
      (hostCfg (some .flushW) none [] [] [] [] wRev hout)
      (some (hostCfg none none [] [] [] [] [] (prependPairs wRev hout)))
      (wRev.length + 1) := by
  induction wRev generalizing hout with
  | nil =>
      simpa [prependPairs] using host_evals_step (host_step_flushW_nil hout)
  | cons b bs ih =>
      have h1 := host_evals_step (host_step_flushW_bit b bs hout)
      have h2 := ih (true :: b :: hout)
      have h := EvalsToInTime.trans sanitizeComputer.step 1 (bs.length + 1) _ _ _ h1 h2
      simpa [prependPairs, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

noncomputable def host_evals_clear (hold work aux hout : List Bool) :
    EvalsToInTime sanitizeComputer.step
      (hostCfg (some .clearHold) none [] work aux [] hold hout)
      (some (hostCfg none none [] work aux [] []
        (true :: false :: false :: false :: false :: false :: hout)))
      (hold.length + 1) := by
  induction hold generalizing hout with
  | nil =>
      exact host_evals_step (host_step_clear_nil work aux hout)
  | cons b bs ih =>
      have h1 := host_evals_step (host_step_clear_bit b bs work aux hout)
      have h2 := ih hout
      have h := EvalsToInTime.trans sanitizeComputer.step 1 (bs.length + 1) _ _ _ h1 h2
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Decode failure clears the parked witness and emits the fixed false instance. -/
noncomputable def host_evals_emit_none (wRev : List Bool) :
    EvalsToInTime sanitizeComputer.step
      (hostCfg (some .after) none [] [] [] [true] wRev [])
      (some (haltList sanitizeComputer dummyEvalInput))
      (wRev.length + 3) := by
  have h1 := host_evals_step (host_step_after_true [] [] [] wRev [])
  have h2 := host_evals_step (host_step_dummy_nil (some true) [] [] wRev [])
  have h3 := host_evals_clear wRev [] [] []
  have h12 := EvalsToInTime.trans sanitizeComputer.step 1 1 _ _ _ h1 h2
  have h := EvalsToInTime.trans sanitizeComputer.step (1 + 1) (wRev.length + 1) _ _ _ h12 h3
  simpa [sanitize_haltList, dummyEvalInput_eq, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using h

/-- Decode success emits `encodePair (w, x)` from the reversed witness. -/
noncomputable def host_evals_emit_some (x w : List Bool) :
    EvalsToInTime sanitizeComputer.step
      (hostCfg (some .after) none [] [] [] (false :: x) w.reverse [])
      (some (haltList sanitizeComputer (encodePair (w, x))))
      (2 * x.length + w.length + 4) := by
  have hpop := host_evals_step (host_step_after_false x [] [] (w.reverse) [])
  have hrev := host_evals_revCode (some false) x [] (w.reverse) []
  have h1 := EvalsToInTime.trans sanitizeComputer.step 1 (x.length + 1) _ _ _ hpop hrev
  have hflush0 := host_evals_flush (x.reverse ++ []) (w.reverse) []
  have hflush : EvalsToInTime sanitizeComputer.step
      (hostCfg (some .flushX) none [] [] (x.reverse ++ []) [] w.reverse [])
      (some (hostCfg (some .flushW) none [] [] [] [] w.reverse (false :: x)))
      (x.reverse.length + 1) := by
    simpa [List.append_nil, List.reverse_reverse] using hflush0
  have h2 := EvalsToInTime.trans sanitizeComputer.step (x.length + 1 + 1)
    (x.reverse.length + 1) _ _ _ h1 hflush
  have hW := host_evals_flushW w.reverse (false :: x)
  have h3 := EvalsToInTime.trans sanitizeComputer.step
    (x.reverse.length + 1 + (x.length + 1 + 1)) (w.reverse.length + 1)
    _ _ _ h2 hW
  have hm : w.reverse.length + 1 + (x.reverse.length + 1 + (x.length + 1 + 1)) ≤
      2 * x.length + w.length + 4 := by
    simp [List.length_reverse]
    omega
  have h3' : EvalsToInTime sanitizeComputer.step
      (hostCfg (some .after) none [] [] [] (false :: x) w.reverse [])
      (some (hostCfg none none [] [] [] [] [] (encodePair (w, x))))
      (2 * x.length + w.length + 4) :=
    evalsToInTime_le_mono
      (by simpa [prependPairs_encodePair] using h3) hm
  simpa [sanitize_haltList] using h3'

noncomputable def host_evals_sanitize (x w : List Bool) :
    EvalsToInTime sanitizeComputer.step
      (initList sanitizeComputer (encodePair (x, w)))
      (some (haltList sanitizeComputer (sanitizeInput x w)))
      (20 * (encodePair (x, w)).length + 40) := by
  have h0 := host_evals_phase0 x w
  have hd := host_evals_dfr x w.reverse
  have h01 := EvalsToInTime.trans sanitizeComputer.step
    (3 * x.length + w.length + 3) (10 * x.length + 10) _ _ _ h0 hd
  cases hdec : decodeFormula x with
  | none =>
      have htag : decodeFormulaResult x = [true] := decodeFormulaResult_of_none hdec
      have hem := host_evals_emit_none w.reverse
      have h := EvalsToInTime.trans sanitizeComputer.step
        ((10 * x.length + 10) + (3 * x.length + w.length + 3))
        (w.reverse.length + 3) _ _ _ h01
        (by simpa [htag] using hem)
      have hlen := length_encodePair (x, w)
      have hle : w.reverse.length + 3 +
          (10 * x.length + 10 + (3 * x.length + w.length + 3)) ≤
          20 * (encodePair (x, w)).length + 40 := by
        simp only [hlen, List.length_reverse]
        omega
      simpa [sanitizeInput, hdec] using evalsToInTime_le_mono h hle
  | some φ =>
      have hx : x = encodeFormula φ := (encodeFormula_of_decodeFormula hdec).symm
      have htag : decodeFormulaResult x = false :: x := by
        simpa [hx] using decodeFormulaResult_encodeFormula φ
      have hem := host_evals_emit_some x w
      have h := EvalsToInTime.trans sanitizeComputer.step
        ((10 * x.length + 10) + (3 * x.length + w.length + 3))
        (2 * x.length + w.length + 4) _ _ _ h01 (by simpa [htag] using hem)
      have hlen := length_encodePair (x, w)
      have hle : 2 * x.length + w.length + 4 +
          (10 * x.length + 10 + (3 * x.length + w.length + 3)) ≤
          20 * (encodePair (x, w)).length + 40 := by
        simp only [hlen]
        omega
      simpa [sanitizeInput, hdec] using evalsToInTime_le_mono h hle

/-! ## Package `sanitizeInput` as poly time under `encodePair` -/

noncomputable def sanitizeTime : Polynomial ℕ := 20 * Polynomial.X + 40

theorem sanitizeTime_eval (n : ℕ) : sanitizeTime.eval n = 20 * n + 40 := by
  simp [sanitizeTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_ofNat]

/-- `sanitizeComputer` realizes `sanitizeInput` under the pair encoding. -/
noncomputable def sanitizeComputableInPolyTime :
    TM2ComputableInPolyTime encodePair idBitEnc (fun pw => sanitizeInput pw.1 pw.2) where
  tm := sanitizeComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := sanitizeTime
  outputsFun pw := by
    rcases pw with ⟨x, w⟩
    change TM2OutputsInTime sanitizeComputer (List.map id (encodePair (x, w)))
      (some (List.map id (idBitEnc (sanitizeInput x w))))
      (sanitizeTime.eval (encodePair (x, w)).length)
    simp only [idBitEnc, List.map_id, id_eq, sanitizeTime_eval]
    exact evalsToInTime_le_mono (host_evals_sanitize x w) (by omega)

/-! ## Evaluate a sanitized tape, then negate -/

/-- Semantic bit produced by evaluating the sanitized tape. -/
def evalOnSanitizeInput (x w : List Bool) : Bool :=
  match decodeFormula x with
  | none => false
  | some φ => φ.evalOn w

theorem tautComplV_eq_not_eval (x w : List Bool) :
    tautComplV x w = !(evalOnSanitizeInput x w) := by
  cases h : decodeFormula x with
  | none => simp [tautComplV, evalOnSanitizeInput, h]
  | some φ => simp [tautComplV, evalOnSanitizeInput, h]

theorem dummyEvalInput_length : dummyEvalInput.length = 6 := by
  simp [dummyEvalInput_eq]

theorem length_sanitizeInput_le (x w : List Bool) :
    (sanitizeInput x w).length ≤ 2 * (encodePair (x, w)).length + 6 := by
  cases hdec : decodeFormula x with
  | none =>
      simpa [sanitizeInput, hdec, dummyEvalInput_length] using
        (Nat.le_add_left 6 (2 * (encodePair (x, w)).length))
  | some _ =>
      simp [sanitizeInput, hdec, length_encodePair]
      omega

theorem evalEncodedTime_mono {a b : ℕ} (h : a ≤ b) :
    evalEncodedTime.eval a ≤ evalEncodedTime.eval b := by
  simp only [evalEncodedTime_eval]
  exact Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (Nat.succ_le_succ h) 3)

noncomputable def evalEncoded_sanitize (x w : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (initList evalEncodedComputer (sanitizeInput x w))
      (some (haltList evalEncodedComputer [evalOnSanitizeInput x w]))
      (evalEncodedTime.eval (sanitizeInput x w).length) := by
  cases hdec : decodeFormula x with
  | none =>
      have hs : sanitizeInput x w = dummyEvalInput := sanitizeInput_none hdec
      have he : evalOnSanitizeInput x w = false := by simp [evalOnSanitizeInput, hdec]
      have h := evalEncodedComputableInPolyTime.outputsFun (dummyAssign, .var 0)
      change TM2OutputsInTime evalEncodedComputer
          (List.map id (encodePair (dummyAssign, encodeFormula (.var 0))))
          (some (List.map id (bitEnc ((PropFormula.var 0).evalOn dummyAssign))))
          (evalEncodedTime.eval (encodePair (dummyAssign, encodeFormula (.var 0))).length) at h
      simp only [List.map_id, bitEnc, var0_evalOn_false] at h
      simpa [hs, he, dummyEvalInput, var0Code] using h
  | some φ =>
      have hx : encodeFormula φ = x := encodeFormula_of_decodeFormula hdec
      have hs : sanitizeInput x w = encodePair (w, x) := sanitizeInput_some hdec
      have he : evalOnSanitizeInput x w = φ.evalOn w := by simp [evalOnSanitizeInput, hdec]
      have h := evalEncodedComputableInPolyTime.outputsFun (w, φ)
      change TM2OutputsInTime evalEncodedComputer
          (List.map id (encodePair (w, encodeFormula φ)))
          (some (List.map id (bitEnc (φ.evalOn w))))
          (evalEncodedTime.eval (encodePair (w, encodeFormula φ)).length) at h
      simpa [hs, he, hx, List.map_id, bitEnc] using h

/-- Combined verifier bit after sanitize then eval then negate. -/
noncomputable def tautComplComputableInPolyTime :
    TM2ComputableInPolyTime encodePair bitEnc (fun pw => tautComplV pw.1 pw.2) := by
  let decodeOut1 : sanitizeComputer.Γ sanitizeComputer.k₁ → Bool := id
  let encodeIn1 : Bool → evalEncodedComputer.Γ evalEncodedComputer.k₀ := id
  let tm1 :=
    seqCompComputer (βΓ := Bool) sanitizeComputer evalEncodedComputer decodeOut1 encodeIn1
  let decodeOut2 : tm1.Γ tm1.k₁ → Bool := id
  let encodeIn2 : Bool → notBitComputer.Γ notBitComputer.k₀ := id
  let tm := seqCompComputer (βΓ := Bool) tm1 notBitComputer decodeOut2 encodeIn2
  let inA : tm.Γ tm.k₀ ≃ Bool := by
    simpa [tm, tm1, seqCompComputer, CompΓ, CompK] using (Equiv.refl Bool)
  let outA : tm.Γ tm.k₁ ≃ Bool := by
    simpa [tm, seqCompComputer, CompΓ, CompK] using (Equiv.refl Bool)
  -- Exact analytic majorant: sanitize + pair-copy linear + eval at length ≤ 2|pair|+6.
  let timeBound : Polynomial ℕ :=
    sanitizeTime + (8 * Polynomial.X + 34) +
      evalEncodedTime.comp (2 * Polynomial.X + 6)
  refine
    { tm := tm
      inputAlphabet := inA
      outputAlphabet := outA
      time := timeBound
      outputsFun := ?out }
  case out =>
    intro pw
    rcases pw with ⟨x, w⟩
    change TM2OutputsInTime tm (List.map inA.invFun (encodePair (x, w)))
      (some (List.map outA.invFun (bitEnc (tautComplV x w))))
      (timeBound.eval (encodePair (x, w)).length)
    have hin :
        List.map inA.invFun (encodePair (x, w)) = encodePair (x, w) := by
      change List.map (Equiv.refl Bool).symm (encodePair (x, w)) = encodePair (x, w)
      simp
    have hout :
        List.map outA.invFun (bitEnc (tautComplV x w)) = [tautComplV x w] := by
      change List.map (Equiv.refl Bool).symm (bitEnc (tautComplV x w)) = [tautComplV x w]
      simp [bitEnc]
    have hsan' : EvalsToInTime sanitizeComputer.step
        (initList sanitizeComputer (encodePair (x, w)))
        (some (haltList sanitizeComputer (sanitizeInput x w)))
        (sanitizeTime.eval (encodePair (x, w)).length) := by
      simpa [sanitizeTime_eval] using
        evalsToInTime_le_mono (host_evals_sanitize x w) (by omega)
    have heval := evalEncoded_sanitize x w
    have hmid_map :
        (sanitizeInput x w).map (encodeIn1 ∘ decodeOut1) = sanitizeInput x w := by
      change List.map (id ∘ id) (sanitizeInput x w) = sanitizeInput x w
      simp [List.map_id]
    have heval' : EvalsToInTime evalEncodedComputer.step
        (initList evalEncodedComputer
          ((sanitizeInput x w).map (encodeIn1 ∘ decodeOut1)))
        (some (haltList evalEncodedComputer [evalOnSanitizeInput x w]))
        (evalEncodedTime.eval (sanitizeInput x w).length) := by
      simpa [hmid_map] using heval
    have hcomp1 :=
      seqComp_evals_compose (βΓ := Bool) sanitizeComputer evalEncodedComputer
        decodeOut1 encodeIn1 (encodePair (x, w)) (sanitizeInput x w)
        [evalOnSanitizeInput x w]
        (sanitizeTime.eval (encodePair (x, w)).length)
        (evalEncodedTime.eval (sanitizeInput x w).length)
        hsan' heval'
    have hnot : EvalsToInTime notBitComputer.step
        (initList notBitComputer [evalOnSanitizeInput x w])
        (some (haltList notBitComputer [!(evalOnSanitizeInput x w)])) 2 :=
      notBit_evals_one (evalOnSanitizeInput x w)
    have hmid2_map :
        [evalOnSanitizeInput x w].map (encodeIn2 ∘ decodeOut2) =
          [evalOnSanitizeInput x w] := by
      change List.map (id ∘ id) [evalOnSanitizeInput x w] = [evalOnSanitizeInput x w]
      simp [List.map_id]
    have hnot' : EvalsToInTime notBitComputer.step
        (initList notBitComputer
          ([evalOnSanitizeInput x w].map (encodeIn2 ∘ decodeOut2)))
        (some (haltList notBitComputer [!(evalOnSanitizeInput x w)])) 2 := by
      simpa [hmid2_map] using hnot
    set m1 :=
      sanitizeTime.eval (encodePair (x, w)).length +
        (2 * (sanitizeInput x w).length + 1) +
        (2 * (sanitizeInput x w).length + 1) +
        evalEncodedTime.eval (sanitizeInput x w).length with hm1
    have hcomp2 :=
      seqComp_evals_compose (βΓ := Bool) tm1 notBitComputer decodeOut2 encodeIn2
        (encodePair (x, w)) [evalOnSanitizeInput x w] [!(evalOnSanitizeInput x w)]
        m1 2 (by simpa [hm1] using hcomp1) hnot'
    have hle : m1 + (2 * [evalOnSanitizeInput x w].length + 1) +
        (2 * [evalOnSanitizeInput x w].length + 1) + 2 ≤
        timeBound.eval (encodePair (x, w)).length := by
      have hsan_len := length_sanitizeInput_le x w
      have heval_le := evalEncodedTime_mono hsan_len
      -- |san| ≤ 2n+6, so eval cost ≤ evalEncodedTime.eval (2n+6)
      simp only [hm1, timeBound, sanitizeTime_eval, evalEncodedTime_eval,
        List.length_singleton, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.eval_ofNat, Polynomial.eval_comp] at heval_le ⊢
      omega
    have hfinal := evalsToInTime_le_mono hcomp2 hle
    have hout' : List.map outA.invFun (bitEnc (tautComplV x w)) =
        [!(evalOnSanitizeInput x w)] := by
      simpa [tautComplV_eq_not_eval] using hout
    have hraw : EvalsToInTime tm.step
        (initList tm (encodePair (x, w)))
        (some (haltList tm [!(evalOnSanitizeInput x w)]))
        (timeBound.eval (encodePair (x, w)).length) := by
      simpa [tm] using hfinal
    refine evalsToInTime_congr_end
      (by
        have hstart :
            initList tm (List.map inA.invFun (encodePair (x, w))) =
              initList tm (encodePair (x, w)) :=
          congrArg (initList tm) hin
        exact { steps := hraw.steps
                steps_le_m := hraw.steps_le_m
                evals_in_steps := by
                  rw [hstart]
                  exact hraw.evals_in_steps })
      (congrArg some (congrArg (haltList tm) hout'.symm))

/-- Witness length bound for the coNP verifier of `TAUT`: one bit past `maxVar`. -/
noncomputable def tautComplWitnessBound : Polynomial ℕ := Polynomial.X + 1

/-- `TAUT` is in coNP: nontautologies (and malformed codes) have short NP witnesses. -/
theorem TAUT_in_coNP : InCoNP TAUT := by
  refine ⟨tautComplWitnessBound, tautComplV, tautComplComputableInPolyTime, ?_⟩
  intro x
  simpa [complement, tautComplWitnessBound] using tautComplV_witness x

/-! ## Poly-bounded proof systems put `TAUT` in NP (hard direction, local fragment) -/

/-- Verifier that checks a candidate proof string under a fixed proof map `f`. -/
def proofCheck (f : List Bool → List Bool) (φ π : List Bool) : Bool :=
  decide (f π = φ)

theorem proofCheck_iff (f : List Bool → List Bool) (φ π : List Bool) :
    proofCheck f φ π = true ↔ f π = φ := by
  simp [proofCheck]

/-- Semantic half of the hard direction: a polynomially bounded proof system yields
short NP witnesses for `TAUT`. The poly-time TM packaging of `proofCheck` is the
remaining FinTM2 glue (decode pair, run `f`, compare). -/
theorem TAUT_short_proofs_of_polyBounded {f : List Bool → List Bool}
    (hf : IsPropProofSystem f) {q : Polynomial ℕ}
    (hq : ∀ φ, TAUT φ → ∃ π, f π = φ ∧ π.length ≤ q.eval φ.length)
    (φ : List Bool) :
    TAUT φ ↔ ∃ π, π.length ≤ q.eval φ.length ∧ proofCheck f φ π = true := by
  constructor
  · intro hφ
    rcases hq φ hφ with ⟨π, hπ, hlen⟩
    exact ⟨π, hlen, (proofCheck_iff f φ π).2 hπ⟩
  · intro ⟨π, _, hcheck⟩
    have hπ : f π = φ := (proofCheck_iff f φ π).1 hcheck
    simpa [hπ] using hf.sound π

theorem TAUT_short_proofs_of_polyBounded' {f : List Bool → List Bool}
    (hf : IsPropProofSystem f) (hb : PolynomiallyBounded f) (φ : List Bool) :
    TAUT φ ↔
      ∃ π, π.length ≤ (Classical.choose hb).eval φ.length ∧ proofCheck f φ π = true := by
  have hq := Classical.choose_spec hb
  exact TAUT_short_proofs_of_polyBounded hf hq φ
/-! ## Easy direction scaffolding: NP verifier to proof map -/

/-- From an NP verifier for `TAUT`, build the Cook Reckhow proof map:
decode a pair `(φ, w)`; emit `φ` when the witness is short and accepted; otherwise
emit the fixed tautology seed. -/
def proofSystemOfNPVerifier (p : Polynomial ℕ)
    (V : List Bool → List Bool → Bool) (π : List Bool) : List Bool :=
  match decodePair π with
  | none => encodeFormula tautSeed
  | some (φ, w) =>
      if decide (w.length ≤ p.eval φ.length) && V φ w then φ
      else encodeFormula tautSeed

theorem proofSystemOfNPVerifier_sound (p : Polynomial ℕ)
    (V : List Bool → List Bool → Bool)
    (hV : ∀ φ, TAUT φ ↔
      ∃ w, w.length ≤ p.eval φ.length ∧ V φ w = true)
    (π : List Bool) : TAUT (proofSystemOfNPVerifier p V π) := by
  simp only [proofSystemOfNPVerifier]
  cases hdec : decodePair π with
  | none => exact tautSeed_mem_TAUT
  | some pw =>
      rcases pw with ⟨φ, w⟩
      cases hacc : (decide (w.length ≤ p.eval φ.length) && V φ w) with
      | false =>
          simp [hdec, hacc]
          exact tautSeed_mem_TAUT
      | true =>
          simp [hdec, hacc]
          have hw : w.length ≤ p.eval φ.length ∧ V φ w = true := by
            simpa [Bool.and_eq_true, decide_eq_true_iff] using hacc
          exact (hV φ).2 ⟨w, hw.1, hw.2⟩

theorem proofSystemOfNPVerifier_complete (p : Polynomial ℕ)
    (V : List Bool → List Bool → Bool)
    (hV : ∀ φ, TAUT φ ↔
      ∃ w, w.length ≤ p.eval φ.length ∧ V φ w = true)
    (φ : List Bool) (hφ : TAUT φ) :
    ∃ π, proofSystemOfNPVerifier p V π = φ := by
  rcases (hV φ).1 hφ with ⟨w, hlen, hacc⟩
  refine ⟨encodePair (φ, w), ?_⟩
  simp [proofSystemOfNPVerifier, decodePair_encodePair, hlen, hacc]

theorem proofSystemOfNPVerifier_polyBounded (p : Polynomial ℕ)
    (V : List Bool → List Bool → Bool)
    (hV : ∀ φ, TAUT φ ↔
      ∃ w, w.length ≤ p.eval φ.length ∧ V φ w = true) :
    PolynomiallyBounded (proofSystemOfNPVerifier p V) := by
  refine ⟨2 * Polynomial.X + 1 + p, ?_⟩
  intro φ hφ
  rcases (hV φ).1 hφ with ⟨w, hlen, hacc⟩
  refine ⟨encodePair (φ, w), ?_, ?_⟩
  · simp [proofSystemOfNPVerifier, decodePair_encodePair, hlen, hacc]
  · simp [length_encodePair, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
    omega

/-! ## Easy direction FinTM2 scaffolding: strip decode tag, then accept or seed

`decodePairResult` tags success as `false :: π` and failure as `[true]`.
The post map below mirrors `afterDecodePairResult`: fail tags and reject
branches emit `encodeFormula tautSeed`; an accepting short witness emits `φ`.
Packaging `proofSystemOfNPVerifier` is then
`comp_idBitEnc_idBitEnc` of `decodePairResult` with this post map. -/

/-- Length gate used by the NP verifier proof map. -/
def lengthOk (p : Polynomial ℕ) (φ w : List Bool) : Bool :=
  decide (w.length ≤ p.eval φ.length)

theorem lengthOk_iff (p : Polynomial ℕ) (φ w : List Bool) :
    lengthOk p φ w = true ↔ w.length ≤ p.eval φ.length := by
  simp [lengthOk]

/-- Combined accept bit: short witness and `V` both succeed. -/
def acceptWitness (p : Polynomial ℕ) (V : List Bool → List Bool → Bool)
    (φ w : List Bool) : Bool :=
  lengthOk p φ w && V φ w

theorem acceptWitness_iff (p : Polynomial ℕ) (V : List Bool → List Bool → Bool)
    (φ w : List Bool) :
    acceptWitness p V φ w = true ↔
      w.length ≤ p.eval φ.length ∧ V φ w = true := by
  simp [acceptWitness, lengthOk_iff, Bool.and_eq_true]

/-- Post decode map: tagged `decodePairResult` tape to proof system output. -/
def afterDecodeProofSystem (p : Polynomial ℕ)
    (V : List Bool → List Bool → Bool) (s : List Bool) : List Bool :=
  match decodeDecodePairResult s with
  | none => encodeFormula tautSeed
  | some none => encodeFormula tautSeed
  | some (some (φ, w)) =>
      if acceptWitness p V φ w then φ else encodeFormula tautSeed

theorem afterDecodeProofSystem_fail_tag (p : Polynomial ℕ)
    (V : List Bool → List Bool → Bool) :
    afterDecodeProofSystem p V [true] = encodeFormula tautSeed := by
  simp [afterDecodeProofSystem, decodeDecodePairResult]

theorem afterDecodeProofSystem_success (p : Polynomial ℕ)
    (V : List Bool → List Bool → Bool) (φ w : List Bool) :
    afterDecodeProofSystem p V (false :: encodePair (φ, w)) =
      (if acceptWitness p V φ w then φ else encodeFormula tautSeed) := by
  simp [afterDecodeProofSystem, decodeDecodePairResult, decodePair_encodePair]

theorem afterDecodeProofSystem_of_decodePairResult (p : Polynomial ℕ)
    (V : List Bool → List Bool → Bool) (π : List Bool) :
    afterDecodeProofSystem p V (decodePairResult π) =
      proofSystemOfNPVerifier p V π := by
  cases h : decodePair π with
  | none =>
      simp [decodePairResult_of_none h, proofSystemOfNPVerifier, h,
        afterDecodeProofSystem_fail_tag]
  | some pw =>
      rcases pw with ⟨φ, w⟩
      have henc := encodePair_of_decodePair h
      subst henc
      simp [decodePairResult_of_some (decodePair_encodePair (φ, w)),
        afterDecodeProofSystem_success, proofSystemOfNPVerifier, acceptWitness,
        lengthOk, decodePair_encodePair]

theorem proofSystemOfNPVerifier_eq_afterDecode_comp (p : Polynomial ℕ)
    (V : List Bool → List Bool → Bool) (π : List Bool) :
    proofSystemOfNPVerifier p V π =
      (afterDecodeProofSystem p V ∘ decodePairResult) π :=
  (afterDecodeProofSystem_of_decodePairResult p V π).symm

/-- Output length of `afterDecodeProofSystem` is at most the input length
(plus a constant seed of length 10). -/
theorem length_afterDecodeProofSystem_le (p : Polynomial ℕ)
    (V : List Bool → List Bool → Bool) (s : List Bool) :
    (afterDecodeProofSystem p V s).length ≤ s.length + 10 := by
  unfold afterDecodeProofSystem
  cases h : decodeDecodePairResult s with
  | none =>
      simp [h, length_encodeFormula_tautSeed]
  | some r =>
      cases r with
      | none =>
          simp [h, length_encodeFormula_tautSeed]
      | some pw =>
          rcases pw with ⟨φ, w⟩
          have hφ : φ.length ≤ s.length := by
            match s with
            | [] => simp [decodeDecodePairResult] at h
            | true :: rest =>
                cases rest with
                | nil => simp [decodeDecodePairResult] at h
                | cons _ _ => simp [decodeDecodePairResult] at h
            | false :: rest =>
                simp only [decodeDecodePairResult] at h
                cases hp : decodePair rest with
                | none => simp [hp] at h
                | some p' =>
                    simp [hp] at h
                    rcases h with ⟨rfl, rfl⟩
                    exact Nat.le_trans (length_fst_le_of_decodePair hp)
                      (Nat.le_succ_of_le le_rfl)
          cases hacc : acceptWitness p V φ w with
          | false =>
              simp [h, hacc, length_encodeFormula_tautSeed]
          | true =>
              simp [h, hacc]
              exact Nat.le_trans hφ (Nat.le_add_right _ 10)

/-- Polynomial out bound for `comp_idBitEnc_idBitEnc` of `decodePairResult`. -/
noncomputable def afterDecodeProofSystemOutBound : Polynomial ℕ :=
  Polynomial.X + 10

theorem afterDecodeProofSystemOutBound_eval (n : ℕ) :
    afterDecodeProofSystemOutBound.eval n = n + 10 := by
  simp [afterDecodeProofSystemOutBound, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_ofNat]

theorem length_afterDecodeProofSystem_le_outBound (p : Polynomial ℕ)
    (V : List Bool → List Bool → Bool) (s : List Bool) :
    (afterDecodeProofSystem p V s).length ≤
      afterDecodeProofSystemOutBound.eval s.length := by
  simpa [afterDecodeProofSystemOutBound_eval] using
    length_afterDecodeProofSystem_le p V s

/-! ## Unary length compare (FinTM2 target for `lengthOk`)

Represent a Nat as a list of `true` bits. Comparing `|w| ≤ B` is lockstep
consumption of `w` against a unary budget of length `B = p.eval |φ|`. -/

/-- Unary encoding of a natural: `n` copies of `true`. -/
def unaryNat (n : ℕ) : List Bool := List.replicate n true

theorem length_unaryNat (n : ℕ) : (unaryNat n).length = n := by
  simp [unaryNat]

theorem unaryNat_succ (n : ℕ) : unaryNat (n + 1) = true :: unaryNat n := by
  simp [unaryNat, List.replicate_succ]

/-- Lockstep unary compare: `|xs| ≤ |ys|`. -/
def unaryLE (xs ys : List Bool) : Bool :=
  match xs, ys with
  | [], _ => true
  | _ :: _, [] => false
  | _ :: xs', _ :: ys' => unaryLE xs' ys'

theorem unaryLE_nil_left (ys : List Bool) : unaryLE [] ys = true := by
  cases ys <;> rfl

theorem unaryLE_cons_nil (x : Bool) (xs : List Bool) :
    unaryLE (x :: xs) [] = false := rfl

theorem unaryLE_cons_cons (x y : Bool) (xs ys : List Bool) :
    unaryLE (x :: xs) (y :: ys) = unaryLE xs ys := rfl

theorem unaryLE_iff (xs ys : List Bool) :
    unaryLE xs ys = true ↔ xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => simp [unaryLE]
      | cons y ys => simp [unaryLE]
  | cons x xs ih =>
      cases ys with
      | nil => simp [unaryLE]
      | cons y ys =>
          simp only [unaryLE_cons_cons, List.length_cons]
          rw [ih, Nat.succ_le_succ_iff]

theorem lengthOk_eq_unaryLE (p : Polynomial ℕ) (φ w : List Bool) :
    lengthOk p φ w = unaryLE w (unaryNat (p.eval φ.length)) := by
  refine Bool.eq_iff_iff.mpr ?_
  rw [lengthOk_iff, unaryLE_iff, length_unaryNat]

/-- Unary image of a polynomial evaluation (budget tape for `lengthOk`). -/
def polyEvalUnary (p : Polynomial ℕ) (n : ℕ) : List Bool :=
  unaryNat (p.eval n)

theorem length_polyEvalUnary (p : Polynomial ℕ) (n : ℕ) :
    (polyEvalUnary p n).length = p.eval n := by
  simp [polyEvalUnary, length_unaryNat]

theorem lengthOk_eq_unaryLE_poly (p : Polynomial ℕ) (φ w : List Bool) :
    lengthOk p φ w = unaryLE w (polyEvalUnary p φ.length) :=
  lengthOk_eq_unaryLE p φ w

/-! ## FinTM2: unary length compare under `encodePair`

Load `encodePair (xs, ys)` onto compare stacks (same parse as `bitsEqualComputer`),
then lockstep pop. If `xs` empties first, emit `true`. If `ys` empties while
`xs` remains, emit `false`. Realizes `unaryLE xs ys`. -/

open TM2.Stmt

inductive UnaryLEStack where
  | inp | left | right | out
  deriving DecidableEq, Repr

instance : Fintype UnaryLEStack where
  elems := {.inp, .left, .right, .out}
  complete s := by cases s <;> simp

inductive UnaryLELabel where
  | parse | expectBit | loadRight | loop | takeRight
  | acceptDrain | reject | drainRight
  deriving DecidableEq, Repr

instance : Fintype UnaryLELabel where
  elems := {.parse, .expectBit, .loadRight, .loop, .takeRight,
    .acceptDrain, .reject, .drainRight}
  complete s := by cases s <;> simp

/-- FinTM2 realizing `unaryLE` on `encodePair` inputs. -/
def unaryLEComputer : FinTM2 where
  K := UnaryLEStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := UnaryLELabel
  main := .parse
  σ := Option Bool
  initialState := none
  m
    | .parse =>
        pop UnaryLEStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => UnaryLELabel.reject)
            (branch (fun s => decide (s = some false))
              (load (fun _ => none) <| goto fun _ => UnaryLELabel.loadRight)
              (load (fun _ => none) <| goto fun _ => UnaryLELabel.expectBit))
    | .expectBit =>
        pop UnaryLEStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => UnaryLELabel.reject)
            (push UnaryLEStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => UnaryLELabel.parse)
    | .loadRight =>
        pop UnaryLEStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => UnaryLELabel.loop)
            (push UnaryLEStack.right (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => UnaryLELabel.loadRight)
    | .loop =>
        pop UnaryLEStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => UnaryLELabel.acceptDrain)
            (load (fun _ => none) <| goto fun _ => UnaryLELabel.takeRight)
    | .takeRight =>
        pop UnaryLEStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => UnaryLELabel.reject)
            (load (fun _ => none) <| goto fun _ => UnaryLELabel.loop)
    | .acceptDrain =>
        pop UnaryLEStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push UnaryLEStack.out (fun _ => true) <|
              load (fun _ => none) halt)
            (load (fun _ => none) <| goto fun _ => UnaryLELabel.acceptDrain)
    | .reject =>
        pop UnaryLEStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => UnaryLELabel.drainRight)
            (load (fun _ => none) <| goto fun _ => UnaryLELabel.reject)
    | .drainRight =>
        pop UnaryLEStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push UnaryLEStack.out (fun _ => false) <|
              load (fun _ => none) halt)
            (load (fun _ => none) <| goto fun _ => UnaryLELabel.drainRight)

def unaryLEStk (inp left right out : List Bool) : UnaryLEStack → List Bool
  | .inp => inp
  | .left => left
  | .right => right
  | .out => out

def unaryLECfg (l : Option UnaryLELabel) (v : Option Bool)
    (left right out : List Bool) : unaryLEComputer.Cfg :=
  ⟨l, v, unaryLEStk [] left right out⟩

def unaryLECfgInp (l : Option UnaryLELabel) (v : Option Bool)
    (inp left right out : List Bool) : unaryLEComputer.Cfg :=
  ⟨l, v, unaryLEStk inp left right out⟩

theorem unaryLE_step_loop_nil (right out : List Bool) :
    TM2.step unaryLEComputer.m
      (unaryLECfg (some .loop) none [] right out) =
      some (unaryLECfg (some .acceptDrain) none [] right out) := by
  simp [unaryLEComputer, unaryLECfg, unaryLEStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryLELabel.acceptDrain, none, stk⟩ : unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryLEStk]

theorem unaryLE_step_loop_cons (b : Bool) (xs right out : List Bool) :
    TM2.step unaryLEComputer.m
      (unaryLECfg (some .loop) none (b :: xs) right out) =
      some (unaryLECfg (some .takeRight) none xs right out) := by
  simp [unaryLEComputer, unaryLECfg, unaryLEStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryLELabel.takeRight, none, stk⟩ : unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryLEStk]

theorem unaryLE_step_takeRight_nil (left out : List Bool) :
    TM2.step unaryLEComputer.m
      (unaryLECfg (some .takeRight) none left [] out) =
      some (unaryLECfg (some .reject) none left [] out) := by
  simp [unaryLEComputer, unaryLECfg, unaryLEStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryLELabel.reject, none, stk⟩ : unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryLEStk]

theorem unaryLE_step_takeRight_cons (left : List Bool) (c : Bool) (ys out : List Bool) :
    TM2.step unaryLEComputer.m
      (unaryLECfg (some .takeRight) none left (c :: ys) out) =
      some (unaryLECfg (some .loop) none left ys out) := by
  simp [unaryLEComputer, unaryLECfg, unaryLEStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryLELabel.loop, none, stk⟩ : unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryLEStk]

theorem unaryLE_step_acceptDrain_nil :
    TM2.step unaryLEComputer.m
      (unaryLECfg (some .acceptDrain) none [] [] []) =
      some (unaryLECfg none none [] [] [true]) := by
  simp [unaryLEComputer, unaryLECfg, unaryLEStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨none, none, stk⟩ : unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryLEStk]

theorem unaryLE_step_acceptDrain_cons (c : Bool) (ys : List Bool) :
    TM2.step unaryLEComputer.m
      (unaryLECfg (some .acceptDrain) none [] (c :: ys) []) =
      some (unaryLECfg (some .acceptDrain) none [] ys []) := by
  simp [unaryLEComputer, unaryLECfg, unaryLEStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryLELabel.acceptDrain, none, stk⟩ : unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryLEStk]

theorem unaryLE_step_reject_nil (right : List Bool) :
    TM2.step unaryLEComputer.m
      (unaryLECfg (some .reject) none [] right []) =
      some (unaryLECfg (some .drainRight) none [] right []) := by
  simp [unaryLEComputer, unaryLECfg, unaryLEStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryLELabel.drainRight, none, stk⟩ : unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryLEStk]

theorem unaryLE_step_reject_cons (b : Bool) (xs right : List Bool) :
    TM2.step unaryLEComputer.m
      (unaryLECfg (some .reject) none (b :: xs) right []) =
      some (unaryLECfg (some .reject) none xs right []) := by
  simp [unaryLEComputer, unaryLECfg, unaryLEStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryLELabel.reject, none, stk⟩ : unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryLEStk]

theorem unaryLE_step_drainRight_nil :
    TM2.step unaryLEComputer.m
      (unaryLECfg (some .drainRight) none [] [] []) =
      some (unaryLECfg none none [] [] [false]) := by
  simp [unaryLEComputer, unaryLECfg, unaryLEStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨none, none, stk⟩ : unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryLEStk]

theorem unaryLE_step_drainRight_cons (c : Bool) (ys : List Bool) :
    TM2.step unaryLEComputer.m
      (unaryLECfg (some .drainRight) none [] (c :: ys) []) =
      some (unaryLECfg (some .drainRight) none [] ys []) := by
  simp [unaryLEComputer, unaryLECfg, unaryLEStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryLELabel.drainRight, none, stk⟩ : unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryLEStk]

theorem unaryLE_haltList (b : Bool) :
    haltList unaryLEComputer [b] = unaryLECfg none none [] [] [b] := by
  refine congrArg (fun stk =>
      (⟨(none : Option UnaryLELabel), (none : Option Bool), stk⟩ :
        unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [haltList, unaryLEComputer, unaryLEStk]

/-- One-step eval helper. -/
def unaryLE_evals_one {c c' : unaryLEComputer.Cfg}
    (h : TM2.step unaryLEComputer.m c = some c') :
    EvalsToInTime unaryLEComputer.step c (some c') 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := by
    change (some c).bind unaryLEComputer.step = some c'
    simpa [FinTM2.step] using h

/-- Drain leftover right stack then emit `false`. -/
def unaryLE_evals_drain (ys : List Bool) :
    EvalsToInTime unaryLEComputer.step
      (unaryLECfg (some .drainRight) none [] ys [])
      (some (haltList unaryLEComputer [false]))
      (ys.length + 1) := by
  induction ys with
  | nil =>
      have h := unaryLE_evals_one (unaryLE_step_drainRight_nil)
      simpa [unaryLE_haltList] using h
  | cons c ys ih =>
      have h1 := unaryLE_evals_one (unaryLE_step_drainRight_cons c ys)
      exact EvalsToInTime.trans unaryLEComputer.step 1 (ys.length + 1)
        _ _ _ h1 ih

/-- Drain leftover right stack then emit `true`. -/
def unaryLE_evals_acceptDrain (ys : List Bool) :
    EvalsToInTime unaryLEComputer.step
      (unaryLECfg (some .acceptDrain) none [] ys [])
      (some (haltList unaryLEComputer [true]))
      (ys.length + 1) := by
  induction ys with
  | nil =>
      have h := unaryLE_evals_one (unaryLE_step_acceptDrain_nil)
      simpa [unaryLE_haltList] using h
  | cons c ys ih =>
      have h1 := unaryLE_evals_one (unaryLE_step_acceptDrain_cons c ys)
      exact EvalsToInTime.trans unaryLEComputer.step 1 (ys.length + 1)
        _ _ _ h1 ih

/-- Drain leftover left then right, emit `false`. -/
def unaryLE_evals_reject (xs ys : List Bool) :
    EvalsToInTime unaryLEComputer.step
      (unaryLECfg (some .reject) none xs ys [])
      (some (haltList unaryLEComputer [false]))
      (xs.length + ys.length + 2) := by
  induction xs generalizing ys with
  | nil =>
      have h0 := unaryLE_evals_one (unaryLE_step_reject_nil ys)
      have h1 := unaryLE_evals_drain ys
      have h := EvalsToInTime.trans unaryLEComputer.step 1 (ys.length + 1)
        _ _ _ h0 h1
      exact evalsToInTime_le_mono h (by omega)
  | cons b xs ih =>
      have h1 := unaryLE_evals_one (unaryLE_step_reject_cons b xs ys)
      have h2 := ih ys
      have h := EvalsToInTime.trans unaryLEComputer.step 1
        (xs.length + ys.length + 2) _ _ _ h1 h2
      convert h using 1
      simp [List.length_cons]
      ring

/-- Lockstep compare from `loop`. -/
def unaryLE_evals_loop (xs ys : List Bool) :
    EvalsToInTime unaryLEComputer.step
      (unaryLECfg (some .loop) none xs ys [])
      (some (haltList unaryLEComputer [unaryLE xs ys]))
      (2 * xs.length + ys.length + 2) := by
  induction xs generalizing ys with
  | nil =>
      have h0 := unaryLE_evals_one (unaryLE_step_loop_nil ys [])
      have h1 := unaryLE_evals_acceptDrain ys
      have h := EvalsToInTime.trans unaryLEComputer.step 1 (ys.length + 1)
        _ _ _ h0 h1
      simpa [unaryLE_nil_left] using evalsToInTime_le_mono h (by omega)
  | cons b xs ih =>
      have h1 := unaryLE_evals_one (unaryLE_step_loop_cons b xs ys [])
      cases ys with
      | nil =>
          have h2 := unaryLE_evals_one (unaryLE_step_takeRight_nil xs [])
          have h01 := EvalsToInTime.trans unaryLEComputer.step 1 1 _ _ _ h1 h2
          have h3 := unaryLE_evals_reject xs []
          have h := EvalsToInTime.trans unaryLEComputer.step 2
            (xs.length + 2) _ _ _ h01 h3
          have hle : xs.length + 2 + 2 ≤ 2 * (b :: xs).length + 2 := by
            simp [List.length_cons]; omega
          simpa [unaryLE_cons_nil] using evalsToInTime_le_mono h hle
      | cons c ys =>
          have h2 := unaryLE_evals_one (unaryLE_step_takeRight_cons xs c ys [])
          have h01 := EvalsToInTime.trans unaryLEComputer.step 1 1 _ _ _ h1 h2
          have h3 := ih ys
          have h := EvalsToInTime.trans unaryLEComputer.step 2
            (2 * xs.length + ys.length + 2) _ _ _ h01 h3
          have hle :
              2 * xs.length + ys.length + 2 + 2 ≤
                2 * (b :: xs).length + (c :: ys).length + 2 := by
            simp [List.length_cons]; omega
          simpa [unaryLE_cons_cons] using evalsToInTime_le_mono h hle

/-! ### encodePair load for unaryLE (mirror bitsEqual load) -/

theorem unaryLE_step_parse_false (rest left right out : List Bool) :
    TM2.step unaryLEComputer.m
      (unaryLECfgInp (some .parse) none (false :: rest) left right out) =
      some (unaryLECfgInp (some .loadRight) none rest left right out) := by
  simp [unaryLEComputer, unaryLECfgInp, unaryLEStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryLELabel.loadRight, none, stk⟩ : unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryLEStk]

theorem unaryLE_step_parse_true (b : Bool) (rest left right out : List Bool) :
    TM2.step unaryLEComputer.m
      (unaryLECfgInp (some .parse) none (true :: b :: rest) left right out) =
      some (unaryLECfgInp (some .expectBit) none (b :: rest) left right out) := by
  simp [unaryLEComputer, unaryLECfgInp, unaryLEStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryLELabel.expectBit, none, stk⟩ : unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryLEStk]

theorem unaryLE_step_expectBit (b : Bool) (rest left right out : List Bool) :
    TM2.step unaryLEComputer.m
      (unaryLECfgInp (some .expectBit) none (b :: rest) left right out) =
      some (unaryLECfgInp (some .parse) none rest (b :: left) right out) := by
  simp [unaryLEComputer, unaryLECfgInp, unaryLEStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryLELabel.parse, none, stk⟩ : unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryLEStk]

theorem unaryLE_step_loadRight_cons (b : Bool) (rest left right out : List Bool) :
    TM2.step unaryLEComputer.m
      (unaryLECfgInp (some .loadRight) none (b :: rest) left right out) =
      some (unaryLECfgInp (some .loadRight) none rest left (b :: right) out) := by
  simp [unaryLEComputer, unaryLECfgInp, unaryLEStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryLELabel.loadRight, none, stk⟩ : unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryLEStk]

theorem unaryLE_step_loadRight_nil (left right out : List Bool) :
    TM2.step unaryLEComputer.m
      (unaryLECfgInp (some .loadRight) none [] left right out) =
      some (unaryLECfg (some .loop) none left right out) := by
  simp [unaryLEComputer, unaryLECfgInp, unaryLECfg, unaryLEStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryLELabel.loop, none, stk⟩ : unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryLEStk]

theorem unaryLE_initList (s : List Bool) :
    initList unaryLEComputer s =
      unaryLECfgInp (some .parse) none s [] [] [] := by
  refine congrArg (fun stk =>
      (⟨some UnaryLELabel.parse, none, stk⟩ : unaryLEComputer.Cfg)) ?_
  funext k; cases k <;> simp [unaryLEComputer, unaryLEStk]

def unaryLE_evals_parse_one (b : Bool) (rest left right out : List Bool) :
    EvalsToInTime unaryLEComputer.step
      (unaryLECfgInp (some .parse) none (true :: b :: rest) left right out)
      (some (unaryLECfgInp (some .parse) none rest (b :: left) right out))
      2 := by
  have h1 := unaryLE_evals_one (unaryLE_step_parse_true b rest left right out)
  have h2 := unaryLE_evals_one (unaryLE_step_expectBit b rest left right out)
  exact EvalsToInTime.trans unaryLEComputer.step 1 1 _ _ _ h1 h2

noncomputable def unaryLE_evals_parse (xs rest left right out : List Bool) :
    EvalsToInTime unaryLEComputer.step
      (unaryLECfgInp (some .parse) none
        ((xs.flatMap fun b => [true, b]) ++ rest) left right out)
      (some (unaryLECfgInp (some .parse) none rest (xs.reverse ++ left) right out))
      (2 * xs.length) := by
  induction xs generalizing left with
  | nil =>
      simpa using EvalsToInTime.refl unaryLEComputer.step
        (unaryLECfgInp (some .parse) none rest left right out)
  | cons b xs ih =>
      have h1 := unaryLE_evals_parse_one b
        ((xs.flatMap fun c => [true, c]) ++ rest) left right out
      have h2 := ih (b :: left)
      have h := EvalsToInTime.trans unaryLEComputer.step 2 (2 * xs.length)
        _ _ _ h1 (by simpa [List.append_assoc] using h2)
      simpa [List.length_cons, List.reverse_cons, two_mul, Nat.succ_eq_add_one]
        using evalsToInTime_le_mono h (by omega)

noncomputable def unaryLE_evals_loadRight (ys left right out : List Bool) :
    EvalsToInTime unaryLEComputer.step
      (unaryLECfgInp (some .loadRight) none ys left right out)
      (some (unaryLECfg (some .loop) none left (ys.reverse ++ right) out))
      (ys.length + 1) := by
  induction ys generalizing right with
  | nil =>
      exact unaryLE_evals_one (unaryLE_step_loadRight_nil left right out)
  | cons y ys ih =>
      have h1 := unaryLE_evals_one
        (unaryLE_step_loadRight_cons y ys left right out)
      have h2 := ih (y :: right)
      exact EvalsToInTime.trans unaryLEComputer.step 1 (ys.length + 1)
        _ _ _ h1 (by simpa [List.reverse_cons] using h2)

theorem unaryLE_reverse (xs ys : List Bool) :
    unaryLE xs.reverse ys.reverse = unaryLE xs ys := by
  refine Bool.eq_iff_iff.mpr ?_
  simp [unaryLE_iff, List.length_reverse]

noncomputable def unaryLE_evals_load_encodePair (xs ys : List Bool) :
    EvalsToInTime unaryLEComputer.step
      (unaryLECfgInp (some .parse) none (encodePair (xs, ys)) [] [] [])
      (some (unaryLECfg (some .loop) none xs.reverse ys.reverse []))
      (2 * xs.length + ys.length + 2) := by
  have hparse := unaryLE_evals_parse xs (false :: ys) [] [] []
  have h1 : EvalsToInTime unaryLEComputer.step
      (unaryLECfgInp (some .parse) none (encodePair (xs, ys)) [] [] [])
      (some (unaryLECfgInp (some .parse) none (false :: ys) xs.reverse [] []))
      (2 * xs.length) := by
    simpa [encodePair, List.append_assoc] using hparse
  have hfalse := unaryLE_evals_one
    (unaryLE_step_parse_false ys xs.reverse [] [])
  have h12 :=
    EvalsToInTime.trans unaryLEComputer.step (2 * xs.length) 1 _ _ _ h1 hfalse
  have h12' : EvalsToInTime unaryLEComputer.step
      (unaryLECfgInp (some .parse) none (encodePair (xs, ys)) [] [] [])
      (some (unaryLECfgInp (some .loadRight) none ys xs.reverse [] []))
      (2 * xs.length + 1) := by
    simpa [Nat.add_comm] using h12
  have hload := unaryLE_evals_loadRight ys xs.reverse [] []
  have h :=
    EvalsToInTime.trans unaryLEComputer.step (2 * xs.length + 1) (ys.length + 1)
      _ _ _ h12' hload
  refine ⟨⟨h.steps, ?_⟩, ?_⟩
  · simpa [List.append_nil] using h.evals_in_steps
  · refine le_trans h.steps_le_m ?_
    omega

noncomputable def unaryLE_evals (xs ys : List Bool) :
    TM2OutputsInTime unaryLEComputer (encodePair (xs, ys))
      (some [unaryLE xs ys])
      (4 * xs.length + 2 * ys.length + 4) := by
  have hload := unaryLE_evals_load_encodePair xs ys
  have hloop0 := unaryLE_evals_loop xs.reverse ys.reverse
  have hloop : EvalsToInTime unaryLEComputer.step
      (unaryLECfg (some .loop) none xs.reverse ys.reverse [])
      (some (haltList unaryLEComputer [unaryLE xs ys]))
      (2 * xs.length + ys.length + 2) := by
    simpa [List.length_reverse, unaryLE_reverse] using hloop0
  have h1 : EvalsToInTime unaryLEComputer.step
      (initList unaryLEComputer (encodePair (xs, ys)))
      (some (unaryLECfg (some .loop) none xs.reverse ys.reverse []))
      (2 * xs.length + ys.length + 2) := by
    simpa [unaryLE_initList] using hload
  have h := EvalsToInTime.trans unaryLEComputer.step
    (2 * xs.length + ys.length + 2)
    (2 * xs.length + ys.length + 2)
    _ _ _ h1 hloop
  refine ⟨⟨h.steps, ?_⟩, ?_⟩
  · simpa [bitEnc] using h.evals_in_steps
  · refine le_trans h.steps_le_m ?_
    omega

noncomputable def unaryLETime : Polynomial ℕ := 4 * Polynomial.X + 4

theorem unaryLETime_eval (n : ℕ) : unaryLETime.eval n = 4 * n + 4 := by
  simp [unaryLETime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_ofNat]

theorem unaryLETime_bound (xs ys : List Bool) :
    4 * xs.length + 2 * ys.length + 4 ≤
      unaryLETime.eval (encodePair (xs, ys)).length := by
  simp [unaryLETime, length_encodePair, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  omega

/-- Unary length compare under `encodePair` is poly time. -/
noncomputable def unaryLEComputableInPolyTime :
    TM2ComputableInPolyTime encodePair bitEnc (fun p => unaryLE p.1 p.2) where
  tm := unaryLEComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := unaryLETime
  outputsFun p := by
    rcases p with ⟨xs, ys⟩
    change TM2OutputsInTime unaryLEComputer (List.map id (encodePair (xs, ys)))
      (some (List.map id (bitEnc (unaryLE xs ys))))
      (unaryLETime.eval (encodePair (xs, ys)).length)
    simp only [List.map_id, id_eq, bitEnc]
    exact evalsToInTime_le_mono (unaryLE_evals xs ys) (unaryLETime_bound xs ys)

/-! ## Unary helpers for dominating length gates

`toUnary s = true^{|s|}`. Together with `unaryMul` and `unaryLE`, a fixed
polynomial length bound becomes a FinTM2 circuit: raise `|φ|+1` to the
degree, scale by a coefficient sum, then compare to `|w|`. -/

/-- Map any bit string to unary of the same length. -/
def toUnary (s : List Bool) : List Bool := unaryNat s.length

theorem length_toUnary (s : List Bool) : (toUnary s).length = s.length := by
  simp [toUnary, length_unaryNat]

theorem toUnary_eq_replicate (s : List Bool) :
    toUnary s = List.replicate s.length true := rfl

/-- Unary multiply: length `|acc| * |n|`. -/
def unaryMul (acc n : List Bool) : List Bool :=
  n.flatMap (fun _ => acc)

theorem length_unaryMul (acc n : List Bool) :
    (unaryMul acc n).length = acc.length * n.length := by
  induction n with
  | nil => simp [unaryMul]
  | cons _ n ih =>
      simp [unaryMul, List.flatMap, ih, Nat.mul_succ]
      ring

/-- Unary power by iterating multiply. `unaryPow u 0 = [true]` (one). -/
def unaryPow (u : List Bool) : ℕ → List Bool
  | 0 => [true]
  | k + 1 => unaryMul (unaryPow u k) u

theorem length_unaryPow (u : List Bool) (k : ℕ) :
    (unaryPow u k).length = u.length ^ k := by
  induction k with
  | zero => simp [unaryPow]
  | succ k ih =>
      simp [unaryPow, length_unaryMul, ih, Nat.pow_succ]

/-- Scale unary length by a constant `k`. -/
def unaryScale (k : ℕ) (u : List Bool) : List Bool :=
  unaryMul u (unaryNat k)

theorem length_unaryScale (k : ℕ) (u : List Bool) :
    (unaryScale k u).length = u.length * k := by
  simp [unaryScale, length_unaryMul, length_unaryNat]

open Polynomial

/-- Sum of coefficients `coeff 0 + ... + coeff natDegree`. -/
noncomputable def polyCoeffSum (p : Polynomial ℕ) : ℕ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i

/-- Dominating constant and degree for a length gate. -/
noncomputable def polyDomK (p : Polynomial ℕ) : ℕ :=
  (p.natDegree + 1) * (polyCoeffSum p + 1)

noncomputable def polyDomD (p : Polynomial ℕ) : ℕ := p.natDegree

/-- Dominating unary budget: `K * (|φ| + 1) ^ D`. -/
noncomputable def polyDomUnary (p : Polynomial ℕ) (φ : List Bool) : List Bool :=
  unaryScale (polyDomK p) (unaryPow (true :: toUnary φ) (polyDomD p))

theorem length_polyDomUnary (p : Polynomial ℕ) (φ : List Bool) :
    (polyDomUnary p φ).length =
      polyDomK p * (φ.length + 1) ^ polyDomD p := by
  simp [polyDomUnary, length_unaryScale, length_unaryPow, toUnary,
    length_unaryNat, List.length_cons]
  ring

theorem poly_eval_le_dom (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ polyDomK p * (n + 1) ^ polyDomD p := by
  classical
  have heval :
      p.eval n = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * n ^ i :=
    Polynomial.eval_eq_sum_range (R := ℕ) (p := p) n
  rw [heval]
  have hpoint (i : ℕ) (hi : i ∈ Finset.range (p.natDegree + 1)) :
      p.coeff i * n ^ i ≤ p.coeff i * (n + 1) ^ p.natDegree := by
    have hi' : i < p.natDegree + 1 := Finset.mem_range.mp hi
    have hile : i ≤ p.natDegree := Nat.le_of_lt_succ hi'
    refine Nat.mul_le_mul_left _ ?_
    calc
      n ^ i ≤ (n + 1) ^ i := Nat.pow_le_pow_left (Nat.le_succ n) i
      _ ≤ (n + 1) ^ p.natDegree :=
        Nat.pow_le_pow_right (Nat.succ_pos n) hile
  have hsum :
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * n ^ i ≤
        ∑ i ∈ Finset.range (p.natDegree + 1),
          p.coeff i * (n + 1) ^ p.natDegree :=
    Finset.sum_le_sum fun i hi => hpoint i hi
  refine le_trans hsum ?_
  have hfac :
      ∑ i ∈ Finset.range (p.natDegree + 1),
          p.coeff i * (n + 1) ^ p.natDegree =
        (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) *
          ((n + 1) ^ p.natDegree) := by
    simp [Finset.sum_mul]
  rw [hfac]
  simp only [polyDomK, polyDomD, polyCoeffSum]
  have hcs :
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i ≤
        (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) + 1 := by
    omega
  calc
    (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) * (n + 1) ^ p.natDegree ≤
        ((∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) + 1) *
          (n + 1) ^ p.natDegree :=
      Nat.mul_le_mul_right _ hcs
    _ ≤ (p.natDegree + 1) *
          ((∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) + 1) *
          (n + 1) ^ p.natDegree := by
      have h1 : 1 ≤ p.natDegree + 1 := Nat.succ_pos _
      have hmul :=
        Nat.mul_le_mul_right
          (((∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) + 1) *
            (n + 1) ^ p.natDegree) h1
      convert hmul using 1
      · ring
      · ring

/-- Looser length gate still implied by the tight `lengthOk`. -/
theorem lengthOk_implies_dom (p : Polynomial ℕ) (φ w : List Bool)
    (h : lengthOk p φ w = true) :
    unaryLE w (polyDomUnary p φ) = true := by
  rw [lengthOk_iff] at h
  rw [unaryLE_iff, length_polyDomUnary]
  exact le_trans h (poly_eval_le_dom p φ.length)

/-! ## FinTM2: `toUnary` (drain input, write that many `true`s) -/

inductive ToUnaryStack where
  | inp | out
  deriving DecidableEq, Repr

instance : Fintype ToUnaryStack where
  elems := {.inp, .out}
  complete s := by cases s <;> simp

/-- Single label loop: pop inp, push true to out. -/
def toUnaryComputer : FinTM2 where
  K := ToUnaryStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m _ :=
    pop ToUnaryStack.inp (fun _ o => o) <|
      branch (fun s => decide (s = none))
        halt
        (push ToUnaryStack.out (fun _ => true) <|
          load (fun _ => none) <|
            goto fun _ => ())

def toUnaryStk (inp out : List Bool) : ToUnaryStack → List Bool
  | .inp => inp
  | .out => out

def toUnaryCfg (l : Option Unit) (inp out : List Bool) : toUnaryComputer.Cfg :=
  ⟨l, none, toUnaryStk inp out⟩

theorem toUnary_step_cons (b : Bool) (rest out : List Bool) :
    TM2.step toUnaryComputer.m
      (toUnaryCfg (some ()) (b :: rest) out) =
      some (toUnaryCfg (some ()) rest (true :: out)) := by
  simp [toUnaryComputer, toUnaryCfg, toUnaryStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk => (⟨some (), none, stk⟩ : toUnaryComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, toUnaryStk]

theorem toUnary_step_nil (out : List Bool) :
    TM2.step toUnaryComputer.m
      (toUnaryCfg (some ()) [] out) =
      some (toUnaryCfg none [] out) := by
  simp [toUnaryComputer, toUnaryCfg, toUnaryStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk => (⟨none, none, stk⟩ : toUnaryComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, toUnaryStk]

theorem toUnary_initList (s : List Bool) :
    initList toUnaryComputer s = toUnaryCfg (some ()) s [] := by
  refine congrArg (fun stk => (⟨some (), none, stk⟩ : toUnaryComputer.Cfg)) ?_
  funext k; cases k <;> simp [toUnaryComputer, toUnaryStk]

theorem toUnary_haltList (out : List Bool) :
    haltList toUnaryComputer out = toUnaryCfg none [] out := by
  refine congrArg (fun stk =>
      (⟨(none : Option Unit), none, stk⟩ : toUnaryComputer.Cfg)) ?_
  funext k; cases k <;> simp [toUnaryComputer, toUnaryStk]

def toUnary_evals_one {c c' : toUnaryComputer.Cfg}
    (h : TM2.step toUnaryComputer.m c = some c') :
    EvalsToInTime toUnaryComputer.step c (some c') 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := by
    change (some c).bind toUnaryComputer.step = some c'
    simpa [FinTM2.step] using h

/-- Drain writing `true` onto out (reversed unary). -/
def toUnary_evals_loop (s out : List Bool) :
    EvalsToInTime toUnaryComputer.step
      (toUnaryCfg (some ()) s out)
      (some (toUnaryCfg none [] (List.replicate s.length true ++ out)))
      (s.length + 1) := by
  induction s generalizing out with
  | nil =>
      have h := toUnary_evals_one (toUnary_step_nil out)
      simpa [List.replicate_zero] using h
  | cons b s ih =>
      have h1 := toUnary_evals_one (toUnary_step_cons b s out)
      have h2 := ih (true :: out)
      have h := EvalsToInTime.trans toUnaryComputer.step 1 (s.length + 1)
        _ _ _ h1 h2
      -- machine writes replicate s.length ++ true :: out; reorder to replicate (s.length+1)
      have h' : EvalsToInTime toUnaryComputer.step
          (toUnaryCfg (some ()) (b :: s) out)
          (some (toUnaryCfg none []
            (List.replicate (b :: s).length true ++ out)))
          ((b :: s).length + 1) := by
        simpa [List.replicate_succ, List.cons_append, List.length_cons,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
          replicate_true_append_cons] using h
      exact h'

noncomputable def toUnary_evals (s : List Bool) :
    TM2OutputsInTime toUnaryComputer s (some (toUnary s)) (s.length + 1) := by
  have h := toUnary_evals_loop s []
  -- loop writes reverse unary onto out; reverse of true^n is true^n
  have hrev : List.replicate s.length true ++ [] = toUnary s := by
    simp [toUnary, unaryNat]
  refine ⟨⟨h.steps, ?_⟩, ?_⟩
  · simpa [toUnary_initList, toUnary_haltList, hrev, List.append_nil] using
      h.evals_in_steps
  · exact h.steps_le_m

noncomputable def toUnaryTime : Polynomial ℕ := Polynomial.X + 1

theorem toUnaryTime_eval (n : ℕ) : toUnaryTime.eval n = n + 1 := by
  simp [toUnaryTime, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]

/-- Converting a string to unary of equal length is poly time. -/
noncomputable def toUnaryComputableInPolyTime :
    TM2ComputableInPolyTime idBitEnc idBitEnc toUnary where
  tm := toUnaryComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := toUnaryTime
  outputsFun s := by
    change TM2OutputsInTime toUnaryComputer (List.map id (idBitEnc s))
      (some (List.map id (idBitEnc (toUnary s))))
      (toUnaryTime.eval (idBitEnc s).length)
    simp only [idBitEnc, List.map_id, id_eq, toUnaryTime_eval]
    exact toUnary_evals s

/-! ## Summit corollary (from theorem 2 + easy direction of theorem 1) -/

/-- If every propositional proof system fails to be polynomially bounded, then
`P ≠ NP`. Depends on the easy direction of bridge theorem 1 (NP = coNP yields a
poly-bounded proof system), whose FinTM2 packaging remains open. -/
theorem summit_corollary_of_easy
    (heasy : ClassNP_eq_ClassCoNP →
      ∃ f, Nonempty (IsPropProofSystem f) ∧ PolynomiallyBounded f)
    (h : ∀ f, Nonempty (IsPropProofSystem f) → ¬ PolynomiallyBounded f) :
    ¬ ClassP_eq_ClassNP := by
  intro hP
  have hNP := bridge_theorem_2 hP
  rcases heasy hNP with ⟨f, hf, hb⟩
  exact (h f hf) hb

end SATurday.Bridge
