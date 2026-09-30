import Theory.ProofComplexity.Bridge.ProofSystem
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
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

/-- `proofCheck` is pairwise bit equality of `f π` against `φ`. -/
theorem proofCheck_eq_bitsEqualPair (f : List Bool → List Bool) (φ π : List Bool) :
    proofCheck f φ π = bitsEqualPair (f π, φ) := by
  simp [proofCheck, bitsEqualPair, bitsEqual]

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

/-- Hard-half packaging: a poly-bounded proof system plus a FinTM2 `proofCheck`
witness puts `TAUT` in NP. -/
theorem TAUT_in_NP_of_polyBounded {f : List Bool → List Bool}
    (hf : IsPropProofSystem f) (hb : PolynomiallyBounded f)
    (hcheck : TM2ComputableInPolyTime encodePair bitEnc
      (fun pw => proofCheck f pw.1 pw.2)) :
    InNP TAUT := by
  refine ⟨Classical.choose hb, proofCheck f, hcheck, ?_⟩
  intro φ
  exact TAUT_short_proofs_of_polyBounded' hf hb φ

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

/-! ## FinTM2: `unaryMul` under `encodePair`

For each bit of the right tape, copy the left tape onto `out` (restoring left
via `work`). Realizes `n.flatMap (fun _ => acc)`. -/

inductive UnaryMulStack where
  | inp | left | right | work | out
  deriving DecidableEq, Repr

instance : Fintype UnaryMulStack where
  elems := {.inp, .left, .right, .work, .out}
  complete s := by cases s <;> simp

inductive UnaryMulLabel where
  | parse | expectBit | loadRight | loop | moveWork | writeOut | haltDrain
  deriving DecidableEq, Repr

instance : Fintype UnaryMulLabel where
  elems := {.parse, .expectBit, .loadRight, .loop, .moveWork, .writeOut, .haltDrain}
  complete s := by cases s <;> simp

/-- FinTM2 realizing `unaryMul` on `encodePair (acc, n)`. -/
def unaryMulComputer : FinTM2 where
  K := UnaryMulStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := UnaryMulLabel
  main := .parse
  σ := Option Bool
  initialState := none
  m
    | .parse =>
        pop UnaryMulStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => UnaryMulLabel.haltDrain)
            (branch (fun s => decide (s = some false))
              (load (fun _ => none) <| goto fun _ => UnaryMulLabel.loadRight)
              (load (fun _ => none) <| goto fun _ => UnaryMulLabel.expectBit))
    | .expectBit =>
        pop UnaryMulStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => UnaryMulLabel.haltDrain)
            (push UnaryMulStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => UnaryMulLabel.parse)
    | .loadRight =>
        pop UnaryMulStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => UnaryMulLabel.loop)
            (push UnaryMulStack.right (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => UnaryMulLabel.loadRight)
    | .loop =>
        pop UnaryMulStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => UnaryMulLabel.haltDrain)
            (load (fun _ => none) <| goto fun _ => UnaryMulLabel.moveWork)
    | .moveWork =>
        pop UnaryMulStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => UnaryMulLabel.writeOut)
            (push UnaryMulStack.work (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => UnaryMulLabel.moveWork)
    | .writeOut =>
        pop UnaryMulStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => UnaryMulLabel.loop)
            (push UnaryMulStack.left (fun s => s.getD false) <|
              push UnaryMulStack.out (fun s => s.getD false) <|
                load (fun _ => none) <| goto fun _ => UnaryMulLabel.writeOut)
    | .haltDrain =>
        -- discard leftover left/work/right; leave `out` as the product
        pop UnaryMulStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (pop UnaryMulStack.work (fun _ o => o) <|
              branch (fun s => decide (s = none))
                (pop UnaryMulStack.right (fun _ o => o) <|
                  branch (fun s => decide (s = none))
                    (load (fun _ => none) halt)
                    (load (fun _ => none) <| goto fun _ => UnaryMulLabel.haltDrain))
                (load (fun _ => none) <| goto fun _ => UnaryMulLabel.haltDrain))
            (load (fun _ => none) <| goto fun _ => UnaryMulLabel.haltDrain)

def unaryMulStk (inp left right work out : List Bool) : UnaryMulStack → List Bool
  | .inp => inp
  | .left => left
  | .right => right
  | .work => work
  | .out => out

def unaryMulCfg (l : Option UnaryMulLabel) (v : Option Bool)
    (left right work out : List Bool) : unaryMulComputer.Cfg :=
  ⟨l, v, unaryMulStk [] left right work out⟩

def unaryMulCfgInp (l : Option UnaryMulLabel) (v : Option Bool)
    (inp left right work out : List Bool) : unaryMulComputer.Cfg :=
  ⟨l, v, unaryMulStk inp left right work out⟩

theorem unaryMul_step_loop_nil (left work out : List Bool) :
    TM2.step unaryMulComputer.m
      (unaryMulCfg (some .loop) none left [] work out) =
      some (unaryMulCfg (some .haltDrain) none left [] work out) := by
  simp [unaryMulComputer, unaryMulCfg, unaryMulStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryMulLabel.haltDrain, none, stk⟩ : unaryMulComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryMulStk]

theorem unaryMul_step_loop_cons (c : Bool) (ys left work out : List Bool) :
    TM2.step unaryMulComputer.m
      (unaryMulCfg (some .loop) none left (c :: ys) work out) =
      some (unaryMulCfg (some .moveWork) none left ys work out) := by
  simp [unaryMulComputer, unaryMulCfg, unaryMulStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryMulLabel.moveWork, none, stk⟩ : unaryMulComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryMulStk]

theorem unaryMul_step_moveWork_nil (right work out : List Bool) :
    TM2.step unaryMulComputer.m
      (unaryMulCfg (some .moveWork) none [] right work out) =
      some (unaryMulCfg (some .writeOut) none [] right work out) := by
  simp [unaryMulComputer, unaryMulCfg, unaryMulStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryMulLabel.writeOut, none, stk⟩ : unaryMulComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryMulStk]

theorem unaryMul_step_moveWork_cons (b : Bool) (xs right work out : List Bool) :
    TM2.step unaryMulComputer.m
      (unaryMulCfg (some .moveWork) none (b :: xs) right work out) =
      some (unaryMulCfg (some .moveWork) none xs right (b :: work) out) := by
  simp [unaryMulComputer, unaryMulCfg, unaryMulStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryMulLabel.moveWork, none, stk⟩ : unaryMulComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryMulStk]

theorem unaryMul_step_writeOut_nil (left right out : List Bool) :
    TM2.step unaryMulComputer.m
      (unaryMulCfg (some .writeOut) none left right [] out) =
      some (unaryMulCfg (some .loop) none left right [] out) := by
  simp [unaryMulComputer, unaryMulCfg, unaryMulStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryMulLabel.loop, none, stk⟩ : unaryMulComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryMulStk]

theorem unaryMul_step_writeOut_cons (b : Bool) (ws left right out : List Bool) :
    TM2.step unaryMulComputer.m
      (unaryMulCfg (some .writeOut) none left right (b :: ws) out) =
      some (unaryMulCfg (some .writeOut) none (b :: left) right ws (b :: out)) := by
  simp [unaryMulComputer, unaryMulCfg, unaryMulStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryMulLabel.writeOut, none, stk⟩ : unaryMulComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryMulStk]

theorem unaryMul_step_haltDrain_all_nil (out : List Bool) :
    TM2.step unaryMulComputer.m
      (unaryMulCfg (some .haltDrain) none [] [] [] out) =
      some (unaryMulCfg none none [] [] [] out) := by
  simp [unaryMulComputer, unaryMulCfg, unaryMulStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option UnaryMulLabel), none, stk⟩ : unaryMulComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryMulStk]

def unaryMul_evals_one {c c' : unaryMulComputer.Cfg}
    (h : TM2.step unaryMulComputer.m c = some c') :
    EvalsToInTime unaryMulComputer.step c (some c') 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := by
    change (some c).bind unaryMulComputer.step = some c'
    simpa [FinTM2.step] using h

/-- Move all of `left` onto `work` (reversing). -/
def unaryMul_evals_moveWork (left right work out : List Bool) :
    EvalsToInTime unaryMulComputer.step
      (unaryMulCfg (some .moveWork) none left right work out)
      (some (unaryMulCfg (some .writeOut) none [] right
        (List.reverse left ++ work) out))
      (left.length + 1) := by
  induction left generalizing work with
  | nil =>
      simpa using unaryMul_evals_one (unaryMul_step_moveWork_nil right work out)
  | cons b xs ih =>
      have h1 := unaryMul_evals_one
        (unaryMul_step_moveWork_cons b xs right work out)
      have h2 := ih (b :: work)
      have h := EvalsToInTime.trans unaryMulComputer.step 1 (xs.length + 1)
        _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, List.length_cons,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Restore `work` onto `left` while copying each bit to `out`. -/
def unaryMul_evals_writeOut (left right work out : List Bool) :
    EvalsToInTime unaryMulComputer.step
      (unaryMulCfg (some .writeOut) none left right work out)
      (some (unaryMulCfg (some .loop) none
        (List.reverse work ++ left) right []
        (List.reverse work ++ out)))
      (work.length + 1) := by
  induction work generalizing left out with
  | nil =>
      simpa using unaryMul_evals_one
        (unaryMul_step_writeOut_nil left right out)
  | cons b ws ih =>
      have h1 := unaryMul_evals_one
        (unaryMul_step_writeOut_cons b ws left right out)
      have h2 := ih (b :: left) (b :: out)
      have h := EvalsToInTime.trans unaryMulComputer.step 1 (ws.length + 1)
        _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, List.length_cons,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- One right-bit: copy `left` onto `out` (left restored). -/
def unaryMul_evals_one_right (left : List Bool) (c : Bool) (ys out : List Bool) :
    EvalsToInTime unaryMulComputer.step
      (unaryMulCfg (some .loop) none left (c :: ys) [] out)
      (some (unaryMulCfg (some .loop) none left ys []
        (left ++ out)))
      (2 * left.length + 3) := by
  have h1 := unaryMul_evals_one
    (unaryMul_step_loop_cons c ys left [] out)
  have h2 := unaryMul_evals_moveWork left ys [] out
  have h12 := EvalsToInTime.trans unaryMulComputer.step 1 (left.length + 1)
    _ _ _ h1 h2
  have h12' : EvalsToInTime unaryMulComputer.step
      (unaryMulCfg (some .loop) none left (c :: ys) [] out)
      (some (unaryMulCfg (some .writeOut) none [] ys (List.reverse left) out))
      (left.length + 1 + 1) := by
    simpa [List.append_nil] using h12
  have h3 := unaryMul_evals_writeOut [] ys (List.reverse left) out
  have h := EvalsToInTime.trans unaryMulComputer.step
    (left.length + 1 + 1) ((List.reverse left).length + 1)
    _ _ _ h12' h3
  have hrev : List.reverse (List.reverse left) = left := List.reverse_reverse left
  simpa [hrev, List.append_nil, List.length_reverse, two_mul, Nat.succ_eq_add_one,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    evalsToInTime_le_mono h (by simp [List.length_reverse]; omega)

/-- `foldr` copy-blocks commute past a leading `left ++`. -/
theorem foldr_left_append_comm (left ys out : List Bool) :
    List.foldr (fun _ acc => left ++ acc) (left ++ out) ys =
      left ++ List.foldr (fun _ acc => left ++ acc) out ys := by
  induction ys generalizing out with
  | nil => simp [List.foldr]
  | cons _ ys ih =>
      simp only [List.foldr]
      rw [ih]

/-- Drain right tape, copying left once per right bit. -/
def unaryMul_evals_loop (left right out : List Bool) :
    EvalsToInTime unaryMulComputer.step
      (unaryMulCfg (some .loop) none left right [] out)
      (some (unaryMulCfg (some .haltDrain) none left [] []
        (List.foldr (fun _ acc => left ++ acc) out right)))
      (right.length * (2 * left.length + 3) + 1) := by
  induction right generalizing out with
  | nil =>
      simpa [List.foldr] using
        unaryMul_evals_one (unaryMul_step_loop_nil left [] out)
  | cons c ys ih =>
      have h1 := unaryMul_evals_one_right left c ys out
      have h2 := ih (left ++ out)
      have h2' : EvalsToInTime unaryMulComputer.step
          (unaryMulCfg (some .loop) none left ys [] (left ++ out))
          (some (unaryMulCfg (some .haltDrain) none left [] []
            (left ++ List.foldr (fun _ acc => left ++ acc) out ys)))
          (ys.length * (2 * left.length + 3) + 1) := by
        simpa [foldr_left_append_comm left ys out] using h2
      have h := EvalsToInTime.trans unaryMulComputer.step
        (2 * left.length + 3)
        (ys.length * (2 * left.length + 3) + 1)
        _ _ _ h1 h2'
      have htime :
          (ys.length * (2 * left.length + 3) + 1) + (2 * left.length + 3) =
            (c :: ys).length * (2 * left.length + 3) + 1 := by
        simp [List.length_cons]; ring
      simpa [List.foldr] using evalsToInTime_le_mono h (le_of_eq htime)

theorem foldr_left_append_eq_flatMap (left right out : List Bool) :
    List.foldr (fun _ acc => left ++ acc) out right =
      right.flatMap (fun _ => left) ++ out := by
  induction right generalizing out with
  | nil => simp [List.flatMap]
  | cons _ ys ih =>
      simp [List.foldr, List.flatMap_cons, ih, List.append_assoc]

theorem unaryMul_step_halt_clean (out : List Bool) :
    TM2.step unaryMulComputer.m
      (unaryMulCfg (some .haltDrain) none [] [] [] out) =
      some (unaryMulCfg none none [] [] [] out) :=
  unaryMul_step_haltDrain_all_nil out

/-- After loop, haltDrain with empty aux stacks finishes in one step. -/
def unaryMul_evals_halt (left out : List Bool) :
    EvalsToInTime unaryMulComputer.step
      (unaryMulCfg (some .haltDrain) none left [] [] out)
      (some (unaryMulCfg none none [] [] [] out))
      (left.length + 1) := by
  induction left generalizing out with
  | nil =>
      exact unaryMul_evals_one (unaryMul_step_halt_clean out)
  | cons b xs ih =>
      have h1 : EvalsToInTime unaryMulComputer.step
          (unaryMulCfg (some .haltDrain) none (b :: xs) [] [] out)
          (some (unaryMulCfg (some .haltDrain) none xs [] [] out)) 1 := by
        refine unaryMul_evals_one ?_
        simp [unaryMulComputer, unaryMulCfg, unaryMulStk, TM2.step, TM2.stepAux]
        refine congrArg some <|
          congrArg (fun stk =>
            (⟨some UnaryMulLabel.haltDrain, none, stk⟩ : unaryMulComputer.Cfg)) ?_
        funext k; cases k <;> simp [Function.update, unaryMulStk]
      have h := EvalsToInTime.trans unaryMulComputer.step 1 (xs.length + 1)
        _ _ _ h1 (ih out)
      simpa [List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-! ### encodePair load for unaryMul (mirror unaryLE load) -/

theorem unaryMul_step_parse_false (rest left right work out : List Bool) :
    TM2.step unaryMulComputer.m
      (unaryMulCfgInp (some .parse) none (false :: rest) left right work out) =
      some (unaryMulCfgInp (some .loadRight) none rest left right work out) := by
  simp [unaryMulComputer, unaryMulCfgInp, unaryMulStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryMulLabel.loadRight, none, stk⟩ : unaryMulComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryMulStk]

theorem unaryMul_step_parse_true (b : Bool) (rest left right work out : List Bool) :
    TM2.step unaryMulComputer.m
      (unaryMulCfgInp (some .parse) none (true :: b :: rest) left right work out) =
      some (unaryMulCfgInp (some .expectBit) none (b :: rest) left right work out) := by
  simp [unaryMulComputer, unaryMulCfgInp, unaryMulStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryMulLabel.expectBit, none, stk⟩ : unaryMulComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryMulStk]

theorem unaryMul_step_expectBit (b : Bool) (rest left right work out : List Bool) :
    TM2.step unaryMulComputer.m
      (unaryMulCfgInp (some .expectBit) none (b :: rest) left right work out) =
      some (unaryMulCfgInp (some .parse) none rest (b :: left) right work out) := by
  simp [unaryMulComputer, unaryMulCfgInp, unaryMulStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryMulLabel.parse, none, stk⟩ : unaryMulComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryMulStk]

theorem unaryMul_step_loadRight_cons (b : Bool) (rest left right work out : List Bool) :
    TM2.step unaryMulComputer.m
      (unaryMulCfgInp (some .loadRight) none (b :: rest) left right work out) =
      some (unaryMulCfgInp (some .loadRight) none rest left (b :: right) work out) := by
  simp [unaryMulComputer, unaryMulCfgInp, unaryMulStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryMulLabel.loadRight, none, stk⟩ : unaryMulComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryMulStk]

theorem unaryMul_step_loadRight_nil (left right work out : List Bool) :
    TM2.step unaryMulComputer.m
      (unaryMulCfgInp (some .loadRight) none [] left right work out) =
      some (unaryMulCfg (some .loop) none left right work out) := by
  simp [unaryMulComputer, unaryMulCfgInp, unaryMulCfg, unaryMulStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some UnaryMulLabel.loop, none, stk⟩ : unaryMulComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, unaryMulStk]

theorem unaryMul_initList (s : List Bool) :
    initList unaryMulComputer s =
      unaryMulCfgInp (some .parse) none s [] [] [] [] := by
  refine congrArg (fun stk =>
      (⟨some UnaryMulLabel.parse, none, stk⟩ : unaryMulComputer.Cfg)) ?_
  funext k; cases k <;> simp [unaryMulComputer, unaryMulStk]

theorem unaryMul_haltList (out : List Bool) :
    haltList unaryMulComputer out =
      unaryMulCfg none none [] [] [] out := by
  refine congrArg (fun stk =>
      (⟨(none : Option UnaryMulLabel), (none : Option Bool), stk⟩ :
        unaryMulComputer.Cfg)) ?_
  funext k; cases k <;> simp [haltList, unaryMulComputer, unaryMulStk]

def unaryMul_evals_parse_one (b : Bool) (rest left right work out : List Bool) :
    EvalsToInTime unaryMulComputer.step
      (unaryMulCfgInp (some .parse) none (true :: b :: rest) left right work out)
      (some (unaryMulCfgInp (some .parse) none rest (b :: left) right work out))
      2 := by
  have h1 := unaryMul_evals_one
    (unaryMul_step_parse_true b rest left right work out)
  have h2 := unaryMul_evals_one
    (unaryMul_step_expectBit b rest left right work out)
  exact EvalsToInTime.trans unaryMulComputer.step 1 1 _ _ _ h1 h2

noncomputable def unaryMul_evals_parse (xs rest left right work out : List Bool) :
    EvalsToInTime unaryMulComputer.step
      (unaryMulCfgInp (some .parse) none
        ((xs.flatMap fun b => [true, b]) ++ rest) left right work out)
      (some (unaryMulCfgInp (some .parse) none rest
        (xs.reverse ++ left) right work out))
      (2 * xs.length) := by
  induction xs generalizing left with
  | nil =>
      simpa using EvalsToInTime.refl unaryMulComputer.step
        (unaryMulCfgInp (some .parse) none rest left right work out)
  | cons b xs ih =>
      have h1 := unaryMul_evals_parse_one b
        ((xs.flatMap fun c => [true, c]) ++ rest) left right work out
      have h2 := ih (b :: left)
      have h := EvalsToInTime.trans unaryMulComputer.step 2 (2 * xs.length)
        _ _ _ h1 (by simpa [List.append_assoc] using h2)
      simpa [List.length_cons, List.reverse_cons, two_mul, Nat.succ_eq_add_one]
        using evalsToInTime_le_mono h (by omega)

noncomputable def unaryMul_evals_loadRight (ys left right work out : List Bool) :
    EvalsToInTime unaryMulComputer.step
      (unaryMulCfgInp (some .loadRight) none ys left right work out)
      (some (unaryMulCfg (some .loop) none left (ys.reverse ++ right) work out))
      (ys.length + 1) := by
  induction ys generalizing right with
  | nil =>
      exact unaryMul_evals_one
        (unaryMul_step_loadRight_nil left right work out)
  | cons y ys ih =>
      have h1 := unaryMul_evals_one
        (unaryMul_step_loadRight_cons y ys left right work out)
      have h2 := ih (y :: right)
      exact EvalsToInTime.trans unaryMulComputer.step 1 (ys.length + 1)
        _ _ _ h1 (by simpa [List.reverse_cons] using h2)

/-- Parse load lands in loop with reversed stacks. -/
noncomputable def unaryMul_evals_load_encodePair (xs ys : List Bool) :
    EvalsToInTime unaryMulComputer.step
      (unaryMulCfgInp (some .parse) none (encodePair (xs, ys)) [] [] [] [])
      (some (unaryMulCfg (some .loop) none xs.reverse ys.reverse [] []))
      (2 * xs.length + ys.length + 2) := by
  have hparse := unaryMul_evals_parse xs (false :: ys) [] [] [] []
  have h1 : EvalsToInTime unaryMulComputer.step
      (unaryMulCfgInp (some .parse) none (encodePair (xs, ys)) [] [] [] [])
      (some (unaryMulCfgInp (some .parse) none (false :: ys) xs.reverse [] [] []))
      (2 * xs.length) := by
    simpa [encodePair, List.append_assoc] using hparse
  have hfalse := unaryMul_evals_one
    (unaryMul_step_parse_false ys xs.reverse [] [] [])
  have h12 :=
    EvalsToInTime.trans unaryMulComputer.step (2 * xs.length) 1 _ _ _ h1 hfalse
  have h12' : EvalsToInTime unaryMulComputer.step
      (unaryMulCfgInp (some .parse) none (encodePair (xs, ys)) [] [] [] [])
      (some (unaryMulCfgInp (some .loadRight) none ys xs.reverse [] [] []))
      (2 * xs.length + 1) := by
    simpa [Nat.add_comm] using h12
  have hload := unaryMul_evals_loadRight ys xs.reverse [] [] []
  have h :=
    EvalsToInTime.trans unaryMulComputer.step (2 * xs.length + 1) (ys.length + 1)
      _ _ _ h12' hload
  refine ⟨⟨h.steps, ?_⟩, ?_⟩
  · simpa [List.append_nil] using h.evals_in_steps
  · refine le_trans h.steps_le_m ?_
    omega

/-- Parse reverses both tapes; machine then emits `(unaryMul xs ys).reverse`. -/
theorem unaryMul_reverse (xs ys : List Bool) :
    unaryMul xs.reverse ys.reverse = (unaryMul xs ys).reverse := by
  simp only [unaryMul]
  induction ys with
  | nil => simp [List.flatMap]
  | cons _ ys ih =>
      simp [List.reverse_cons, List.flatMap_cons, List.reverse_append, ih]

/-- Full run: emit `(unaryMul xs ys).reverse` under `encodePair`. -/
noncomputable def unaryMul_evals (xs ys : List Bool) :
    TM2OutputsInTime unaryMulComputer (encodePair (xs, ys))
      (some (unaryMul xs ys).reverse)
      ((xs.length + 1) +
        ((ys.length * (2 * xs.length + 3) + 1) + (2 * xs.length + ys.length + 2))) := by
  have hload := unaryMul_evals_load_encodePair xs ys
  have hloop0 := unaryMul_evals_loop xs.reverse ys.reverse []
  have hout :
      List.foldr (fun _ acc => xs.reverse ++ acc) [] ys.reverse =
        (unaryMul xs ys).reverse := by
    rw [foldr_left_append_eq_flatMap, List.append_nil, ← unaryMul,
      unaryMul_reverse]
  have hloop : EvalsToInTime unaryMulComputer.step
      (unaryMulCfg (some .loop) none xs.reverse ys.reverse [] [])
      (some (unaryMulCfg (some .haltDrain) none xs.reverse [] []
        (unaryMul xs ys).reverse))
      (ys.length * (2 * xs.length + 3) + 1) := by
    simpa [List.length_reverse, hout] using hloop0
  have hhalt0 := unaryMul_evals_halt xs.reverse (unaryMul xs ys).reverse
  have hhalt : EvalsToInTime unaryMulComputer.step
      (unaryMulCfg (some .haltDrain) none xs.reverse [] []
        (unaryMul xs ys).reverse)
      (some (haltList unaryMulComputer (unaryMul xs ys).reverse))
      (xs.length + 1) := by
    simpa [List.length_reverse, unaryMul_haltList] using hhalt0
  have h1 : EvalsToInTime unaryMulComputer.step
      (initList unaryMulComputer (encodePair (xs, ys)))
      (some (unaryMulCfg (some .loop) none xs.reverse ys.reverse [] []))
      (2 * xs.length + ys.length + 2) := by
    simpa [unaryMul_initList] using hload
  have h12 := EvalsToInTime.trans unaryMulComputer.step
    (2 * xs.length + ys.length + 2)
    (ys.length * (2 * xs.length + 3) + 1)
    _ _ _ h1 hloop
  have h := EvalsToInTime.trans unaryMulComputer.step
    ((ys.length * (2 * xs.length + 3) + 1) + (2 * xs.length + ys.length + 2))
    (xs.length + 1)
    _ _ _ h12 hhalt
  exact ⟨⟨h.steps, h.evals_in_steps⟩, h.steps_le_m⟩

/-- Quadratic time bound in `|encodePair|`. -/
noncomputable def unaryMulTime : Polynomial ℕ :=
  2 * Polynomial.X ^ 2 + 7 * Polynomial.X + 4

theorem unaryMulTime_eval (n : ℕ) :
    unaryMulTime.eval n = 2 * n ^ 2 + 7 * n + 4 := by
  simp [unaryMulTime, pow_two, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat]

theorem unaryMulTime_bound (xs ys : List Bool) :
    (xs.length + 1) +
      ((ys.length * (2 * xs.length + 3) + 1) + (2 * xs.length + ys.length + 2)) ≤
      unaryMulTime.eval (encodePair (xs, ys)).length := by
  simp [unaryMulTime_eval, length_encodePair]
  have hxs : xs.length ≤ 2 * xs.length + ys.length + 1 := by omega
  have hys : ys.length ≤ 2 * xs.length + ys.length + 1 := by omega
  have hprod : xs.length * ys.length ≤
      (2 * xs.length + ys.length + 1) * (2 * xs.length + ys.length + 1) :=
    Nat.mul_le_mul hxs hys
  nlinarith

/-- `unaryMul` under `encodePair`, emitting the reverse (identity on unary tapes). -/
noncomputable def unaryMulRevComputableInPolyTime :
    TM2ComputableInPolyTime encodePair idBitEnc
      (fun p => (unaryMul p.1 p.2).reverse) where
  tm := unaryMulComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := unaryMulTime
  outputsFun p := by
    rcases p with ⟨xs, ys⟩
    change TM2OutputsInTime unaryMulComputer (List.map id (encodePair (xs, ys)))
      (some (List.map id (idBitEnc (unaryMul xs ys).reverse)))
      (unaryMulTime.eval (encodePair (xs, ys)).length)
    simp only [List.map_id, id_eq, idBitEnc]
    exact evalsToInTime_le_mono (unaryMul_evals xs ys) (unaryMulTime_bound xs ys)

theorem flatMap_replicate_true (m n : ℕ) :
    (List.replicate n true).flatMap (fun _ => List.replicate m true) =
      List.replicate (m * n) true := by
  induction n with
  | zero => simp [List.flatMap]
  | succ n ih =>
      simp [List.replicate_succ, List.flatMap_cons, ih, Nat.mul_succ,
        List.replicate_append_replicate, Nat.add_comm]

theorem unaryMul_of_replicate (m n : ℕ) :
    unaryMul (List.replicate m true) (List.replicate n true) =
      List.replicate (m * n) true := by
  simpa [unaryMul] using flatMap_replicate_true m n

theorem unaryMul_reverse_eq_of_unary (xs ys : List Bool)
    (hxs : xs = List.replicate xs.length true)
    (hys : ys = List.replicate ys.length true) :
    (unaryMul xs ys).reverse = unaryMul xs ys := by
  rw [hxs, hys, unaryMul_of_replicate, List.reverse_replicate]

/-! ## Unary scale / dominating length gate (semantic packaging)

`unaryScale k (toUnary s)` is the dominating building block for
`polyDomUnary`. FinTM2 packaging reuses `unaryMulComputer` once a
constant-right `encodePair (-, true^k)` adapter is certified; until then the
semantic equalities below close the length-arithmetic side of Block C. -/

theorem unaryScale_eq_mul_toUnary (k : ℕ) (s : List Bool) :
    unaryScale k (toUnary s) = unaryMul (toUnary s) (unaryNat k) := rfl

theorem unaryScale_length (k : ℕ) (s : List Bool) :
    (unaryScale k (toUnary s)).length = k * s.length := by
  simp [unaryScale, toUnary, length_unaryMul, length_unaryNat, Nat.mul_comm]

theorem unaryScale_eq_replicate (k : ℕ) (s : List Bool) :
    unaryScale k (toUnary s) = List.replicate (k * s.length) true := by
  simpa [unaryScale, toUnary, unaryNat, Nat.mul_comm] using
    unaryMul_of_replicate s.length k

/-- Dominating length gate as a Boolean. -/
noncomputable def lengthOkDom (p : Polynomial ℕ) (φ w : List Bool) : Bool :=
  unaryLE w (polyDomUnary p φ)

theorem lengthOkDom_iff (p : Polynomial ℕ) (φ w : List Bool) :
    lengthOkDom p φ w = true ↔
      w.length ≤ polyDomK p * (φ.length + 1) ^ polyDomD p := by
  simp [lengthOkDom, unaryLE_iff, length_polyDomUnary]

theorem lengthOk_implies_lengthOkDom (p : Polynomial ℕ) (φ w : List Bool)
    (h : lengthOk p φ w = true) : lengthOkDom p φ w = true :=
  lengthOk_implies_dom p φ w h

/-- Polynomial realizing the dominating length bound. -/
noncomputable def polyDomBound (p : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (polyDomK p) * (Polynomial.X + 1) ^ polyDomD p

theorem polyDomBound_eval (p : Polynomial ℕ) (n : ℕ) :
    (polyDomBound p).eval n = polyDomK p * (n + 1) ^ polyDomD p := by
  simp [polyDomBound, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]

theorem poly_eval_le_polyDomBound (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ (polyDomBound p).eval n := by
  simpa [polyDomBound_eval] using poly_eval_le_dom p n

/-! ## FinTM2: `unaryScale k` via nested push Stmt of size `k`

`TM2.stepAux` runs an entire Stmt in one `step`, so writing `k` trues is a
single transition. Time is `|s| + 1`. -/

inductive ScaleStack where
  | inp | out
  deriving DecidableEq, Repr

instance : Fintype ScaleStack where
  elems := {.inp, .out}
  complete s := by cases s <;> simp

def scaleStk (inp out : List Bool) : ScaleStack → List Bool
  | .inp => inp
  | .out => out

/-- Nested Stmt: push `true` onto out, `k` times, then `goto` main. -/
def writeKTruesStmt (k : ℕ) :
    TM2.Stmt (fun _ : ScaleStack => Bool) Unit (Option Bool) :=
  match k with
  | 0 => load (fun _ => none) <| goto fun _ => ()
  | n + 1 =>
      push ScaleStack.out (fun _ => true) <| writeKTruesStmt n

theorem writeKTruesStmt_stepAux (k : ℕ) (v : Option Bool) (inp out : List Bool) :
    TM2.stepAux (writeKTruesStmt k) v (scaleStk inp out) =
      ⟨some (), none, scaleStk inp (List.replicate k true ++ out)⟩ := by
  induction k generalizing out with
  | zero =>
      simp [writeKTruesStmt, TM2.stepAux, List.replicate_zero, scaleStk]
  | succ n ih =>
      simp only [writeKTruesStmt, TM2.stepAux]
      have hstk :
          Function.update (scaleStk inp out) ScaleStack.out
              (true :: scaleStk inp out ScaleStack.out) =
            scaleStk inp (true :: out) := by
        funext s; cases s <;> simp [Function.update, scaleStk]
      rw [hstk]
      simpa [List.replicate_succ, replicate_true_append_cons] using ih (true :: out)

/-- Write `k` output trues for each input bit. -/
def unaryScaleComputer (k : ℕ) : FinTM2 where
  K := ScaleStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m _ :=
    pop ScaleStack.inp (fun _ o => o) <|
      branch (fun s => decide (s = none))
        halt
        (writeKTruesStmt k)

def scaleCfg (k : ℕ) (l : Option Unit) (v : Option Bool) (inp out : List Bool) :
    (unaryScaleComputer k).Cfg :=
  ⟨l, v, scaleStk inp out⟩

theorem scale_step_nil (k : ℕ) (out : List Bool) :
    TM2.step (unaryScaleComputer k).m
      (scaleCfg k (some ()) none [] out) =
      some (scaleCfg k none none [] out) := by
  simp [unaryScaleComputer, scaleCfg, scaleStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option Unit), none, stk⟩ : (unaryScaleComputer k).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, scaleStk]

theorem scale_step_cons (k : ℕ) (b : Bool) (rest out : List Bool) :
    TM2.step (unaryScaleComputer k).m
      (scaleCfg k (some ()) none (b :: rest) out) =
      some (scaleCfg k (some ()) none rest
        (List.replicate k true ++ out)) := by
  simp [unaryScaleComputer, scaleCfg, scaleStk, TM2.step, TM2.stepAux]
  have hstk :
      Function.update (scaleStk (b :: rest) out) ScaleStack.inp rest =
        scaleStk rest out := by
    funext s; cases s <;> simp [Function.update, scaleStk]
  have h := writeKTruesStmt_stepAux k (some b) rest out
  exact congrArg some
    (Eq.trans (congrArg (TM2.stepAux (writeKTruesStmt k) (some b)) hstk) h)

def scale_evals_one {k : ℕ} {c c' : (unaryScaleComputer k).Cfg}
    (h : TM2.step (unaryScaleComputer k).m c = some c') :
    EvalsToInTime (unaryScaleComputer k).step c (some c') 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := by
    change (some c).bind (unaryScaleComputer k).step = some c'
    simpa [FinTM2.step] using h

/-- `foldr` of identical `replicate k` blocks commutes past a leading block. -/
theorem foldr_replicate_comm (k : ℕ) (s out : List Bool) :
    List.foldr (fun _ acc => List.replicate k true ++ acc)
        (List.replicate k true ++ out) s =
      List.replicate k true ++
        List.foldr (fun _ acc => List.replicate k true ++ acc) out s := by
  induction s generalizing out with
  | nil => simp [List.foldr]
  | cons _ s ih =>
      simp only [List.foldr]
      rw [ih]

def scale_evals_loop (k : ℕ) (s out : List Bool) :
    EvalsToInTime (unaryScaleComputer k).step
      (scaleCfg k (some ()) none s out)
      (some (scaleCfg k none none []
        (List.foldr (fun _ acc => List.replicate k true ++ acc) out s)))
      (s.length + 1) := by
  induction s generalizing out with
  | nil =>
      simpa [List.foldr] using scale_evals_one (scale_step_nil k out)
  | cons b s ih =>
      have h1 := scale_evals_one (scale_step_cons k b s out)
      have h2 := ih (List.replicate k true ++ out)
      have h2' : EvalsToInTime (unaryScaleComputer k).step
          (scaleCfg k (some ()) none s (List.replicate k true ++ out))
          (some (scaleCfg k none none []
            (List.replicate k true ++
              List.foldr (fun _ acc => List.replicate k true ++ acc) out s)))
          (s.length + 1) := by
        simpa [foldr_replicate_comm k s out] using h2
      have h := EvalsToInTime.trans (unaryScaleComputer k).step 1 (s.length + 1)
        _ _ _ h1 h2'
      have htime : (s.length + 1) + 1 = (b :: s).length + 1 := by
        simp [List.length_cons]
      simpa [List.foldr] using evalsToInTime_le_mono h (le_of_eq htime)

theorem foldr_replicate_scale (k : ℕ) (s out : List Bool) :
    List.foldr (fun _ acc => List.replicate k true ++ acc) out s =
      List.replicate (k * s.length) true ++ out := by
  induction s generalizing out with
  | nil => simp [List.foldr]
  | cons _ s ih =>
      simp only [List.foldr, List.length_cons]
      rw [ih, ← List.append_assoc, List.replicate_append_replicate]
      congr 1
      ring_nf

theorem scale_initList (k : ℕ) (s : List Bool) :
    initList (unaryScaleComputer k) s =
      scaleCfg k (some ()) none s [] := by
  refine congrArg (fun stk =>
      (⟨some (), none, stk⟩ : (unaryScaleComputer k).Cfg)) ?_
  funext t; cases t <;> simp [unaryScaleComputer, scaleStk]

theorem scale_haltList (k : ℕ) (out : List Bool) :
    haltList (unaryScaleComputer k) out =
      scaleCfg k none none [] out := by
  refine congrArg (fun stk =>
      (⟨(none : Option Unit), none, stk⟩ : (unaryScaleComputer k).Cfg)) ?_
  funext t; cases t <;> simp [unaryScaleComputer, scaleStk]

noncomputable def unaryScale_evals (k : ℕ) (s : List Bool) :
    TM2OutputsInTime (unaryScaleComputer k) s
      (some (unaryScale k (toUnary s)))
      (s.length + 1) := by
  have h := scale_evals_loop k s []
  have hout :
      List.foldr (fun _ acc => List.replicate k true ++ acc) [] s =
        unaryScale k (toUnary s) := by
    rw [foldr_replicate_scale, List.append_nil]
    simp [unaryScale, toUnary, unaryMul, unaryNat, flatMap_replicate_true, Nat.mul_comm]
  refine ⟨⟨h.steps, ?_⟩, ?_⟩
  · simpa [scale_initList, scale_haltList, hout] using h.evals_in_steps
  · exact h.steps_le_m

noncomputable def unaryScaleTime (_k : ℕ) : Polynomial ℕ := Polynomial.X + 1

theorem unaryScaleTime_eval (_k n : ℕ) :
    (unaryScaleTime _k).eval n = n + 1 := by
  simp [unaryScaleTime, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]

/-- `unaryScale k ∘ toUnary` is poly time (one step per input bit). -/
noncomputable def unaryScaleComputableInPolyTime (k : ℕ) :
    TM2ComputableInPolyTime idBitEnc idBitEnc
      (fun s => unaryScale k (toUnary s)) where
  tm := unaryScaleComputer k
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := unaryScaleTime k
  outputsFun s := by
    change TM2OutputsInTime (unaryScaleComputer k) (List.map id (idBitEnc s))
      (some (List.map id (idBitEnc (unaryScale k (toUnary s)))))
      ((unaryScaleTime k).eval (idBitEnc s).length)
    simp only [idBitEnc, List.map_id, id_eq, unaryScaleTime_eval]
    exact unaryScale_evals k s

/-! ## Exact unary poly-eval for degree ≤ 1

`polyEvalUnary (C a * X + C b) n = true^(a*n + b)`. Built from scale-then-append. -/

theorem polyEvalUnary_linear (a b n : ℕ) :
    polyEvalUnary (Polynomial.C a * Polynomial.X + Polynomial.C b) n =
      List.replicate (a * n + b) true := by
  simp [polyEvalUnary, unaryNat, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

/-- Nested push of `k` trues then `goto cont` (Bool labels). -/
def writeKTruesStmtBool (k : ℕ) (cont : Bool) :
    TM2.Stmt (fun _ : ScaleStack => Bool) Bool (Option Bool) :=
  match k with
  | 0 => load (fun _ => none) <| goto fun _ => cont
  | n + 1 =>
      push ScaleStack.out (fun _ => true) <| writeKTruesStmtBool n cont

theorem writeKTruesStmtBool_stepAux (k : ℕ) (cont : Bool) (v : Option Bool)
    (inp out : List Bool) :
    TM2.stepAux (writeKTruesStmtBool k cont) v (scaleStk inp out) =
      ⟨some cont, none, scaleStk inp (List.replicate k true ++ out)⟩ := by
  induction k generalizing out with
  | zero =>
      simp [writeKTruesStmtBool, TM2.stepAux, List.replicate_zero, scaleStk]
  | succ n ih =>
      simp only [writeKTruesStmtBool, TM2.stepAux]
      have hstk :
          Function.update (scaleStk inp out) ScaleStack.out
              (true :: scaleStk inp out ScaleStack.out) =
            scaleStk inp (true :: out) := by
        funext s; cases s <;> simp [Function.update, scaleStk]
      rw [hstk]
      simpa [List.replicate_succ, replicate_true_append_cons] using ih (true :: out)

/-- Append exactly `b` trues then halt. -/
def appendKTruesStmt (b : ℕ) :
    TM2.Stmt (fun _ : ScaleStack => Bool) Bool (Option Bool) :=
  match b with
  | 0 => halt
  | n + 1 =>
      push ScaleStack.out (fun _ => true) <| appendKTruesStmt n

theorem appendKTruesStmt_stepAux (b : ℕ) (v : Option Bool) (inp out : List Bool) :
    TM2.stepAux (appendKTruesStmt b) v (scaleStk inp out) =
      ⟨none, v, scaleStk inp (List.replicate b true ++ out)⟩ := by
  induction b generalizing out with
  | zero =>
      simp [appendKTruesStmt, TM2.stepAux, List.replicate_zero, scaleStk]
  | succ n ih =>
      simp only [appendKTruesStmt, TM2.stepAux]
      have hstk :
          Function.update (scaleStk inp out) ScaleStack.out
              (true :: scaleStk inp out ScaleStack.out) =
            scaleStk inp (true :: out) := by
        funext s; cases s <;> simp [Function.update, scaleStk]
      rw [hstk]
      simpa [List.replicate_succ, replicate_true_append_cons] using ih (true :: out)

/-- Scale by `a` per input bit, then append `b` trues. -/
def scaleAppendComputer (a b : ℕ) : FinTM2 where
  K := ScaleStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := Bool
  main := false
  σ := Option Bool
  initialState := none
  m
    | false =>
        pop ScaleStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => true)
            (writeKTruesStmtBool a false)
    | true =>
        appendKTruesStmt b

def scaleAppendCfg (a b : ℕ) (l : Option Bool) (v : Option Bool)
    (inp out : List Bool) : (scaleAppendComputer a b).Cfg :=
  ⟨l, v, scaleStk inp out⟩

theorem scaleAppend_step_scale_nil (a b : ℕ) (out : List Bool) :
    TM2.step (scaleAppendComputer a b).m
      (scaleAppendCfg a b (some false) none [] out) =
      some (scaleAppendCfg a b (some true) none [] out) := by
  simp [scaleAppendComputer, scaleAppendCfg, scaleStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some true, none, stk⟩ : (scaleAppendComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, scaleStk]

theorem scaleAppend_step_scale_cons (a b : ℕ) (c : Bool) (rest out : List Bool) :
    TM2.step (scaleAppendComputer a b).m
      (scaleAppendCfg a b (some false) none (c :: rest) out) =
      some (scaleAppendCfg a b (some false) none rest
        (List.replicate a true ++ out)) := by
  simp [scaleAppendComputer, scaleAppendCfg, scaleStk, TM2.step, TM2.stepAux]
  have hstk :
      Function.update (scaleStk (c :: rest) out) ScaleStack.inp rest =
        scaleStk rest out := by
    funext s; cases s <;> simp [Function.update, scaleStk]
  have h := writeKTruesStmtBool_stepAux a false (some c) rest out
  exact congrArg some
    (Eq.trans (congrArg (TM2.stepAux (writeKTruesStmtBool a false) (some c)) hstk) h)

theorem scaleAppend_step_append (a b : ℕ) (inp out : List Bool) :
    TM2.step (scaleAppendComputer a b).m
      (scaleAppendCfg a b (some true) none inp out) =
      some (scaleAppendCfg a b none none inp
        (List.replicate b true ++ out)) := by
  simp [scaleAppendComputer, scaleAppendCfg, scaleStk, TM2.step]
  exact congrArg some (appendKTruesStmt_stepAux b none inp out)

def scaleAppend_evals_one {a b : ℕ} {c c' : (scaleAppendComputer a b).Cfg}
    (h : TM2.step (scaleAppendComputer a b).m c = some c') :
    EvalsToInTime (scaleAppendComputer a b).step c (some c') 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := by
    change (some c).bind (scaleAppendComputer a b).step = some c'
    simpa [FinTM2.step] using h

/-- Scale loop then one append transition. -/
def scaleAppend_evals_loop (a b : ℕ) (s out : List Bool) :
    EvalsToInTime (scaleAppendComputer a b).step
      (scaleAppendCfg a b (some false) none s out)
      (some (scaleAppendCfg a b none none []
        (List.replicate b true ++
          List.foldr (fun _ acc => List.replicate a true ++ acc) out s)))
      (s.length + 2) := by
  induction s generalizing out with
  | nil =>
      have h1 := scaleAppend_evals_one (scaleAppend_step_scale_nil a b out)
      have h2 := scaleAppend_evals_one (scaleAppend_step_append a b [] out)
      have h := EvalsToInTime.trans (scaleAppendComputer a b).step 1 1 _ _ _ h1 h2
      simpa [List.foldr] using h
  | cons c s ih =>
      have h1 := scaleAppend_evals_one
        (scaleAppend_step_scale_cons a b c s out)
      have h2 := ih (List.replicate a true ++ out)
      have h2' : EvalsToInTime (scaleAppendComputer a b).step
          (scaleAppendCfg a b (some false) none s
            (List.replicate a true ++ out))
          (some (scaleAppendCfg a b none none []
            (List.replicate b true ++
              (List.replicate a true ++
                List.foldr (fun _ acc => List.replicate a true ++ acc) out s))))
          (s.length + 2) := by
        simpa [foldr_replicate_comm a s out, List.append_assoc] using h2
      have h := EvalsToInTime.trans (scaleAppendComputer a b).step 1
        (s.length + 2) _ _ _ h1 h2'
      have htime : (s.length + 2) + 1 = (c :: s).length + 2 := by
        simp [List.length_cons]
      simpa [List.foldr, List.append_assoc] using
        evalsToInTime_le_mono h (le_of_eq htime)

theorem scaleAppend_initList (a b : ℕ) (s : List Bool) :
    initList (scaleAppendComputer a b) s =
      scaleAppendCfg a b (some false) none s [] := by
  refine congrArg (fun stk =>
      (⟨some false, none, stk⟩ : (scaleAppendComputer a b).Cfg)) ?_
  funext t; cases t <;> simp [scaleAppendComputer, scaleStk]

theorem scaleAppend_haltList (a b : ℕ) (out : List Bool) :
    haltList (scaleAppendComputer a b) out =
      scaleAppendCfg a b none none [] out := by
  refine congrArg (fun stk =>
      (⟨(none : Option Bool), none, stk⟩ : (scaleAppendComputer a b).Cfg)) ?_
  funext t; cases t <;> simp [scaleAppendComputer, scaleStk]

/-- Output of scale-append on input length `n` is `true^(a*n + b)`. -/
theorem scaleAppend_foldr_eq (a b : ℕ) (s : List Bool) :
    List.replicate b true ++
        List.foldr (fun _ acc => List.replicate a true ++ acc) ([] : List Bool) s =
      List.replicate (b + a * s.length) true := by
  rw [foldr_replicate_scale, List.append_nil, List.replicate_append_replicate]

theorem scaleAppend_replicate_comm (a b : ℕ) (n : ℕ) :
    List.replicate (b + a * n) true = List.replicate (a * n + b) true := by
  rw [Nat.add_comm]

noncomputable def scaleAppend_evals (a b : ℕ) (s : List Bool) :
    TM2OutputsInTime (scaleAppendComputer a b) s
      (some
        (List.replicate b true ++
          List.foldr (fun _ acc => List.replicate a true ++ acc) ([] : List Bool) s))
      (s.length + 2) := by
  have h := scaleAppend_evals_loop a b s []
  refine ⟨⟨h.steps, ?_⟩, ?_⟩
  · simpa [scaleAppend_initList, scaleAppend_haltList] using h.evals_in_steps
  · exact h.steps_le_m

noncomputable def scaleAppendTime (_a _b : ℕ) : Polynomial ℕ :=
  Polynomial.X + 2

theorem scaleAppendTime_eval (_a _b n : ℕ) :
    (scaleAppendTime _a _b).eval n = n + 2 := by
  simp [scaleAppendTime, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_ofNat]

/-- `s ↦ true^(a*|s| + b)` in linear time (degree-1 unary poly-eval). -/
noncomputable def scaleAppendComputableInPolyTime (a b : ℕ) :
    TM2ComputableInPolyTime idBitEnc idBitEnc
      (fun s => List.replicate (a * s.length + b) true) where
  tm := scaleAppendComputer a b
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := scaleAppendTime a b
  outputsFun s := by
    change TM2OutputsInTime (scaleAppendComputer a b) (List.map id (idBitEnc s))
      (some (List.map id (idBitEnc (List.replicate (a * s.length + b) true))))
      ((scaleAppendTime a b).eval (idBitEnc s).length)
    simp only [idBitEnc, List.map_id, id_eq, scaleAppendTime_eval]
    have h := scaleAppend_evals a b s
    convert h using 1
    refine congrArg some ?_
    calc
      List.replicate (a * s.length + b) true =
          List.replicate (b + a * s.length) true := (scaleAppend_replicate_comm a b s.length).symm
      _ = List.replicate b true ++
            List.foldr (fun _ acc => List.replicate a true ++ acc) ([] : List Bool) s :=
          (scaleAppend_foldr_eq a b s).symm

/-- Degree-1 exact `polyEvalUnary` is poly-time on the length of `s`. -/
noncomputable def polyEvalUnaryLinearComputableInPolyTime (a b : ℕ) :
    TM2ComputableInPolyTime idBitEnc idBitEnc
      (fun s =>
        polyEvalUnary (Polynomial.C a * Polynomial.X + Polynomial.C b) s.length) := by
  convert scaleAppendComputableInPolyTime a b using 1
  funext s
  exact polyEvalUnary_linear a b s.length

/-! ## Exact polyEval via divX (semantic Horner step)

`p.eval n = n * (divX p).eval n + p.coeff 0`. Exact unary budgets reduce to
recursive scale-append once `polyEvalUnary` for `divX p` is packaged. -/

theorem polyEvalUnary_divX (p : Polynomial ℕ) (n : ℕ) :
    polyEvalUnary p n =
      List.replicate (n * (Polynomial.divX p).eval n + p.coeff 0) true := by
  unfold polyEvalUnary unaryNat
  congr 1
  calc
    p.eval n
        = (Polynomial.X * Polynomial.divX p + Polynomial.C (p.coeff 0)).eval n := by
          rw [Polynomial.X_mul_divX_add]
    _ = n * (Polynomial.divX p).eval n + p.coeff 0 := by
          simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
            Polynomial.eval_C]

/-- Horner: `polyEvalUnary p` equals scaleAppend-1-c after unary mul of toUnary
against `polyEvalUnary (divX p)`. -/
theorem polyEvalUnary_horner_scaleAppend (p : Polynomial ℕ) (s : List Bool) :
    polyEvalUnary p s.length =
      List.replicate
        ((unaryMul (toUnary s)
            (polyEvalUnary (Polynomial.divX p) s.length)).length + p.coeff 0)
        true := by
  have hmul :
      unaryMul (toUnary s) (polyEvalUnary (Polynomial.divX p) s.length) =
        List.replicate (s.length * (Polynomial.divX p).eval s.length) true := by
    simpa [toUnary, unaryNat, polyEvalUnary, length_unaryNat] using
      unaryMul_of_replicate s.length ((Polynomial.divX p).eval s.length)
  have hep := polyEvalUnary_divX p s.length
  rw [hep, hmul, List.length_replicate]

theorem polyEvalUnary_horner_eq_scaleAppend_one (p : Polynomial ℕ) (s : List Bool) :
    polyEvalUnary p s.length =
      List.replicate
        (1 * (unaryMul (toUnary s)
            (polyEvalUnary (Polynomial.divX p) s.length)).length + p.coeff 0)
        true := by
  simpa [Nat.one_mul] using polyEvalUnary_horner_scaleAppend p s

theorem length_dupEncodePair (s : List Bool) :
    (encodePair (s, s)).length = 3 * s.length + 1 := by
  simp [length_encodePair]; omega

/-! ## FinTM2: duplicate `s ↦ encodePair (s, s)` (Horner fan-out) -/

inductive DupStack where
  | inp | left | right | work | out
  deriving DecidableEq, Repr

instance : Fintype DupStack where
  elems := {.inp, .left, .right, .work, .out}
  complete s := by cases s <;> simp

inductive DupLabel where
  | load | toWork | toOut | toLeft
  | emitW | emitSep | emitFstPrep | emitFst
  | rev1 | rev2 | rev3 | haltDrain
  deriving DecidableEq, Repr

instance : Fintype DupLabel where
  elems := {.load, .toWork, .toOut, .toLeft, .emitW, .emitSep, .emitFstPrep,
    .emitFst, .rev1, .rev2, .rev3, .haltDrain}
  complete s := by cases s <;> simp

def dupStk (inp left right work out : List Bool) : DupStack → List Bool
  | .inp => inp
  | .left => left
  | .right => right
  | .work => work
  | .out => out

/-- Copy each input bit onto `left` and `right` (both end as `reverse s`), restore
`left = s` via a three-stack bounce, then emit `encodePair (s, s)` (same emit
pipeline as `swapPairComputer`). -/
def dupEncodePairComputer : FinTM2 where
  K := DupStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := DupLabel
  main := .load
  σ := Option Bool
  initialState := none
  m
    | .load =>
        pop DupStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => DupLabel.toWork)
            (push DupStack.left (fun s => s.getD false) <|
              push DupStack.right (fun s => s.getD false) <|
                load (fun _ => none) <| goto fun _ => DupLabel.load)
    | .toWork =>
        pop DupStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => DupLabel.toOut)
            (push DupStack.work (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => DupLabel.toWork)
    | .toOut =>
        pop DupStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => DupLabel.toLeft)
            (push DupStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => DupLabel.toOut)
    | .toLeft =>
        pop DupStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => DupLabel.emitW)
            (push DupStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => DupLabel.toLeft)
    | .emitW =>
        pop DupStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => DupLabel.emitSep)
            (push DupStack.out (fun _ => true) <|
              push DupStack.out (fun s => s.getD false) <|
                load (fun _ => none) <| goto fun _ => DupLabel.emitW)
    | .emitSep =>
        push DupStack.out (fun _ => false) <|
          load (fun _ => none) <| goto fun _ => DupLabel.emitFstPrep
    | .emitFstPrep =>
        pop DupStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => DupLabel.emitFst)
            (push DupStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => DupLabel.emitFstPrep)
    | .emitFst =>
        pop DupStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => DupLabel.rev1)
            (push DupStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => DupLabel.emitFst)
    | .rev1 =>
        pop DupStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => DupLabel.rev2)
            (push DupStack.right (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => DupLabel.rev1)
    | .rev2 =>
        pop DupStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => DupLabel.rev3)
            (push DupStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => DupLabel.rev2)
    | .rev3 =>
        pop DupStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => DupLabel.haltDrain)
            (push DupStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => DupLabel.rev3)
    | .haltDrain =>
        pop DupStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            halt
            (load (fun _ => none) <| goto fun _ => DupLabel.haltDrain)

def dupCfg (l : Option DupLabel) (v : Option Bool)
    (inp left right work out : List Bool) : dupEncodePairComputer.Cfg :=
  ⟨l, v, dupStk inp left right work out⟩

theorem dup_step_load_cons (c : Bool) (rest left right work out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .load) none (c :: rest) left right work out) =
      some (dupCfg (some .load) none rest (c :: left) (c :: right) work out) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.load, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

theorem dup_step_load_nil (left right work out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .load) none [] left right work out) =
      some (dupCfg (some .toWork) none [] left right work out) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.toWork, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

def dup_evals_one {c c' : dupEncodePairComputer.Cfg}
    (h : TM2.step dupEncodePairComputer.m c = some c') :
    EvalsToInTime dupEncodePairComputer.step c (some c') 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := by
    change (some c).bind dupEncodePairComputer.step = some c'
    simpa [FinTM2.step] using h

noncomputable def dup_evals_load (s left right work out : List Bool) :
    EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .load) none s left right work out)
      (some (dupCfg (some .toWork) none [] (List.reverse s ++ left)
        (List.reverse s ++ right) work out))
      (s.length + 1) := by
  induction s generalizing left right with
  | nil =>
      exact dup_evals_one (dup_step_load_nil left right work out)
  | cons c s ih =>
      have h1 := dup_evals_one (dup_step_load_cons c s left right work out)
      have h2 := ih (c :: left) (c :: right)
      have h := EvalsToInTime.trans dupEncodePairComputer.step 1 (s.length + 1) _ _ _ h1 h2
      have htime : (s.length + 1) + 1 = (c :: s).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem dup_step_toWork_cons (c : Bool) (rest right work out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .toWork) none [] (c :: rest) right work out) =
      some (dupCfg (some .toWork) none [] rest right (c :: work) out) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.toWork, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

theorem dup_step_toWork_nil (right work out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .toWork) none [] [] right work out) =
      some (dupCfg (some .toOut) none [] [] right work out) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.toOut, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

noncomputable def dup_evals_toWork (left right work out : List Bool) :
    EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .toWork) none [] left right work out)
      (some (dupCfg (some .toOut) none [] [] right
        (List.reverse left ++ work) out))
      (left.length + 1) := by
  induction left generalizing work with
  | nil =>
      exact dup_evals_one (dup_step_toWork_nil right work out)
  | cons c left ih =>
      have h1 := dup_evals_one (dup_step_toWork_cons c left right work out)
      have h2 := ih (c :: work)
      have h := EvalsToInTime.trans dupEncodePairComputer.step 1 (left.length + 1) _ _ _ h1 h2
      have htime : (left.length + 1) + 1 = (c :: left).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem dup_step_toOut_cons (c : Bool) (rest right out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .toOut) none [] [] right (c :: rest) out) =
      some (dupCfg (some .toOut) none [] [] right rest (c :: out)) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.toOut, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

theorem dup_step_toOut_nil (right out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .toOut) none [] [] right [] out) =
      some (dupCfg (some .toLeft) none [] [] right [] out) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.toLeft, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

noncomputable def dup_evals_toOut (work right out : List Bool) :
    EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .toOut) none [] [] right work out)
      (some (dupCfg (some .toLeft) none [] [] right []
        (List.reverse work ++ out)))
      (work.length + 1) := by
  induction work generalizing out with
  | nil =>
      exact dup_evals_one (dup_step_toOut_nil right out)
  | cons c work ih =>
      have h1 := dup_evals_one (dup_step_toOut_cons c work right out)
      have h2 := ih (c :: out)
      have h := EvalsToInTime.trans dupEncodePairComputer.step 1 (work.length + 1) _ _ _ h1 h2
      have htime : (work.length + 1) + 1 = (c :: work).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem dup_step_toLeft_cons (c : Bool) (rest left right work : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .toLeft) none [] left right work (c :: rest)) =
      some (dupCfg (some .toLeft) none [] (c :: left) right work rest) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.toLeft, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

theorem dup_step_toLeft_nil (left right work : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .toLeft) none [] left right work []) =
      some (dupCfg (some .emitW) none [] left right work []) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.emitW, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

noncomputable def dup_evals_toLeft (out left right work : List Bool) :
    EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .toLeft) none [] left right work out)
      (some (dupCfg (some .emitW) none [] (List.reverse out ++ left) right work []))
      (out.length + 1) := by
  induction out generalizing left with
  | nil =>
      exact dup_evals_one (dup_step_toLeft_nil left right work)
  | cons c out ih =>
      have h1 := dup_evals_one (dup_step_toLeft_cons c out left right work)
      have h2 := ih (c :: left)
      have h := EvalsToInTime.trans dupEncodePairComputer.step 1 (out.length + 1) _ _ _ h1 h2
      have htime : (out.length + 1) + 1 = (c :: out).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

/-- Load and bounce: at `emitW` with `left = s` and `right = reverse s`. -/
noncomputable def dup_evals_load_to_emitW (s : List Bool) :
    EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .load) none s [] [] [] [])
      (some (dupCfg (some .emitW) none [] s (List.reverse s) [] []))
      ((s.length + 1) + ((s.length + 1) + ((s.length + 1) + (s.length + 1)))) := by
  have hload := dup_evals_load s [] [] [] []
  have hload' : EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .load) none s [] [] [] [])
      (some (dupCfg (some .toWork) none [] (List.reverse s) (List.reverse s) [] []))
      (s.length + 1) := by
    simpa [List.append_nil] using hload
  have hwork := dup_evals_toWork (List.reverse s) (List.reverse s) [] []
  have hwork' : EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .toWork) none [] (List.reverse s) (List.reverse s) [] [])
      (some (dupCfg (some .toOut) none [] [] (List.reverse s) s []))
      (s.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using hwork
  have h12 := EvalsToInTime.trans dupEncodePairComputer.step
    (s.length + 1) (s.length + 1) _ _ _ hload' hwork'
  have hout := dup_evals_toOut s (List.reverse s) []
  have hout' : EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .toOut) none [] [] (List.reverse s) s [])
      (some (dupCfg (some .toLeft) none [] [] (List.reverse s) [] (List.reverse s)))
      (s.length + 1) := by
    simpa [List.append_nil] using hout
  have h123 := EvalsToInTime.trans dupEncodePairComputer.step
    ((s.length + 1) + (s.length + 1)) (s.length + 1) _ _ _ h12 hout'
  have hleft := dup_evals_toLeft (List.reverse s) [] (List.reverse s) []
  have hleft' : EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .toLeft) none [] [] (List.reverse s) [] (List.reverse s))
      (some (dupCfg (some .emitW) none [] s (List.reverse s) [] []))
      (s.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using hleft
  exact EvalsToInTime.trans dupEncodePairComputer.step
    ((s.length + 1) + ((s.length + 1) + (s.length + 1))) (s.length + 1)
    _ _ _ h123 hleft'

theorem dup_step_emitW_nil (right work out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .emitW) none [] [] right work out) =
      some (dupCfg (some .emitSep) none [] [] right work out) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.emitSep, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

theorem dup_step_emitW_cons (c : Bool) (rest right work out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .emitW) none [] (c :: rest) right work out) =
      some (dupCfg (some .emitW) none [] rest right work (c :: true :: out)) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.emitW, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

def dup_evals_emitW (left right work out : List Bool) :
    EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .emitW) none [] left right work out)
      (some (dupCfg (some .emitSep) none [] [] right work
        (List.reverse (left.flatMap fun c => [true, c]) ++ out)))
      (left.length + 1) := by
  induction left generalizing out with
  | nil =>
      simpa [List.flatMap] using dup_evals_one (dup_step_emitW_nil right work out)
  | cons c left ih =>
      have h1 := dup_evals_one (dup_step_emitW_cons c left right work out)
      have h2 := ih (c :: true :: out)
      have h := EvalsToInTime.trans dupEncodePairComputer.step 1 (left.length + 1) _ _ _ h1 h2
      have htime : (left.length + 1) + 1 = (c :: left).length + 1 := by
        simp [List.length_cons]
      have hout :
          List.reverse ((c :: left).flatMap fun c => [true, c]) ++ out =
            List.reverse (left.flatMap fun c => [true, c]) ++ c :: true :: out := by
        simp [List.flatMap_cons, List.reverse_cons]
      simpa [htime, hout, List.append_assoc] using h

theorem dup_step_emitSep (right work out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .emitSep) none [] [] right work out) =
      some (dupCfg (some .emitFstPrep) none [] [] right work (false :: out)) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.emitFstPrep, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

theorem dup_step_emitFstPrep_cons (c : Bool) (rest left work out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .emitFstPrep) none [] left (c :: rest) work out) =
      some (dupCfg (some .emitFstPrep) none [] (c :: left) rest work out) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.emitFstPrep, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

theorem dup_step_emitFstPrep_nil (left work out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .emitFstPrep) none [] left [] work out) =
      some (dupCfg (some .emitFst) none [] left [] work out) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.emitFst, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

noncomputable def dup_evals_emitFstPrep (right left work out : List Bool) :
    EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .emitFstPrep) none [] left right work out)
      (some (dupCfg (some .emitFst) none [] (List.reverse right ++ left) [] work out))
      (right.length + 1) := by
  induction right generalizing left with
  | nil =>
      exact dup_evals_one (dup_step_emitFstPrep_nil left work out)
  | cons c right ih =>
      have h1 := dup_evals_one (dup_step_emitFstPrep_cons c right left work out)
      have h2 := ih (c :: left)
      have h := EvalsToInTime.trans dupEncodePairComputer.step 1 (right.length + 1) _ _ _ h1 h2
      have htime : (right.length + 1) + 1 = (c :: right).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem dup_step_emitFst_cons (c : Bool) (rest work out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .emitFst) none [] (c :: rest) [] work out) =
      some (dupCfg (some .emitFst) none [] rest [] work (c :: out)) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.emitFst, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

theorem dup_step_emitFst_nil (work out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .emitFst) none [] [] [] work out) =
      some (dupCfg (some .rev1) none [] [] [] work out) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.rev1, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

def dup_evals_emitFst (left work out : List Bool) :
    EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .emitFst) none [] left [] work out)
      (some (dupCfg (some .rev1) none [] [] [] work
        (List.reverse left ++ out)))
      (left.length + 1) := by
  induction left generalizing out with
  | nil =>
      exact dup_evals_one (dup_step_emitFst_nil work out)
  | cons c left ih =>
      have h1 := dup_evals_one (dup_step_emitFst_cons c left work out)
      have h2 := ih (c :: out)
      have h := EvalsToInTime.trans dupEncodePairComputer.step 1 (left.length + 1) _ _ _ h1 h2
      have htime : (left.length + 1) + 1 = (c :: left).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem dup_step_rev1_cons (c : Bool) (rest right work : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .rev1) none [] [] right work (c :: rest)) =
      some (dupCfg (some .rev1) none [] [] (c :: right) work rest) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.rev1, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

theorem dup_step_rev1_nil (right work : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .rev1) none [] [] right work []) =
      some (dupCfg (some .rev2) none [] [] right work []) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.rev2, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

def dup_evals_rev1 (out right work : List Bool) :
    EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .rev1) none [] [] right work out)
      (some (dupCfg (some .rev2) none [] [] (List.reverse out ++ right) work []))
      (out.length + 1) := by
  induction out generalizing right with
  | nil =>
      exact dup_evals_one (dup_step_rev1_nil right work)
  | cons c out ih =>
      have h1 := dup_evals_one (dup_step_rev1_cons c out right work)
      have h2 := ih (c :: right)
      have h := EvalsToInTime.trans dupEncodePairComputer.step 1 (out.length + 1) _ _ _ h1 h2
      have htime : (out.length + 1) + 1 = (c :: out).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem dup_step_rev2_cons (c : Bool) (rest left work out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .rev2) none [] left (c :: rest) work out) =
      some (dupCfg (some .rev2) none [] (c :: left) rest work out) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.rev2, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

theorem dup_step_rev2_nil (left work out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .rev2) none [] left [] work out) =
      some (dupCfg (some .rev3) none [] left [] work out) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.rev3, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

def dup_evals_rev2 (right left work out : List Bool) :
    EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .rev2) none [] left right work out)
      (some (dupCfg (some .rev3) none [] (List.reverse right ++ left) [] work out))
      (right.length + 1) := by
  induction right generalizing left with
  | nil =>
      exact dup_evals_one (dup_step_rev2_nil left work out)
  | cons c right ih =>
      have h1 := dup_evals_one (dup_step_rev2_cons c right left work out)
      have h2 := ih (c :: left)
      have h := EvalsToInTime.trans dupEncodePairComputer.step 1 (right.length + 1) _ _ _ h1 h2
      have htime : (right.length + 1) + 1 = (c :: right).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem dup_step_rev3_cons (c : Bool) (rest work out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .rev3) none [] (c :: rest) [] work out) =
      some (dupCfg (some .rev3) none [] rest [] work (c :: out)) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.rev3, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

theorem dup_step_rev3_nil (work out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .rev3) none [] [] [] work out) =
      some (dupCfg (some .haltDrain) none [] [] [] work out) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DupLabel.haltDrain, (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

def dup_evals_rev3 (left work out : List Bool) :
    EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .rev3) none [] left [] work out)
      (some (dupCfg (some .haltDrain) none [] [] [] work
        (List.reverse left ++ out)))
      (left.length + 1) := by
  induction left generalizing out with
  | nil =>
      exact dup_evals_one (dup_step_rev3_nil work out)
  | cons c left ih =>
      have h1 := dup_evals_one (dup_step_rev3_cons c left work out)
      have h2 := ih (c :: out)
      have h := EvalsToInTime.trans dupEncodePairComputer.step 1 (left.length + 1) _ _ _ h1 h2
      have htime : (left.length + 1) + 1 = (c :: left).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

def dup_evals_unreverse (ep : List Bool) :
    EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .rev1) none [] [] [] [] (List.reverse ep))
      (some (dupCfg (some .haltDrain) none [] [] [] [] ep))
      ((ep.length + 1) + ((ep.length + 1) + (ep.length + 1))) := by
  have h1 := dup_evals_rev1 (List.reverse ep) [] []
  have h1' : EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .rev1) none [] [] [] [] (List.reverse ep))
      (some (dupCfg (some .rev2) none [] [] ep [] []))
      (ep.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using h1
  have h2 := dup_evals_rev2 ep [] [] []
  have h2' : EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .rev2) none [] [] ep [] [])
      (some (dupCfg (some .rev3) none [] (List.reverse ep) [] [] []))
      (ep.length + 1) := by
    simpa [List.append_nil] using h2
  have h3 := dup_evals_rev3 (List.reverse ep) [] []
  have h3' : EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .rev3) none [] (List.reverse ep) [] [] [])
      (some (dupCfg (some .haltDrain) none [] [] [] [] ep))
      (ep.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using h3
  have h12 := EvalsToInTime.trans dupEncodePairComputer.step
    (ep.length + 1) (ep.length + 1) _ _ _ h1' h2'
  exact EvalsToInTime.trans dupEncodePairComputer.step
    ((ep.length + 1) + (ep.length + 1)) (ep.length + 1) _ _ _ h12 h3'

theorem dup_step_halt (work out : List Bool) :
    TM2.step dupEncodePairComputer.m
      (dupCfg (some .haltDrain) none [] [] [] work out) =
      some (dupCfg none none [] [] [] work out) := by
  simp [dupEncodePairComputer, dupCfg, dupStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option DupLabel), (none : Option Bool), stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, dupStk]

theorem dup_initList (s : List Bool) :
    initList dupEncodePairComputer s =
      dupCfg (some .load) none s [] [] [] [] := by
  refine congrArg (fun stk =>
      (⟨some DupLabel.load, none, stk⟩ : dupEncodePairComputer.Cfg)) ?_
  funext t; cases t <;> simp [dupEncodePairComputer, dupStk]

theorem dup_haltList (out : List Bool) :
    haltList dupEncodePairComputer out =
      dupCfg none none [] [] [] [] out := by
  refine congrArg (fun stk =>
      (⟨(none : Option DupLabel), (none : Option Bool), stk⟩ :
        dupEncodePairComputer.Cfg)) ?_
  funext t; cases t <;> simp [haltList, dupEncodePairComputer, dupStk]

/-- From `emitW` through halt, emitting `encodePair (s, s)`. -/
noncomputable def dup_evals_emit_to_halt (s : List Bool) :
    EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .emitW) none [] s (List.reverse s) [] [])
      (some (dupCfg none none [] [] [] [] (encodePair (s, s))))
      (1 + ((((encodePair (s, s)).length + 1) +
        (((encodePair (s, s)).length + 1) +
          ((encodePair (s, s)).length + 1))) +
        ((s.length + 1) + ((s.length + 1) + (1 + (s.length + 1)))))) := by
  have hemitW := dup_evals_emitW s (List.reverse s) [] []
  have hemitW' : EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .emitW) none [] s (List.reverse s) [] [])
      (some (dupCfg (some .emitSep) none [] [] (List.reverse s) []
        (List.reverse (s.flatMap fun c => [true, c]))))
      (s.length + 1) := by
    simpa [List.append_nil] using hemitW
  have hsep := dup_evals_one (dup_step_emitSep (List.reverse s) []
    (List.reverse (s.flatMap fun c => [true, c])))
  have h12 := EvalsToInTime.trans dupEncodePairComputer.step
    (s.length + 1) 1 _ _ _ hemitW' hsep
  have hprep := dup_evals_emitFstPrep (List.reverse s) [] []
    (false :: List.reverse (s.flatMap fun c => [true, c]))
  have hprep' : EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .emitFstPrep) none [] [] (List.reverse s) []
        (false :: List.reverse (s.flatMap fun c => [true, c])))
      (some (dupCfg (some .emitFst) none [] s [] []
        (false :: List.reverse (s.flatMap fun c => [true, c]))))
      (s.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using hprep
  have h123 := EvalsToInTime.trans dupEncodePairComputer.step
    (1 + (s.length + 1)) (s.length + 1) _ _ _ h12 hprep'
  have hemitF := dup_evals_emitFst s []
    (false :: List.reverse (s.flatMap fun c => [true, c]))
  have hout_emit :
      List.reverse s ++ false :: List.reverse (s.flatMap fun c => [true, c]) =
        List.reverse (encodePair (s, s)) := by
    simp [encodePair, List.reverse_append, List.reverse_cons]
  have h1234 := EvalsToInTime.trans dupEncodePairComputer.step
    ((s.length + 1) + (1 + (s.length + 1))) (s.length + 1) _ _ _ h123 hemitF
  have h1234' : EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .emitW) none [] s (List.reverse s) [] [])
      (some (dupCfg (some .rev1) none [] [] [] []
        (List.reverse (encodePair (s, s)))))
      ((s.length + 1) + ((s.length + 1) + (1 + (s.length + 1)))) := by
    simpa [hout_emit] using h1234
  have hunrev := dup_evals_unreverse (encodePair (s, s))
  have h5 := EvalsToInTime.trans dupEncodePairComputer.step
    ((s.length + 1) + ((s.length + 1) + (1 + (s.length + 1))))
    (((encodePair (s, s)).length + 1) +
      (((encodePair (s, s)).length + 1) +
        ((encodePair (s, s)).length + 1)))
    _ _ _ h1234' hunrev
  have hhalt := dup_evals_one (dup_step_halt [] (encodePair (s, s)))
  exact EvalsToInTime.trans dupEncodePairComputer.step
    ((((encodePair (s, s)).length + 1) +
      (((encodePair (s, s)).length + 1) +
        ((encodePair (s, s)).length + 1))) +
      ((s.length + 1) + ((s.length + 1) + (1 + (s.length + 1)))))
    1
    _ _ _ h5 hhalt

noncomputable def dup_evals (s : List Bool) :
    TM2OutputsInTime dupEncodePairComputer s
      (some (encodePair (s, s)))
      ((1 + ((((encodePair (s, s)).length + 1) +
        (((encodePair (s, s)).length + 1) +
          ((encodePair (s, s)).length + 1))) +
        ((s.length + 1) + ((s.length + 1) + (1 + (s.length + 1)))))) +
        ((s.length + 1) + ((s.length + 1) + ((s.length + 1) + (s.length + 1))))) := by
  have hload := dup_evals_load_to_emitW s
  have hemit := dup_evals_emit_to_halt s
  have hload' : EvalsToInTime dupEncodePairComputer.step
      (initList dupEncodePairComputer s)
      (some (dupCfg (some .emitW) none [] s (List.reverse s) [] []))
      ((s.length + 1) + ((s.length + 1) + ((s.length + 1) + (s.length + 1)))) := by
    simpa [dup_initList] using hload
  have hemit' : EvalsToInTime dupEncodePairComputer.step
      (dupCfg (some .emitW) none [] s (List.reverse s) [] [])
      (some (haltList dupEncodePairComputer (encodePair (s, s))))
      (1 + ((((encodePair (s, s)).length + 1) +
        (((encodePair (s, s)).length + 1) +
          ((encodePair (s, s)).length + 1))) +
        ((s.length + 1) + ((s.length + 1) + (1 + (s.length + 1)))))) := by
    simpa [dup_haltList] using hemit
  have h := EvalsToInTime.trans dupEncodePairComputer.step
    ((s.length + 1) + ((s.length + 1) + ((s.length + 1) + (s.length + 1))))
    (1 + ((((encodePair (s, s)).length + 1) +
      (((encodePair (s, s)).length + 1) +
        ((encodePair (s, s)).length + 1))) +
      ((s.length + 1) + ((s.length + 1) + (1 + (s.length + 1))))))
    _ _ _ hload' hemit'
  exact ⟨⟨h.steps, h.evals_in_steps⟩, h.steps_le_m⟩

noncomputable def dupEncodePairTime : Polynomial ℕ :=
  64 * (Polynomial.X ^ 2 + Polynomial.X + 1)

theorem dupEncodePairTime_eval (n : ℕ) :
    dupEncodePairTime.eval n = 64 * (n ^ 2 + n + 1) := by
  simp [dupEncodePairTime, pow_two, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one]

theorem dupEncodePairTime_bound (s : List Bool) :
    ((1 + ((((encodePair (s, s)).length + 1) +
      (((encodePair (s, s)).length + 1) +
        ((encodePair (s, s)).length + 1))) +
      ((s.length + 1) + ((s.length + 1) + (1 + (s.length + 1)))))) +
      ((s.length + 1) + ((s.length + 1) + ((s.length + 1) + (s.length + 1))))) ≤
      dupEncodePairTime.eval s.length := by
  simp [dupEncodePairTime_eval, length_encodePair]
  set N := s.length
  have hLHS :
      1 + (2 * N + 1 + N + 1 + (2 * N + 1 + N + 1 + (2 * N + 1 + N + 1)) +
        (N + 1 + (N + 1 + (1 + (N + 1))))) +
        (N + 1 + (N + 1 + (N + 1 + (N + 1)))) ≤
      32 * (N ^ 2 + N + 1) := by omega
  refine le_trans hLHS ?_
  omega

noncomputable def dupEncodePairComputableInPolyTime :
    TM2ComputableInPolyTime idBitEnc encodePair (fun s => (s, s)) where
  tm := dupEncodePairComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := dupEncodePairTime
  outputsFun s := by
    change TM2OutputsInTime dupEncodePairComputer
      (List.map id (idBitEnc s))
      (some (List.map id (encodePair (s, s))))
      (dupEncodePairTime.eval (idBitEnc s).length)
    simp only [List.map_id, id_eq, idBitEnc]
    exact evalsToInTime_le_mono (dup_evals s) (dupEncodePairTime_bound s)

/-! ## FinTM2: map first component to unary under `encodePair`

`encodePair (x, y) ↦ encodePair (toUnary x, y)`. Parse pushes `true` per
first-component bit (so `left = toUnary x`), load `y` reversed, then the same
emit pipeline as `swapPairComputer`. -/

inductive MapUStack where
  | inp | left | right | out
  deriving DecidableEq, Repr

instance : Fintype MapUStack where
  elems := {.inp, .left, .right, .out}
  complete s := by cases s <;> simp

inductive MapULabel where
  | parse | expectBit | loadRight
  | emitW | emitSep | emitFstPrep | emitFst
  | rev1 | rev2 | rev3 | haltDrain
  deriving DecidableEq, Repr

instance : Fintype MapULabel where
  elems := {.parse, .expectBit, .loadRight, .emitW, .emitSep, .emitFstPrep,
    .emitFst, .rev1, .rev2, .rev3, .haltDrain}
  complete s := by cases s <;> simp

def mapUStk (inp left right out : List Bool) : MapUStack → List Bool
  | .inp => inp
  | .left => left
  | .right => right
  | .out => out

def mapFstToUnaryComputer : FinTM2 where
  K := MapUStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := MapULabel
  main := .parse
  σ := Option Bool
  initialState := none
  m
    | .parse =>
        pop MapUStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => MapULabel.haltDrain)
            (branch (fun s => decide (s = some false))
              (load (fun _ => none) <| goto fun _ => MapULabel.loadRight)
              (load (fun _ => none) <| goto fun _ => MapULabel.expectBit))
    | .expectBit =>
        pop MapUStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => MapULabel.haltDrain)
            (push MapUStack.left (fun _ => true) <|
              load (fun _ => none) <| goto fun _ => MapULabel.parse)
    | .loadRight =>
        pop MapUStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => MapULabel.emitW)
            (push MapUStack.right (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => MapULabel.loadRight)
    | .emitW =>
        pop MapUStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => MapULabel.emitSep)
            (push MapUStack.out (fun _ => true) <|
              push MapUStack.out (fun s => s.getD false) <|
                load (fun _ => none) <| goto fun _ => MapULabel.emitW)
    | .emitSep =>
        push MapUStack.out (fun _ => false) <|
          load (fun _ => none) <| goto fun _ => MapULabel.emitFstPrep
    | .emitFstPrep =>
        pop MapUStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => MapULabel.emitFst)
            (push MapUStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => MapULabel.emitFstPrep)
    | .emitFst =>
        pop MapUStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => MapULabel.rev1)
            (push MapUStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => MapULabel.emitFst)
    | .rev1 =>
        pop MapUStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => MapULabel.rev2)
            (push MapUStack.right (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => MapULabel.rev1)
    | .rev2 =>
        pop MapUStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => MapULabel.rev3)
            (push MapUStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => MapULabel.rev2)
    | .rev3 =>
        pop MapUStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => MapULabel.haltDrain)
            (push MapUStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => MapULabel.rev3)
    | .haltDrain =>
        pop MapUStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            halt
            (load (fun _ => none) <| goto fun _ => MapULabel.haltDrain)

def mapUCfg (l : Option MapULabel) (v : Option Bool)
    (inp left right out : List Bool) : mapFstToUnaryComputer.Cfg :=
  ⟨l, v, mapUStk inp left right out⟩

def mapFstToUnaryPair (p : List Bool × List Bool) : List Bool :=
  encodePair (toUnary p.1, p.2)

theorem mapFstToUnaryPair_encode (x y : List Bool) :
    mapFstToUnaryPair (x, y) = encodePair (toUnary x, y) := rfl

theorem mapU_step_parse_true (rest left right out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .parse) none (true :: rest) left right out) =
      some (mapUCfg (some .expectBit) none rest left right out) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.expectBit, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

theorem mapU_step_expectBit (b : Bool) (rest left right out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .expectBit) none (b :: rest) left right out) =
      some (mapUCfg (some .parse) none rest (true :: left) right out) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.parse, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

theorem mapU_step_parse_false (rest left right out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .parse) none (false :: rest) left right out) =
      some (mapUCfg (some .loadRight) none rest left right out) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.loadRight, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

theorem mapU_step_loadRight_cons (c : Bool) (rest left right out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .loadRight) none (c :: rest) left right out) =
      some (mapUCfg (some .loadRight) none rest left (c :: right) out) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.loadRight, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

theorem mapU_step_loadRight_nil (left right out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .loadRight) none [] left right out) =
      some (mapUCfg (some .emitW) none [] left right out) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.emitW, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

def mapU_evals_one {c c' : mapFstToUnaryComputer.Cfg}
    (h : TM2.step mapFstToUnaryComputer.m c = some c') :
    EvalsToInTime mapFstToUnaryComputer.step c (some c') 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := by
    change (some c).bind mapFstToUnaryComputer.step = some c'
    simpa [FinTM2.step] using h

def mapU_evals_parse_one (c : Bool) (rest left right out : List Bool) :
    EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .parse) none (true :: c :: rest) left right out)
      (some (mapUCfg (some .parse) none rest (true :: left) right out)) 2 := by
  exact EvalsToInTime.trans mapFstToUnaryComputer.step 1 1 _ _ _
    (mapU_evals_one (mapU_step_parse_true (c :: rest) left right out))
    (mapU_evals_one (mapU_step_expectBit c rest left right out))

theorem replicate_true_append_cons_eq (n : ℕ) (left : List Bool) :
    List.replicate n true ++ true :: left =
      true :: (List.replicate n true ++ left) := by
  induction n generalizing left with
  | zero => simp
  | succ n ih =>
      simpa [List.replicate_succ, List.cons_append] using
        congrArg (List.cons true) (ih left)

noncomputable def mapU_evals_parse (xs rest left right out : List Bool) :
    EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .parse) none
        (xs.flatMap (fun b => [true, b]) ++ rest) left right out)
      (some (mapUCfg (some .parse) none rest
        (List.replicate xs.length true ++ left) right out))
      (2 * xs.length) := by
  induction xs generalizing left with
  | nil =>
      simpa [List.flatMap, List.replicate] using
        (EvalsToInTime.refl mapFstToUnaryComputer.step
          (mapUCfg (some .parse) none rest left right out))
  | cons c xs ih =>
      have h1 := mapU_evals_parse_one c (xs.flatMap (fun b => [true, b]) ++ rest)
        left right out
      have h2 := ih (true :: left)
      have h := EvalsToInTime.trans mapFstToUnaryComputer.step 2 (2 * xs.length) _ _ _ h1 h2
      have htime : 2 * xs.length + 2 = 2 * (c :: xs).length := by
        simp [List.length_cons]; ring
      simpa [List.flatMap_cons, replicate_true_append_cons_eq, List.replicate_succ,
        htime] using h

noncomputable def mapU_evals_loadRight (ys left right out : List Bool) :
    EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .loadRight) none ys left right out)
      (some (mapUCfg (some .emitW) none [] left (List.reverse ys ++ right) out))
      (ys.length + 1) := by
  induction ys generalizing right with
  | nil =>
      exact mapU_evals_one (mapU_step_loadRight_nil left right out)
  | cons c ys ih =>
      have h1 := mapU_evals_one (mapU_step_loadRight_cons c ys left right out)
      have h2 := ih (c :: right)
      have h := EvalsToInTime.trans mapFstToUnaryComputer.step 1 (ys.length + 1) _ _ _ h1 h2
      have htime : (ys.length + 1) + 1 = (c :: ys).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

/-- Parse through load: at emitW with left = toUnary x and right = reverse y. -/
noncomputable def mapU_evals_load_to_emitW (x y : List Bool) :
    EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .parse) none (encodePair (x, y)) [] [] [])
      (some (mapUCfg (some .emitW) none [] (toUnary x) (List.reverse y) []))
      ((y.length + 1) + (1 + 2 * x.length)) := by
  have hparse := mapU_evals_parse x (false :: y) [] [] []
  have h1 : EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .parse) none (encodePair (x, y)) [] [] [])
      (some (mapUCfg (some .parse) none (false :: y)
        (List.replicate x.length true) [] []))
      (2 * x.length) := by
    simpa [encodePair, List.append_assoc] using hparse
  have hfalse := mapU_evals_one
    (mapU_step_parse_false y (List.replicate x.length true) [] [])
  have h12 := EvalsToInTime.trans mapFstToUnaryComputer.step
    (2 * x.length) 1 _ _ _ h1 hfalse
  have hload := mapU_evals_loadRight y (List.replicate x.length true) [] []
  have h123 := EvalsToInTime.trans mapFstToUnaryComputer.step
    (1 + 2 * x.length) (y.length + 1) _ _ _ h12 hload
  simpa [toUnary, unaryNat, List.append_nil] using h123

theorem mapU_step_emitW_nil (right out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .emitW) none [] [] right out) =
      some (mapUCfg (some .emitSep) none [] [] right out) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.emitSep, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

theorem mapU_step_emitW_cons (c : Bool) (rest right out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .emitW) none [] (c :: rest) right out) =
      some (mapUCfg (some .emitW) none [] rest right (c :: true :: out)) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.emitW, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

def mapU_evals_emitW (left right out : List Bool) :
    EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .emitW) none [] left right out)
      (some (mapUCfg (some .emitSep) none [] [] right
        (List.reverse (left.flatMap fun c => [true, c]) ++ out)))
      (left.length + 1) := by
  induction left generalizing out with
  | nil =>
      simpa [List.flatMap] using mapU_evals_one (mapU_step_emitW_nil right out)
  | cons c left ih =>
      have h1 := mapU_evals_one (mapU_step_emitW_cons c left right out)
      have h2 := ih (c :: true :: out)
      have h := EvalsToInTime.trans mapFstToUnaryComputer.step 1 (left.length + 1) _ _ _ h1 h2
      have htime : (left.length + 1) + 1 = (c :: left).length + 1 := by
        simp [List.length_cons]
      have hout :
          List.reverse ((c :: left).flatMap fun c => [true, c]) ++ out =
            List.reverse (left.flatMap fun c => [true, c]) ++ c :: true :: out := by
        simp [List.flatMap_cons, List.reverse_cons]
      simpa [htime, hout, List.append_assoc] using h

theorem mapU_step_emitSep (right out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .emitSep) none [] [] right out) =
      some (mapUCfg (some .emitFstPrep) none [] [] right (false :: out)) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.emitFstPrep, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

theorem mapU_step_emitFstPrep_cons (c : Bool) (rest left out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .emitFstPrep) none [] left (c :: rest) out) =
      some (mapUCfg (some .emitFstPrep) none [] (c :: left) rest out) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.emitFstPrep, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

theorem mapU_step_emitFstPrep_nil (left out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .emitFstPrep) none [] left [] out) =
      some (mapUCfg (some .emitFst) none [] left [] out) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.emitFst, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

noncomputable def mapU_evals_emitFstPrep (right left out : List Bool) :
    EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .emitFstPrep) none [] left right out)
      (some (mapUCfg (some .emitFst) none [] (List.reverse right ++ left) [] out))
      (right.length + 1) := by
  induction right generalizing left with
  | nil =>
      exact mapU_evals_one (mapU_step_emitFstPrep_nil left out)
  | cons c right ih =>
      have h1 := mapU_evals_one (mapU_step_emitFstPrep_cons c right left out)
      have h2 := ih (c :: left)
      have h := EvalsToInTime.trans mapFstToUnaryComputer.step 1 (right.length + 1) _ _ _ h1 h2
      have htime : (right.length + 1) + 1 = (c :: right).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem mapU_step_emitFst_cons (c : Bool) (rest out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .emitFst) none [] (c :: rest) [] out) =
      some (mapUCfg (some .emitFst) none [] rest [] (c :: out)) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.emitFst, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

theorem mapU_step_emitFst_nil (out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .emitFst) none [] [] [] out) =
      some (mapUCfg (some .rev1) none [] [] [] out) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.rev1, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

def mapU_evals_emitFst (left out : List Bool) :
    EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .emitFst) none [] left [] out)
      (some (mapUCfg (some .rev1) none [] [] [] (List.reverse left ++ out)))
      (left.length + 1) := by
  induction left generalizing out with
  | nil =>
      exact mapU_evals_one (mapU_step_emitFst_nil out)
  | cons c left ih =>
      have h1 := mapU_evals_one (mapU_step_emitFst_cons c left out)
      have h2 := ih (c :: out)
      have h := EvalsToInTime.trans mapFstToUnaryComputer.step 1 (left.length + 1) _ _ _ h1 h2
      have htime : (left.length + 1) + 1 = (c :: left).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem mapU_step_rev1_cons (c : Bool) (rest right : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .rev1) none [] [] right (c :: rest)) =
      some (mapUCfg (some .rev1) none [] [] (c :: right) rest) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.rev1, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

theorem mapU_step_rev1_nil (right : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .rev1) none [] [] right []) =
      some (mapUCfg (some .rev2) none [] [] right []) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.rev2, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

def mapU_evals_rev1 (out right : List Bool) :
    EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .rev1) none [] [] right out)
      (some (mapUCfg (some .rev2) none [] [] (List.reverse out ++ right) []))
      (out.length + 1) := by
  induction out generalizing right with
  | nil =>
      exact mapU_evals_one (mapU_step_rev1_nil right)
  | cons c out ih =>
      have h1 := mapU_evals_one (mapU_step_rev1_cons c out right)
      have h2 := ih (c :: right)
      have h := EvalsToInTime.trans mapFstToUnaryComputer.step 1 (out.length + 1) _ _ _ h1 h2
      have htime : (out.length + 1) + 1 = (c :: out).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem mapU_step_rev2_cons (c : Bool) (rest left out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .rev2) none [] left (c :: rest) out) =
      some (mapUCfg (some .rev2) none [] (c :: left) rest out) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.rev2, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

theorem mapU_step_rev2_nil (left out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .rev2) none [] left [] out) =
      some (mapUCfg (some .rev3) none [] left [] out) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.rev3, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

def mapU_evals_rev2 (right left out : List Bool) :
    EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .rev2) none [] left right out)
      (some (mapUCfg (some .rev3) none [] (List.reverse right ++ left) [] out))
      (right.length + 1) := by
  induction right generalizing left with
  | nil =>
      exact mapU_evals_one (mapU_step_rev2_nil left out)
  | cons c right ih =>
      have h1 := mapU_evals_one (mapU_step_rev2_cons c right left out)
      have h2 := ih (c :: left)
      have h := EvalsToInTime.trans mapFstToUnaryComputer.step 1 (right.length + 1) _ _ _ h1 h2
      have htime : (right.length + 1) + 1 = (c :: right).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem mapU_step_rev3_cons (c : Bool) (rest out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .rev3) none [] (c :: rest) [] out) =
      some (mapUCfg (some .rev3) none [] rest [] (c :: out)) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.rev3, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

theorem mapU_step_rev3_nil (out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .rev3) none [] [] [] out) =
      some (mapUCfg (some .haltDrain) none [] [] [] out) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some MapULabel.haltDrain, (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

def mapU_evals_rev3 (left out : List Bool) :
    EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .rev3) none [] left [] out)
      (some (mapUCfg (some .haltDrain) none [] [] [] (List.reverse left ++ out)))
      (left.length + 1) := by
  induction left generalizing out with
  | nil =>
      exact mapU_evals_one (mapU_step_rev3_nil out)
  | cons c left ih =>
      have h1 := mapU_evals_one (mapU_step_rev3_cons c left out)
      have h2 := ih (c :: out)
      have h := EvalsToInTime.trans mapFstToUnaryComputer.step 1 (left.length + 1) _ _ _ h1 h2
      have htime : (left.length + 1) + 1 = (c :: left).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

def mapU_evals_unreverse (ep : List Bool) :
    EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .rev1) none [] [] [] (List.reverse ep))
      (some (mapUCfg (some .haltDrain) none [] [] [] ep))
      ((ep.length + 1) + ((ep.length + 1) + (ep.length + 1))) := by
  have h1 := mapU_evals_rev1 (List.reverse ep) []
  have h1' : EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .rev1) none [] [] [] (List.reverse ep))
      (some (mapUCfg (some .rev2) none [] [] ep []))
      (ep.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using h1
  have h2 := mapU_evals_rev2 ep [] []
  have h2' : EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .rev2) none [] [] ep [])
      (some (mapUCfg (some .rev3) none [] (List.reverse ep) [] []))
      (ep.length + 1) := by
    simpa [List.append_nil] using h2
  have h3 := mapU_evals_rev3 (List.reverse ep) []
  have h3' : EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .rev3) none [] (List.reverse ep) [] [])
      (some (mapUCfg (some .haltDrain) none [] [] [] ep))
      (ep.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using h3
  have h12 := EvalsToInTime.trans mapFstToUnaryComputer.step
    (ep.length + 1) (ep.length + 1) _ _ _ h1' h2'
  exact EvalsToInTime.trans mapFstToUnaryComputer.step
    ((ep.length + 1) + (ep.length + 1)) (ep.length + 1) _ _ _ h12 h3'

theorem mapU_step_halt (out : List Bool) :
    TM2.step mapFstToUnaryComputer.m
      (mapUCfg (some .haltDrain) none [] [] [] out) =
      some (mapUCfg none none [] [] [] out) := by
  simp [mapFstToUnaryComputer, mapUCfg, mapUStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option MapULabel), (none : Option Bool), stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, mapUStk]

theorem mapU_initList (s : List Bool) :
    initList mapFstToUnaryComputer s =
      mapUCfg (some .parse) none s [] [] [] := by
  refine congrArg (fun stk =>
      (⟨some MapULabel.parse, none, stk⟩ : mapFstToUnaryComputer.Cfg)) ?_
  funext t; cases t <;> simp [mapFstToUnaryComputer, mapUStk]

theorem mapU_haltList (out : List Bool) :
    haltList mapFstToUnaryComputer out =
      mapUCfg none none [] [] [] out := by
  refine congrArg (fun stk =>
      (⟨(none : Option MapULabel), (none : Option Bool), stk⟩ :
        mapFstToUnaryComputer.Cfg)) ?_
  funext t; cases t <;> simp [haltList, mapFstToUnaryComputer, mapUStk]

/-- From emitW (left = toUnary x, right = reverse y) through halt. -/
noncomputable def mapU_evals_emit_to_halt (x y : List Bool) :
    EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .emitW) none [] (toUnary x) (List.reverse y) [])
      (some (mapUCfg none none [] [] [] (encodePair (toUnary x, y))))
      (1 + ((((encodePair (toUnary x, y)).length + 1) +
        (((encodePair (toUnary x, y)).length + 1) +
          ((encodePair (toUnary x, y)).length + 1))) +
        ((y.length + 1) + ((y.length + 1) + (1 + (x.length + 1)))))) := by
  have hemitW := mapU_evals_emitW (toUnary x) (List.reverse y) []
  have hemitW' : EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .emitW) none [] (toUnary x) (List.reverse y) [])
      (some (mapUCfg (some .emitSep) none [] [] (List.reverse y)
        (List.reverse ((toUnary x).flatMap fun c => [true, c]))))
      (x.length + 1) := by
    simpa [toUnary, unaryNat, length_unaryNat, List.append_nil] using hemitW
  have hsep := mapU_evals_one (mapU_step_emitSep (List.reverse y)
    (List.reverse ((toUnary x).flatMap fun c => [true, c])))
  have h12 := EvalsToInTime.trans mapFstToUnaryComputer.step
    (x.length + 1) 1 _ _ _ hemitW' hsep
  have hprep := mapU_evals_emitFstPrep (List.reverse y) []
    (false :: List.reverse ((toUnary x).flatMap fun c => [true, c]))
  have hprep' : EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .emitFstPrep) none [] [] (List.reverse y)
        (false :: List.reverse ((toUnary x).flatMap fun c => [true, c])))
      (some (mapUCfg (some .emitFst) none [] y []
        (false :: List.reverse ((toUnary x).flatMap fun c => [true, c]))))
      (y.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using hprep
  have h123 := EvalsToInTime.trans mapFstToUnaryComputer.step
    (1 + (x.length + 1)) (y.length + 1) _ _ _ h12 hprep'
  have hemitF := mapU_evals_emitFst y
    (false :: List.reverse ((toUnary x).flatMap fun c => [true, c]))
  have hout_emit :
      List.reverse y ++ false :: List.reverse ((toUnary x).flatMap fun c => [true, c]) =
        List.reverse (encodePair (toUnary x, y)) := by
    simp [encodePair, List.reverse_append, List.reverse_cons]
  have h1234 := EvalsToInTime.trans mapFstToUnaryComputer.step
    ((y.length + 1) + (1 + (x.length + 1))) (y.length + 1) _ _ _ h123 hemitF
  have h1234' : EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .emitW) none [] (toUnary x) (List.reverse y) [])
      (some (mapUCfg (some .rev1) none [] [] []
        (List.reverse (encodePair (toUnary x, y)))))
      ((y.length + 1) + ((y.length + 1) + (1 + (x.length + 1)))) := by
    simpa [hout_emit] using h1234
  have hunrev := mapU_evals_unreverse (encodePair (toUnary x, y))
  have h5 := EvalsToInTime.trans mapFstToUnaryComputer.step
    ((y.length + 1) + ((y.length + 1) + (1 + (x.length + 1))))
    (((encodePair (toUnary x, y)).length + 1) +
      (((encodePair (toUnary x, y)).length + 1) +
        ((encodePair (toUnary x, y)).length + 1)))
    _ _ _ h1234' hunrev
  have hhalt := mapU_evals_one (mapU_step_halt (encodePair (toUnary x, y)))
  exact EvalsToInTime.trans mapFstToUnaryComputer.step
    ((((encodePair (toUnary x, y)).length + 1) +
      (((encodePair (toUnary x, y)).length + 1) +
        ((encodePair (toUnary x, y)).length + 1))) +
      ((y.length + 1) + ((y.length + 1) + (1 + (x.length + 1)))))
    1
    _ _ _ h5 hhalt

noncomputable def mapU_evals (x y : List Bool) :
    TM2OutputsInTime mapFstToUnaryComputer (encodePair (x, y))
      (some (mapFstToUnaryPair (x, y)))
      ((1 + ((((encodePair (toUnary x, y)).length + 1) +
        (((encodePair (toUnary x, y)).length + 1) +
          ((encodePair (toUnary x, y)).length + 1))) +
        ((y.length + 1) + ((y.length + 1) + (1 + (x.length + 1)))))) +
        ((y.length + 1) + (1 + 2 * x.length))) := by
  have hload := mapU_evals_load_to_emitW x y
  have hemit := mapU_evals_emit_to_halt x y
  have hload' : EvalsToInTime mapFstToUnaryComputer.step
      (initList mapFstToUnaryComputer (encodePair (x, y)))
      (some (mapUCfg (some .emitW) none [] (toUnary x) (List.reverse y) []))
      ((y.length + 1) + (1 + 2 * x.length)) := by
    simpa [mapU_initList] using hload
  have hemit' : EvalsToInTime mapFstToUnaryComputer.step
      (mapUCfg (some .emitW) none [] (toUnary x) (List.reverse y) [])
      (some (haltList mapFstToUnaryComputer (mapFstToUnaryPair (x, y))))
      (1 + ((((encodePair (toUnary x, y)).length + 1) +
        (((encodePair (toUnary x, y)).length + 1) +
          ((encodePair (toUnary x, y)).length + 1))) +
        ((y.length + 1) + ((y.length + 1) + (1 + (x.length + 1)))))) := by
    simpa [mapU_haltList, mapFstToUnaryPair] using hemit
  have h := EvalsToInTime.trans mapFstToUnaryComputer.step
    ((y.length + 1) + (1 + 2 * x.length))
    (1 + ((((encodePair (toUnary x, y)).length + 1) +
      (((encodePair (toUnary x, y)).length + 1) +
        ((encodePair (toUnary x, y)).length + 1))) +
      ((y.length + 1) + ((y.length + 1) + (1 + (x.length + 1))))))
    _ _ _ hload' hemit'
  exact ⟨⟨h.steps, h.evals_in_steps⟩, h.steps_le_m⟩

noncomputable def mapFstToUnaryTime : Polynomial ℕ :=
  64 * (Polynomial.X ^ 2 + Polynomial.X + 1)

theorem mapFstToUnaryTime_eval (n : ℕ) :
    mapFstToUnaryTime.eval n = 64 * (n ^ 2 + n + 1) := by
  simp [mapFstToUnaryTime, pow_two, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one]

theorem mapFstToUnaryTime_bound (x y : List Bool) :
    ((1 + ((((encodePair (toUnary x, y)).length + 1) +
      (((encodePair (toUnary x, y)).length + 1) +
        ((encodePair (toUnary x, y)).length + 1))) +
      ((y.length + 1) + ((y.length + 1) + (1 + (x.length + 1)))))) +
      ((y.length + 1) + (1 + 2 * x.length))) ≤
      mapFstToUnaryTime.eval (encodePair (x, y)).length := by
  simp [mapFstToUnaryTime_eval, length_encodePair, toUnary, length_unaryNat]
  set N := 2 * x.length + 1 + y.length
  have hLHS :
      1 + (2 * x.length + 1 + y.length + 1 +
          (2 * x.length + 1 + y.length + 1 +
            (2 * x.length + 1 + y.length + 1)) +
        (y.length + 1 + (y.length + 1 + (1 + (x.length + 1))))) +
        (y.length + 1 + (1 + 2 * x.length)) ≤
      32 * (N ^ 2 + N + 1) := by omega
  refine le_trans hLHS ?_
  omega

noncomputable def mapFstToUnaryComputableInPolyTime :
    TM2ComputableInPolyTime encodePair encodePair
      (fun p => (toUnary p.1, p.2)) where
  tm := mapFstToUnaryComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := mapFstToUnaryTime
  outputsFun p := by
    rcases p with ⟨x, y⟩
    change TM2OutputsInTime mapFstToUnaryComputer
      (List.map id (encodePair (x, y)))
      (some (List.map id (encodePair (toUnary x, y))))
      (mapFstToUnaryTime.eval (encodePair (x, y)).length)
    simp only [List.map_id, id_eq]
    exact evalsToInTime_le_mono (mapU_evals x y) (mapFstToUnaryTime_bound x y)

/-- Out-bound for `dupEncodePair`: `|encodePair (s,s)| = 3|s|+1`. -/
noncomputable def dupEncodePairOutBound : Polynomial ℕ :=
  3 * Polynomial.X + 1

theorem dupEncodePairOutBound_eval (n : ℕ) :
    dupEncodePairOutBound.eval n = 3 * n + 1 := by
  simp [dupEncodePairOutBound, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one]

theorem length_dupEncodePair_le_outBound (s : List Bool) :
    (encodePair (s, s)).length ≤ dupEncodePairOutBound.eval s.length := by
  simpa [length_dupEncodePair, dupEncodePairOutBound_eval] using le_rfl

/-- `s ↦ encodePair (toUnary s, s)` via dup then mapFstToUnary. -/
noncomputable def toUnarySelfPairComputableInPolyTime :
    TM2ComputableInPolyTime idBitEnc encodePair
      (fun s => (toUnary s, s)) := by
  let decodeOut : dupEncodePairComputer.Γ dupEncodePairComputer.k₁ → Bool := id
  let encodeIn : Bool → mapFstToUnaryComputer.Γ mapFstToUnaryComputer.k₀ := id
  let tm :=
    seqCompComputer (βΓ := Bool) dupEncodePairComputer mapFstToUnaryComputer
      decodeOut encodeIn
  let inA : tm.Γ tm.k₀ ≃ Bool := by
    simpa [tm, seqCompComputer, CompΓ, CompK] using (Equiv.refl Bool)
  let outA : tm.Γ tm.k₁ ≃ Bool := by
    simpa [tm, seqCompComputer, CompΓ, CompK] using (Equiv.refl Bool)
  let outP := dupEncodePairOutBound
  let timeBound : Polynomial ℕ :=
    dupEncodePairTime + (4 * (outP + 1)) + (mapFstToUnaryTime.comp outP)
  refine
    { tm := tm
      inputAlphabet := inA
      outputAlphabet := outA
      time := timeBound
      outputsFun := ?out }
  case out =>
    intro s
    change TM2OutputsInTime tm (List.map inA.invFun (idBitEnc s))
      (some (List.map outA.invFun (encodePair (toUnary s, s))))
      (timeBound.eval (idBitEnc s).length)
    set mid := encodePair (s, s) with hmid_def
    have hin :
        List.map inA.invFun (idBitEnc s) = idBitEnc s := by
      change List.map (Equiv.refl Bool).symm (idBitEnc s) = idBitEnc s
      simp [idBitEnc]
    have hout :
        List.map outA.invFun (encodePair (toUnary s, s)) =
          encodePair (toUnary s, s) := by
      change List.map (Equiv.refl Bool).symm (encodePair (toUnary s, s)) =
        encodePair (toUnary s, s)
      simp
    have h1 : EvalsToInTime dupEncodePairComputer.step
        (initList dupEncodePairComputer (idBitEnc s))
        (some (haltList dupEncodePairComputer mid))
        (dupEncodePairTime.eval (idBitEnc s).length) := by
      simpa [hmid_def, idBitEnc, List.map_id] using
        evalsToInTime_le_mono (dup_evals s) (dupEncodePairTime_bound s)
    have h2 : EvalsToInTime mapFstToUnaryComputer.step
        (initList mapFstToUnaryComputer (mid.map (encodeIn ∘ decodeOut)))
        (some (haltList mapFstToUnaryComputer (encodePair (toUnary s, s))))
        (mapFstToUnaryTime.eval mid.length) := by
      have hmap : mid.map (encodeIn ∘ decodeOut) = mid := by
        change List.map (id ∘ id) mid = mid
        simp [List.map_id]
      rw [hmap, hmid_def]
      simpa using
        evalsToInTime_le_mono (mapU_evals s s) (mapFstToUnaryTime_bound s s)
    have heval :=
      seqComp_evals_compose (βΓ := Bool) dupEncodePairComputer mapFstToUnaryComputer
        decodeOut encodeIn (idBitEnc s) mid (encodePair (toUnary s, s))
        (dupEncodePairTime.eval (idBitEnc s).length)
        (mapFstToUnaryTime.eval mid.length) h1 h2
    set n := (idBitEnc s).length with hn_def
    have hflen : mid.length ≤ outP.eval n := by
      simpa [hmid_def, hn_def, idBitEnc, outP] using length_dupEncodePair_le_outBound s
    have hcopy :
        (2 * mid.length + 1) + (2 * mid.length + 1) ≤ 4 * (outP.eval n + 1) := by
      have : 4 * (mid.length + 1) ≤ 4 * (outP.eval n + 1) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right hflen 1)
      omega
    have hmapT :
        mapFstToUnaryTime.eval mid.length ≤ (mapFstToUnaryTime.comp outP).eval n := by
      have h1' : mapFstToUnaryTime.eval mid.length ≤
          mapFstToUnaryTime.eval (outP.eval n) :=
        poly_eval_mono mapFstToUnaryTime hflen
      simpa [Polynomial.eval_comp] using h1'
    have hbound :
        dupEncodePairTime.eval n +
          (2 * mid.length + 1) + (2 * mid.length + 1) +
          mapFstToUnaryTime.eval mid.length ≤
        timeBound.eval n := by
      have hc := hcopy
      have hu := hmapT
      have hstep :
          dupEncodePairTime.eval n +
              ((2 * mid.length + 1) + (2 * mid.length + 1)) +
              mapFstToUnaryTime.eval mid.length ≤
            dupEncodePairTime.eval n + 4 * (outP.eval n + 1) +
              (mapFstToUnaryTime.comp outP).eval n := by
        refine Nat.add_le_add ?_ hu
        exact Nat.add_le_add_left hc _
      convert hstep using 1
      · ac_rfl
      · simp [timeBound, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_one, Polynomial.eval_ofNat]
    have hfinal := evalsToInTime_le_mono (by simpa [hn_def] using heval) hbound
    have hraw : EvalsToInTime tm.step
        (initList tm (idBitEnc s))
        (some (haltList tm (encodePair (toUnary s, s))))
        (timeBound.eval n) := by
      simpa [tm, hn_def] using hfinal
    refine evalsToInTime_congr_end
      (by
        have hstart :
            initList tm (List.map inA.invFun (idBitEnc s)) =
              initList tm (idBitEnc s) :=
          congrArg (initList tm) hin
        exact { steps := hraw.steps
                steps_le_m := by simpa [hn_def] using hraw.steps_le_m
                evals_in_steps := by
                  rw [hstart]
                  exact hraw.evals_in_steps })
      (congrArg some (congrArg (haltList tm) hout.symm))

/-- Quadratic unary eval expands to `a n^2 + b n + c`. -/
theorem polyEvalUnary_quadratic (a b c n : ℕ) :
    polyEvalUnary
        (Polynomial.C a * Polynomial.X ^ 2 +
          Polynomial.C b * Polynomial.X + Polynomial.C c) n =
      List.replicate (a * n ^ 2 + b * n + c) true := by
  simp [polyEvalUnary, unaryNat, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, pow_two]

theorem unaryPow_succ_eq_mul (u : List Bool) (k : ℕ) :
    unaryPow u (k + 1) = unaryMul (unaryPow u k) u := rfl

theorem polyEvalUnary_C (c n : ℕ) :
    polyEvalUnary (Polynomial.C c) n = List.replicate c true := by
  simp [polyEvalUnary, unaryNat]

/-- Constant polynomial unary eval ignores input length (drain+write via scaleAppend 0). -/
noncomputable def polyEvalUnaryConstComputableInPolyTime (c : ℕ) :
    TM2ComputableInPolyTime idBitEnc idBitEnc
      (fun s => polyEvalUnary (Polynomial.C c) s.length) := by
  convert scaleAppendComputableInPolyTime 0 c using 1
  funext s
  simpa [Nat.zero_mul, Nat.zero_add] using polyEvalUnary_C c s.length

/-- Degree ≤ 1 polynomials are exact poly-time unary budgets. -/
noncomputable def polyEvalUnaryDegLeOneComputableInPolyTime (p : Polynomial ℕ)
    (hp : p.natDegree ≤ 1) :
    TM2ComputableInPolyTime idBitEnc idBitEnc
      (fun s => polyEvalUnary p s.length) := by
  let a := p.coeff 1
  let b := p.coeff 0
  have hform : p = Polynomial.C a * Polynomial.X + Polynomial.C b :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hp
  convert polyEvalUnaryLinearComputableInPolyTime a b using 1
  funext s
  rw [hform, polyEvalUnary_linear]

theorem unaryMul_one_left_replicate (n : ℕ) :
    unaryMul [true] (List.replicate n true) = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [unaryMul, List.replicate_succ, List.flatMap_cons, List.singleton_append]
      simpa [unaryMul] using congrArg (List.cons true) ih

theorem unaryPow_two_toUnary (s : List Bool) :
    unaryPow (toUnary s) 2 = List.replicate (s.length ^ 2) true := by
  have h1 : unaryPow (toUnary s) 1 = toUnary s := by
    simp [unaryPow, toUnary, unaryNat, unaryMul_one_left_replicate]
  rw [show unaryPow (toUnary s) 2 = unaryMul (unaryPow (toUnary s) 1) (toUnary s) from rfl,
    h1, toUnary, unaryNat, Nat.pow_two]
  exact unaryMul_of_replicate s.length s.length

/-- Linear length gate equals unary compare against `scaleAppend` output. -/
theorem lengthOk_linear (a b : ℕ) (φ w : List Bool) :
    lengthOk (Polynomial.C a * Polynomial.X + Polynomial.C b) φ w =
      unaryLE w (List.replicate (a * φ.length + b) true) := by
  rw [lengthOk_eq_unaryLE_poly, polyEvalUnary_linear]

/-- Degree ≤ 1 length gate reduces to the linear case. -/
theorem lengthOk_of_natDegree_le_one (p : Polynomial ℕ) (hp : p.natDegree ≤ 1)
    (φ w : List Bool) :
    lengthOk p φ w =
      unaryLE w (List.replicate (p.coeff 1 * φ.length + p.coeff 0) true) := by
  let a := p.coeff 1
  let b := p.coeff 0
  change lengthOk p φ w = unaryLE w (List.replicate (a * φ.length + b) true)
  have hform : p = Polynomial.C a * Polynomial.X + Polynomial.C b :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hp
  rw [hform, lengthOk_linear]

/-- Prep map for linear lengthOk: rebuild `encodePair (w, budget)`. -/
def lengthOkLinearPair (a b : ℕ) (φ w : List Bool) : List Bool :=
  encodePair (w, List.replicate (a * φ.length + b) true)

theorem lengthOk_linear_eq_unaryLE_pair (a b : ℕ) (φ w : List Bool) :
    lengthOk (Polynomial.C a * Polynomial.X + Polynomial.C b) φ w =
      unaryLE w (List.replicate (a * φ.length + b) true) :=
  lengthOk_linear a b φ w

theorem unaryLE_lengthOkLinearPair (a b : ℕ) (φ w : List Bool) :
    unaryLE ((decodePair (lengthOkLinearPair a b φ w)).getD ([], [])).1
        ((decodePair (lengthOkLinearPair a b φ w)).getD ([], [])).2 =
      lengthOk (Polynomial.C a * Polynomial.X + Polynomial.C b) φ w := by
  simp [lengthOkLinearPair, decodePair_encodePair]
  exact (lengthOk_linear a b φ w).symm

/-! ## FinTM2 sketch: rebuild `lengthOkLinearPair` under `encodePair`

Parse `(φ, w)`, write budget `true^(a*|φ|+b)` while draining `φ`, then emit
`encodePair (w, budget)`. Composition with `unaryLEComputer` yields linear
`lengthOk`. -/

inductive LokStack where
  | inp | left | right | budget | out
  deriving DecidableEq, Repr

instance : Fintype LokStack where
  elems := {.inp, .left, .right, .budget, .out}
  complete s := by cases s <;> simp

inductive LokLabel where
  | parse | expectBit | loadRight | scale | appendB | revRight | unrevRight
  | emitW | emitSep | emitBudget | rev1 | rev2 | rev3 | haltDrain
  deriving DecidableEq, Repr

instance : Fintype LokLabel where
  elems := {.parse, .expectBit, .loadRight, .scale, .appendB, .revRight, .unrevRight,
    .emitW, .emitSep, .emitBudget, .rev1, .rev2, .rev3, .haltDrain}
  complete s := by cases s <;> simp

def lokStk (inp left right budget out : List Bool) : LokStack → List Bool
  | .inp => inp
  | .left => left
  | .right => right
  | .budget => budget
  | .out => out

/-- Nested write of `a` budget trues then return to `scale`. -/
def lokWriteAStmt (a : ℕ) :
    TM2.Stmt (fun _ : LokStack => Bool) LokLabel (Option Bool) :=
  match a with
  | 0 => load (fun _ => none) <| goto fun _ => LokLabel.scale
  | n + 1 =>
      push LokStack.budget (fun _ => true) <| lokWriteAStmt n

theorem lokWriteAStmt_stepAux (a : ℕ) (v : Option Bool)
    (inp left right budget out : List Bool) :
    TM2.stepAux (lokWriteAStmt a) v (lokStk inp left right budget out) =
      ⟨some LokLabel.scale, none,
        lokStk inp left right (List.replicate a true ++ budget) out⟩ := by
  induction a generalizing budget with
  | zero =>
      simp [lokWriteAStmt, TM2.stepAux, List.replicate_zero, lokStk]
  | succ n ih =>
      simp only [lokWriteAStmt, TM2.stepAux]
      have hstk :
          Function.update (lokStk inp left right budget out) LokStack.budget
              (true :: lokStk inp left right budget out LokStack.budget) =
            lokStk inp left right (true :: budget) out := by
        funext s; cases s <;> simp [Function.update, lokStk]
      rw [hstk]
      simpa [List.replicate_succ, replicate_true_append_cons] using
        ih (true :: budget)

/-- Nested write of `b` budget trues then go to `revRight` (restore w onto left). -/
def lokWriteBStmt (b : ℕ) :
    TM2.Stmt (fun _ : LokStack => Bool) LokLabel (Option Bool) :=
  match b with
  | 0 => load (fun _ => none) <| goto fun _ => LokLabel.revRight
  | n + 1 =>
      push LokStack.budget (fun _ => true) <| lokWriteBStmt n

theorem lokWriteBStmt_stepAux (b : ℕ) (v : Option Bool)
    (inp left right budget out : List Bool) :
    TM2.stepAux (lokWriteBStmt b) v (lokStk inp left right budget out) =
      ⟨some LokLabel.revRight, none,
        lokStk inp left right (List.replicate b true ++ budget) out⟩ := by
  induction b generalizing budget with
  | zero =>
      simp [lokWriteBStmt, TM2.stepAux, List.replicate_zero, lokStk]
  | succ n ih =>
      simp only [lokWriteBStmt, TM2.stepAux]
      have hstk :
          Function.update (lokStk inp left right budget out) LokStack.budget
              (true :: lokStk inp left right budget out LokStack.budget) =
            lokStk inp left right (true :: budget) out := by
        funext s; cases s <;> simp [Function.update, lokStk]
      rw [hstk]
      simpa [List.replicate_succ, replicate_true_append_cons] using
        ih (true :: budget)

def lengthOkLinearPairComputer (a b : ℕ) : FinTM2 where
  K := LokStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := LokLabel
  main := .parse
  σ := Option Bool
  initialState := none
  m
    | .parse =>
        pop LokStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => LokLabel.haltDrain)
            (branch (fun s => decide (s = some false))
              (load (fun _ => none) <| goto fun _ => LokLabel.loadRight)
              (load (fun _ => none) <| goto fun _ => LokLabel.expectBit))
    | .expectBit =>
        pop LokStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => LokLabel.haltDrain)
            (push LokStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => LokLabel.parse)
    | .loadRight =>
        pop LokStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => LokLabel.scale)
            (push LokStack.right (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => LokLabel.loadRight)
    | .scale =>
        pop LokStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (lokWriteBStmt b)
            (lokWriteAStmt a)
    | .appendB =>
        -- unused label kept for Fintype completeness; scale jumps via Stmt
        lokWriteBStmt b
    | .revRight =>
        -- right holds reverse(w); move onto left so left = w
        pop LokStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => LokLabel.emitW)
            (push LokStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => LokLabel.revRight)
    | .unrevRight =>
        -- unused (kept for Fintype); emit reads restored w from left
        load (fun _ => none) <| goto fun _ => LokLabel.emitW
    | .emitW =>
        pop LokStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => LokLabel.emitSep)
            (push LokStack.out (fun _ => true) <|
              push LokStack.out (fun s => s.getD false) <|
                load (fun _ => none) <| goto fun _ => LokLabel.emitW)
    | .emitSep =>
        push LokStack.out (fun _ => false) <|
          load (fun _ => none) <| goto fun _ => LokLabel.emitBudget
    | .emitBudget =>
        pop LokStack.budget (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => LokLabel.rev1)
            (push LokStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => LokLabel.emitBudget)
    | .rev1 =>
        -- out = reverse(EP) → budget = EP
        pop LokStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => LokLabel.rev2)
            (push LokStack.budget (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => LokLabel.rev1)
    | .rev2 =>
        -- budget = EP → left = reverse(EP)
        pop LokStack.budget (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => LokLabel.rev3)
            (push LokStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => LokLabel.rev2)
    | .rev3 =>
        -- left = reverse(EP) → out = EP
        pop LokStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => LokLabel.haltDrain)
            (push LokStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => LokLabel.rev3)
    | .haltDrain =>
        pop LokStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) halt)
            (load (fun _ => none) <| goto fun _ => LokLabel.haltDrain)

def lokCfg (a b : ℕ) (l : Option LokLabel) (v : Option Bool)
    (inp left right budget out : List Bool) :
    (lengthOkLinearPairComputer a b).Cfg :=
  ⟨l, v, lokStk inp left right budget out⟩

theorem lok_step_scale_nil (a b : ℕ) (inp right budget out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .scale) none inp [] right budget out) =
      some (lokCfg a b (some .revRight) none inp [] right
        (List.replicate b true ++ budget) out) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  have hstk :
      Function.update (lokStk inp [] right budget out) LokStack.left [] =
        lokStk inp [] right budget out := by
    funext s; cases s <;> simp [Function.update, lokStk]
  have h := lokWriteBStmt_stepAux b none inp [] right budget out
  exact congrArg some
    (Eq.trans (congrArg (TM2.stepAux (lokWriteBStmt b) none) hstk) h)

theorem lok_step_scale_cons (a b : ℕ) (c : Bool) (rest inp right budget out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .scale) none inp (c :: rest) right budget out) =
      some (lokCfg a b (some .scale) none inp rest right
        (List.replicate a true ++ budget) out) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  have hstk :
      Function.update (lokStk inp (c :: rest) right budget out) LokStack.left rest =
        lokStk inp rest right budget out := by
    funext s; cases s <;> simp [Function.update, lokStk]
  have h := lokWriteAStmt_stepAux a (some c) inp rest right budget out
  exact congrArg some
    (Eq.trans (congrArg (TM2.stepAux (lokWriteAStmt a) (some c)) hstk) h)

def lok_evals_one {a b : ℕ} {c c' : (lengthOkLinearPairComputer a b).Cfg}
    (h : TM2.step (lengthOkLinearPairComputer a b).m c = some c') :
    EvalsToInTime (lengthOkLinearPairComputer a b).step c (some c') 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := by
    change (some c).bind (lengthOkLinearPairComputer a b).step = some c'
    simpa [FinTM2.step] using h

/-- Drain `left` writing `a` budget trues per bit, then append `b`. -/
def lok_evals_scale (a b : ℕ) (left inp right budget out : List Bool) :
    EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .scale) none inp left right budget out)
      (some (lokCfg a b (some .revRight) none inp [] right
        (List.replicate b true ++
          List.foldr (fun _ acc => List.replicate a true ++ acc) budget left)
        out))
      (left.length + 1) := by
  induction left generalizing budget with
  | nil =>
      simpa [List.foldr] using lok_evals_one (lok_step_scale_nil a b inp right budget out)
  | cons c left ih =>
      have h1 := lok_evals_one
        (lok_step_scale_cons a b c left inp right budget out)
      have h2 := ih (List.replicate a true ++ budget)
      have h2' : EvalsToInTime (lengthOkLinearPairComputer a b).step
          (lokCfg a b (some .scale) none inp left right
            (List.replicate a true ++ budget) out)
          (some (lokCfg a b (some .revRight) none inp [] right
            (List.replicate b true ++
              (List.replicate a true ++
                List.foldr (fun _ acc => List.replicate a true ++ acc) budget left))
            out))
          (left.length + 1) := by
        simpa [foldr_replicate_comm a left budget, List.append_assoc] using h2
      have h := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step 1
        (left.length + 1) _ _ _ h1 h2'
      have htime : (left.length + 1) + 1 = (c :: left).length + 1 := by
        simp [List.length_cons]
      simpa [List.foldr, List.append_assoc, htime] using
        evalsToInTime_le_mono h (le_of_eq htime)

theorem lok_step_revRight_nil (a b : ℕ) (inp left budget out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .revRight) none inp left [] budget out) =
      some (lokCfg a b (some .emitW) none inp left [] budget out) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.emitW, none, stk⟩ :
        (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

theorem lok_step_revRight_cons (a b : ℕ) (c : Bool) (rest inp left budget out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .revRight) none inp left (c :: rest) budget out) =
      some (lokCfg a b (some .revRight) none inp (c :: left) rest budget out) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.revRight, none, stk⟩ :
        (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

def lok_evals_revRight (a b : ℕ) (right inp left budget out : List Bool) :
    EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .revRight) none inp left right budget out)
      (some (lokCfg a b (some .emitW) none inp
        (List.reverse right ++ left) [] budget out))
      (right.length + 1) := by
  induction right generalizing left with
  | nil =>
      simpa using lok_evals_one (lok_step_revRight_nil a b inp left budget out)
  | cons c right ih =>
      have h1 := lok_evals_one
        (lok_step_revRight_cons a b c right inp left budget out)
      have h2 := ih (c :: left)
      have h := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step 1
        (right.length + 1) _ _ _ h1 h2
      have htime : (right.length + 1) + 1 = (c :: right).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

/-- Restore `w` onto left after scale left `reverse w` on right. -/
def lok_evals_restore_w (a b : ℕ) (w inp budget out : List Bool) :
    EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .revRight) none inp [] (List.reverse w) budget out)
      (some (lokCfg a b (some .emitW) none inp w [] budget out))
      (w.length + 1) := by
  have h := lok_evals_revRight a b (List.reverse w) inp [] budget out
  simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using h

theorem lok_step_emitW_nil (a b : ℕ) (inp right budget out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .emitW) none inp [] right budget out) =
      some (lokCfg a b (some .emitSep) none inp [] right budget out) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.emitSep, none, stk⟩ : (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

theorem lok_step_emitW_cons (a b : ℕ) (c : Bool) (rest inp right budget out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .emitW) none inp (c :: rest) right budget out) =
      some (lokCfg a b (some .emitW) none inp rest right budget
        (c :: true :: out)) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.emitW, none, stk⟩ : (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

theorem lok_step_emitSep (a b : ℕ) (inp left right budget out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .emitSep) none inp left right budget out) =
      some (lokCfg a b (some .emitBudget) none inp left right budget
        (false :: out)) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.emitBudget, none, stk⟩ : (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

/-- Drain `left` (= w) writing reverse of encodePair left-half onto out. -/
def lok_evals_emitW (a b : ℕ) (left inp right budget out : List Bool) :
    EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .emitW) none inp left right budget out)
      (some (lokCfg a b (some .emitSep) none inp [] right budget
        (List.reverse (left.flatMap fun c => [true, c]) ++ out)))
      (left.length + 1) := by
  induction left generalizing out with
  | nil =>
      simpa [List.flatMap] using lok_evals_one (lok_step_emitW_nil a b inp right budget out)
  | cons c left ih =>
      have h1 := lok_evals_one (lok_step_emitW_cons a b c left inp right budget out)
      have h2 := ih (c :: true :: out)
      have h := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step 1
        (left.length + 1) _ _ _ h1 h2
      have htime : (left.length + 1) + 1 = (c :: left).length + 1 := by
        simp [List.length_cons]
      have hout :
          List.reverse ((c :: left).flatMap fun c => [true, c]) ++ out =
            List.reverse (left.flatMap fun c => [true, c]) ++ c :: true :: out := by
        simp [List.flatMap_cons, List.reverse_cons]
      simpa [htime, hout, List.append_assoc] using h

theorem lok_step_emitBudget_nil (a b : ℕ) (inp left right out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .emitBudget) none inp left right [] out) =
      some (lokCfg a b (some .rev1) none inp left right [] out) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.rev1, none, stk⟩ : (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

theorem lok_step_emitBudget_cons (a b : ℕ) (c : Bool) (rest inp left right out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .emitBudget) none inp left right (c :: rest) out) =
      some (lokCfg a b (some .emitBudget) none inp left right rest (c :: out)) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.emitBudget, none, stk⟩ : (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

def lok_evals_emitBudget (a b : ℕ) (budget inp left right out : List Bool) :
    EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .emitBudget) none inp left right budget out)
      (some (lokCfg a b (some .rev1) none inp left right []
        (List.reverse budget ++ out)))
      (budget.length + 1) := by
  induction budget generalizing out with
  | nil =>
      simpa using lok_evals_one (lok_step_emitBudget_nil a b inp left right out)
  | cons c budget ih =>
      have h1 := lok_evals_one
        (lok_step_emitBudget_cons a b c budget inp left right out)
      have h2 := ih (c :: out)
      have h := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step 1
        (budget.length + 1) _ _ _ h1 h2
      have htime : (budget.length + 1) + 1 = (c :: budget).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem lok_step_rev1_nil (a b : ℕ) (inp left right budget : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .rev1) none inp left right budget []) =
      some (lokCfg a b (some .rev2) none inp left right budget []) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.rev2, none, stk⟩ : (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

theorem lok_step_rev1_cons (a b : ℕ) (c : Bool) (rest inp left right budget : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .rev1) none inp left right budget (c :: rest)) =
      some (lokCfg a b (some .rev1) none inp left right (c :: budget) rest) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.rev1, none, stk⟩ : (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

theorem lok_step_rev2_nil (a b : ℕ) (inp left right out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .rev2) none inp left right [] out) =
      some (lokCfg a b (some .rev3) none inp left right [] out) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.rev3, none, stk⟩ : (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

theorem lok_step_rev2_cons (a b : ℕ) (c : Bool) (rest inp left right out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .rev2) none inp left right (c :: rest) out) =
      some (lokCfg a b (some .rev2) none inp (c :: left) right rest out) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.rev2, none, stk⟩ : (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

theorem lok_step_rev3_nil (a b : ℕ) (inp right budget out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .rev3) none inp [] right budget out) =
      some (lokCfg a b (some .haltDrain) none inp [] right budget out) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.haltDrain, none, stk⟩ : (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

theorem lok_step_rev3_cons (a b : ℕ) (c : Bool) (rest inp right budget out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .rev3) none inp (c :: rest) right budget out) =
      some (lokCfg a b (some .rev3) none inp rest right budget (c :: out)) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.rev3, none, stk⟩ : (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

def lok_evals_rev1 (a b : ℕ) (out inp left right budget : List Bool) :
    EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .rev1) none inp left right budget out)
      (some (lokCfg a b (some .rev2) none inp left right
        (List.reverse out ++ budget) []))
      (out.length + 1) := by
  induction out generalizing budget with
  | nil =>
      simpa using lok_evals_one (lok_step_rev1_nil a b inp left right budget)
  | cons c out ih =>
      have h1 := lok_evals_one
        (lok_step_rev1_cons a b c out inp left right budget)
      have h2 := ih (c :: budget)
      have h := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step 1
        (out.length + 1) _ _ _ h1 h2
      have htime : (out.length + 1) + 1 = (c :: out).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

def lok_evals_rev2 (a b : ℕ) (budget inp left right out : List Bool) :
    EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .rev2) none inp left right budget out)
      (some (lokCfg a b (some .rev3) none inp
        (List.reverse budget ++ left) right [] out))
      (budget.length + 1) := by
  induction budget generalizing left with
  | nil =>
      simpa using lok_evals_one (lok_step_rev2_nil a b inp left right out)
  | cons c budget ih =>
      have h1 := lok_evals_one
        (lok_step_rev2_cons a b c budget inp left right out)
      have h2 := ih (c :: left)
      have h := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step 1
        (budget.length + 1) _ _ _ h1 h2
      have htime : (budget.length + 1) + 1 = (c :: budget).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

def lok_evals_rev3 (a b : ℕ) (left inp right budget out : List Bool) :
    EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .rev3) none inp left right budget out)
      (some (lokCfg a b (some .haltDrain) none inp [] right budget
        (List.reverse left ++ out)))
      (left.length + 1) := by
  induction left generalizing out with
  | nil =>
      simpa using lok_evals_one (lok_step_rev3_nil a b inp right budget out)
  | cons c left ih =>
      have h1 := lok_evals_one
        (lok_step_rev3_cons a b c left inp right budget out)
      have h2 := ih (c :: out)
      have h := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step 1
        (left.length + 1) _ _ _ h1 h2
      have htime : (left.length + 1) + 1 = (c :: left).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

/-- Triple reverse restores `encodePair` onto out from `reverse encodePair`. -/
def lok_evals_unreverse (a b : ℕ) (ep : List Bool) :
    EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .rev1) none [] [] [] [] (List.reverse ep))
      (some (lokCfg a b (some .haltDrain) none [] [] [] [] ep))
      ((ep.length + 1) + ((ep.length + 1) + (ep.length + 1))) := by
  have h1 := lok_evals_rev1 a b (List.reverse ep) [] [] [] []
  have h1' : EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .rev1) none [] [] [] [] (List.reverse ep))
      (some (lokCfg a b (some .rev2) none [] [] [] ep []))
      (ep.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using h1
  have h2 := lok_evals_rev2 a b ep [] [] [] []
  have h2' : EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .rev2) none [] [] [] ep [])
      (some (lokCfg a b (some .rev3) none [] (List.reverse ep) [] [] []))
      (ep.length + 1) := by
    simpa [List.append_nil] using h2
  have h3 := lok_evals_rev3 a b (List.reverse ep) [] [] [] []
  have h3' : EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .rev3) none [] (List.reverse ep) [] [] [])
      (some (lokCfg a b (some .haltDrain) none [] [] [] [] ep))
      (ep.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using h3
  have h12 := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step
    (ep.length + 1) (ep.length + 1) _ _ _ h1' h2'
  exact EvalsToInTime.trans (lengthOkLinearPairComputer a b).step
    ((ep.length + 1) + (ep.length + 1)) (ep.length + 1) _ _ _ h12 h3'

theorem lok_step_halt (a b : ℕ) (left right budget out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .haltDrain) none [] left right budget out) =
      some (lokCfg a b none none [] left right budget out) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option LokLabel), none, stk⟩ :
        (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

theorem lok_step_parse_false (a b : ℕ) (rest left right budget out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .parse) none (false :: rest) left right budget out) =
      some (lokCfg a b (some .loadRight) none rest left right budget out) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.loadRight, none, stk⟩ :
        (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

theorem lok_step_parse_true (a b : ℕ) (c : Bool) (rest left right budget out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .parse) none (true :: c :: rest) left right budget out) =
      some (lokCfg a b (some .expectBit) none (c :: rest) left right budget out) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.expectBit, none, stk⟩ :
        (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

theorem lok_step_expectBit (a b : ℕ) (c : Bool) (rest left right budget out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .expectBit) none (c :: rest) left right budget out) =
      some (lokCfg a b (some .parse) none rest (c :: left) right budget out) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.parse, none, stk⟩ :
        (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

theorem lok_step_loadRight_nil (a b : ℕ) (left right budget out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .loadRight) none [] left right budget out) =
      some (lokCfg a b (some .scale) none [] left right budget out) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.scale, none, stk⟩ :
        (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

theorem lok_step_loadRight_cons (a b : ℕ) (c : Bool) (rest left right budget out : List Bool) :
    TM2.step (lengthOkLinearPairComputer a b).m
      (lokCfg a b (some .loadRight) none (c :: rest) left right budget out) =
      some (lokCfg a b (some .loadRight) none rest left (c :: right) budget out) := by
  simp [lengthOkLinearPairComputer, lokCfg, lokStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some LokLabel.loadRight, none, stk⟩ :
        (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext s; cases s <;> simp [Function.update, lokStk]

def lok_evals_parse_one (a b : ℕ) (c : Bool) (rest left right budget out : List Bool) :
    EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .parse) none (true :: c :: rest) left right budget out)
      (some (lokCfg a b (some .parse) none rest (c :: left) right budget out))
      2 := by
  have h1 := lok_evals_one
    (lok_step_parse_true a b c rest left right budget out)
  have h2 := lok_evals_one
    (lok_step_expectBit a b c rest left right budget out)
  exact EvalsToInTime.trans (lengthOkLinearPairComputer a b).step 1 1 _ _ _ h1 h2

noncomputable def lok_evals_parse (a b : ℕ) (xs rest left right budget out : List Bool) :
    EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .parse) none
        ((xs.flatMap fun c => [true, c]) ++ rest) left right budget out)
      (some (lokCfg a b (some .parse) none rest (List.reverse xs ++ left) right
        budget out))
      (2 * xs.length) := by
  induction xs generalizing left with
  | nil =>
      simpa [List.flatMap] using
        (EvalsToInTime.refl (lengthOkLinearPairComputer a b).step
          (lokCfg a b (some .parse) none rest left right budget out))
  | cons c xs ih =>
      have h1 := lok_evals_parse_one a b c
        ((xs.flatMap fun c => [true, c]) ++ rest) left right budget out
      have h2 := ih (c :: left)
      have h2' : EvalsToInTime (lengthOkLinearPairComputer a b).step
          (lokCfg a b (some .parse) none
            ((xs.flatMap fun c => [true, c]) ++ rest) (c :: left) right budget out)
          (some (lokCfg a b (some .parse) none rest
            (List.reverse xs ++ c :: left) right budget out))
          (2 * xs.length) := by
        simpa [List.reverse_cons, List.append_assoc] using h2
      have h := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step 2
        (2 * xs.length) _ _ _ h1 h2'
      have htime : 2 * xs.length + 2 = 2 * (c :: xs).length := by
        simp [List.length_cons]; omega
      simpa [List.flatMap_cons, List.append_assoc, htime] using
        evalsToInTime_le_mono h (le_of_eq htime)

noncomputable def lok_evals_loadRight (a b : ℕ) (ys left right budget out : List Bool) :
    EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .loadRight) none ys left right budget out)
      (some (lokCfg a b (some .scale) none [] left (List.reverse ys ++ right)
        budget out))
      (ys.length + 1) := by
  induction ys generalizing right with
  | nil =>
      exact lok_evals_one (lok_step_loadRight_nil a b left right budget out)
  | cons c ys ih =>
      have h1 := lok_evals_one
        (lok_step_loadRight_cons a b c ys left right budget out)
      have h2 := ih (c :: right)
      have h := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step 1
        (ys.length + 1) _ _ _ h1 h2
      have htime : (ys.length + 1) + 1 = (c :: ys).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

/-- Parse `encodePair (φ, w)` through scale and restore: at `emitW` with
`left = w` and budget `true^(a*|φ|+b)`. -/
noncomputable def lok_evals_load_to_emitW (a b : ℕ) (φ w : List Bool) :
    EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .parse) none (encodePair (φ, w)) [] [] [] [])
      (some (lokCfg a b (some .emitW) none [] w []
        (List.replicate (b + a * φ.length) true) []))
      ((w.length + 1) +
        ((φ.length + 1) + ((w.length + 1) + (1 + 2 * φ.length)))) := by
  have hparse := lok_evals_parse a b φ (false :: w) [] [] [] []
  have h1 : EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .parse) none (encodePair (φ, w)) [] [] [] [])
      (some (lokCfg a b (some .parse) none (false :: w) (List.reverse φ) [] [] []))
      (2 * φ.length) := by
    simpa [encodePair, List.append_assoc] using hparse
  have hfalse := lok_evals_one
    (lok_step_parse_false a b w (List.reverse φ) [] [] [])
  have h12 := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step
    (2 * φ.length) 1 _ _ _ h1 hfalse
  have hload := lok_evals_loadRight a b w (List.reverse φ) [] [] []
  have h123 := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step
    (1 + 2 * φ.length) (w.length + 1) _ _ _ h12 hload
  have h123' : EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .parse) none (encodePair (φ, w)) [] [] [] [])
      (some (lokCfg a b (some .scale) none [] (List.reverse φ)
        (List.reverse w) [] []))
      ((w.length + 1) + (1 + 2 * φ.length)) := by
    simpa [List.append_nil] using h123
  have hscale := lok_evals_scale a b (List.reverse φ) [] (List.reverse w) [] []
  have hscale' : EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .scale) none [] (List.reverse φ) (List.reverse w) [] [])
      (some (lokCfg a b (some .revRight) none [] [] (List.reverse w)
        (List.replicate (b + a * φ.length) true) []))
      (φ.length + 1) := by
    have hout :
        List.replicate b true ++
            List.foldr (fun _ acc => List.replicate a true ++ acc) ([] : List Bool)
              (List.reverse φ) =
          List.replicate (b + a * φ.length) true := by
      rw [foldr_replicate_scale, List.append_nil, List.replicate_append_replicate,
        List.length_reverse]
    have h := hscale
    simpa [hout, List.length_reverse, Nat.mul_comm] using h
  have htoRev := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step
    ((w.length + 1) + (1 + 2 * φ.length)) (φ.length + 1)
    _ _ _ h123' hscale'
  have hrest := lok_evals_restore_w a b w []
    (List.replicate (b + a * φ.length) true) []
  exact EvalsToInTime.trans (lengthOkLinearPairComputer a b).step
    ((φ.length + 1) + ((w.length + 1) + (1 + 2 * φ.length)))
    (w.length + 1)
    _ _ _ htoRev hrest

theorem replicate_budget_mul_comm (a b n : ℕ) :
    List.replicate (b + n * a) true = List.replicate (b + a * n) true := by
  rw [Nat.mul_comm]

/-- From `emitW` (with `left = w`) through halt, emitting `encodePair (w, budget)`. -/
noncomputable def lok_evals_emit_to_halt (a b : ℕ) (w budget : List Bool) :
    EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .emitW) none [] w [] budget [])
      (some (lokCfg a b none none [] [] [] [] (encodePair (w, budget))))
      (1 + ((((encodePair (w, budget)).length + 1) +
        (((encodePair (w, budget)).length + 1) +
          ((encodePair (w, budget)).length + 1))) +
        ((budget.length + 1) + (1 + (w.length + 1))))) := by
  have hemitW := lok_evals_emitW a b w [] [] budget []
  have hemitW' : EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .emitW) none [] w [] budget [])
      (some (lokCfg a b (some .emitSep) none [] [] [] budget
        (List.reverse (w.flatMap fun c => [true, c]))))
      (w.length + 1) := by
    simpa [List.append_nil] using hemitW
  have hsep := lok_evals_one (lok_step_emitSep a b [] [] [] budget
    (List.reverse (w.flatMap fun c => [true, c])))
  have h12 := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step
    (w.length + 1) 1 _ _ _ hemitW' hsep
  have hbud := lok_evals_emitBudget a b budget [] [] []
    (false :: List.reverse (w.flatMap fun c => [true, c]))
  have h123 := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step
    (1 + (w.length + 1)) (budget.length + 1) _ _ _ h12 hbud
  have hout_emit :
      List.reverse budget ++
          false :: List.reverse (w.flatMap fun c => [true, c]) =
        List.reverse (encodePair (w, budget)) := by
    simp [encodePair, List.reverse_append, List.reverse_cons]
  have h123' : EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .emitW) none [] w [] budget [])
      (some (lokCfg a b (some .rev1) none [] [] [] []
        (List.reverse (encodePair (w, budget)))))
      ((budget.length + 1) + (1 + (w.length + 1))) := by
    simpa [hout_emit] using h123
  have hunrev := lok_evals_unreverse a b (encodePair (w, budget))
  have h4 := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step
    ((budget.length + 1) + (1 + (w.length + 1)))
    (((encodePair (w, budget)).length + 1) +
      (((encodePair (w, budget)).length + 1) +
        ((encodePair (w, budget)).length + 1)))
    _ _ _ h123' hunrev
  have hhalt := lok_evals_one (lok_step_halt a b [] [] [] (encodePair (w, budget)))
  exact EvalsToInTime.trans (lengthOkLinearPairComputer a b).step
    ((((encodePair (w, budget)).length + 1) +
      (((encodePair (w, budget)).length + 1) +
        ((encodePair (w, budget)).length + 1))) +
      ((budget.length + 1) + (1 + (w.length + 1))))
    1
    _ _ _ h4 hhalt

theorem lok_initList (a b : ℕ) (s : List Bool) :
    initList (lengthOkLinearPairComputer a b) s =
      lokCfg a b (some .parse) none s [] [] [] [] := by
  refine congrArg (fun stk =>
      (⟨some LokLabel.parse, none, stk⟩ :
        (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext t; cases t <;> simp [lengthOkLinearPairComputer, lokStk]

theorem lok_haltList (a b : ℕ) (out : List Bool) :
    haltList (lengthOkLinearPairComputer a b) out =
      lokCfg a b none none [] [] [] [] out := by
  refine congrArg (fun stk =>
      (⟨(none : Option LokLabel), (none : Option Bool), stk⟩ :
        (lengthOkLinearPairComputer a b).Cfg)) ?_
  funext t; cases t <;> simp [haltList, lengthOkLinearPairComputer, lokStk]

/-- Full run: `encodePair (φ, w)` maps to `lengthOkLinearPair a b φ w`. -/
noncomputable def lok_evals (a b : ℕ) (φ w : List Bool) :
    TM2OutputsInTime (lengthOkLinearPairComputer a b) (encodePair (φ, w))
      (some (lengthOkLinearPair a b φ w))
      ((1 + ((((encodePair (w, List.replicate (b + a * φ.length) true)).length + 1) +
        (((encodePair (w, List.replicate (b + a * φ.length) true)).length + 1) +
          ((encodePair (w, List.replicate (b + a * φ.length) true)).length + 1))) +
        ((b + a * φ.length + 1) + (1 + (w.length + 1))))) +
        ((w.length + 1) +
          ((φ.length + 1) + ((w.length + 1) + (1 + 2 * φ.length))))) := by
  have hload := lok_evals_load_to_emitW a b φ w
  have hemit := lok_evals_emit_to_halt a b w
    (List.replicate (b + a * φ.length) true)
  have hload' : EvalsToInTime (lengthOkLinearPairComputer a b).step
      (initList (lengthOkLinearPairComputer a b) (encodePair (φ, w)))
      (some (lokCfg a b (some .emitW) none [] w []
        (List.replicate (b + a * φ.length) true) []))
      ((w.length + 1) +
        ((φ.length + 1) + ((w.length + 1) + (1 + 2 * φ.length)))) := by
    simpa [lok_initList] using hload
  have hemit' : EvalsToInTime (lengthOkLinearPairComputer a b).step
      (lokCfg a b (some .emitW) none [] w []
        (List.replicate (b + a * φ.length) true) [])
      (some (haltList (lengthOkLinearPairComputer a b)
        (lengthOkLinearPair a b φ w)))
      (1 + ((((encodePair (w, List.replicate (b + a * φ.length) true)).length + 1) +
        (((encodePair (w, List.replicate (b + a * φ.length) true)).length + 1) +
          ((encodePair (w, List.replicate (b + a * φ.length) true)).length + 1))) +
        ((b + a * φ.length + 1) + (1 + (w.length + 1))))) := by
    have hep :
        encodePair (w, List.replicate (b + a * φ.length) true) =
          lengthOkLinearPair a b φ w := by
      simp [lengthOkLinearPair, Nat.add_comm (a * φ.length), Nat.mul_comm]
    simpa [lok_haltList, List.length_replicate, hep] using hemit
  have h := EvalsToInTime.trans (lengthOkLinearPairComputer a b).step
    ((w.length + 1) +
      ((φ.length + 1) + ((w.length + 1) + (1 + 2 * φ.length))))
    (1 + ((((encodePair (w, List.replicate (b + a * φ.length) true)).length + 1) +
      (((encodePair (w, List.replicate (b + a * φ.length) true)).length + 1) +
        ((encodePair (w, List.replicate (b + a * φ.length) true)).length + 1))) +
      ((b + a * φ.length + 1) + (1 + (w.length + 1)))))
    _ _ _ hload' hemit'
  exact ⟨⟨h.steps, h.evals_in_steps⟩, h.steps_le_m⟩

/-- Time bound depending on fixed scale coeffs `a,b` and input length. -/
noncomputable def lengthOkLinearPairTime (a b : ℕ) : Polynomial ℕ :=
  (48 * (Polynomial.C (a + b + 1) + 1)) * (Polynomial.X ^ 2 + Polynomial.X + 1)

theorem lengthOkLinearPairTime_eval (a b n : ℕ) :
    (lengthOkLinearPairTime a b).eval n =
      (48 * (a + b + 1 + 1)) * (n ^ 2 + n + 1) := by
  simp [lengthOkLinearPairTime, pow_two, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one]

theorem lengthOkLinearPairTime_bound (a b : ℕ) (φ w : List Bool) :
    ((1 + ((((encodePair (w, List.replicate (b + a * φ.length) true)).length + 1) +
      (((encodePair (w, List.replicate (b + a * φ.length) true)).length + 1) +
        ((encodePair (w, List.replicate (b + a * φ.length) true)).length + 1))) +
      ((b + a * φ.length + 1) + (1 + (w.length + 1))))) +
      ((w.length + 1) +
        ((φ.length + 1) + ((w.length + 1) + (1 + 2 * φ.length))))) ≤
      (lengthOkLinearPairTime a b).eval (encodePair (φ, w)).length := by
  simp [lengthOkLinearPairTime_eval, length_encodePair, List.length_replicate]
  set N := 2 * φ.length + 1 + w.length
  have hφ : φ.length ≤ N := by omega
  have hw : w.length ≤ N := by omega
  have ha : a * φ.length ≤ (a + b + 1) * N :=
    calc
      a * φ.length ≤ (a + b + 1) * φ.length :=
        Nat.mul_le_mul_right _ (by omega : a ≤ a + b + 1)
      _ ≤ (a + b + 1) * N := Nat.mul_le_mul_left _ hφ
  have hbud : b + a * φ.length ≤ (a + b + 1) * (N + 1) :=
    calc
      b + a * φ.length ≤ b + (a + b + 1) * N := Nat.add_le_add_left ha _
      _ ≤ (a + b + 1) + (a + b + 1) * N := Nat.add_le_add_right (by omega : b ≤ a + b + 1) _
      _ = (a + b + 1) * (N + 1) := by ring
  have hNsq : N + 1 ≤ N ^ 2 + N + 1 := by nlinarith
  have hM : (a + b + 1) * (N + 1) ≤ (a + b + 2) * (N ^ 2 + N + 1) :=
    calc
      (a + b + 1) * (N + 1) ≤ (a + b + 1) * (N ^ 2 + N + 1) := Nat.mul_le_mul_left _ hNsq
      _ ≤ (a + b + 2) * (N ^ 2 + N + 1) := Nat.mul_le_mul_right _ (by omega)
  have hw1 : w.length ≤ (a + b + 2) * (N ^ 2 + N + 1) :=
    calc
      w.length ≤ N := hw
      _ ≤ N + 1 := Nat.le_succ _
      _ ≤ (a + b + 1) * (N + 1) := by
        simpa [Nat.mul_one] using Nat.mul_le_mul_right (N + 1) (by omega : 1 ≤ a + b + 1)
      _ ≤ (a + b + 2) * (N ^ 2 + N + 1) := hM
  have hφ1 : φ.length ≤ (a + b + 2) * (N ^ 2 + N + 1) :=
    calc
      φ.length ≤ N := hφ
      _ ≤ N + 1 := Nat.le_succ _
      _ ≤ (a + b + 1) * (N + 1) := by
        simpa [Nat.mul_one] using Nat.mul_le_mul_right (N + 1) (by omega : 1 ≤ a + b + 1)
      _ ≤ (a + b + 2) * (N ^ 2 + N + 1) := hM
  have hbud1 : b + a * φ.length ≤ (a + b + 2) * (N ^ 2 + N + 1) :=
    le_trans hbud hM
  have h3 : 3 ≤ (a + b + 2) * (N ^ 2 + N + 1) := by
    have hN1 : 1 ≤ N := by omega
    have hsq : 3 ≤ N ^ 2 + N + 1 := by nlinarith
    have hab : 1 ≤ a + b + 2 := by omega
    calc
      3 ≤ N ^ 2 + N + 1 := hsq
      _ ≤ (a + b + 2) * (N ^ 2 + N + 1) := by
        simpa [Nat.mul_one] using Nat.mul_le_mul_right (N ^ 2 + N + 1) hab
  have hLHS :
      1 + (2 * w.length + 1 + (b + a * φ.length) + 1 +
          (2 * w.length + 1 + (b + a * φ.length) + 1 +
            (2 * w.length + 1 + (b + a * φ.length) + 1)) +
        (b + a * φ.length + 1 + (1 + (w.length + 1)))) +
        (w.length + 1 + (φ.length + 1 + (w.length + 1 + (1 + 2 * φ.length)))) ≤
      12 * (w.length + (b + a * φ.length) + φ.length + 3) := by omega
  refine le_trans hLHS ?_
  have hsum : w.length + (b + a * φ.length) + φ.length + 3 ≤
      4 * (a + b + 2) * (N ^ 2 + N + 1) := by
    have := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hw1 hbud1) hφ1) h3
    convert this using 1 <;> ring
  have : 12 * (w.length + (b + a * φ.length) + φ.length + 3) ≤
      48 * (a + b + 2) * (N ^ 2 + N + 1) := by
    have := Nat.mul_le_mul_left 12 hsum
    convert this using 1 <;> ring
  exact this

/-- Rebuild `encodePair (w, true^(a*|φ|+b))` under `encodePair` input. -/
noncomputable def lengthOkLinearPairComputableInPolyTime (a b : ℕ) :
    TM2ComputableInPolyTime encodePair idBitEnc
      (fun p => lengthOkLinearPair a b p.1 p.2) where
  tm := lengthOkLinearPairComputer a b
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := lengthOkLinearPairTime a b
  outputsFun p := by
    rcases p with ⟨φ, w⟩
    change TM2OutputsInTime (lengthOkLinearPairComputer a b)
      (List.map id (encodePair (φ, w)))
      (some (List.map id (idBitEnc (lengthOkLinearPair a b φ w))))
      ((lengthOkLinearPairTime a b).eval (encodePair (φ, w)).length)
    simp only [List.map_id, id_eq, idBitEnc]
    exact evalsToInTime_le_mono (lok_evals a b φ w)
      (lengthOkLinearPairTime_bound a b φ w)

/-- Output length of the linear lengthOk prep map. -/
theorem length_lengthOkLinearPair (a b : ℕ) (φ w : List Bool) :
    (lengthOkLinearPair a b φ w).length =
      2 * w.length + 1 + (a * φ.length + b) := by
  simp [lengthOkLinearPair, length_encodePair, List.length_replicate]

/-- Polynomial out-bound for `lengthOkLinearPair` under pair input length. -/
noncomputable def lengthOkLinearPairOutBound (a b : ℕ) : Polynomial ℕ :=
  (Polynomial.C (a + b + 3) + 1) * (Polynomial.X + 1)

theorem lengthOkLinearPairOutBound_eval (a b n : ℕ) :
    (lengthOkLinearPairOutBound a b).eval n = (a + b + 3 + 1) * (n + 1) := by
  simp [lengthOkLinearPairOutBound, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one]

theorem length_lengthOkLinearPair_le_outBound (a b : ℕ) (φ w : List Bool) :
    (lengthOkLinearPair a b φ w).length ≤
      (lengthOkLinearPairOutBound a b).eval (encodePair (φ, w)).length := by
  simp [length_lengthOkLinearPair, lengthOkLinearPairOutBound_eval, length_encodePair]
  set N := 2 * φ.length + 1 + w.length
  have hφ : φ.length ≤ N := by omega
  have hw : w.length ≤ N := by omega
  have : 2 * w.length + 1 + (a * φ.length + b) ≤ (a + b + 4) * (N + 1) := by
    have hw' : 2 * w.length ≤ 2 * (N + 1) := by omega
    have ha' : a * φ.length ≤ a * (N + 1) := Nat.mul_le_mul_left _ (by omega)
    have hb' : b ≤ b * (N + 1) := by
      have : 1 ≤ N + 1 := Nat.succ_pos _
      simpa [Nat.mul_one] using Nat.mul_le_mul_left b this
    calc
      2 * w.length + 1 + (a * φ.length + b)
          ≤ 2 * (N + 1) + (N + 1) + (a * (N + 1) + b * (N + 1)) := by omega
      _ = (2 + 1 + a + b) * (N + 1) := by ring
      _ = (a + b + 3) * (N + 1) := by ring
      _ ≤ (a + b + 4) * (N + 1) := Nat.mul_le_mul_right _ (by omega)
  exact this
/-- Linear `lengthOk` under `encodePair`: prep then unary compare. -/
noncomputable def lengthOkLinearComputableInPolyTime (a b : ℕ) :
    TM2ComputableInPolyTime encodePair bitEnc
      (fun pw => lengthOk (Polynomial.C a * Polynomial.X + Polynomial.C b)
        pw.1 pw.2) := by
  let decodeOut : (lengthOkLinearPairComputer a b).Γ
      (lengthOkLinearPairComputer a b).k₁ → Bool := id
  let encodeIn : Bool → unaryLEComputer.Γ unaryLEComputer.k₀ := id
  let tm :=
    seqCompComputer (βΓ := Bool) (lengthOkLinearPairComputer a b) unaryLEComputer
      decodeOut encodeIn
  let inA : tm.Γ tm.k₀ ≃ Bool := by
    simpa [tm, seqCompComputer, CompΓ, CompK] using (Equiv.refl Bool)
  let outA : tm.Γ tm.k₁ ≃ Bool := by
    simpa [tm, seqCompComputer, CompΓ, CompK] using (Equiv.refl Bool)
  let outP := lengthOkLinearPairOutBound a b
  let timeBound : Polynomial ℕ :=
    lengthOkLinearPairTime a b + (4 * (outP + 1)) + (unaryLETime.comp outP)
  refine
    { tm := tm
      inputAlphabet := inA
      outputAlphabet := outA
      time := timeBound
      outputsFun := ?out }
  case out =>
    intro pw
    rcases pw with ⟨φ, w⟩
    change TM2OutputsInTime tm (List.map inA.invFun (encodePair (φ, w)))
      (some (List.map outA.invFun
        (bitEnc (lengthOk (Polynomial.C a * Polynomial.X + Polynomial.C b) φ w))))
      (timeBound.eval (encodePair (φ, w)).length)
    set mid := lengthOkLinearPair a b φ w with hmid_def
    set bud := List.replicate (a * φ.length + b) true with hbud_def
    have hbit := lengthOk_linear a b φ w
    have hin :
        List.map inA.invFun (encodePair (φ, w)) = encodePair (φ, w) := by
      change List.map (Equiv.refl Bool).symm (encodePair (φ, w)) = encodePair (φ, w)
      simp
    have hout :
        List.map outA.invFun
            (bitEnc (lengthOk (Polynomial.C a * Polynomial.X + Polynomial.C b) φ w)) =
          [unaryLE w bud] := by
      simp only [bitEnc, List.map_cons, List.map_nil]
      exact congrArg (fun b => [b]) (hbit.trans (by rw [hbud_def]))
    have h1 : EvalsToInTime (lengthOkLinearPairComputer a b).step
        (initList (lengthOkLinearPairComputer a b) (encodePair (φ, w)))
        (some (haltList (lengthOkLinearPairComputer a b) mid))
        ((lengthOkLinearPairTime a b).eval (encodePair (φ, w)).length) := by
      simpa [hmid_def] using
        evalsToInTime_le_mono (lok_evals a b φ w)
          (lengthOkLinearPairTime_bound a b φ w)
    have h2 : EvalsToInTime unaryLEComputer.step
        (initList unaryLEComputer (mid.map (encodeIn ∘ decodeOut)))
        (some (haltList unaryLEComputer [unaryLE w bud]))
        (unaryLETime.eval mid.length) := by
      have hmap : mid.map (encodeIn ∘ decodeOut) = mid := by
        change List.map (id ∘ id) mid = mid
        simp [List.map_id]
      rw [hmap]
      have hmid_enc : mid = encodePair (w, bud) := by
        simp [hmid_def, hbud_def, lengthOkLinearPair]
      rw [hmid_enc]
      simpa [hbud_def, bitEnc] using
        evalsToInTime_le_mono (unaryLE_evals w bud) (unaryLETime_bound w bud)
    have heval :=
      seqComp_evals_compose (βΓ := Bool) (lengthOkLinearPairComputer a b)
        unaryLEComputer decodeOut encodeIn (encodePair (φ, w)) mid
        [unaryLE w bud]
        ((lengthOkLinearPairTime a b).eval (encodePair (φ, w)).length)
        (unaryLETime.eval mid.length) h1 h2
    set n := (encodePair (φ, w)).length with hn_def
    have hflen : mid.length ≤ outP.eval n := by
      simpa [hmid_def, hn_def] using length_lengthOkLinearPair_le_outBound a b φ w
    have hcopy :
        (2 * mid.length + 1) + (2 * mid.length + 1) ≤ 4 * (outP.eval n + 1) := by
      have : 4 * (mid.length + 1) ≤ 4 * (outP.eval n + 1) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right hflen 1)
      omega
    have hule :
        unaryLETime.eval mid.length ≤ (unaryLETime.comp outP).eval n := by
      have h1' : unaryLETime.eval mid.length ≤ unaryLETime.eval (outP.eval n) :=
        poly_eval_mono unaryLETime hflen
      simpa [Polynomial.eval_comp] using h1'
    have hbound :
        (lengthOkLinearPairTime a b).eval n +
          (2 * mid.length + 1) + (2 * mid.length + 1) +
          unaryLETime.eval mid.length ≤
        timeBound.eval n := by
      have hc := hcopy
      have hu := hule
      -- Left-assoc Nat add: rearrange then apply the out-bound pieces.
      have hstep :
          (lengthOkLinearPairTime a b).eval n +
              ((2 * mid.length + 1) + (2 * mid.length + 1)) +
              unaryLETime.eval mid.length ≤
            (lengthOkLinearPairTime a b).eval n + 4 * (outP.eval n + 1) +
              (unaryLETime.comp outP).eval n := by
        refine Nat.add_le_add ?_ hu
        exact Nat.add_le_add_left hc _
      convert hstep using 1
      · ac_rfl
      · simp [timeBound, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_one, Polynomial.eval_ofNat]
    have hfinal := evalsToInTime_le_mono (by simpa [hn_def] using heval) hbound
    have hraw : EvalsToInTime tm.step
        (initList tm (encodePair (φ, w)))
        (some (haltList tm [unaryLE w bud]))
        (timeBound.eval n) := by
      simpa [tm, hn_def] using hfinal
    refine evalsToInTime_congr_end
      (by
        have hstart :
            initList tm (List.map inA.invFun (encodePair (φ, w))) =
              initList tm (encodePair (φ, w)) :=
          congrArg (initList tm) hin
        exact { steps := hraw.steps
                steps_le_m := by simpa [hn_def] using hraw.steps_le_m
                evals_in_steps := by
                  rw [hstart]
                  exact hraw.evals_in_steps })
      (congrArg some (congrArg (haltList tm) hout.symm))

/-- Degree ≤ 1 `lengthOk` reduces to the linear case. -/
noncomputable def lengthOkDegLeOneComputableInPolyTime (p : Polynomial ℕ)
    (hp : p.natDegree ≤ 1) :
    TM2ComputableInPolyTime encodePair bitEnc
      (fun pw => lengthOk p pw.1 pw.2) := by
  let a := p.coeff 1
  let b := p.coeff 0
  have hform : p = Polynomial.C a * Polynomial.X + Polynomial.C b :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hp
  convert lengthOkLinearComputableInPolyTime a b using 1
  funext pw
  rcases pw with ⟨φ, w⟩
  rw [hform]

/-! ## Easy direction packaging: NP witness to `IsPropProofSystem` -/

/-- `NP = coNP` lifts the certified `TAUT ∈ coNP` witness into `TAUT ∈ NP`. -/
theorem TAUT_in_NP_of_NP_eq_coNP (h : ClassNP_eq_ClassCoNP) : InNP TAUT :=
  (h TAUT).mpr TAUT_in_coNP

/-- Package an NP verifier for `TAUT` as a propositional proof system, given the
FinTM2 witness for `proofSystemOfNPVerifier`. -/
noncomputable def isPropProofSystemOfNPVerifier (p : Polynomial ℕ)
    (V : List Bool → List Bool → Bool)
    (hV : ∀ φ, TAUT φ ↔
      ∃ w, w.length ≤ p.eval φ.length ∧ V φ w = true)
    (hpoly : TM2ComputableInPolyTime idBitEnc idBitEnc
      (proofSystemOfNPVerifier p V)) :
    IsPropProofSystem (proofSystemOfNPVerifier p V) where
  poly := hpoly
  sound := proofSystemOfNPVerifier_sound p V hV
  complete := proofSystemOfNPVerifier_complete p V hV

/-- Easy half of bridge theorem 1, conditional on FinTM2 packaging of the proof map. -/
theorem bridge_theorem_1_easy_of_packaging
    (h : ClassNP_eq_ClassCoNP)
    (hpack : ∀ (p : Polynomial ℕ) (V : List Bool → List Bool → Bool),
      (∀ φ, TAUT φ ↔ ∃ w, w.length ≤ p.eval φ.length ∧ V φ w = true) →
      TM2ComputableInPolyTime encodePair bitEnc (fun pw => V pw.1 pw.2) →
      TM2ComputableInPolyTime idBitEnc idBitEnc (proofSystemOfNPVerifier p V)) :
    ∃ f, Nonempty (IsPropProofSystem f) ∧ PolynomiallyBounded f := by
  rcases TAUT_in_NP_of_NP_eq_coNP h with ⟨p, V, hVpoly, hV⟩
  refine ⟨proofSystemOfNPVerifier p V, ?_, proofSystemOfNPVerifier_polyBounded p V hV⟩
  exact ⟨isPropProofSystemOfNPVerifier p V hV (hpack p V hV hVpoly)⟩

/-! ## Two-bit AND (glue for `acceptWitness = lengthOk && V`) -/

/-- Pop two bits, push their conjunction, halt. -/
def andBitComputer : FinTM2 where
  K := Unit
  k₀ := ⟨⟩
  k₁ := ⟨⟩
  Γ _ := Bool
  Λ := Fin 3
  main := (0 : Fin 3)
  σ := Bool × Bool
  initialState := (false, false)
  m
    | ⟨0, _⟩ =>
        pop ⟨⟩ (fun _ o => (Option.getD o false, false)) <|
          goto fun _ => (1 : Fin 3)
    | ⟨1, _⟩ =>
        pop ⟨⟩ (fun s o => (s.1, Option.getD o false)) <|
          goto fun _ => (2 : Fin 3)
    | ⟨2, _⟩ =>
        push ⟨⟩ (fun s => s.1 && s.2) <|
          load (fun _ => (false, false)) halt

def andBitCfg (l : Option (Fin 3)) (v : Bool × Bool) (s : List Bool) :
    andBitComputer.Cfg :=
  ⟨l, v, fun _ => s⟩

theorem update_andBit_stk (s t : List Bool) :
    Function.update (fun _ : Unit => s) PUnit.unit t = fun _ => t := by
  funext k; cases k; simp [Function.update]

theorem andBit_step_read1 (b1 b2 : Bool) (rest : List Bool) :
    TM2.step andBitComputer.m
      (andBitCfg (some (0 : Fin 3)) (false, false) (b1 :: b2 :: rest)) =
      some (andBitCfg (some (1 : Fin 3)) (b1, false) (b2 :: rest)) := by
  simp [andBitComputer, andBitCfg, TM2.step, TM2.stepAux]
  exact congrArg some <|
    congrArg (fun stk =>
      (⟨some (1 : Fin 3), (b1, false), stk⟩ : andBitComputer.Cfg))
      (update_andBit_stk (b1 :: b2 :: rest) (b2 :: rest))

theorem andBit_step_read2 (b1 b2 : Bool) (rest : List Bool) :
    TM2.step andBitComputer.m
      (andBitCfg (some (1 : Fin 3)) (b1, false) (b2 :: rest)) =
      some (andBitCfg (some (2 : Fin 3)) (b1, b2) rest) := by
  simp [andBitComputer, andBitCfg, TM2.step, TM2.stepAux]
  exact congrArg some <|
    congrArg (fun stk =>
      (⟨some (2 : Fin 3), (b1, b2), stk⟩ : andBitComputer.Cfg))
      (update_andBit_stk (b2 :: rest) rest)

theorem andBit_step_write (b1 b2 : Bool) (rest : List Bool) :
    TM2.step andBitComputer.m
      (andBitCfg (some (2 : Fin 3)) (b1, b2) rest) =
      some (andBitCfg none (false, false) ((b1 && b2) :: rest)) := by
  simp [andBitComputer, andBitCfg, TM2.step, TM2.stepAux]
  exact congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option (Fin 3)), (false, false), stk⟩ : andBitComputer.Cfg))
      (update_andBit_stk rest ((b1 && b2) :: rest))

theorem andBit_initList (s : List Bool) :
    initList andBitComputer s = andBitCfg (some (0 : Fin 3)) (false, false) s := by
  simp [initList, andBitComputer, andBitCfg]

theorem andBit_haltList (b : Bool) (rest : List Bool) :
    haltList andBitComputer (b :: rest) =
      andBitCfg none (false, false) (b :: rest) := by
  simp [haltList, andBitComputer, andBitCfg]

/-- Two-bit AND in three steps on the shared tape. -/
def andBit_evals (b1 b2 : Bool) :
    EvalsToInTime andBitComputer.step
      (initList andBitComputer [b1, b2])
      (some (haltList andBitComputer [b1 && b2])) 3 where
  steps := 3
  steps_le_m := le_rfl
  evals_in_steps := by
    change
      (((some (initList andBitComputer [b1, b2])).bind andBitComputer.step).bind
        andBitComputer.step).bind andBitComputer.step =
      some (haltList andBitComputer [b1 && b2])
    simp only [FinTM2.step, andBit_initList, andBit_haltList]
    change
      ((TM2.step andBitComputer.m
          (andBitCfg (some (0 : Fin 3)) (false, false) [b1, b2])).bind
        (TM2.step andBitComputer.m)).bind (TM2.step andBitComputer.m) =
      some (andBitCfg none (false, false) [b1 && b2])
    rw [andBit_step_read1 b1 b2 []]
    change
      ((TM2.step andBitComputer.m
          (andBitCfg (some (1 : Fin 3)) (b1, false) [b2])).bind
        (TM2.step andBitComputer.m)) =
      some (andBitCfg none (false, false) [b1 && b2])
    rw [andBit_step_read2 b1 b2 []]
    exact andBit_step_write b1 b2 []

noncomputable def andBitTime : Polynomial ℕ := 3

theorem andBitTime_eval (n : ℕ) : andBitTime.eval n = 3 := by
  simp [andBitTime]

/-- AND of two bits under `bitEnc` of a pair (via `encodePair` of singletons). -/
noncomputable def andBitComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun p : Bool × Bool => [p.1, p.2]) bitEnc (fun p => p.1 && p.2) where
  tm := andBitComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := andBitTime
  outputsFun p := by
    rcases p with ⟨b1, b2⟩
    change TM2OutputsInTime andBitComputer (List.map id [b1, b2])
      (some (List.map id (bitEnc (b1 && b2))))
      (andBitTime.eval [b1, b2].length)
    simp only [List.map_id, id_eq, bitEnc, andBitTime_eval]
    exact evalsToInTime_le_mono (andBit_evals b1 b2) (by omega)

/-! ## Pair swap under `encodePair` (proofCheck rearrange: `(φ,π) ↦ (π,φ)`) -/

/-- Swap components of a decoded pair, re-encoded. -/
def swapPair (p : List Bool × List Bool) : List Bool :=
  encodePair (p.2, p.1)

theorem swapPair_encode (φ π : List Bool) :
    swapPair (φ, π) = encodePair (π, φ) := rfl

theorem length_swapPair (p : List Bool × List Bool) :
    (swapPair p).length = 2 * p.2.length + 1 + p.1.length := by
  simp [swapPair, length_encodePair]

/-- Swap output is linearly bounded by the input pair encoding length. -/
theorem length_swapPair_le_encodePair (φ π : List Bool) :
    (swapPair (φ, π)).length ≤ 2 * (encodePair (φ, π)).length := by
  simp [swapPair, length_encodePair]
  omega

theorem proofCheck_eq_bitsEqualPair_swap (f : List Bool → List Bool) (φ π : List Bool) :
    proofCheck f φ π = bitsEqualPair (f π, φ) :=
  proofCheck_eq_bitsEqualPair f φ π

/-! ## FinTM2: `swapPair` under `encodePair`

Parse `(φ, π)` to `left = reverse φ`, `right = reverse π`. Park `φ` on `out`,
restore `π` onto `left`, repark `φ` on `right`, then emit `encodePair (π, φ)`. -/

inductive SwapStack where
  | inp | left | right | out
  deriving DecidableEq, Repr

instance : Fintype SwapStack where
  elems := {.inp, .left, .right, .out}
  complete s := by cases s <;> simp

inductive SwapLabel where
  | parse | expectBit | loadRight
  | parkL | revRight | parkOut
  | emitW | emitSep | emitFstPrep | emitFst
  | rev1 | rev2 | rev3 | haltDrain
  deriving DecidableEq, Repr

instance : Fintype SwapLabel where
  elems := {.parse, .expectBit, .loadRight, .parkL, .revRight, .parkOut,
    .emitW, .emitSep, .emitFstPrep, .emitFst, .rev1, .rev2, .rev3, .haltDrain}
  complete s := by cases s <;> simp

def swapStk (inp left right out : List Bool) : SwapStack → List Bool
  | .inp => inp
  | .left => left
  | .right => right
  | .out => out

def swapPairComputer : FinTM2 where
  K := SwapStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := SwapLabel
  main := .parse
  σ := Option Bool
  initialState := none
  m
    | .parse =>
        pop SwapStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => SwapLabel.haltDrain)
            (branch (fun s => decide (s = some false))
              (load (fun _ => none) <| goto fun _ => SwapLabel.loadRight)
              (load (fun _ => none) <| goto fun _ => SwapLabel.expectBit))
    | .expectBit =>
        pop SwapStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => SwapLabel.haltDrain)
            (push SwapStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => SwapLabel.parse)
    | .loadRight =>
        pop SwapStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => SwapLabel.parkL)
            (push SwapStack.right (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => SwapLabel.loadRight)
    | .parkL =>
        pop SwapStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => SwapLabel.revRight)
            (push SwapStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => SwapLabel.parkL)
    | .revRight =>
        pop SwapStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => SwapLabel.parkOut)
            (push SwapStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => SwapLabel.revRight)
    | .parkOut =>
        pop SwapStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => SwapLabel.emitW)
            (push SwapStack.right (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => SwapLabel.parkOut)
    | .emitW =>
        pop SwapStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => SwapLabel.emitSep)
            (push SwapStack.out (fun _ => true) <|
              push SwapStack.out (fun s => s.getD false) <|
                load (fun _ => none) <| goto fun _ => SwapLabel.emitW)
    | .emitSep =>
        push SwapStack.out (fun _ => false) <|
          load (fun _ => none) <| goto fun _ => SwapLabel.emitFstPrep
    | .emitFstPrep =>
        pop SwapStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => SwapLabel.emitFst)
            (push SwapStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => SwapLabel.emitFstPrep)
    | .emitFst =>
        pop SwapStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => SwapLabel.rev1)
            (push SwapStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => SwapLabel.emitFst)
    | .rev1 =>
        pop SwapStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => SwapLabel.rev2)
            (push SwapStack.right (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => SwapLabel.rev1)
    | .rev2 =>
        pop SwapStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => SwapLabel.rev3)
            (push SwapStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => SwapLabel.rev2)
    | .rev3 =>
        pop SwapStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => SwapLabel.haltDrain)
            (push SwapStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => SwapLabel.rev3)
    | .haltDrain =>
        pop SwapStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            halt
            (load (fun _ => none) <| goto fun _ => SwapLabel.haltDrain)

def swapCfg (l : Option SwapLabel) (v : Option Bool)
    (inp left right out : List Bool) : swapPairComputer.Cfg :=
  ⟨l, v, swapStk inp left right out⟩

theorem swap_step_parse_true (b : Bool) (rest left right out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .parse) none (true :: b :: rest) left right out) =
      some (swapCfg (some .expectBit) none (b :: rest) left right out) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.expectBit, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

theorem swap_step_parse_false (rest left right out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .parse) none (false :: rest) left right out) =
      some (swapCfg (some .loadRight) none rest left right out) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.loadRight, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

theorem swap_step_expectBit (b : Bool) (rest left right out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .expectBit) none (b :: rest) left right out) =
      some (swapCfg (some .parse) none rest (b :: left) right out) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.parse, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

theorem swap_step_loadRight_cons (c : Bool) (rest left right out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .loadRight) none (c :: rest) left right out) =
      some (swapCfg (some .loadRight) none rest left (c :: right) out) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.loadRight, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

theorem swap_step_loadRight_nil (left right out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .loadRight) none [] left right out) =
      some (swapCfg (some .parkL) none [] left right out) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.parkL, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

def swap_evals_one {c c' : swapPairComputer.Cfg}
    (h : TM2.step swapPairComputer.m c = some c') :
    EvalsToInTime swapPairComputer.step c (some c') 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := by
    change (some c).bind swapPairComputer.step = some c'
    simpa [FinTM2.step] using h

def swap_evals_parse_one (c : Bool) (rest left right out : List Bool) :
    EvalsToInTime swapPairComputer.step
      (swapCfg (some .parse) none (true :: c :: rest) left right out)
      (some (swapCfg (some .parse) none rest (c :: left) right out)) 2 := by
  exact EvalsToInTime.trans swapPairComputer.step 1 1 _ _ _
    (swap_evals_one (swap_step_parse_true c rest left right out))
    (swap_evals_one (swap_step_expectBit c rest left right out))

noncomputable def swap_evals_parse (xs rest left right out : List Bool) :
    EvalsToInTime swapPairComputer.step
      (swapCfg (some .parse) none
        (xs.flatMap (fun b => [true, b]) ++ rest) left right out)
      (some (swapCfg (some .parse) none rest (List.reverse xs ++ left) right out))
      (2 * xs.length) := by
  induction xs generalizing left with
  | nil =>
      simpa [List.flatMap] using
        (EvalsToInTime.refl swapPairComputer.step
          (swapCfg (some .parse) none rest left right out))
  | cons c xs ih =>
      have h1 := swap_evals_parse_one c (xs.flatMap (fun b => [true, b]) ++ rest)
        left right out
      have h2 := ih (c :: left)
      have h := EvalsToInTime.trans swapPairComputer.step 2 (2 * xs.length) _ _ _ h1 h2
      have htime : 2 * xs.length + 2 = 2 * (c :: xs).length := by
        simp [List.length_cons]; ring
      simpa [List.flatMap_cons, List.reverse_cons, List.append_assoc, htime] using h

noncomputable def swap_evals_loadRight (ys left right out : List Bool) :
    EvalsToInTime swapPairComputer.step
      (swapCfg (some .loadRight) none ys left right out)
      (some (swapCfg (some .parkL) none [] left (List.reverse ys ++ right) out))
      (ys.length + 1) := by
  induction ys generalizing right with
  | nil =>
      exact swap_evals_one (swap_step_loadRight_nil left right out)
  | cons c ys ih =>
      have h1 := swap_evals_one (swap_step_loadRight_cons c ys left right out)
      have h2 := ih (c :: right)
      have h := EvalsToInTime.trans swapPairComputer.step 1 (ys.length + 1) _ _ _ h1 h2
      have htime : (ys.length + 1) + 1 = (c :: ys).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem swap_step_parkL_cons (c : Bool) (rest right out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .parkL) none [] (c :: rest) right out) =
      some (swapCfg (some .parkL) none [] rest right (c :: out)) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.parkL, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

theorem swap_step_parkL_nil (right out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .parkL) none [] [] right out) =
      some (swapCfg (some .revRight) none [] [] right out) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.revRight, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

noncomputable def swap_evals_parkL (left right out : List Bool) :
    EvalsToInTime swapPairComputer.step
      (swapCfg (some .parkL) none [] left right out)
      (some (swapCfg (some .revRight) none [] [] right
        (List.reverse left ++ out)))
      (left.length + 1) := by
  induction left generalizing out with
  | nil =>
      exact swap_evals_one (swap_step_parkL_nil right out)
  | cons c left ih =>
      have h1 := swap_evals_one (swap_step_parkL_cons c left right out)
      have h2 := ih (c :: out)
      have h := EvalsToInTime.trans swapPairComputer.step 1 (left.length + 1) _ _ _ h1 h2
      have htime : (left.length + 1) + 1 = (c :: left).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem swap_step_revRight_cons (c : Bool) (rest left out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .revRight) none [] left (c :: rest) out) =
      some (swapCfg (some .revRight) none [] (c :: left) rest out) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.revRight, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

theorem swap_step_revRight_nil (left out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .revRight) none [] left [] out) =
      some (swapCfg (some .parkOut) none [] left [] out) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.parkOut, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

noncomputable def swap_evals_revRight (right left out : List Bool) :
    EvalsToInTime swapPairComputer.step
      (swapCfg (some .revRight) none [] left right out)
      (some (swapCfg (some .parkOut) none [] (List.reverse right ++ left) [] out))
      (right.length + 1) := by
  induction right generalizing left with
  | nil =>
      exact swap_evals_one (swap_step_revRight_nil left out)
  | cons c right ih =>
      have h1 := swap_evals_one (swap_step_revRight_cons c right left out)
      have h2 := ih (c :: left)
      have h := EvalsToInTime.trans swapPairComputer.step 1 (right.length + 1) _ _ _ h1 h2
      have htime : (right.length + 1) + 1 = (c :: right).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem swap_step_parkOut_cons (c : Bool) (rest left right : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .parkOut) none [] left right (c :: rest)) =
      some (swapCfg (some .parkOut) none [] left (c :: right) rest) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.parkOut, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

theorem swap_step_parkOut_nil (left right : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .parkOut) none [] left right []) =
      some (swapCfg (some .emitW) none [] left right []) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.emitW, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

noncomputable def swap_evals_parkOut (out left right : List Bool) :
    EvalsToInTime swapPairComputer.step
      (swapCfg (some .parkOut) none [] left right out)
      (some (swapCfg (some .emitW) none [] left (List.reverse out ++ right) []))
      (out.length + 1) := by
  induction out generalizing right with
  | nil =>
      exact swap_evals_one (swap_step_parkOut_nil left right)
  | cons c out ih =>
      have h1 := swap_evals_one (swap_step_parkOut_cons c out left right)
      have h2 := ih (c :: right)
      have h := EvalsToInTime.trans swapPairComputer.step 1 (out.length + 1) _ _ _ h1 h2
      have htime : (out.length + 1) + 1 = (c :: out).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem swap_step_emitW_nil (right out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .emitW) none [] [] right out) =
      some (swapCfg (some .emitSep) none [] [] right out) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.emitSep, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

theorem swap_step_emitW_cons (c : Bool) (rest right out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .emitW) none [] (c :: rest) right out) =
      some (swapCfg (some .emitW) none [] rest right (c :: true :: out)) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.emitW, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

/-- Drain `left` (= π) writing reverse of encodePair left-half onto out. -/
def swap_evals_emitW (left right out : List Bool) :
    EvalsToInTime swapPairComputer.step
      (swapCfg (some .emitW) none [] left right out)
      (some (swapCfg (some .emitSep) none [] [] right
        (List.reverse (left.flatMap fun c => [true, c]) ++ out)))
      (left.length + 1) := by
  induction left generalizing out with
  | nil =>
      simpa [List.flatMap] using swap_evals_one (swap_step_emitW_nil right out)
  | cons c left ih =>
      have h1 := swap_evals_one (swap_step_emitW_cons c left right out)
      have h2 := ih (c :: true :: out)
      have h := EvalsToInTime.trans swapPairComputer.step 1 (left.length + 1) _ _ _ h1 h2
      have htime : (left.length + 1) + 1 = (c :: left).length + 1 := by
        simp [List.length_cons]
      have hout :
          List.reverse ((c :: left).flatMap fun c => [true, c]) ++ out =
            List.reverse (left.flatMap fun c => [true, c]) ++ c :: true :: out := by
        simp [List.flatMap_cons, List.reverse_cons]
      simpa [htime, hout, List.append_assoc] using h

theorem swap_step_emitSep (right out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .emitSep) none [] [] right out) =
      some (swapCfg (some .emitFstPrep) none [] [] right (false :: out)) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.emitFstPrep, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

theorem swap_step_emitFstPrep_cons (c : Bool) (rest left out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .emitFstPrep) none [] left (c :: rest) out) =
      some (swapCfg (some .emitFstPrep) none [] (c :: left) rest out) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.emitFstPrep, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

theorem swap_step_emitFstPrep_nil (left out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .emitFstPrep) none [] left [] out) =
      some (swapCfg (some .emitFst) none [] left [] out) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.emitFst, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

noncomputable def swap_evals_emitFstPrep (right left out : List Bool) :
    EvalsToInTime swapPairComputer.step
      (swapCfg (some .emitFstPrep) none [] left right out)
      (some (swapCfg (some .emitFst) none [] (List.reverse right ++ left) [] out))
      (right.length + 1) := by
  induction right generalizing left with
  | nil =>
      exact swap_evals_one (swap_step_emitFstPrep_nil left out)
  | cons c right ih =>
      have h1 := swap_evals_one (swap_step_emitFstPrep_cons c right left out)
      have h2 := ih (c :: left)
      have h := EvalsToInTime.trans swapPairComputer.step 1 (right.length + 1) _ _ _ h1 h2
      have htime : (right.length + 1) + 1 = (c :: right).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem swap_step_emitFst_cons (c : Bool) (rest out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .emitFst) none [] (c :: rest) [] out) =
      some (swapCfg (some .emitFst) none [] rest [] (c :: out)) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.emitFst, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

theorem swap_step_emitFst_nil (out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .emitFst) none [] [] [] out) =
      some (swapCfg (some .rev1) none [] [] [] out) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.rev1, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

def swap_evals_emitFst (left out : List Bool) :
    EvalsToInTime swapPairComputer.step
      (swapCfg (some .emitFst) none [] left [] out)
      (some (swapCfg (some .rev1) none [] [] []
        (List.reverse left ++ out)))
      (left.length + 1) := by
  induction left generalizing out with
  | nil =>
      exact swap_evals_one (swap_step_emitFst_nil out)
  | cons c left ih =>
      have h1 := swap_evals_one (swap_step_emitFst_cons c left out)
      have h2 := ih (c :: out)
      have h := EvalsToInTime.trans swapPairComputer.step 1 (left.length + 1) _ _ _ h1 h2
      have htime : (left.length + 1) + 1 = (c :: left).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem swap_step_rev1_cons (c : Bool) (rest right : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .rev1) none [] [] right (c :: rest)) =
      some (swapCfg (some .rev1) none [] [] (c :: right) rest) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.rev1, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

theorem swap_step_rev1_nil (right : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .rev1) none [] [] right []) =
      some (swapCfg (some .rev2) none [] [] right []) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.rev2, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

def swap_evals_rev1 (out right : List Bool) :
    EvalsToInTime swapPairComputer.step
      (swapCfg (some .rev1) none [] [] right out)
      (some (swapCfg (some .rev2) none [] [] (List.reverse out ++ right) []))
      (out.length + 1) := by
  induction out generalizing right with
  | nil =>
      exact swap_evals_one (swap_step_rev1_nil right)
  | cons c out ih =>
      have h1 := swap_evals_one (swap_step_rev1_cons c out right)
      have h2 := ih (c :: right)
      have h := EvalsToInTime.trans swapPairComputer.step 1 (out.length + 1) _ _ _ h1 h2
      have htime : (out.length + 1) + 1 = (c :: out).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem swap_step_rev2_cons (c : Bool) (rest left : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .rev2) none [] left (c :: rest) []) =
      some (swapCfg (some .rev2) none [] (c :: left) rest []) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.rev2, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

theorem swap_step_rev2_nil (left : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .rev2) none [] left [] []) =
      some (swapCfg (some .rev3) none [] left [] []) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.rev3, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

def swap_evals_rev2 (right left : List Bool) :
    EvalsToInTime swapPairComputer.step
      (swapCfg (some .rev2) none [] left right [])
      (some (swapCfg (some .rev3) none [] (List.reverse right ++ left) [] []))
      (right.length + 1) := by
  induction right generalizing left with
  | nil =>
      exact swap_evals_one (swap_step_rev2_nil left)
  | cons c right ih =>
      have h1 := swap_evals_one (swap_step_rev2_cons c right left)
      have h2 := ih (c :: left)
      have h := EvalsToInTime.trans swapPairComputer.step 1 (right.length + 1) _ _ _ h1 h2
      have htime : (right.length + 1) + 1 = (c :: right).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

theorem swap_step_rev3_cons (c : Bool) (rest out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .rev3) none [] (c :: rest) [] out) =
      some (swapCfg (some .rev3) none [] rest [] (c :: out)) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.rev3, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

theorem swap_step_rev3_nil (out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .rev3) none [] [] [] out) =
      some (swapCfg (some .haltDrain) none [] [] [] out) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some SwapLabel.haltDrain, (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

def swap_evals_rev3 (left out : List Bool) :
    EvalsToInTime swapPairComputer.step
      (swapCfg (some .rev3) none [] left [] out)
      (some (swapCfg (some .haltDrain) none [] [] []
        (List.reverse left ++ out)))
      (left.length + 1) := by
  induction left generalizing out with
  | nil =>
      exact swap_evals_one (swap_step_rev3_nil out)
  | cons c left ih =>
      have h1 := swap_evals_one (swap_step_rev3_cons c left out)
      have h2 := ih (c :: out)
      have h := EvalsToInTime.trans swapPairComputer.step 1 (left.length + 1) _ _ _ h1 h2
      have htime : (left.length + 1) + 1 = (c :: left).length + 1 := by
        simp [List.length_cons]
      simpa [List.reverse_cons, List.append_assoc, htime] using h

/-- Triple reverse restores `encodePair` onto out. -/
def swap_evals_unreverse (ep : List Bool) :
    EvalsToInTime swapPairComputer.step
      (swapCfg (some .rev1) none [] [] [] (List.reverse ep))
      (some (swapCfg (some .haltDrain) none [] [] [] ep))
      ((ep.length + 1) + ((ep.length + 1) + (ep.length + 1))) := by
  have h1 := swap_evals_rev1 (List.reverse ep) []
  have h1' : EvalsToInTime swapPairComputer.step
      (swapCfg (some .rev1) none [] [] [] (List.reverse ep))
      (some (swapCfg (some .rev2) none [] [] ep []))
      (ep.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using h1
  have h2 := swap_evals_rev2 ep []
  have h2' : EvalsToInTime swapPairComputer.step
      (swapCfg (some .rev2) none [] [] ep [])
      (some (swapCfg (some .rev3) none [] (List.reverse ep) [] []))
      (ep.length + 1) := by
    simpa [List.append_nil] using h2
  have h3 := swap_evals_rev3 (List.reverse ep) []
  have h3' : EvalsToInTime swapPairComputer.step
      (swapCfg (some .rev3) none [] (List.reverse ep) [] [])
      (some (swapCfg (some .haltDrain) none [] [] [] ep))
      (ep.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using h3
  have h12 := EvalsToInTime.trans swapPairComputer.step
    (ep.length + 1) (ep.length + 1) _ _ _ h1' h2'
  exact EvalsToInTime.trans swapPairComputer.step
    ((ep.length + 1) + (ep.length + 1)) (ep.length + 1) _ _ _ h12 h3'

theorem swap_step_halt (out : List Bool) :
    TM2.step swapPairComputer.m
      (swapCfg (some .haltDrain) none [] [] [] out) =
      some (swapCfg none none [] [] [] out) := by
  simp [swapPairComputer, swapCfg, swapStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option SwapLabel), (none : Option Bool), stk⟩ : swapPairComputer.Cfg)) ?_
  funext s; cases s <;> simp [Function.update, swapStk]

theorem swap_initList (s : List Bool) :
    initList swapPairComputer s =
      swapCfg (some .parse) none s [] [] [] := by
  refine congrArg (fun stk =>
      (⟨some SwapLabel.parse, none, stk⟩ : swapPairComputer.Cfg)) ?_
  funext t; cases t <;> simp [swapPairComputer, swapStk]

theorem swap_haltList (out : List Bool) :
    haltList swapPairComputer out =
      swapCfg none none [] [] [] out := by
  refine congrArg (fun stk =>
      (⟨(none : Option SwapLabel), (none : Option Bool), stk⟩ :
        swapPairComputer.Cfg)) ?_
  funext t; cases t <;> simp [haltList, swapPairComputer, swapStk]

/-- Parse `encodePair (φ, π)` through park: at `emitW` with `left = π` and
`right = reverse φ`. -/
noncomputable def swap_evals_load_to_emitW (φ π : List Bool) :
    EvalsToInTime swapPairComputer.step
      (swapCfg (some .parse) none (encodePair (φ, π)) [] [] [])
      (some (swapCfg (some .emitW) none [] π (List.reverse φ) []))
      ((φ.length + 1) + ((π.length + 1) +
        ((φ.length + 1) + ((π.length + 1) + (1 + 2 * φ.length))))) := by
  have hparse := swap_evals_parse φ (false :: π) [] [] []
  have h1 : EvalsToInTime swapPairComputer.step
      (swapCfg (some .parse) none (encodePair (φ, π)) [] [] [])
      (some (swapCfg (some .parse) none (false :: π) (List.reverse φ) [] []))
      (2 * φ.length) := by
    simpa [encodePair, List.append_assoc] using hparse
  have hfalse := swap_evals_one
    (swap_step_parse_false π (List.reverse φ) [] [])
  have h12 := EvalsToInTime.trans swapPairComputer.step
    (2 * φ.length) 1 _ _ _ h1 hfalse
  have hload := swap_evals_loadRight π (List.reverse φ) [] []
  have h123 := EvalsToInTime.trans swapPairComputer.step
    (1 + 2 * φ.length) (π.length + 1) _ _ _ h12 hload
  have h123' : EvalsToInTime swapPairComputer.step
      (swapCfg (some .parse) none (encodePair (φ, π)) [] [] [])
      (some (swapCfg (some .parkL) none [] (List.reverse φ)
        (List.reverse π) []))
      ((π.length + 1) + (1 + 2 * φ.length)) := by
    simpa [List.append_nil] using h123
  have hparkL := swap_evals_parkL (List.reverse φ) (List.reverse π) []
  have hparkL' : EvalsToInTime swapPairComputer.step
      (swapCfg (some .parkL) none [] (List.reverse φ) (List.reverse π) [])
      (some (swapCfg (some .revRight) none [] [] (List.reverse π) φ))
      (φ.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using hparkL
  have htoRev := EvalsToInTime.trans swapPairComputer.step
    ((π.length + 1) + (1 + 2 * φ.length)) (φ.length + 1)
    _ _ _ h123' hparkL'
  have hrevR := swap_evals_revRight (List.reverse π) [] φ
  have hrevR' : EvalsToInTime swapPairComputer.step
      (swapCfg (some .revRight) none [] [] (List.reverse π) φ)
      (some (swapCfg (some .parkOut) none [] π [] φ))
      (π.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using hrevR
  have htoPark := EvalsToInTime.trans swapPairComputer.step
    ((φ.length + 1) + ((π.length + 1) + (1 + 2 * φ.length)))
    (π.length + 1)
    _ _ _ htoRev hrevR'
  have hparkOut := swap_evals_parkOut φ π []
  have hparkOut' : EvalsToInTime swapPairComputer.step
      (swapCfg (some .parkOut) none [] π [] φ)
      (some (swapCfg (some .emitW) none [] π (List.reverse φ) []))
      (φ.length + 1) := by
    simpa [List.append_nil] using hparkOut
  exact EvalsToInTime.trans swapPairComputer.step
    ((π.length + 1) + ((φ.length + 1) + ((π.length + 1) + (1 + 2 * φ.length))))
    (φ.length + 1)
    _ _ _ htoPark hparkOut'

/-- From `emitW` (left = π, right = reverse φ) through halt, emitting
`encodePair (π, φ)`. -/
noncomputable def swap_evals_emit_to_halt (φ π : List Bool) :
    EvalsToInTime swapPairComputer.step
      (swapCfg (some .emitW) none [] π (List.reverse φ) [])
      (some (swapCfg none none [] [] [] (encodePair (π, φ))))
      (1 + ((((encodePair (π, φ)).length + 1) +
        (((encodePair (π, φ)).length + 1) +
          ((encodePair (π, φ)).length + 1))) +
        ((φ.length + 1) + ((φ.length + 1) + (1 + (π.length + 1)))))) := by
  have hemitW := swap_evals_emitW π (List.reverse φ) []
  have hemitW' : EvalsToInTime swapPairComputer.step
      (swapCfg (some .emitW) none [] π (List.reverse φ) [])
      (some (swapCfg (some .emitSep) none [] [] (List.reverse φ)
        (List.reverse (π.flatMap fun c => [true, c]))))
      (π.length + 1) := by
    simpa [List.append_nil] using hemitW
  have hsep := swap_evals_one (swap_step_emitSep (List.reverse φ)
    (List.reverse (π.flatMap fun c => [true, c])))
  have h12 := EvalsToInTime.trans swapPairComputer.step
    (π.length + 1) 1 _ _ _ hemitW' hsep
  have hprep := swap_evals_emitFstPrep (List.reverse φ) []
    (false :: List.reverse (π.flatMap fun c => [true, c]))
  have hprep' : EvalsToInTime swapPairComputer.step
      (swapCfg (some .emitFstPrep) none [] [] (List.reverse φ)
        (false :: List.reverse (π.flatMap fun c => [true, c])))
      (some (swapCfg (some .emitFst) none [] φ []
        (false :: List.reverse (π.flatMap fun c => [true, c]))))
      (φ.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using hprep
  have h123 := EvalsToInTime.trans swapPairComputer.step
    (1 + (π.length + 1)) (φ.length + 1) _ _ _ h12 hprep'
  have hemitF := swap_evals_emitFst φ
    (false :: List.reverse (π.flatMap fun c => [true, c]))
  have hout_emit :
      List.reverse φ ++ false :: List.reverse (π.flatMap fun c => [true, c]) =
        List.reverse (encodePair (π, φ)) := by
    simp [encodePair, List.reverse_append, List.reverse_cons]
  have h1234 := EvalsToInTime.trans swapPairComputer.step
    ((φ.length + 1) + (1 + (π.length + 1))) (φ.length + 1) _ _ _ h123 hemitF
  have h1234' : EvalsToInTime swapPairComputer.step
      (swapCfg (some .emitW) none [] π (List.reverse φ) [])
      (some (swapCfg (some .rev1) none [] [] []
        (List.reverse (encodePair (π, φ)))))
      ((φ.length + 1) + ((φ.length + 1) + (1 + (π.length + 1)))) := by
    simpa [hout_emit] using h1234
  have hunrev := swap_evals_unreverse (encodePair (π, φ))
  have h5 := EvalsToInTime.trans swapPairComputer.step
    ((φ.length + 1) + ((φ.length + 1) + (1 + (π.length + 1))))
    (((encodePair (π, φ)).length + 1) +
      (((encodePair (π, φ)).length + 1) +
        ((encodePair (π, φ)).length + 1)))
    _ _ _ h1234' hunrev
  have hhalt := swap_evals_one (swap_step_halt (encodePair (π, φ)))
  exact EvalsToInTime.trans swapPairComputer.step
    ((((encodePair (π, φ)).length + 1) +
      (((encodePair (π, φ)).length + 1) +
        ((encodePair (π, φ)).length + 1))) +
      ((φ.length + 1) + ((φ.length + 1) + (1 + (π.length + 1)))))
    1
    _ _ _ h5 hhalt

/-- Full run: `encodePair (φ, π)` maps to `swapPair (φ, π)`. -/
noncomputable def swap_evals (φ π : List Bool) :
    TM2OutputsInTime swapPairComputer (encodePair (φ, π))
      (some (swapPair (φ, π)))
      ((1 + ((((encodePair (π, φ)).length + 1) +
        (((encodePair (π, φ)).length + 1) +
          ((encodePair (π, φ)).length + 1))) +
        ((φ.length + 1) + ((φ.length + 1) + (1 + (π.length + 1)))))) +
        ((φ.length + 1) + ((π.length + 1) +
          ((φ.length + 1) + ((π.length + 1) + (1 + 2 * φ.length)))))) := by
  have hload := swap_evals_load_to_emitW φ π
  have hemit := swap_evals_emit_to_halt φ π
  have hload' : EvalsToInTime swapPairComputer.step
      (initList swapPairComputer (encodePair (φ, π)))
      (some (swapCfg (some .emitW) none [] π (List.reverse φ) []))
      ((φ.length + 1) + ((π.length + 1) +
        ((φ.length + 1) + ((π.length + 1) + (1 + 2 * φ.length))))) := by
    simpa [swap_initList] using hload
  have hemit' : EvalsToInTime swapPairComputer.step
      (swapCfg (some .emitW) none [] π (List.reverse φ) [])
      (some (haltList swapPairComputer (swapPair (φ, π))))
      (1 + ((((encodePair (π, φ)).length + 1) +
        (((encodePair (π, φ)).length + 1) +
          ((encodePair (π, φ)).length + 1))) +
        ((φ.length + 1) + ((φ.length + 1) + (1 + (π.length + 1)))))) := by
    simpa [swap_haltList, swapPair] using hemit
  have h := EvalsToInTime.trans swapPairComputer.step
    ((φ.length + 1) + ((π.length + 1) +
      ((φ.length + 1) + ((π.length + 1) + (1 + 2 * φ.length)))))
    (1 + ((((encodePair (π, φ)).length + 1) +
      (((encodePair (π, φ)).length + 1) +
        ((encodePair (π, φ)).length + 1))) +
      ((φ.length + 1) + ((φ.length + 1) + (1 + (π.length + 1))))))
    _ _ _ hload' hemit'
  exact ⟨⟨h.steps, h.evals_in_steps⟩, h.steps_le_m⟩

/-- Time bound depending on input length only. -/
noncomputable def swapPairTime : Polynomial ℕ :=
  64 * (Polynomial.X ^ 2 + Polynomial.X + 1)

theorem swapPairTime_eval (n : ℕ) :
    swapPairTime.eval n = 64 * (n ^ 2 + n + 1) := by
  simp [swapPairTime, pow_two, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one]

theorem swapPairTime_bound (φ π : List Bool) :
    ((1 + ((((encodePair (π, φ)).length + 1) +
      (((encodePair (π, φ)).length + 1) +
        ((encodePair (π, φ)).length + 1))) +
      ((φ.length + 1) + ((φ.length + 1) + (1 + (π.length + 1)))))) +
      ((φ.length + 1) + ((π.length + 1) +
        ((φ.length + 1) + ((π.length + 1) + (1 + 2 * φ.length)))))) ≤
      swapPairTime.eval (encodePair (φ, π)).length := by
  simp [swapPairTime_eval, length_encodePair]
  set N := 2 * φ.length + 1 + π.length
  have hφ : φ.length ≤ N := by omega
  have hπ : π.length ≤ N := by omega
  have hLHS :
      1 + (2 * π.length + 1 + φ.length + 1 +
          (2 * π.length + 1 + φ.length + 1 +
            (2 * π.length + 1 + φ.length + 1)) +
        (φ.length + 1 + (φ.length + 1 + (1 + (π.length + 1))))) +
        (φ.length + 1 + (π.length + 1 + (φ.length + 1 + (π.length + 1 +
          (1 + 2 * φ.length))))) ≤
      16 * (φ.length + π.length + 2) := by omega
  refine le_trans hLHS ?_
  have hsum : φ.length + π.length + 2 ≤ 4 * (N ^ 2 + N + 1) := by
    have hφ' : φ.length ≤ N ^ 2 + N + 1 := by omega
    have hπ' : π.length ≤ N ^ 2 + N + 1 := by omega
    have h2 : 2 ≤ 2 * (N ^ 2 + N + 1) := by omega
    calc
      φ.length + π.length + 2
          ≤ (N ^ 2 + N + 1) + (N ^ 2 + N + 1) + 2 * (N ^ 2 + N + 1) :=
            Nat.add_le_add (Nat.add_le_add hφ' hπ') h2
      _ = 4 * (N ^ 2 + N + 1) := by ring
  have : 16 * (φ.length + π.length + 2) ≤ 64 * (N ^ 2 + N + 1) := by
    have := Nat.mul_le_mul_left 16 hsum
    convert this using 1 <;> ring
  exact this

/-- Rebuild `encodePair (π, φ)` under `encodePair` input. -/
noncomputable def swapPairComputableInPolyTime :
    TM2ComputableInPolyTime encodePair idBitEnc swapPair where
  tm := swapPairComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := swapPairTime
  outputsFun p := by
    rcases p with ⟨φ, π⟩
    change TM2OutputsInTime swapPairComputer
      (List.map id (encodePair (φ, π)))
      (some (List.map id (idBitEnc (swapPair (φ, π)))))
      (swapPairTime.eval (encodePair (φ, π)).length)
    simp only [List.map_id, id_eq, idBitEnc]
    exact evalsToInTime_le_mono (swap_evals φ π) (swapPairTime_bound φ π)

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
