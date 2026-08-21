import Theory.ProofComplexity.Bridge.Encoding
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

/-!
# Complexity classes over TM2 poly time (Ladder Rung R5)

Pinned class predicates `InP`, `InNP`, `InCoNP` using mathlib's
`Turing.TM2ComputableInPolyTime`. Class equality propositions match the
Cook Reckhow bridge pin. Constant bit InP nonvacuity, `encodePair`
projection (`projFirstComputableInPolyTime`), local statement surgery toward
composition (`seqCompComputer` with order preserving out→aux→in copy), and
Bool right-constant composition (`comp_const_right`, NP nonvacuity) are
certified. Phase `stepAux` lifts, multi-step iterate, full-list order preserving
copy, product `initList` / `haltList` packaging, and sequential `outputsFun`
glue for `compose_projFirst_bitEnc` / `InP_implies_InNP`, output bit flip
closure of P, and `classP_eq_classNP_implies_NP_eq_coNP` are certified
(mathlib `TM2ComputableInPolyTime.comp` remains `proof_wanted` in general).

LOG: R5 Bridge Complexity module (InP InNP seqComp full-list copy)
-/

open Turing
open TM2.Stmt
open StateTransition
open scoped Polynomial

namespace SATurday.Bridge

set_option maxHeartbeats 2000000

/-! ## Class predicates (pinned 2026-08-04) -/

/-- Deterministic polynomial time: a Boolean characteristic function computed by
a poly time TM2 under identity input encoding and single bit output encoding. -/
def InP (L : Language) : Prop :=
  ∃ (χ : List Bool → Bool)
    (_h : TM2ComputableInPolyTime idBitEnc bitEnc χ),
      ∀ x, χ x = true ↔ L x

/-- Nondeterministic polynomial time: poly length witnesses checked by a poly
time verifier on the fixed `encodePair` input encoding. -/
def InNP (L : Language) : Prop :=
  ∃ (p : Polynomial ℕ) (V : List Bool → List Bool → Bool)
    (_h : TM2ComputableInPolyTime encodePair bitEnc fun pw => V pw.1 pw.2),
      ∀ x, L x ↔ ∃ w, w.length ≤ p.eval x.length ∧ V x w = true

/-- Complement of a language. -/
def complement (L : Language) : Language := fun x => ¬ L x

/-- CoNP is NP of the complement. -/
def InCoNP (L : Language) : Prop := InNP (complement L)

/-- Class equality P = NP as a proposition over all languages. -/
def ClassP_eq_ClassNP : Prop := ∀ L : Language, InP L ↔ InNP L

/-- Class equality NP = coNP as a proposition over all languages. -/
def ClassNP_eq_ClassCoNP : Prop := ∀ L : Language, InNP L ↔ InCoNP L

/-! ## Definitional lemmas (certified) -/

/-- `InCoNP` unfolds to `InNP` of the complement. -/
theorem InCoNP_iff (L : Language) : InCoNP L ↔ InNP (complement L) := Iff.rfl

/-- Complement is involutive. -/
theorem complement_complement (L : Language) : complement (complement L) = L := by
  funext x
  simp [complement]

/-- Double complement preserves NP membership. -/
theorem InNP_complement_complement (L : Language) :
    InNP (complement (complement L)) ↔ InNP L := by
  rw [complement_complement]

/-- If NP equals coNP then every NP language has its complement in NP. -/
theorem ClassNP_eq_ClassCoNP.complement_in_NP
    (h : ClassNP_eq_ClassCoNP) (L : Language) (hL : InNP L) :
    InNP (complement L) := by
  have := (h L).mp hL
  simpa [InCoNP] using this

/-- Empty language predicate. -/
def emptyLanguage : Language := fun _ => False

/-- Full language predicate (all bit strings). -/
def fullLanguage : Language := fun _ => True

/-- Characteristic function constantly false decides the empty language. -/
theorem constFalse_decides_empty :
    ∀ x, (fun _ : List Bool => false) x = true ↔ emptyLanguage x := by
  intro x
  simp [emptyLanguage]

/-- Characteristic function constantly true decides the full language. -/
theorem constTrue_decides_full :
    ∀ x, (fun _ : List Bool => true) x = true ↔ fullLanguage x := by
  intro x
  simp [fullLanguage]

/-- Constant false verifier ignoring the witness (shape for P ⊆ NP). -/
def ignoreWitness (χ : List Bool → Bool) : List Bool → List Bool → Bool :=
  fun x _ => χ x

/-- Zero polynomial used as a trivial witness length bound. -/
noncomputable def zeroWitnessBound : Polynomial ℕ := 0

/-- Trivial witness length bound holds for the empty witness. -/
theorem empty_witness_length_bound (x : List Bool) :
    ([] : List Bool).length ≤ zeroWitnessBound.eval x.length := by
  simp [zeroWitnessBound]

/-! ## Constant bit TM2 (certified nonvacuity engine) -/

/-- Clear loop TM2 for a constant output bit.
Label `false`: pop one input bit; if the stack was empty go to `true`, else loop.
Label `true`: reset state to `false`, push the constant bit, halt.
Step count on input of length `n` is exactly `n + 2`. -/
def constBitComputer (b : Bool) : FinTM2 where
  K := Unit
  k₀ := ⟨⟩
  k₁ := ⟨⟩
  Γ _ := Bool
  Λ := Bool
  main := false
  σ := Bool
  initialState := false
  m
    | false =>
        TM2.Stmt.pop ⟨⟩ (fun _ o => decide (o = none)) <|
          TM2.Stmt.branch id
            (TM2.Stmt.goto fun _ => true)
            (TM2.Stmt.goto fun _ => false)
    | true =>
        TM2.Stmt.load (fun _ => false) <|
          TM2.Stmt.push ⟨⟩ (fun _ => b) TM2.Stmt.halt

/-- Polynomial time bound `X + 2` for the constant bit machine. -/
noncomputable def constBitTime : Polynomial ℕ := Polynomial.X + 2

/-- Unit stack family used by `constBitComputer` configurations. -/
def constBitStk (s : List Bool) : Unit → List Bool := fun _ => s

/-- Updating a constant Unit stack family replaces it. -/
theorem update_unit_stk (s t : List Bool) :
    Function.update (fun _ : Unit => s) PUnit.unit t = fun _ => t := by
  funext k
  cases k
  simp [Function.update]

/-- Configuration helper for `constBitComputer`. -/
def constBitCfg (b : Bool) (l : Option Bool) (v : Bool) (s : List Bool) :
    (constBitComputer b).Cfg :=
  ⟨l, v, constBitStk s⟩

/-- Stack update residual after a clear or write step. -/
theorem update_constBitStk (s t : List Bool) :
    Function.update (constBitStk s) PUnit.unit t = constBitStk t := by
  simpa [constBitStk] using update_unit_stk s t

/-- Popping a nonempty stack at the clear label shortens the stack by one. -/
theorem constBitComputer_step_cons (b x : Bool) (xs : List Bool) :
    TM2.step (constBitComputer b).m (constBitCfg b (some false) false (x :: xs)) =
      some (constBitCfg b (some false) false xs) := by
  simp [constBitComputer, constBitCfg, constBitStk, TM2.step, TM2.stepAux]
  exact congrArg some <|
    congrArg (fun stk => (⟨some false, false, stk⟩ : (constBitComputer b).Cfg))
      (update_constBitStk (x :: xs) xs)

/-- Popping the empty stack at the clear label jumps to the write label. -/
theorem constBitComputer_step_nil (b : Bool) :
    TM2.step (constBitComputer b).m (constBitCfg b (some false) false []) =
      some (constBitCfg b (some true) true []) := by
  simp [constBitComputer, constBitCfg, constBitStk, TM2.step, TM2.stepAux]
  exact congrArg some <|
    congrArg (fun stk => (⟨some true, true, stk⟩ : (constBitComputer b).Cfg))
      (update_constBitStk [] [])

/-- The write label pushes the constant bit and halts with state reset. -/
theorem constBitComputer_step_write (b : Bool) :
    TM2.step (constBitComputer b).m (constBitCfg b (some true) true []) =
      some (constBitCfg b none false [b]) := by
  simp [constBitComputer, constBitCfg, constBitStk, TM2.step, TM2.stepAux]
  exact congrArg some <|
    congrArg (fun stk => (⟨none, false, stk⟩ : (constBitComputer b).Cfg))
      (update_constBitStk [] [b])

/-- Initial configuration matches the clear label with the full input stack. -/
theorem constBitComputer_initList (b : Bool) (s : List Bool) :
    initList (constBitComputer b) s = constBitCfg b (some false) false s := by
  simp [initList, constBitComputer, constBitCfg]
  exact congrArg (fun stk => (⟨some false, false, stk⟩ : (constBitComputer b).Cfg))
    (rfl : (fun _ : Unit => s) = constBitStk s)

/-- Halting configuration matches `haltList` on the singleton output. -/
theorem constBitComputer_haltList (b : Bool) :
    haltList (constBitComputer b) [b] = constBitCfg b none false [b] := by
  simp [haltList, constBitComputer, constBitCfg]
  exact congrArg (fun stk => (⟨none, false, stk⟩ : (constBitComputer b).Cfg))
    (rfl : (fun _ : Unit => [b]) = constBitStk [b])

/-- One clear step removes the head of a nonempty input. -/
def constBitComputer_evals_cons_step (b x : Bool) (xs : List Bool) :
    EvalsToInTime (constBitComputer b).step
      (initList (constBitComputer b) (x :: xs))
      (some (initList (constBitComputer b) xs)) 1 where
  steps := 1
  steps_le_m := le_rfl
  evals_in_steps := by
    -- One bind step from init (x::xs) lands on init xs.
    change (some (initList (constBitComputer b) (x :: xs))).bind (constBitComputer b).step =
      some (initList (constBitComputer b) xs)
    simp only [FinTM2.step, Option.bind, constBitComputer_initList]
    exact constBitComputer_step_cons b x xs

/-- Empty input: empty pop then write (2 steps) yields `[b]`. -/
def constBitComputer_evals_nil (b : Bool) :
    EvalsToInTime (constBitComputer b).step
      (initList (constBitComputer b) [])
      (some (haltList (constBitComputer b) [b])) 2 where
  steps := 2
  steps_le_m := le_rfl
  evals_in_steps := by
    -- Two bind steps: empty pop to write label, then push and halt.
    change ((some (initList (constBitComputer b) [])).bind (constBitComputer b).step).bind
        (constBitComputer b).step =
      some (haltList (constBitComputer b) [b])
    simp only [FinTM2.step, constBitComputer_initList, constBitComputer_haltList]
    -- Reduce `(some cfg).bind step` to `step cfg`, then apply the two step lemmas.
    change ((TM2.step (constBitComputer b).m (constBitCfg b (some false) false [])).bind
        (TM2.step (constBitComputer b).m)) =
      some (constBitCfg b none false [b])
    rw [constBitComputer_step_nil b]
    change TM2.step (constBitComputer b).m (constBitCfg b (some true) true []) =
      some (constBitCfg b none false [b])
    exact constBitComputer_step_write b

/-- After clearing `s`, one empty pop and one write, the machine outputs `[b]`. -/
noncomputable def constBitComputer_evals (b : Bool) (s : List Bool) :
    TM2OutputsInTime (constBitComputer b) s (some [b]) (s.length + 2) := by
  induction s with
  | nil =>
      exact constBitComputer_evals_nil b
  | cons x xs ih =>
      have h :=
        EvalsToInTime.trans (constBitComputer b).step 1 (xs.length + 2)
          (initList (constBitComputer b) (x :: xs))
          (initList (constBitComputer b) xs)
          (some (haltList (constBitComputer b) [b]))
          (constBitComputer_evals_cons_step b x xs) ih
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Time polynomial evaluates as length plus two. -/
theorem constBitTime_eval (n : ℕ) : constBitTime.eval n = n + 2 := by
  simp [constBitTime, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]

/-- Constant bit function is computable in poly time by `constBitComputer`. -/
noncomputable def constBitComputableInPolyTime (b : Bool) :
    TM2ComputableInPolyTime idBitEnc bitEnc (fun _ : List Bool => b) where
  tm := constBitComputer b
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := constBitTime
  outputsFun a := by
    change TM2OutputsInTime (constBitComputer b) (List.map id (idBitEnc a))
      (some (List.map id (bitEnc ((fun _ : List Bool => b) a))))
      (constBitTime.eval (idBitEnc a).length)
    simp only [idBitEnc, bitEnc, List.map_id, id_eq, constBitTime_eval]
    exact constBitComputer_evals b a

/-- Empty language is in P via the constant false machine. -/
theorem emptyLanguage_in_P : InP emptyLanguage :=
  ⟨fun _ => false, constBitComputableInPolyTime false, constFalse_decides_empty⟩

/-- Full language is in P via the constant true machine. -/
theorem fullLanguage_in_P : InP fullLanguage :=
  ⟨fun _ => true, constBitComputableInPolyTime true, constTrue_decides_full⟩

/-! ## encodePair first projection TM (certified step toward P ⊆ NP) -/

inductive ProjStack where
  | inp | work | out
  deriving DecidableEq, Repr

instance : Fintype ProjStack where
  elems := {.inp, .work, .out}
  complete s := by cases s <;> simp

inductive ProjLabel where
  | parse | expectBit | clear | rev
  deriving DecidableEq, Repr

instance : Fintype ProjLabel where
  elems := {.parse, .expectBit, .clear, .rev}
  complete s := by cases s <;> simp

def projFirstComputer : FinTM2 where
  K := ProjStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := ProjLabel
  main := .parse
  σ := Option Bool
  initialState := none
  m
    | .parse =>
        pop ProjStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => ProjLabel.rev)
            (branch (fun s => decide (s = some false))
              (goto fun _ => ProjLabel.clear)
              (goto fun _ => ProjLabel.expectBit))
    | .expectBit =>
        pop ProjStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            halt
            (push ProjStack.work (fun s => s.getD false) <|
              load (fun _ => none) <|
                goto fun _ => ProjLabel.parse)
    | .clear =>
        pop ProjStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => ProjLabel.rev)
            (goto fun _ => ProjLabel.clear)
    | .rev =>
        pop ProjStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            halt
            (push ProjStack.out (fun s => s.getD false) <|
              load (fun _ => none) <|
                goto fun _ => ProjLabel.rev)

def projStk (inp work out : List Bool) : ProjStack → List Bool
  | .inp => inp
  | .work => work
  | .out => out

def projCfg (l : Option ProjLabel) (v : Option Bool) (inp work out : List Bool) :
    projFirstComputer.Cfg :=
  ⟨l, v, projStk inp work out⟩

theorem proj_step_parse_true (b : Bool) (rest work out : List Bool) :
    TM2.step projFirstComputer.m
      (projCfg (some .parse) none (true :: b :: rest) work out) =
      some (projCfg (some .expectBit) (some true) (b :: rest) work out) := by
  simp [projFirstComputer, projCfg, projStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk => (⟨some ProjLabel.expectBit, some true, stk⟩ : projFirstComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, projStk]

theorem proj_step_parse_false (rest work out : List Bool) :
    TM2.step projFirstComputer.m
      (projCfg (some .parse) none (false :: rest) work out) =
      some (projCfg (some .clear) (some false) rest work out) := by
  simp [projFirstComputer, projCfg, projStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk => (⟨some ProjLabel.clear, some false, stk⟩ : projFirstComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, projStk]

theorem proj_step_expectBit (b : Bool) (rest work out : List Bool) :
    TM2.step projFirstComputer.m
      (projCfg (some .expectBit) (some true) (b :: rest) work out) =
      some (projCfg (some .parse) none rest (b :: work) out) := by
  simp [projFirstComputer, projCfg, projStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk => (⟨some ProjLabel.parse, (none : Option Bool), stk⟩ : projFirstComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, projStk]

theorem proj_step_clear_cons (x : Bool) (rest work out : List Bool) (v : Option Bool) :
    TM2.step projFirstComputer.m
      (projCfg (some .clear) v (x :: rest) work out) =
      some (projCfg (some .clear) (some x) rest work out) := by
  simp [projFirstComputer, projCfg, projStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk => (⟨some ProjLabel.clear, some x, stk⟩ : projFirstComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, projStk]

theorem proj_step_clear_nil (v : Option Bool) (work out : List Bool) :
    TM2.step projFirstComputer.m
      (projCfg (some .clear) v [] work out) =
      some (projCfg (some .rev) none [] work out) := by
  simp [projFirstComputer, projCfg, projStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk => (⟨some ProjLabel.rev, (none : Option Bool), stk⟩ : projFirstComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, projStk]

theorem proj_step_rev_cons (b : Bool) (rest inp out : List Bool) (v : Option Bool) :
    TM2.step projFirstComputer.m
      (projCfg (some .rev) v inp (b :: rest) out) =
      some (projCfg (some .rev) none inp rest (b :: out)) := by
  simp [projFirstComputer, projCfg, projStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk => (⟨some ProjLabel.rev, (none : Option Bool), stk⟩ : projFirstComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, projStk]

theorem proj_step_rev_nil (inp out : List Bool) (v : Option Bool) :
    TM2.step projFirstComputer.m
      (projCfg (some .rev) v inp [] out) =
      some (projCfg none none inp [] out) := by
  simp [projFirstComputer, projCfg, projStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk => (⟨(none : Option ProjLabel), (none : Option Bool), stk⟩ : projFirstComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, projStk]

theorem projFirst_initList (s : List Bool) :
    initList projFirstComputer s = projCfg (some .parse) none s [] [] := by
  refine congrArg (fun stk =>
      (⟨some ProjLabel.parse, (none : Option Bool), stk⟩ : projFirstComputer.Cfg)) ?_
  funext k; cases k <;> simp [projFirstComputer, projStk]

theorem projFirst_haltList (s : List Bool) :
    haltList projFirstComputer s = projCfg none none [] [] s := by
  refine congrArg (fun stk =>
      (⟨(none : Option ProjLabel), (none : Option Bool), stk⟩ : projFirstComputer.Cfg)) ?_
  funext k; cases k <;> simp [projFirstComputer, projStk]

def proj_evals_one_bit (b : Bool) (rest work out : List Bool) :
    EvalsToInTime projFirstComputer.step
      (projCfg (some .parse) none (true :: b :: rest) work out)
      (some (projCfg (some .parse) none rest (b :: work) out)) 2 where
  steps := 2
  steps_le_m := by decide
  evals_in_steps := by
    change ((some (projCfg (some .parse) none (true :: b :: rest) work out)).bind
        projFirstComputer.step).bind projFirstComputer.step =
      some (projCfg (some .parse) none rest (b :: work) out)
    simp only [FinTM2.step]
    change ((TM2.step projFirstComputer.m
        (projCfg (some .parse) none (true :: b :: rest) work out)).bind
        (TM2.step projFirstComputer.m)) =
      some (projCfg (some .parse) none rest (b :: work) out)
    rw [proj_step_parse_true]
    change TM2.step projFirstComputer.m
        (projCfg (some .expectBit) (some true) (b :: rest) work out) =
      some (projCfg (some .parse) none rest (b :: work) out)
    exact proj_step_expectBit b rest work out

noncomputable def proj_evals_parse (x rest work out : List Bool) :
    EvalsToInTime projFirstComputer.step
      (projCfg (some .parse) none ((x.flatMap fun b => [true, b]) ++ rest) work out)
      (some (projCfg (some .parse) none rest (x.reverse ++ work) out))
      (2 * x.length) := by
  induction x generalizing work with
  | nil =>
      simpa using EvalsToInTime.refl projFirstComputer.step
        (projCfg (some .parse) none rest work out)
  | cons b xs ih =>
      have h1 := proj_evals_one_bit b ((xs.flatMap fun b => [true, b]) ++ rest) work out
      have h2 := ih (b :: work)
      have h := EvalsToInTime.trans projFirstComputer.step 2 (2 * xs.length)
        (projCfg (some .parse) none ((b :: xs).flatMap (fun b => [true, b]) ++ rest) work out)
        (projCfg (some .parse) none ((xs.flatMap fun b => [true, b]) ++ rest) (b :: work) out)
        (some (projCfg (some .parse) none rest (xs.reverse ++ (b :: work)) out))
        (by simpa [List.flatMap] using h1) h2
      simpa [List.flatMap, List.reverse_cons, List.append_assoc, Nat.mul_succ, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc, two_mul] using h

def proj_evals_to_clear (w work out : List Bool) :
    EvalsToInTime projFirstComputer.step
      (projCfg (some .parse) none (false :: w) work out)
      (some (projCfg (some .clear) (some false) w work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (projCfg (some .parse) none (false :: w) work out)).bind
        projFirstComputer.step =
      some (projCfg (some .clear) (some false) w work out)
    simp only [FinTM2.step]
    exact proj_step_parse_false w work out

def proj_evals_clear_one (x : Bool) (rest work out : List Bool) (v : Option Bool) :
    EvalsToInTime projFirstComputer.step
      (projCfg (some .clear) v (x :: rest) work out)
      (some (projCfg (some .clear) (some x) rest work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (projCfg (some .clear) v (x :: rest) work out)).bind
        projFirstComputer.step =
      some (projCfg (some .clear) (some x) rest work out)
    simp only [FinTM2.step]
    exact proj_step_clear_cons x rest work out v

def proj_evals_clear_nil (v : Option Bool) (work out : List Bool) :
    EvalsToInTime projFirstComputer.step
      (projCfg (some .clear) v [] work out)
      (some (projCfg (some .rev) none [] work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (projCfg (some .clear) v [] work out)).bind projFirstComputer.step =
      some (projCfg (some .rev) none [] work out)
    simp only [FinTM2.step]
    exact proj_step_clear_nil v work out

noncomputable def proj_evals_clear (w work out : List Bool) (v : Option Bool) :
    EvalsToInTime projFirstComputer.step
      (projCfg (some .clear) v w work out)
      (some (projCfg (some .rev) none [] work out))
      (w.length + 1) := by
  induction w generalizing v with
  | nil =>
      simpa using proj_evals_clear_nil v work out
  | cons x xs ih =>
      have h := EvalsToInTime.trans projFirstComputer.step 1 (xs.length + 1)
        _ _ _ (proj_evals_clear_one x xs work out v) (ih (some x))
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

def proj_evals_rev_one (b : Bool) (rest out : List Bool) (v : Option Bool) :
    EvalsToInTime projFirstComputer.step
      (projCfg (some .rev) v [] (b :: rest) out)
      (some (projCfg (some .rev) none [] rest (b :: out))) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (projCfg (some .rev) v [] (b :: rest) out)).bind
        projFirstComputer.step =
      some (projCfg (some .rev) none [] rest (b :: out))
    simp only [FinTM2.step]
    exact proj_step_rev_cons b rest [] out v

def proj_evals_rev_nil (out : List Bool) (v : Option Bool) :
    EvalsToInTime projFirstComputer.step
      (projCfg (some .rev) v [] [] out)
      (some (projCfg none none [] [] out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (projCfg (some .rev) v [] [] out)).bind projFirstComputer.step =
      some (projCfg none none [] [] out)
    simp only [FinTM2.step]
    exact proj_step_rev_nil [] out v

noncomputable def proj_evals_rev (work out : List Bool) (v : Option Bool) :
    EvalsToInTime projFirstComputer.step
      (projCfg (some .rev) v [] work out)
      (some (projCfg none none [] [] (work.reverse ++ out)))
      (work.length + 1) := by
  induction work generalizing out v with
  | nil =>
      simpa using proj_evals_rev_nil out v
  | cons b bs ih =>
      have h := EvalsToInTime.trans projFirstComputer.step 1 (bs.length + 1)
        _ _ _ (proj_evals_rev_one b bs out v) (ih (b :: out) none)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

def evalsToInTime_le_mono {σ} {f : σ → Option σ} {a : σ} {b : Option σ} {m n : ℕ}
    (h : EvalsToInTime f a b m) (hle : m ≤ n) : EvalsToInTime f a b n :=
  ⟨h.toEvalsTo, le_trans h.steps_le_m hle⟩

noncomputable def projFirst_evals (x w : List Bool) :
    TM2OutputsInTime projFirstComputer (encodePair (x, w)) (some x)
      (3 * x.length + w.length + 3) := by
  have hparse : EvalsToInTime projFirstComputer.step
      (projCfg (some .parse) none (encodePair (x, w)) [] [])
      (some (projCfg (some .parse) none (false :: w) x.reverse []))
      (2 * x.length) := by
    simpa [encodePair] using proj_evals_parse x (false :: w) [] []
  let h1 := EvalsToInTime.trans projFirstComputer.step (2 * x.length) 1
    _ _ _ hparse (proj_evals_to_clear w x.reverse [])
  let h1' : EvalsToInTime projFirstComputer.step
      (projCfg (some .parse) none (encodePair (x, w)) [] [])
      (some (projCfg (some .clear) (some false) w x.reverse []))
      (2 * x.length + 1) :=
    evalsToInTime_le_mono h1 (by omega)
  let h2 := EvalsToInTime.trans projFirstComputer.step (2 * x.length + 1) (w.length + 1)
    _ _ _ h1' (proj_evals_clear w x.reverse [] (some false))
  let h2' : EvalsToInTime projFirstComputer.step
      (projCfg (some .parse) none (encodePair (x, w)) [] [])
      (some (projCfg (some .rev) none [] x.reverse []))
      (2 * x.length + 1 + (w.length + 1)) :=
    evalsToInTime_le_mono h2 (by omega)
  have hrev : EvalsToInTime projFirstComputer.step
      (projCfg (some .rev) none [] x.reverse [])
      (some (projCfg none none [] [] x))
      (x.length + 1) := by
    simpa [List.reverse_reverse, List.length_reverse] using
      proj_evals_rev x.reverse [] none
  let h3 := EvalsToInTime.trans projFirstComputer.step
      (2 * x.length + 1 + (w.length + 1)) (x.length + 1) _ _ _ h2' hrev
  let h3' : EvalsToInTime projFirstComputer.step
      (projCfg (some .parse) none (encodePair (x, w)) [] [])
      (some (projCfg none none [] [] x))
      (3 * x.length + w.length + 3) :=
    evalsToInTime_le_mono h3 (by omega)
  -- Rewrite endpoints to initList / haltList
  have : EvalsToInTime projFirstComputer.step
      (initList projFirstComputer (encodePair (x, w)))
      (some (haltList projFirstComputer x))
      (3 * x.length + w.length + 3) := by
    rw [projFirst_initList, projFirst_haltList]
    exact h3'
  exact this

noncomputable def projFirstTime : Polynomial ℕ := 3 * Polynomial.X + 3

theorem projFirstTime_bound (x w : List Bool) :
    3 * x.length + w.length + 3 ≤ projFirstTime.eval (encodePair (x, w)).length := by
  simp [projFirstTime, length_encodePair, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_add]
  omega

noncomputable def projFirstComputableInPolyTime :
    TM2ComputableInPolyTime encodePair idBitEnc (fun pw => pw.1) where
  tm := projFirstComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := projFirstTime
  outputsFun pw := by
    rcases pw with ⟨x, w⟩
    change TM2OutputsInTime projFirstComputer (List.map id (encodePair (x, w)))
      (some (List.map id (idBitEnc x)))
      (projFirstTime.eval (encodePair (x, w)).length)
    simp only [idBitEnc, List.map_id, id_eq]
    exact evalsToInTime_le_mono (projFirst_evals x w) (projFirstTime_bound x w)

/-! ## Prefix false copy TM (decodePairResult on encodePair inputs) -/

inductive PrefixStack where
  | inp | work | out
  deriving DecidableEq, Repr

instance : Fintype PrefixStack where
  elems := {.inp, .work, .out}
  complete s := by cases s <;> simp

inductive PrefixLabel where
  | writeFalse | copy | rev
  deriving DecidableEq, Repr

instance : Fintype PrefixLabel where
  elems := {.writeFalse, .copy, .rev}
  complete s := by cases s <;> simp

/-- Push `false` onto the work stack, copy input onto work, reverse onto out.
Realizes `fun s => false :: s` in `2|s| + 2` steps. -/
def prefixFalseCopyComputer : FinTM2 where
  K := PrefixStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := PrefixLabel
  main := .writeFalse
  σ := Option Bool
  initialState := none
  m
    | .writeFalse =>
        push PrefixStack.work (fun _ => false) <|
          load (fun _ => none) <|
            goto fun _ => PrefixLabel.copy
    | .copy =>
        pop PrefixStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => PrefixLabel.rev)
            (push PrefixStack.work (fun s => s.getD false) <|
              load (fun _ => none) <|
                goto fun _ => PrefixLabel.copy)
    | .rev =>
        pop PrefixStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            halt
            (push PrefixStack.out (fun s => s.getD false) <|
              load (fun _ => none) <|
                goto fun _ => PrefixLabel.rev)

def prefixStk (inp work out : List Bool) : PrefixStack → List Bool
  | .inp => inp
  | .work => work
  | .out => out

def prefixCfg (l : Option PrefixLabel) (v : Option Bool)
    (inp work out : List Bool) : prefixFalseCopyComputer.Cfg :=
  ⟨l, v, prefixStk inp work out⟩

theorem prefix_step_writeFalse (inp work out : List Bool) :
    TM2.step prefixFalseCopyComputer.m
      (prefixCfg (some .writeFalse) none inp work out) =
      some (prefixCfg (some .copy) none inp (false :: work) out) := by
  simp [prefixFalseCopyComputer, prefixCfg, prefixStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PrefixLabel.copy, (none : Option Bool), stk⟩ : prefixFalseCopyComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, prefixStk]

theorem prefix_step_copy_cons (b : Bool) (rest work out : List Bool) (v : Option Bool) :
    TM2.step prefixFalseCopyComputer.m
      (prefixCfg (some .copy) v (b :: rest) work out) =
      some (prefixCfg (some .copy) none rest (b :: work) out) := by
  simp [prefixFalseCopyComputer, prefixCfg, prefixStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PrefixLabel.copy, (none : Option Bool), stk⟩ : prefixFalseCopyComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, prefixStk]

theorem prefix_step_copy_nil (work out : List Bool) (v : Option Bool) :
    TM2.step prefixFalseCopyComputer.m
      (prefixCfg (some .copy) v [] work out) =
      some (prefixCfg (some .rev) none [] work out) := by
  simp [prefixFalseCopyComputer, prefixCfg, prefixStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PrefixLabel.rev, (none : Option Bool), stk⟩ : prefixFalseCopyComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, prefixStk]

theorem prefix_step_rev_cons (b : Bool) (rest inp out : List Bool) (v : Option Bool) :
    TM2.step prefixFalseCopyComputer.m
      (prefixCfg (some .rev) v inp (b :: rest) out) =
      some (prefixCfg (some .rev) none inp rest (b :: out)) := by
  simp [prefixFalseCopyComputer, prefixCfg, prefixStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PrefixLabel.rev, (none : Option Bool), stk⟩ : prefixFalseCopyComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, prefixStk]

theorem prefix_step_rev_nil (inp out : List Bool) (v : Option Bool) :
    TM2.step prefixFalseCopyComputer.m
      (prefixCfg (some .rev) v inp [] out) =
      some (prefixCfg none none inp [] out) := by
  simp [prefixFalseCopyComputer, prefixCfg, prefixStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option PrefixLabel), (none : Option Bool), stk⟩ : prefixFalseCopyComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, prefixStk]

theorem prefixFalseCopy_initList (s : List Bool) :
    initList prefixFalseCopyComputer s =
      prefixCfg (some .writeFalse) none s [] [] := by
  refine congrArg (fun stk =>
      (⟨some PrefixLabel.writeFalse, (none : Option Bool), stk⟩ :
        prefixFalseCopyComputer.Cfg)) ?_
  funext k; cases k <;> simp [prefixFalseCopyComputer, prefixStk]

theorem prefixFalseCopy_haltList (s : List Bool) :
    haltList prefixFalseCopyComputer s =
      prefixCfg none none [] [] s := by
  refine congrArg (fun stk =>
      (⟨(none : Option PrefixLabel), (none : Option Bool), stk⟩ :
        prefixFalseCopyComputer.Cfg)) ?_
  funext k; cases k <;> simp [prefixFalseCopyComputer, prefixStk]

def prefix_evals_writeFalse (inp : List Bool) :
    EvalsToInTime prefixFalseCopyComputer.step
      (prefixCfg (some .writeFalse) none inp [] [])
      (some (prefixCfg (some .copy) none inp [false] [])) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (prefixCfg (some .writeFalse) none inp [] [])).bind
        prefixFalseCopyComputer.step =
      some (prefixCfg (some .copy) none inp [false] [])
    simp only [FinTM2.step]
    exact prefix_step_writeFalse inp [] []

def prefix_evals_copy_one (b : Bool) (rest work out : List Bool) (v : Option Bool) :
    EvalsToInTime prefixFalseCopyComputer.step
      (prefixCfg (some .copy) v (b :: rest) work out)
      (some (prefixCfg (some .copy) none rest (b :: work) out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (prefixCfg (some .copy) v (b :: rest) work out)).bind
        prefixFalseCopyComputer.step =
      some (prefixCfg (some .copy) none rest (b :: work) out)
    simp only [FinTM2.step]
    exact prefix_step_copy_cons b rest work out v

def prefix_evals_copy_nil (work out : List Bool) (v : Option Bool) :
    EvalsToInTime prefixFalseCopyComputer.step
      (prefixCfg (some .copy) v [] work out)
      (some (prefixCfg (some .rev) none [] work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (prefixCfg (some .copy) v [] work out)).bind
        prefixFalseCopyComputer.step =
      some (prefixCfg (some .rev) none [] work out)
    simp only [FinTM2.step]
    exact prefix_step_copy_nil work out v

noncomputable def prefix_evals_copy (inp work out : List Bool) (v : Option Bool) :
    EvalsToInTime prefixFalseCopyComputer.step
      (prefixCfg (some .copy) v inp work out)
      (some (prefixCfg (some .rev) none [] (inp.reverse ++ work) out))
      (inp.length + 1) := by
  induction inp generalizing work v with
  | nil =>
      simpa using prefix_evals_copy_nil work out v
  | cons b bs ih =>
      have h := EvalsToInTime.trans prefixFalseCopyComputer.step 1 (bs.length + 1)
        _ _ _ (prefix_evals_copy_one b bs work out v) (ih (b :: work) none)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

def prefix_evals_rev_one (b : Bool) (rest out : List Bool) (v : Option Bool) :
    EvalsToInTime prefixFalseCopyComputer.step
      (prefixCfg (some .rev) v [] (b :: rest) out)
      (some (prefixCfg (some .rev) none [] rest (b :: out))) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (prefixCfg (some .rev) v [] (b :: rest) out)).bind
        prefixFalseCopyComputer.step =
      some (prefixCfg (some .rev) none [] rest (b :: out))
    simp only [FinTM2.step]
    exact prefix_step_rev_cons b rest [] out v

def prefix_evals_rev_nil (out : List Bool) (v : Option Bool) :
    EvalsToInTime prefixFalseCopyComputer.step
      (prefixCfg (some .rev) v [] [] out)
      (some (prefixCfg none none [] [] out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (prefixCfg (some .rev) v [] [] out)).bind
        prefixFalseCopyComputer.step =
      some (prefixCfg none none [] [] out)
    simp only [FinTM2.step]
    exact prefix_step_rev_nil [] out v

noncomputable def prefix_evals_rev (work out : List Bool) (v : Option Bool) :
    EvalsToInTime prefixFalseCopyComputer.step
      (prefixCfg (some .rev) v [] work out)
      (some (prefixCfg none none [] [] (work.reverse ++ out)))
      (work.length + 1) := by
  induction work generalizing out v with
  | nil =>
      simpa using prefix_evals_rev_nil out v
  | cons b bs ih =>
      have h := EvalsToInTime.trans prefixFalseCopyComputer.step 1 (bs.length + 1)
        _ _ _ (prefix_evals_rev_one b bs out v) (ih (b :: out) none)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

noncomputable def prefixFalseCopy_evals (s : List Bool) :
    TM2OutputsInTime prefixFalseCopyComputer s (some (false :: s))
      (2 * s.length + 4) := by
  have h0 := prefix_evals_writeFalse s
  -- after writeFalse: work = [false]
  have h1 := prefix_evals_copy s [false] [] none
  -- after copy: work = s.reverse ++ [false]
  have h01 := EvalsToInTime.trans prefixFalseCopyComputer.step 1 (s.length + 1)
    _ _ _ h0 h1
  have h01' : EvalsToInTime prefixFalseCopyComputer.step
      (prefixCfg (some .writeFalse) none s [] [])
      (some (prefixCfg (some .rev) none [] (s.reverse ++ [false]) []))
      (1 + (s.length + 1)) :=
    evalsToInTime_le_mono h01 (by omega)
  have h2 : EvalsToInTime prefixFalseCopyComputer.step
      (prefixCfg (some .rev) none [] (s.reverse ++ [false]) [])
      (some (prefixCfg none none [] [] ((s.reverse ++ [false]).reverse ++ [])))
      ((s.reverse ++ [false]).length + 1) :=
    prefix_evals_rev (s.reverse ++ [false]) [] none
  have h2' : EvalsToInTime prefixFalseCopyComputer.step
      (prefixCfg (some .rev) none [] (s.reverse ++ [false]) [])
      (some (prefixCfg none none [] [] (false :: s)))
      (s.length + 2) := by
    have hout : (s.reverse ++ [false]).reverse = false :: s := by
      simp [List.reverse_append, List.reverse_reverse]
    simpa [List.length_append, List.length_reverse, List.length_singleton, hout,
      List.append_nil] using h2
  have h3 := EvalsToInTime.trans prefixFalseCopyComputer.step (1 + (s.length + 1))
      (s.length + 2) _ _ _ h01' h2'
  have h3' : EvalsToInTime prefixFalseCopyComputer.step
      (prefixCfg (some .writeFalse) none s [] [])
      (some (prefixCfg none none [] [] (false :: s)))
      (2 * s.length + 4) :=
    evalsToInTime_le_mono h3 (by omega)
  have : EvalsToInTime prefixFalseCopyComputer.step
      (initList prefixFalseCopyComputer s)
      (some (haltList prefixFalseCopyComputer (false :: s)))
      (2 * s.length + 4) := by
    rw [prefixFalseCopy_initList, prefixFalseCopy_haltList]
    exact h3'
  exact this

noncomputable def prefixFalseCopyTime : Polynomial ℕ := 2 * Polynomial.X + 4

theorem prefixFalseCopyTime_eval (n : ℕ) :
    prefixFalseCopyTime.eval n = 2 * n + 4 := by
  simp [prefixFalseCopyTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_ofNat]

/-- `false :: encodePair` is poly time on the `encodePair` domain; equals
`decodePairResult ∘ encodePair`. -/
noncomputable def decodePairResult_on_encodePair_computableInPolyTime :
    TM2ComputableInPolyTime encodePair idBitEnc
      (fun p => decodePairResult (encodePair p)) where
  tm := prefixFalseCopyComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := prefixFalseCopyTime
  outputsFun p := by
    change TM2OutputsInTime prefixFalseCopyComputer (List.map id (encodePair p))
      (some (List.map id (idBitEnc (decodePairResult (encodePair p)))))
      (prefixFalseCopyTime.eval (encodePair p).length)
    simp only [idBitEnc, List.map_id, id_eq, decodePairResult_encodePair,
      prefixFalseCopyTime_eval]
    exact prefixFalseCopy_evals (encodePair p)

/-- Same TM as computing `fun s => false :: s` under identity encodings. -/
noncomputable def prefixFalseCopyComputableInPolyTime :
    TM2ComputableInPolyTime idBitEnc idBitEnc (fun s => false :: s) where
  tm := prefixFalseCopyComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := prefixFalseCopyTime
  outputsFun s := by
    change TM2OutputsInTime prefixFalseCopyComputer (List.map id (idBitEnc s))
      (some (List.map id (idBitEnc (false :: s))))
      (prefixFalseCopyTime.eval (idBitEnc s).length)
    simp only [idBitEnc, List.map_id, id_eq, prefixFalseCopyTime_eval]
    exact prefixFalseCopy_evals s

/-! ## Constant singleton `[true]` TM (decodePairResult none branch) -/

inductive ConstTrueStack where
  | inp | out
  deriving DecidableEq, Repr

instance : Fintype ConstTrueStack where
  elems := {.inp, .out}
  complete s := by cases s <;> simp

inductive ConstTrueLabel where
  | clear | write
  deriving DecidableEq, Repr

instance : Fintype ConstTrueLabel where
  elems := {.clear, .write}
  complete s := by cases s <;> simp

/-- Clear input, then push `true` and halt. Step count `n + 2`. -/
def constTrueListComputer : FinTM2 where
  K := ConstTrueStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := ConstTrueLabel
  main := .clear
  σ := Bool
  initialState := false
  m
    | .clear =>
        pop ConstTrueStack.inp (fun _ o => decide (o = none)) <|
          branch id
            (goto fun _ => ConstTrueLabel.write)
            (goto fun _ => ConstTrueLabel.clear)
    | .write =>
        load (fun _ => false) <|
          push ConstTrueStack.out (fun _ => true) TM2.Stmt.halt

def constTrueStk (inp out : List Bool) : ConstTrueStack → List Bool
  | .inp => inp
  | .out => out

def constTrueCfg (l : Option ConstTrueLabel) (v : Bool) (inp out : List Bool) :
    constTrueListComputer.Cfg :=
  ⟨l, v, constTrueStk inp out⟩

theorem constTrue_step_clear_cons (x : Bool) (xs out : List Bool) :
    TM2.step constTrueListComputer.m
      (constTrueCfg (some .clear) false (x :: xs) out) =
      some (constTrueCfg (some .clear) false xs out) := by
  simp [constTrueListComputer, constTrueCfg, constTrueStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ConstTrueLabel.clear, false, stk⟩ : constTrueListComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, constTrueStk]

theorem constTrue_step_clear_nil (out : List Bool) :
    TM2.step constTrueListComputer.m
      (constTrueCfg (some .clear) false [] out) =
      some (constTrueCfg (some .write) true [] out) := by
  simp [constTrueListComputer, constTrueCfg, constTrueStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ConstTrueLabel.write, true, stk⟩ : constTrueListComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, constTrueStk]

theorem constTrue_step_write (inp out : List Bool) :
    TM2.step constTrueListComputer.m
      (constTrueCfg (some .write) true inp out) =
      some (constTrueCfg none false inp (true :: out)) := by
  simp [constTrueListComputer, constTrueCfg, constTrueStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option ConstTrueLabel), false, stk⟩ : constTrueListComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, constTrueStk]

theorem constTrueList_initList (s : List Bool) :
    initList constTrueListComputer s = constTrueCfg (some .clear) false s [] := by
  refine congrArg (fun stk =>
      (⟨some ConstTrueLabel.clear, false, stk⟩ : constTrueListComputer.Cfg)) ?_
  funext k; cases k <;> simp [constTrueListComputer, constTrueStk]

theorem constTrueList_haltList :
    haltList constTrueListComputer [true] = constTrueCfg none false [] [true] := by
  refine congrArg (fun stk =>
      (⟨(none : Option ConstTrueLabel), false, stk⟩ : constTrueListComputer.Cfg)) ?_
  funext k; cases k <;> simp [constTrueListComputer, constTrueStk]

def constTrue_evals_clear_one (x : Bool) (xs out : List Bool) :
    EvalsToInTime constTrueListComputer.step
      (constTrueCfg (some .clear) false (x :: xs) out)
      (some (constTrueCfg (some .clear) false xs out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (constTrueCfg (some .clear) false (x :: xs) out)).bind
        constTrueListComputer.step =
      some (constTrueCfg (some .clear) false xs out)
    simp only [FinTM2.step]
    exact constTrue_step_clear_cons x xs out

def constTrue_evals_nil :
    EvalsToInTime constTrueListComputer.step
      (constTrueCfg (some .clear) false [] [])
      (some (constTrueCfg none false [] [true])) 2 where
  steps := 2
  steps_le_m := by decide
  evals_in_steps := by
    change ((some (constTrueCfg (some .clear) false [] [])).bind
        constTrueListComputer.step).bind constTrueListComputer.step =
      some (constTrueCfg none false [] [true])
    simp only [FinTM2.step]
    change ((TM2.step constTrueListComputer.m
        (constTrueCfg (some .clear) false [] [])).bind
        (TM2.step constTrueListComputer.m)) =
      some (constTrueCfg none false [] [true])
    rw [constTrue_step_clear_nil]
    change TM2.step constTrueListComputer.m
        (constTrueCfg (some .write) true [] []) =
      some (constTrueCfg none false [] [true])
    exact constTrue_step_write [] []

noncomputable def constTrueList_evals (s : List Bool) :
    TM2OutputsInTime constTrueListComputer s (some [true]) (s.length + 2) := by
  induction s with
  | nil =>
      have h : EvalsToInTime constTrueListComputer.step
          (initList constTrueListComputer [])
          (some (haltList constTrueListComputer [true])) 2 := by
        rw [constTrueList_initList, constTrueList_haltList]
        simpa using constTrue_evals_nil
      exact h
  | cons x xs ih =>
      have h1 := constTrue_evals_clear_one x xs []
      have h1' : EvalsToInTime constTrueListComputer.step
          (initList constTrueListComputer (x :: xs))
          (some (initList constTrueListComputer xs)) 1 := by
        rw [constTrueList_initList, constTrueList_initList]
        exact h1
      have h := EvalsToInTime.trans constTrueListComputer.step 1 (xs.length + 2)
        _ _ _ h1' ih
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

noncomputable def constTrueListTime : Polynomial ℕ := Polynomial.X + 2

theorem constTrueListTime_eval (n : ℕ) : constTrueListTime.eval n = n + 2 := by
  simp [constTrueListTime, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]

/-- Constant `[true]` function is poly time (decodePairResult none branch). -/
noncomputable def constTrueListComputableInPolyTime :
    TM2ComputableInPolyTime idBitEnc idBitEnc (fun _ : List Bool => [true]) where
  tm := constTrueListComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := constTrueListTime
  outputsFun s := by
    change TM2OutputsInTime constTrueListComputer (List.map id (idBitEnc s))
      (some (List.map id (idBitEnc [true])))
      (constTrueListTime.eval (idBitEnc s).length)
    simp only [idBitEnc, List.map_id, id_eq, constTrueListTime_eval]
    exact constTrueList_evals s

/-- Same TM as an InP witness, reindexed to pairs under the abstract first
projection encoding `fun pw => pw.1` (not yet `encodePair`). Composition of
`projFirstComputableInPolyTime` with this witness is the remaining gap for
`InP_implies_InNP`. -/
noncomputable def ignoreWitness_under_fst {χ : List Bool → Bool}
    (h : TM2ComputableInPolyTime idBitEnc bitEnc χ) :
    TM2ComputableInPolyTime (fun pw : List Bool × List Bool => pw.1) bitEnc
      (fun pw => χ pw.1) where
  tm := h.tm
  inputAlphabet := h.inputAlphabet
  outputAlphabet := h.outputAlphabet
  time := h.time
  outputsFun pw := h.outputsFun pw.1

/-- Semantic half of P ⊆ NP: ignoreWitness with zero length witnesses matches L. -/
theorem ignoreWitness_zero_correct (L : Language) (χ : List Bool → Bool)
    (hdec : ∀ x, χ x = true ↔ L x) (x : List Bool) :
    L x ↔ ∃ w, w.length ≤ zeroWitnessBound.eval x.length ∧ ignoreWitness χ x w = true := by
  constructor
  · intro hx
    refine ⟨[], empty_witness_length_bound x, ?_⟩
    simp [ignoreWitness, hdec, hx]
  · intro ⟨w, hw, hV⟩
    have : χ x = true := by simpa [ignoreWitness] using hV
    exact (hdec x).mp this

/-! ## Local TM2 statement surgery (toward poly time composition)

Mathlib leaves `TM2ComputableInPolyTime.comp` as `proof_wanted`. The bridge only
needs the special case: first `encodePair → idBitEnc` (projection), then
`idBitEnc → bitEnc` (an InP characteristic). The helpers below remap labels,
replace `halt` by a goto, and lift stack indices through `Sum`, which is the
skeleton of a sequential product machine. -/

/-- Recursively remap goto labels and replace `halt` by `goto onHalt`. -/
def stmtRemap {K : Type} {Γ : K → Type} {Λ Λ' σ : Type}
    (mapLabel : Λ → Λ') (onHalt : σ → Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f q => .push k f (stmtRemap mapLabel onHalt q)
  | .peek k f q => .peek k f (stmtRemap mapLabel onHalt q)
  | .pop k f q => .pop k f (stmtRemap mapLabel onHalt q)
  | .load f q => .load f (stmtRemap mapLabel onHalt q)
  | .branch p q₁ q₂ =>
      .branch p (stmtRemap mapLabel onHalt q₁) (stmtRemap mapLabel onHalt q₂)
  | .goto f => .goto (fun s => mapLabel (f s))
  | .halt => .goto onHalt

/-- Stack index type for the sequential product: first machine stacks, one aux
stack (needed because a single out→in transfer reverses list order), then second
machine stacks. -/
abbrev CompK (K₁ K₂ : Type) := K₁ ⊕ Unit ⊕ K₂

/-- Alphabet family on `CompK`: aux stack carries the middle alphabet `βΓ`. -/
def CompΓ {K₁ K₂ : Type} (Γ₁ : K₁ → Type) (βΓ : Type) (Γ₂ : K₂ → Type) :
    CompK K₁ K₂ → Type :=
  Sum.elim Γ₁ (Sum.elim (fun _ : Unit => βΓ) Γ₂)

/-- Lift stack indices into the first summand of `CompK`. -/
def stmtLiftFirst {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {βΓ : Type} {Γ₂ : K₂ → Type}
    {Λ σ : Type} :
    TM2.Stmt Γ₁ Λ σ → TM2.Stmt (CompΓ Γ₁ βΓ Γ₂) Λ σ
  | .push k f q => .push (Sum.inl k) f (stmtLiftFirst q)
  | .peek k f q => .peek (Sum.inl k) f (stmtLiftFirst q)
  | .pop k f q => .pop (Sum.inl k) f (stmtLiftFirst q)
  | .load f q => .load f (stmtLiftFirst q)
  | .branch p q₁ q₂ => .branch p (stmtLiftFirst q₁) (stmtLiftFirst q₂)
  | .goto f => .goto f
  | .halt => .halt

/-- Lift stack indices into the second machine summand of `CompK`. -/
def stmtLiftSecond {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {βΓ : Type} {Γ₂ : K₂ → Type}
    {Λ σ : Type} :
    TM2.Stmt Γ₂ Λ σ → TM2.Stmt (CompΓ Γ₁ βΓ Γ₂) Λ σ
  | .push k f q => .push (Sum.inr (Sum.inr k)) f (stmtLiftSecond q)
  | .peek k f q => .peek (Sum.inr (Sum.inr k)) f (stmtLiftSecond q)
  | .pop k f q => .pop (Sum.inr (Sum.inr k)) f (stmtLiftSecond q)
  | .load f q => .load f (stmtLiftSecond q)
  | .branch p q₁ q₂ => .branch p (stmtLiftSecond q₁) (stmtLiftSecond q₂)
  | .goto f => .goto f
  | .halt => .halt

/-- Legacy two-summand inl lift (retained for accepted API continuity). -/
def stmtLiftInl {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {Γ₂ : K₂ → Type} {Λ σ : Type} :
    TM2.Stmt Γ₁ Λ σ → TM2.Stmt (Sum.elim Γ₁ Γ₂) Λ σ
  | .push k f q => .push (Sum.inl k) f (stmtLiftInl q)
  | .peek k f q => .peek (Sum.inl k) f (stmtLiftInl q)
  | .pop k f q => .pop (Sum.inl k) f (stmtLiftInl q)
  | .load f q => .load f (stmtLiftInl q)
  | .branch p q₁ q₂ => .branch p (stmtLiftInl q₁) (stmtLiftInl q₂)
  | .goto f => .goto f
  | .halt => .halt

/-- Legacy two-summand inr lift (retained for accepted API continuity). -/
def stmtLiftInr {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {Γ₂ : K₂ → Type} {Λ σ : Type} :
    TM2.Stmt Γ₂ Λ σ → TM2.Stmt (Sum.elim Γ₁ Γ₂) Λ σ
  | .push k f q => .push (Sum.inr k) f (stmtLiftInr q)
  | .peek k f q => .peek (Sum.inr k) f (stmtLiftInr q)
  | .pop k f q => .pop (Sum.inr k) f (stmtLiftInr q)
  | .load f q => .load f (stmtLiftInr q)
  | .branch p q₁ q₂ => .branch p (stmtLiftInr q₁) (stmtLiftInr q₂)
  | .goto f => .goto f
  | .halt => .halt

/-- Labels: first phase, out→aux copy, aux→in copy, second phase.
Two copy legs restore list order (each leg reverses). -/
inductive CompLabel (Λ₁ Λ₂ : Type) where
  | first : Λ₁ → CompLabel Λ₁ Λ₂
  | copyToAuxPop : CompLabel Λ₁ Λ₂
  | copyToAuxPush : CompLabel Λ₁ Λ₂
  | copyToInPop : CompLabel Λ₁ Λ₂
  | copyToInPush : CompLabel Λ₁ Λ₂
  | second : Λ₂ → CompLabel Λ₁ Λ₂
  deriving Repr

/-- Pack composition labels as a sum for Fintype and DecidableEq. -/
def equivCompLabel (Λ₁ Λ₂ : Type) :
    CompLabel Λ₁ Λ₂ ≃ Λ₁ ⊕ Fin 4 ⊕ Λ₂ where
  toFun
    | .first l => .inl l
    | .copyToAuxPop => .inr (.inl 0)
    | .copyToAuxPush => .inr (.inl 1)
    | .copyToInPop => .inr (.inl 2)
    | .copyToInPush => .inr (.inl 3)
    | .second l => .inr (.inr l)
  invFun
    | .inl l => .first l
    | .inr (.inl 0) => .copyToAuxPop
    | .inr (.inl 1) => .copyToAuxPush
    | .inr (.inl 2) => .copyToInPop
    | .inr (.inl 3) => .copyToInPush
    | .inr (.inr l) => .second l
  left_inv
    | .first _ | .copyToAuxPop | .copyToAuxPush
    | .copyToInPop | .copyToInPush | .second _ => rfl
  right_inv
    | .inl _ | .inr (.inl 0) | .inr (.inl 1)
    | .inr (.inl 2) | .inr (.inl 3) | .inr (.inr _) => rfl

/-- Fintype instance for composition labels via the sum encoding. -/
instance {Λ₁ Λ₂ : Type} [Fintype Λ₁] [Fintype Λ₂] : Fintype (CompLabel Λ₁ Λ₂) :=
  Fintype.ofEquiv _ (equivCompLabel Λ₁ Λ₂).symm

/-- Decidable equality for composition labels via the sum encoding. -/
instance {Λ₁ Λ₂ : Type} [DecidableEq Λ₁] [DecidableEq Λ₂] :
    DecidableEq (CompLabel Λ₁ Λ₂) :=
  Equiv.decidableEq (equivCompLabel Λ₁ Λ₂)

/-- Internal state of the sequential product: pair of component states plus an
optional buffered middle alphabet symbol during the copy phase. -/
abbrev Compσ (σ₁ σ₂ βΓ : Type) := σ₁ × σ₂ × Option βΓ

/-- Lift a statement on σ₁ to the product state `Compσ`, acting on the first
component only. -/
def stmtLiftState₁ {K : Type} {Γ : K → Type} {Λ σ₁ σ₂ βΓ : Type} :
    TM2.Stmt Γ Λ σ₁ → TM2.Stmt Γ Λ (Compσ σ₁ σ₂ βΓ)
  | .push k f q => .push k (fun st => f st.1) (stmtLiftState₁ q)
  | .peek k f q =>
      .peek k (fun st o => (f st.1 o, st.2.1, st.2.2)) (stmtLiftState₁ q)
  | .pop k f q =>
      .pop k (fun st o => (f st.1 o, st.2.1, st.2.2)) (stmtLiftState₁ q)
  | .load f q => .load (fun st => (f st.1, st.2.1, st.2.2)) (stmtLiftState₁ q)
  | .branch p q₁ q₂ =>
      .branch (fun st => p st.1) (stmtLiftState₁ q₁) (stmtLiftState₁ q₂)
  | .goto f => .goto (fun st => f st.1)
  | .halt => .halt

/-- Lift a statement on σ₂ to the product state `Compσ`, acting on the second
component only. -/
def stmtLiftState₂ {K : Type} {Γ : K → Type} {Λ σ₁ σ₂ βΓ : Type} :
    TM2.Stmt Γ Λ σ₂ → TM2.Stmt Γ Λ (Compσ σ₁ σ₂ βΓ)
  | .push k f q => .push k (fun st => f st.2.1) (stmtLiftState₂ q)
  | .peek k f q =>
      .peek k (fun st o => (st.1, f st.2.1 o, st.2.2)) (stmtLiftState₂ q)
  | .pop k f q =>
      .pop k (fun st o => (st.1, f st.2.1 o, st.2.2)) (stmtLiftState₂ q)
  | .load f q => .load (fun st => (st.1, f st.2.1, st.2.2)) (stmtLiftState₂ q)
  | .branch p q₁ q₂ =>
      .branch (fun st => p st.2.1) (stmtLiftState₂ q₁) (stmtLiftState₂ q₂)
  | .goto f => .goto (fun st => f st.2.1)
  | .halt => .halt

/-- Aux stack index. -/
def compAux {K₁ K₂ : Type} : CompK K₁ K₂ := Sum.inr (Sum.inl ())

/-- Pop from first output into buffer; empty out jumps to aux→in copy. -/
def copyToAuxPopStmt {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {βΓ : Type} {Γ₂ : K₂ → Type}
    {Λ₁ Λ₂ σ₁ σ₂ : Type} [Inhabited βΓ] [DecidableEq βΓ]
    (kOut : K₁) (decodeOut : Γ₁ kOut → βΓ) :
    TM2.Stmt (CompΓ Γ₁ βΓ Γ₂) (CompLabel Λ₁ Λ₂) (Compσ σ₁ σ₂ βΓ) :=
  .pop (Sum.inl kOut)
    (fun st o =>
      match o with
      | none => (st.1, st.2.1, none)
      | some x => (st.1, st.2.1, some (decodeOut x))) <|
    .branch (fun st => decide (st.2.2 = none))
      (.goto fun _ => CompLabel.copyToInPop)
      (.goto fun _ => CompLabel.copyToAuxPush)

/-- Push buffered symbol onto aux and loop out→aux. -/
def copyToAuxPushStmt {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {βΓ : Type} {Γ₂ : K₂ → Type}
    {Λ₁ Λ₂ σ₁ σ₂ : Type} [Inhabited βΓ] :
    TM2.Stmt (CompΓ Γ₁ βΓ Γ₂) (CompLabel Λ₁ Λ₂) (Compσ σ₁ σ₂ βΓ) :=
  .push (compAux : CompK K₁ K₂) (fun st => st.2.2.getD default) <|
    .load (fun st => (st.1, st.2.1, none)) <|
      .goto fun _ => CompLabel.copyToAuxPop

/-- Pop from aux into buffer; empty aux jumps to second machine main. -/
def copyToInPopStmt {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {βΓ : Type} {Γ₂ : K₂ → Type}
    {Λ₁ Λ₂ σ₁ σ₂ : Type} [Inhabited βΓ] [DecidableEq βΓ]
    (secondMain : Λ₂) :
    TM2.Stmt (CompΓ Γ₁ βΓ Γ₂) (CompLabel Λ₁ Λ₂) (Compσ σ₁ σ₂ βΓ) :=
  .pop (compAux : CompK K₁ K₂)
    (fun st o =>
      match o with
      | none => (st.1, st.2.1, none)
      | some x => (st.1, st.2.1, some x)) <|
    .branch (fun st => decide (st.2.2 = none))
      (.goto fun _ => CompLabel.second secondMain)
      (.goto fun _ => CompLabel.copyToInPush)

/-- Push buffered symbol onto second input and loop aux→in. -/
def copyToInPushStmt {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {βΓ : Type} {Γ₂ : K₂ → Type}
    {Λ₁ Λ₂ σ₁ σ₂ : Type} [Inhabited βΓ]
    (kIn : K₂) (encodeIn : βΓ → Γ₂ kIn) :
    TM2.Stmt (CompΓ Γ₁ βΓ Γ₂) (CompLabel Λ₁ Λ₂) (Compσ σ₁ σ₂ βΓ) :=
  .push (Sum.inr (Sum.inr kIn)) (fun st => encodeIn (st.2.2.getD default)) <|
    .load (fun st => (st.1, st.2.1, none)) <|
      .goto fun _ => CompLabel.copyToInPop

/-- First-phase program: lift stacks and state, remap into `CompLabel.first`,
send former `halt` to `copyToAuxPop`. -/
def firstPhaseStmt {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {βΓ : Type} {Γ₂ : K₂ → Type}
    {Λ₁ Λ₂ σ₁ σ₂ : Type}
    (q : TM2.Stmt Γ₁ Λ₁ σ₁) :
    TM2.Stmt (CompΓ Γ₁ βΓ Γ₂) (CompLabel Λ₁ Λ₂) (Compσ σ₁ σ₂ βΓ) :=
  stmtRemap CompLabel.first (fun _ => CompLabel.copyToAuxPop)
    (stmtLiftFirst (stmtLiftState₁ q : TM2.Stmt Γ₁ Λ₁ (Compσ σ₁ σ₂ βΓ)))

/-- Remap goto labels only; leave `halt` as `halt`. -/
def stmtRemapGoto {K : Type} {Γ : K → Type} {Λ Λ' σ : Type}
    (mapLabel : Λ → Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f q => .push k f (stmtRemapGoto mapLabel q)
  | .peek k f q => .peek k f (stmtRemapGoto mapLabel q)
  | .pop k f q => .pop k f (stmtRemapGoto mapLabel q)
  | .load f q => .load f (stmtRemapGoto mapLabel q)
  | .branch p q₁ q₂ =>
      .branch p (stmtRemapGoto mapLabel q₁) (stmtRemapGoto mapLabel q₂)
  | .goto f => .goto (fun s => mapLabel (f s))
  | .halt => .halt

/-- Second-phase program: lift stacks and state, remap into `CompLabel.second`,
preserve genuine `halt`. -/
def secondPhaseStmt {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {βΓ : Type} {Γ₂ : K₂ → Type}
    {Λ₁ Λ₂ σ₁ σ₂ : Type}
    (q : TM2.Stmt Γ₂ Λ₂ σ₂) :
    TM2.Stmt (CompΓ Γ₁ βΓ Γ₂) (CompLabel Λ₁ Λ₂) (Compσ σ₁ σ₂ βΓ) :=
  stmtRemapGoto CompLabel.second
    (stmtLiftSecond (stmtLiftState₂ q : TM2.Stmt Γ₂ Λ₂ (Compσ σ₁ σ₂ βΓ)))

/-- Sequential product FinTM2: run `tm1`, copy out→aux→in (order preserving),
then run `tm2`. -/
noncomputable def seqCompComputer {βΓ : Type} [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀) :
    FinTM2 := by
  letI : Fintype tm1.K := tm1.kFin
  letI : Fintype tm2.K := tm2.kFin
  letI : DecidableEq tm1.K := tm1.kDecidableEq
  letI : DecidableEq tm2.K := tm2.kDecidableEq
  letI : Fintype tm1.Λ := tm1.ΛFin
  letI : Fintype tm2.Λ := tm2.ΛFin
  letI : Fintype tm1.σ := tm1.σFin
  letI : Fintype tm2.σ := tm2.σFin
  letI : Fintype (CompΓ tm1.Γ βΓ tm2.Γ (Sum.inl tm1.k₀)) := by
    change Fintype (tm1.Γ tm1.k₀)
    exact tm1.Γk₀Fin
  exact
    { K := CompK tm1.K tm2.K
      k₀ := Sum.inl tm1.k₀
      k₁ := Sum.inr (Sum.inr tm2.k₁)
      Γ := CompΓ tm1.Γ βΓ tm2.Γ
      Λ := CompLabel tm1.Λ tm2.Λ
      main := CompLabel.first tm1.main
      σ := Compσ tm1.σ tm2.σ βΓ
      initialState := (tm1.initialState, tm2.initialState, none)
      m
        | .first l => firstPhaseStmt (tm1.m l)
        | .copyToAuxPop => copyToAuxPopStmt tm1.k₁ decodeOut
        | .copyToAuxPush => copyToAuxPushStmt
        | .copyToInPop => copyToInPopStmt tm2.main
        | .copyToInPush => copyToInPushStmt tm2.k₀ encodeIn
        | .second l => secondPhaseStmt (tm2.m l) }

/-- Deprecated names kept as abbreviations so older session notes still resolve. -/
abbrev copyPopStmt {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {βΓ : Type} {Γ₂ : K₂ → Type}
    {Λ₁ Λ₂ σ₁ σ₂ : Type} [Inhabited βΓ] [DecidableEq βΓ]
    (kOut : K₁) (decodeOut : Γ₁ kOut → βΓ) (_secondMain : Λ₂) :
    TM2.Stmt (CompΓ Γ₁ βΓ Γ₂) (CompLabel Λ₁ Λ₂) (Compσ σ₁ σ₂ βΓ) :=
  copyToAuxPopStmt kOut decodeOut

abbrev copyPushStmt {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {βΓ : Type} {Γ₂ : K₂ → Type}
    {Λ₁ Λ₂ σ₁ σ₂ : Type} [Inhabited βΓ] :
    TM2.Stmt (CompΓ Γ₁ βΓ Γ₂) (CompLabel Λ₁ Λ₂) (Compσ σ₁ σ₂ βΓ) :=
  copyToAuxPushStmt

/-! ## Local Bool composition lemmas (accepted special cases)

Full `TM2ComputableInPolyTime.comp` remains open. The constant-right case is the
poly time identity `(fun _ => b) ∘ f = fun _ => b`, realized by running
`constBitComputer` directly on the first encoding (no product machine needed).
This yields `encodePair → bitEnc` constant maps and therefore NP nonvacuity. -/

/-- Constant bit function under an arbitrary `List Bool` encoding. -/
noncomputable def constBit_of_encoding {α : Type} (ea : α → List Bool) (b : Bool) :
    TM2ComputableInPolyTime ea bitEnc (fun _ : α => b) where
  tm := constBitComputer b
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := constBitTime
  outputsFun a := by
    change TM2OutputsInTime (constBitComputer b) (List.map id (ea a))
      (some (List.map id (bitEnc b))) (constBitTime.eval (ea a).length)
    simp only [bitEnc, List.map_id, constBitTime_eval]
    exact constBitComputer_evals b (ea a)

/-- Right-constant local composition: `(fun _ => b) ∘ f` is poly time whenever the
input encoding lands in `List Bool`, by ignoring `f` and clearing the encoded
input. -/
noncomputable def comp_const_right {α : Type} {ea : α → List Bool}
    {f : α → List Bool} (b : Bool)
    (_hf : TM2ComputableInPolyTime ea idBitEnc f) :
    TM2ComputableInPolyTime ea bitEnc (fun _ : α => b) :=
  constBit_of_encoding ea b

/-- Constant characteristic under `encodePair` (pair projection then constant). -/
noncomputable def constBit_encodePair (b : Bool) :
    TM2ComputableInPolyTime encodePair bitEnc (fun _ : List Bool × List Bool => b) :=
  constBit_of_encoding encodePair b

/-- `ignoreWitness` for a constant characteristic is poly time on `encodePair`. -/
noncomputable def ignoreWitness_const_encodePair (b : Bool) :
    TM2ComputableInPolyTime encodePair bitEnc
      (fun pw => ignoreWitness (fun _ => b) pw.1 pw.2) := by
  simpa [ignoreWitness] using constBit_encodePair b

/-- Empty language is in NP via the constant false verifier. -/
theorem emptyLanguage_in_NP : InNP emptyLanguage :=
  ⟨zeroWitnessBound, ignoreWitness (fun _ => false),
    ignoreWitness_const_encodePair false,
    ignoreWitness_zero_correct emptyLanguage (fun _ => false) constFalse_decides_empty⟩

/-- Full language is in NP via the constant true verifier. -/
theorem fullLanguage_in_NP : InNP fullLanguage :=
  ⟨zeroWitnessBound, ignoreWitness (fun _ => true),
    ignoreWitness_const_encodePair true,
    ignoreWitness_zero_correct fullLanguage (fun _ => true) constTrue_decides_full⟩

/-- Polynomial bound helper: `p + q` evaluates as a sum. -/
theorem poly_add_eval (p q : Polynomial ℕ) (n : ℕ) :
    (p + q).eval n = p.eval n + q.eval n :=
  Polynomial.eval_add

/-- Time bound for sequential composition: first run, two order preserving copy
legs (each symbol costs 2 steps, plus one empty pop per leg), then second run.
Bound uses `4 * (X + 1)` which dominates `2 * (n + 1) + 2 * (n + 1)`. -/
noncomputable def seqCompTime (p q : Polynomial ℕ) : Polynomial ℕ :=
  p + 4 * (Polynomial.X + 1) + q

theorem seqCompTime_eval (p q : Polynomial ℕ) (n : ℕ) :
    (seqCompTime p q).eval n = p.eval n + 4 * (n + 1) + q.eval n := by
  simp [seqCompTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_ofNat]

/-! ## Sequential simulation helpers (accepted scaffolding)

Configuration lifts and copy phase dynamics for `seqCompComputer`. Full
`outputsFun` for arbitrary first or second machines remains Frontier; these
lemmas pin the order preserving copy and the stack layout. -/

/-- Product stack from first stacks, aux list, and second stacks. -/
def seqCompStk {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {βΓ : Type} {Γ₂ : K₂ → Type}
    (S₁ : ∀ k, List (Γ₁ k)) (aux : List βΓ) (S₂ : ∀ k, List (Γ₂ k)) :
    ∀ k : CompK K₁ K₂, List (CompΓ Γ₁ βΓ Γ₂ k)
  | .inl k => S₁ k
  | .inr (.inl _) => aux
  | .inr (.inr k) => S₂ k

/-- Configuration helper for a `seqCompComputer` run. -/
def seqCompCfg {βΓ : Type} [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (l : Option (CompLabel tm1.Λ tm2.Λ))
    (v : Compσ tm1.σ tm2.σ βΓ)
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k)) :
    (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).Cfg :=
  ⟨l, v, seqCompStk S₁ aux S₂⟩

/-- Empty stack family. -/
def emptyStk {K : Type} {Γ : K → Type} : ∀ k : K, List (Γ k) := fun _ => []

/-- DecidableEq on composition stack indices. -/
instance instDecidableEqCompK {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] :
    DecidableEq (CompK K₁ K₂) :=
  inferInstanceAs (DecidableEq (K₁ ⊕ Unit ⊕ K₂))

/-- Update first-machine stack `k` inside a product stack family. -/
theorem seqCompStk_update_first {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂]
    {Γ₁ : K₁ → Type} {βΓ : Type} {Γ₂ : K₂ → Type}
    (S₁ : ∀ k, List (Γ₁ k)) (aux : List βΓ) (S₂ : ∀ k, List (Γ₂ k))
    (k : K₁) (v : List (Γ₁ k)) :
    Function.update (seqCompStk S₁ aux S₂) (Sum.inl k) v =
      seqCompStk (Function.update S₁ k v) aux S₂ := by
  funext t
  cases t with
  | inl k' =>
      by_cases h : k' = k
      · subst h; simp [seqCompStk, Function.update]
      · simp [seqCompStk, Function.update, h]
  | inr t =>
      cases t with
      | inl u => cases u; simp [seqCompStk, Function.update]
      | inr k' => simp [seqCompStk, Function.update]

/-- Update aux stack inside a product stack family. -/
theorem seqCompStk_update_aux {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂]
    {Γ₁ : K₁ → Type} {βΓ : Type} {Γ₂ : K₂ → Type}
    (S₁ : ∀ k, List (Γ₁ k)) (aux : List βΓ) (S₂ : ∀ k, List (Γ₂ k))
    (v : List βΓ) :
    Function.update (seqCompStk S₁ aux S₂) (Sum.inr (Sum.inl ())) v =
      seqCompStk S₁ v S₂ := by
  funext t
  cases t with
  | inl k' => simp [seqCompStk, Function.update]
  | inr t =>
      cases t with
      | inl u => cases u; simp [seqCompStk, Function.update]
      | inr k' => simp [seqCompStk, Function.update]

/-- Update second-machine stack `k` inside a product stack family. -/
theorem seqCompStk_update_second {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂]
    {Γ₁ : K₁ → Type} {βΓ : Type} {Γ₂ : K₂ → Type}
    (S₁ : ∀ k, List (Γ₁ k)) (aux : List βΓ) (S₂ : ∀ k, List (Γ₂ k))
    (k : K₂) (v : List (Γ₂ k)) :
    Function.update (seqCompStk S₁ aux S₂) (Sum.inr (Sum.inr k)) v =
      seqCompStk S₁ aux (Function.update S₂ k v) := by
  funext t
  cases t with
  | inl k' => simp [seqCompStk, Function.update]
  | inr t =>
      cases t with
      | inl u => cases u; simp [seqCompStk, Function.update]
      | inr k' =>
          by_cases h : k' = k
          · subst h; simp [seqCompStk, Function.update]
          · simp [seqCompStk, Function.update, h]

/-- Copy bound: each of two legs costs `2 * length + 1` steps. -/
theorem seqComp_copy_steps_bound (n : ℕ) :
    2 * (2 * n + 1) ≤ 4 * (n + 1) := by omega

/-- Push step of out→aux: buffered symbol is consed onto aux; return to pop.
No first or second stack `Function.update`, so the residual is instance clean. -/
theorem seqComp_step_copyToAuxPush {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₁ : tm1.σ) (σ₂ : tm2.σ)
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k))
    (b : βΓ) :
    TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m
      (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPush)
        (σ₁, σ₂, some b) S₁ aux S₂) =
      some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPop)
        (σ₁, σ₂, none) S₁ (b :: aux) S₂) := by
  simp [seqCompComputer, seqCompCfg, seqCompStk, copyToAuxPushStmt, TM2.step,
    TM2.stepAux, compAux]
  refine congrArg some ?_
  refine congrArg (fun stk =>
    (⟨some CompLabel.copyToAuxPop, (σ₁, σ₂, (none : Option βΓ)), stk⟩ :
      (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).Cfg)) ?_
  funext t
  cases t with
  | inl k' => simp [seqCompStk, Function.update]
  | inr t =>
      cases t with
      | inl u =>
          cases u
          -- Aux coordinate: update writes b :: aux.
          change b :: aux = b :: aux
          rfl
      | inr k' => simp [seqCompStk, Function.update]

/-- Empty aux at copyToInPop jumps to the second machine main label. -/
theorem seqComp_step_copyToInPop_nil {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₁ : tm1.σ) (σ₂ : tm2.σ)
    (S₁ : ∀ k, List (tm1.Γ k)) (S₂ : ∀ k, List (tm2.Γ k)) :
    TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m
      (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
        (σ₁, σ₂, none) S₁ [] S₂) =
      some (seqCompCfg tm1 tm2 decodeOut encodeIn (some (.second tm2.main))
        (σ₁, σ₂, none) S₁ [] S₂) := by
  simp [seqCompComputer, seqCompCfg, seqCompStk, copyToInPopStmt, TM2.step,
    TM2.stepAux, compAux]
  refine congrArg some ?_
  refine congrArg (fun stk =>
    (⟨some (CompLabel.second tm2.main), (σ₁, σ₂, (none : Option βΓ)), stk⟩ :
      (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).Cfg)) ?_
  funext t
  cases t with
  | inl k' => simp [seqCompStk, Function.update]
  | inr t =>
      cases t with
      | inl u =>
          cases u
          -- Empty pop updates aux to [].tail.
          change [].tail = []
          rfl
      | inr k' => simp [seqCompStk, Function.update]

/-- Pop step of aux→in: nonempty aux head enters the buffer and jumps to push. -/
theorem seqComp_step_copyToInPop_cons {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₁ : tm1.σ) (σ₂ : tm2.σ)
    (S₁ : ∀ k, List (tm1.Γ k)) (b : βΓ) (bs : List βΓ)
    (S₂ : ∀ k, List (tm2.Γ k)) :
    TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m
      (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
        (σ₁, σ₂, none) S₁ (b :: bs) S₂) =
      some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPush)
        (σ₁, σ₂, some b) S₁ bs S₂) := by
  simp [seqCompComputer, seqCompCfg, seqCompStk, copyToInPopStmt, TM2.step,
    TM2.stepAux, compAux]
  refine congrArg some ?_
  refine congrArg (fun stk =>
    (⟨some CompLabel.copyToInPush, (σ₁, σ₂, some b), stk⟩ :
      (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).Cfg)) ?_
  funext t
  cases t with
  | inl k' => simp [seqCompStk, Function.update]
  | inr t =>
      cases t with
      | inl u =>
          cases u
          change (b :: bs).tail = bs
          rfl
      | inr k' => simp [seqCompStk, Function.update]

/-- After empty pop of `k`, the stack family is unchanged when that stack is already `[]`. -/
theorem update_self_of_eq_nil {K : Type} [DecidableEq K] {Γ : K → Type}
    (S : ∀ k, List (Γ k)) (k : K) (h : S k = []) :
    Function.update S k [] = S := by
  funext k'
  by_cases hk : k' = k
  · subst hk; simp [Function.update, h]
  · simp [Function.update, hk]

/-- Pointwise: empty pop of first out stack leaves `seqCompStk` unchanged.
Uses `Function.update_self` so the ambient `FinTM2.kDecidableEq` instance matches. -/
theorem seqCompStk_update_first_nil_eq {βΓ : Type}
    (tm1 tm2 : FinTM2)
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k))
    [DecidableEq (CompK tm1.K tm2.K)]
    (hOut : S₁ tm1.k₁ = []) :
    Function.update (seqCompStk S₁ aux S₂) (Sum.inl tm1.k₁) [] =
      seqCompStk S₁ aux S₂ := by
  funext t
  by_cases ht : t = Sum.inl tm1.k₁
  · subst ht
    rw [Function.update_self]
    simpa [seqCompStk] using hOut.symm
  · rw [Function.update_of_ne ht]

/-- Pointwise: first out pop packages as `seqCompStk` of an updated first family. -/
theorem seqCompStk_update_first_eq {βΓ : Type}
    (tm1 tm2 : FinTM2)
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k))
    (xs : List (tm1.Γ tm1.k₁))
    [DecidableEq (CompK tm1.K tm2.K)]
    [DecidableEq tm1.K] :
    Function.update (seqCompStk S₁ aux S₂) (Sum.inl tm1.k₁) xs =
      seqCompStk (Function.update S₁ tm1.k₁ xs) aux S₂ := by
  funext t
  by_cases ht : t = Sum.inl tm1.k₁
  · subst ht
    rw [Function.update_self]
    simp [seqCompStk, Function.update]
  · rw [Function.update_of_ne ht]
    cases t with
    | inl k' =>
        have hk : ¬ k' = tm1.k₁ := by
          intro h; exact ht (by rw [h])
        simp [seqCompStk, Function.update, hk]
    | inr t =>
        cases t with
        | inl u => cases u; simp [seqCompStk]
        | inr k' => simp [seqCompStk]

/-- Pointwise: second input push packages as `seqCompStk` of an updated second family. -/
theorem seqCompStk_update_second_eq {βΓ : Type}
    (tm1 tm2 : FinTM2)
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k))
    (v : List (tm2.Γ tm2.k₀))
    [DecidableEq (CompK tm1.K tm2.K)]
    [DecidableEq tm2.K] :
    Function.update (seqCompStk S₁ aux S₂) (Sum.inr (Sum.inr tm2.k₀)) v =
      seqCompStk S₁ aux (Function.update S₂ tm2.k₀ v) := by
  funext t
  by_cases ht : t = Sum.inr (Sum.inr tm2.k₀)
  · subst ht
    rw [Function.update_self]
    simp [seqCompStk, Function.update]
  · rw [Function.update_of_ne ht]
    cases t with
    | inl k' => simp [seqCompStk]
    | inr t =>
        cases t with
        | inl u => cases u; simp [seqCompStk]
        | inr k' =>
            have hk : ¬ k' = tm2.k₀ := by
              intro h; exact ht (by rw [h])
            simp [seqCompStk, Function.update, hk]

/-- Empty out at `copyToAuxPop` jumps to aux→in without changing stacks. -/
theorem seqComp_step_copyToAuxPop_nil {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₁ : tm1.σ) (σ₂ : tm2.σ)
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k))
    (hOut : S₁ tm1.k₁ = []) :
    TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m
      (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPop)
        (σ₁, σ₂, none) S₁ aux S₂) =
      some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
        (σ₁, σ₂, none) S₁ aux S₂) := by
  letI : DecidableEq tm1.K := tm1.kDecidableEq
  letI : DecidableEq tm2.K := tm2.kDecidableEq
  -- Use the machine's own DecidableEq so `Function.update` instances unify.
  letI : DecidableEq (CompK tm1.K tm2.K) :=
    (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).kDecidableEq
  simp [seqCompComputer, seqCompCfg, seqCompStk, copyToAuxPopStmt, TM2.step,
    TM2.stepAux, hOut, List.head?]
  refine congrArg some ?_
  refine congrArg (fun stk =>
    (⟨some CompLabel.copyToInPop, (σ₁, σ₂, (none : Option βΓ)), stk⟩ :
      (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).Cfg)) ?_
  -- `[].tail` reduces to `[]`; empty update leaves the product stacks unchanged.
  simp only [List.tail]
  exact seqCompStk_update_first_nil_eq (βΓ := βΓ) tm1 tm2 S₁ aux S₂ hOut

/-- Nonempty out pop: buffer gets decoded head; first out stack drops that head. -/
theorem seqComp_step_copyToAuxPop_cons {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₁ : tm1.σ) (σ₂ : tm2.σ)
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k))
    (x : tm1.Γ tm1.k₁) (xs : List (tm1.Γ tm1.k₁))
    (hOut : S₁ tm1.k₁ = x :: xs) :
    TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m
      (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPop)
        (σ₁, σ₂, none) S₁ aux S₂) =
      some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPush)
        (σ₁, σ₂, some (decodeOut x))
        (Function.update S₁ tm1.k₁ xs) aux S₂) := by
  letI : DecidableEq tm1.K := tm1.kDecidableEq
  letI : DecidableEq tm2.K := tm2.kDecidableEq
  letI : DecidableEq (CompK tm1.K tm2.K) :=
    (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).kDecidableEq
  simp [seqCompComputer, seqCompCfg, seqCompStk, copyToAuxPopStmt, TM2.step,
    TM2.stepAux, hOut, List.head?]
  refine congrArg some ?_
  refine congrArg (fun stk =>
    (⟨some CompLabel.copyToAuxPush, (σ₁, σ₂, some (decodeOut x)), stk⟩ :
      (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).Cfg)) ?_
  -- `(x :: xs).tail` reduces to `xs`; package via first-stack update lemma.
  simp only [List.tail]
  exact seqCompStk_update_first_eq (βΓ := βΓ) tm1 tm2 S₁ aux S₂ xs

/-- Push buffered symbol onto second input; return to aux→in pop. -/
theorem seqComp_step_copyToInPush {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₁ : tm1.σ) (σ₂ : tm2.σ)
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k))
    (b : βΓ) :
    TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m
      (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPush)
        (σ₁, σ₂, some b) S₁ aux S₂) =
      some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
        (σ₁, σ₂, none) S₁ aux
        (Function.update S₂ tm2.k₀ (encodeIn b :: S₂ tm2.k₀))) := by
  letI : DecidableEq tm1.K := tm1.kDecidableEq
  letI : DecidableEq tm2.K := tm2.kDecidableEq
  letI : DecidableEq (CompK tm1.K tm2.K) :=
    (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).kDecidableEq
  simp [seqCompComputer, seqCompCfg, seqCompStk, copyToInPushStmt, TM2.step,
    TM2.stepAux]
  refine congrArg some ?_
  refine congrArg (fun stk =>
    (⟨some CompLabel.copyToInPop, (σ₁, σ₂, (none : Option βΓ)), stk⟩ :
      (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).Cfg)) ?_
  exact seqCompStk_update_second_eq (βΓ := βΓ) tm1 tm2 S₁ aux S₂
    (encodeIn b :: S₂ tm2.k₀)

/-! ## First and second phase simulation (lift `stepAux` and multi-step) -/

def liftFirstCfg {βΓ : Type} [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₂ : tm2.σ) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k))
    (c : tm1.Cfg) :
    (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).Cfg :=
  match c.l with
  | none =>
      seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPop)
        (c.var, σ₂, none) c.stk aux S₂
  | some l =>
      seqCompCfg tm1 tm2 decodeOut encodeIn (some (.first l))
        (c.var, σ₂, none) c.stk aux S₂

def liftSecondCfg {βΓ : Type} [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₁ : tm1.σ) (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ)
    (c : tm2.Cfg) :
    (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).Cfg :=
  match c.l with
  | none =>
      seqCompCfg tm1 tm2 decodeOut encodeIn none
        (σ₁, c.var, none) S₁ aux c.stk
  | some l =>
      seqCompCfg tm1 tm2 decodeOut encodeIn (some (.second l))
        (σ₁, c.var, none) S₁ aux c.stk

theorem seqCompStk_update_first_inline {βΓ : Type}
    (tm1 : FinTM2) {K₂ : Type} {Γ₂ : K₂ → Type}
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (Γ₂ k))
    (k : tm1.K) (v : List (tm1.Γ k))
    [DecidableEq (CompK tm1.K K₂)] [DecidableEq tm1.K] :
    Function.update (seqCompStk (K₂ := K₂) (Γ₂ := Γ₂) S₁ aux S₂) (Sum.inl k) v =
      seqCompStk (K₂ := K₂) (Γ₂ := Γ₂) (Function.update S₁ k v) aux S₂ := by
  funext t
  by_cases ht : t = Sum.inl k
  · subst ht; rw [Function.update_self]; simp [seqCompStk, Function.update]
  · rw [Function.update_of_ne ht]
    cases t with
    | inl k' =>
        have hk : ¬ k' = k := by intro h; exact ht (by rw [h])
        simp [seqCompStk, Function.update, hk]
    | inr t =>
        cases t with
        | inl u => cases u; simp [seqCompStk]
        | inr _ => simp [seqCompStk]

theorem seqCompStk_update_second_inline {βΓ : Type}
    {K₁ : Type} (tm2 : FinTM2) {Γ₁ : K₁ → Type}
    (S₁ : ∀ k, List (Γ₁ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k))
    (k : tm2.K) (v : List (tm2.Γ k))
    [DecidableEq (CompK K₁ tm2.K)] [DecidableEq tm2.K] :
    Function.update (seqCompStk (K₁ := K₁) (Γ₁ := Γ₁) S₁ aux S₂) (Sum.inr (Sum.inr k)) v =
      seqCompStk (K₁ := K₁) (Γ₁ := Γ₁) S₁ aux (Function.update S₂ k v) := by
  funext t
  by_cases ht : t = Sum.inr (Sum.inr k)
  · subst ht; rw [Function.update_self]; simp [seqCompStk, Function.update]
  · rw [Function.update_of_ne ht]
    cases t with
    | inl _ => simp [seqCompStk]
    | inr t =>
        cases t with
        | inl u => cases u; simp [seqCompStk]
        | inr k' =>
            have hk : ¬ k' = k := by intro h; exact ht (by rw [h])
            simp [seqCompStk, Function.update, hk]

theorem firstPhase_stepAux {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (q : TM2.Stmt tm1.Γ tm1.Λ tm1.σ)
    (σ₁ : tm1.σ) (σ₂ : tm2.σ)
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k)) :
    TM2.stepAux
      (firstPhaseStmt (K₂ := tm2.K) (Γ₂ := tm2.Γ) (βΓ := βΓ) (Λ₂ := tm2.Λ) (σ₂ := tm2.σ) q)
      (σ₁, σ₂, (none : Option βΓ)) (seqCompStk S₁ aux S₂) =
    liftFirstCfg tm1 tm2 decodeOut encodeIn σ₂ aux S₂ (TM2.stepAux q σ₁ S₁) := by
  letI : DecidableEq tm1.K := tm1.kDecidableEq
  letI : DecidableEq tm2.K := tm2.kDecidableEq
  letI : DecidableEq (CompK tm1.K tm2.K) :=
    (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).kDecidableEq
  induction q generalizing σ₁ S₁ with
  | push k f q ih =>
      have hstk :
          Function.update (seqCompStk S₁ aux S₂) (Sum.inl k) (f σ₁ :: S₁ k) =
            seqCompStk (Function.update S₁ k (f σ₁ :: S₁ k)) aux S₂ :=
        seqCompStk_update_first_inline (βΓ := βΓ) tm1 S₁ aux S₂ k (f σ₁ :: S₁ k)
      have hq :
          firstPhaseStmt (K₂ := tm2.K) (Γ₂ := tm2.Γ) (βΓ := βΓ) (Λ₂ := tm2.Λ) (σ₂ := tm2.σ)
            (push k f q) =
          push (Sum.inl k) (fun st : Compσ tm1.σ tm2.σ βΓ => f st.1)
            (firstPhaseStmt (K₂ := tm2.K) (Γ₂ := tm2.Γ) (βΓ := βΓ) (Λ₂ := tm2.Λ) (σ₂ := tm2.σ) q) :=
        rfl
      rw [hq]
      change TM2.stepAux
          (firstPhaseStmt (K₂ := tm2.K) (Γ₂ := tm2.Γ) (βΓ := βΓ) (Λ₂ := tm2.Λ) (σ₂ := tm2.σ) q)
          (σ₁, σ₂, none)
          (Function.update (seqCompStk S₁ aux S₂) (Sum.inl k) (f σ₁ :: S₁ k)) =
        liftFirstCfg tm1 tm2 decodeOut encodeIn σ₂ aux S₂
          (TM2.stepAux q σ₁ (Function.update S₁ k (f σ₁ :: S₁ k)))
      rw [hstk]
      exact ih σ₁ (Function.update S₁ k (f σ₁ :: S₁ k))
  | peek k f q ih =>
      have hq :
          firstPhaseStmt (K₂ := tm2.K) (Γ₂ := tm2.Γ) (βΓ := βΓ) (Λ₂ := tm2.Λ) (σ₂ := tm2.σ)
            (peek k f q) =
          peek (Sum.inl k) (fun st o => (f st.1 o, st.2.1, st.2.2))
            (firstPhaseStmt (K₂ := tm2.K) (Γ₂ := tm2.Γ) (βΓ := βΓ) (Λ₂ := tm2.Λ) (σ₂ := tm2.σ) q) :=
        rfl
      rw [hq]
      change TM2.stepAux
          (firstPhaseStmt (K₂ := tm2.K) (Γ₂ := tm2.Γ) (βΓ := βΓ) (Λ₂ := tm2.Λ) (σ₂ := tm2.σ) q)
          (f σ₁ (S₁ k).head?, σ₂, none) (seqCompStk S₁ aux S₂) =
        liftFirstCfg tm1 tm2 decodeOut encodeIn σ₂ aux S₂
          (TM2.stepAux q (f σ₁ (S₁ k).head?) S₁)
      exact ih (f σ₁ (S₁ k).head?) S₁
  | pop k f q ih =>
      have hstk :
          Function.update (seqCompStk S₁ aux S₂) (Sum.inl k) (S₁ k).tail =
            seqCompStk (Function.update S₁ k (S₁ k).tail) aux S₂ :=
        seqCompStk_update_first_inline (βΓ := βΓ) tm1 S₁ aux S₂ k (S₁ k).tail
      have hq :
          firstPhaseStmt (K₂ := tm2.K) (Γ₂ := tm2.Γ) (βΓ := βΓ) (Λ₂ := tm2.Λ) (σ₂ := tm2.σ)
            (pop k f q) =
          pop (Sum.inl k) (fun st o => (f st.1 o, st.2.1, st.2.2))
            (firstPhaseStmt (K₂ := tm2.K) (Γ₂ := tm2.Γ) (βΓ := βΓ) (Λ₂ := tm2.Λ) (σ₂ := tm2.σ) q) :=
        rfl
      rw [hq]
      change TM2.stepAux
          (firstPhaseStmt (K₂ := tm2.K) (Γ₂ := tm2.Γ) (βΓ := βΓ) (Λ₂ := tm2.Λ) (σ₂ := tm2.σ) q)
          (f σ₁ (S₁ k).head?, σ₂, none)
          (Function.update (seqCompStk S₁ aux S₂) (Sum.inl k) (S₁ k).tail) =
        liftFirstCfg tm1 tm2 decodeOut encodeIn σ₂ aux S₂
          (TM2.stepAux q (f σ₁ (S₁ k).head?) (Function.update S₁ k (S₁ k).tail))
      rw [hstk]
      exact ih (f σ₁ (S₁ k).head?) (Function.update S₁ k (S₁ k).tail)
  | load f q ih =>
      have hq :
          firstPhaseStmt (K₂ := tm2.K) (Γ₂ := tm2.Γ) (βΓ := βΓ) (Λ₂ := tm2.Λ) (σ₂ := tm2.σ)
            (load f q) =
          load (fun st : Compσ tm1.σ tm2.σ βΓ => (f st.1, st.2.1, st.2.2))
            (firstPhaseStmt (K₂ := tm2.K) (Γ₂ := tm2.Γ) (βΓ := βΓ) (Λ₂ := tm2.Λ) (σ₂ := tm2.σ) q) :=
        rfl
      rw [hq, TM2.stepAux]
      exact ih (f σ₁) S₁
  | branch p q₁ q₂ ih₁ ih₂ =>
      have hq :
          firstPhaseStmt (K₂ := tm2.K) (Γ₂ := tm2.Γ) (βΓ := βΓ) (Λ₂ := tm2.Λ) (σ₂ := tm2.σ)
            (branch p q₁ q₂) =
          branch (fun st : Compσ tm1.σ tm2.σ βΓ => p st.1)
            (firstPhaseStmt (K₂ := tm2.K) (Γ₂ := tm2.Γ) (βΓ := βΓ) (Λ₂ := tm2.Λ) (σ₂ := tm2.σ) q₁)
            (firstPhaseStmt (K₂ := tm2.K) (Γ₂ := tm2.Γ) (βΓ := βΓ) (Λ₂ := tm2.Λ) (σ₂ := tm2.σ) q₂) :=
        rfl
      rw [hq, TM2.stepAux]
      cases h : p σ₁ with
      | true => simpa [h, cond] using ih₁ σ₁ S₁
      | false => simpa [h, cond] using ih₂ σ₁ S₁
  | goto f => rfl
  | halt => rfl

theorem secondPhase_stepAux {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (q : TM2.Stmt tm2.Γ tm2.Λ tm2.σ)
    (σ₁ : tm1.σ) (σ₂ : tm2.σ)
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k)) :
    TM2.stepAux
      (secondPhaseStmt (K₁ := tm1.K) (Γ₁ := tm1.Γ) (βΓ := βΓ) (Λ₁ := tm1.Λ) (σ₁ := tm1.σ) q)
      (σ₁, σ₂, (none : Option βΓ)) (seqCompStk S₁ aux S₂) =
    liftSecondCfg tm1 tm2 decodeOut encodeIn σ₁ S₁ aux (TM2.stepAux q σ₂ S₂) := by
  letI : DecidableEq tm1.K := tm1.kDecidableEq
  letI : DecidableEq tm2.K := tm2.kDecidableEq
  letI : DecidableEq (CompK tm1.K tm2.K) :=
    (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).kDecidableEq
  induction q generalizing σ₂ S₂ with
  | push k f q ih =>
      have hstk :
          Function.update (seqCompStk S₁ aux S₂) (Sum.inr (Sum.inr k)) (f σ₂ :: S₂ k) =
            seqCompStk S₁ aux (Function.update S₂ k (f σ₂ :: S₂ k)) :=
        seqCompStk_update_second_inline (βΓ := βΓ) tm2 S₁ aux S₂ k (f σ₂ :: S₂ k)
      have hq :
          secondPhaseStmt (K₁ := tm1.K) (Γ₁ := tm1.Γ) (βΓ := βΓ) (Λ₁ := tm1.Λ) (σ₁ := tm1.σ)
            (push k f q) =
          push (Sum.inr (Sum.inr k)) (fun st : Compσ tm1.σ tm2.σ βΓ => f st.2.1)
            (secondPhaseStmt (K₁ := tm1.K) (Γ₁ := tm1.Γ) (βΓ := βΓ) (Λ₁ := tm1.Λ) (σ₁ := tm1.σ) q) :=
        rfl
      rw [hq]
      change TM2.stepAux
          (secondPhaseStmt (K₁ := tm1.K) (Γ₁ := tm1.Γ) (βΓ := βΓ) (Λ₁ := tm1.Λ) (σ₁ := tm1.σ) q)
          (σ₁, σ₂, none)
          (Function.update (seqCompStk S₁ aux S₂) (Sum.inr (Sum.inr k)) (f σ₂ :: S₂ k)) =
        liftSecondCfg tm1 tm2 decodeOut encodeIn σ₁ S₁ aux
          (TM2.stepAux q σ₂ (Function.update S₂ k (f σ₂ :: S₂ k)))
      rw [hstk]
      exact ih σ₂ (Function.update S₂ k (f σ₂ :: S₂ k))
  | peek k f q ih =>
      have hq :
          secondPhaseStmt (K₁ := tm1.K) (Γ₁ := tm1.Γ) (βΓ := βΓ) (Λ₁ := tm1.Λ) (σ₁ := tm1.σ)
            (peek k f q) =
          peek (Sum.inr (Sum.inr k)) (fun st o => (st.1, f st.2.1 o, st.2.2))
            (secondPhaseStmt (K₁ := tm1.K) (Γ₁ := tm1.Γ) (βΓ := βΓ) (Λ₁ := tm1.Λ) (σ₁ := tm1.σ) q) :=
        rfl
      rw [hq]
      change TM2.stepAux
          (secondPhaseStmt (K₁ := tm1.K) (Γ₁ := tm1.Γ) (βΓ := βΓ) (Λ₁ := tm1.Λ) (σ₁ := tm1.σ) q)
          (σ₁, f σ₂ (S₂ k).head?, none) (seqCompStk S₁ aux S₂) =
        liftSecondCfg tm1 tm2 decodeOut encodeIn σ₁ S₁ aux
          (TM2.stepAux q (f σ₂ (S₂ k).head?) S₂)
      exact ih (f σ₂ (S₂ k).head?) S₂
  | pop k f q ih =>
      have hstk :
          Function.update (seqCompStk S₁ aux S₂) (Sum.inr (Sum.inr k)) (S₂ k).tail =
            seqCompStk S₁ aux (Function.update S₂ k (S₂ k).tail) :=
        seqCompStk_update_second_inline (βΓ := βΓ) tm2 S₁ aux S₂ k (S₂ k).tail
      have hq :
          secondPhaseStmt (K₁ := tm1.K) (Γ₁ := tm1.Γ) (βΓ := βΓ) (Λ₁ := tm1.Λ) (σ₁ := tm1.σ)
            (pop k f q) =
          pop (Sum.inr (Sum.inr k)) (fun st o => (st.1, f st.2.1 o, st.2.2))
            (secondPhaseStmt (K₁ := tm1.K) (Γ₁ := tm1.Γ) (βΓ := βΓ) (Λ₁ := tm1.Λ) (σ₁ := tm1.σ) q) :=
        rfl
      rw [hq]
      change TM2.stepAux
          (secondPhaseStmt (K₁ := tm1.K) (Γ₁ := tm1.Γ) (βΓ := βΓ) (Λ₁ := tm1.Λ) (σ₁ := tm1.σ) q)
          (σ₁, f σ₂ (S₂ k).head?, none)
          (Function.update (seqCompStk S₁ aux S₂) (Sum.inr (Sum.inr k)) (S₂ k).tail) =
        liftSecondCfg tm1 tm2 decodeOut encodeIn σ₁ S₁ aux
          (TM2.stepAux q (f σ₂ (S₂ k).head?) (Function.update S₂ k (S₂ k).tail))
      rw [hstk]
      exact ih (f σ₂ (S₂ k).head?) (Function.update S₂ k (S₂ k).tail)
  | load f q ih =>
      have hq :
          secondPhaseStmt (K₁ := tm1.K) (Γ₁ := tm1.Γ) (βΓ := βΓ) (Λ₁ := tm1.Λ) (σ₁ := tm1.σ)
            (load f q) =
          load (fun st : Compσ tm1.σ tm2.σ βΓ => (st.1, f st.2.1, st.2.2))
            (secondPhaseStmt (K₁ := tm1.K) (Γ₁ := tm1.Γ) (βΓ := βΓ) (Λ₁ := tm1.Λ) (σ₁ := tm1.σ) q) :=
        rfl
      rw [hq, TM2.stepAux]
      exact ih (f σ₂) S₂
  | branch p q₁ q₂ ih₁ ih₂ =>
      have hq :
          secondPhaseStmt (K₁ := tm1.K) (Γ₁ := tm1.Γ) (βΓ := βΓ) (Λ₁ := tm1.Λ) (σ₁ := tm1.σ)
            (branch p q₁ q₂) =
          branch (fun st : Compσ tm1.σ tm2.σ βΓ => p st.2.1)
            (secondPhaseStmt (K₁ := tm1.K) (Γ₁ := tm1.Γ) (βΓ := βΓ) (Λ₁ := tm1.Λ) (σ₁ := tm1.σ) q₁)
            (secondPhaseStmt (K₁ := tm1.K) (Γ₁ := tm1.Γ) (βΓ := βΓ) (Λ₁ := tm1.Λ) (σ₁ := tm1.σ) q₂) :=
        rfl
      rw [hq, TM2.stepAux]
      cases h : p σ₂ with
      | true => simpa [h, cond] using ih₁ σ₂ S₂
      | false => simpa [h, cond] using ih₂ σ₂ S₂
  | goto f => rfl
  | halt => rfl


theorem seqComp_step_first {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (l : tm1.Λ) (σ₁ : tm1.σ) (σ₂ : tm2.σ)
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k)) :
    TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m
      (seqCompCfg tm1 tm2 decodeOut encodeIn (some (.first l))
        (σ₁, σ₂, none) S₁ aux S₂) =
      some (liftFirstCfg tm1 tm2 decodeOut encodeIn σ₂ aux S₂
        (TM2.stepAux (tm1.m l) σ₁ S₁)) := by
  change some
      (TM2.stepAux
        (firstPhaseStmt (K₂ := tm2.K) (Γ₂ := tm2.Γ) (βΓ := βΓ) (Λ₂ := tm2.Λ) (σ₂ := tm2.σ)
          (tm1.m l))
        (σ₁, σ₂, none) (seqCompStk S₁ aux S₂)) =
    some (liftFirstCfg tm1 tm2 decodeOut encodeIn σ₂ aux S₂
      (TM2.stepAux (tm1.m l) σ₁ S₁))
  exact congrArg some (firstPhase_stepAux tm1 tm2 decodeOut encodeIn (tm1.m l) σ₁ σ₂ S₁ aux S₂)

theorem seqComp_step_second {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (l : tm2.Λ) (σ₁ : tm1.σ) (σ₂ : tm2.σ)
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k)) :
    TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m
      (seqCompCfg tm1 tm2 decodeOut encodeIn (some (.second l))
        (σ₁, σ₂, none) S₁ aux S₂) =
      some (liftSecondCfg tm1 tm2 decodeOut encodeIn σ₁ S₁ aux
        (TM2.stepAux (tm2.m l) σ₂ S₂)) := by
  change some
      (TM2.stepAux
        (secondPhaseStmt (K₁ := tm1.K) (Γ₁ := tm1.Γ) (βΓ := βΓ) (Λ₁ := tm1.Λ) (σ₁ := tm1.σ)
          (tm2.m l))
        (σ₁, σ₂, none) (seqCompStk S₁ aux S₂)) =
    some (liftSecondCfg tm1 tm2 decodeOut encodeIn σ₁ S₁ aux
      (TM2.stepAux (tm2.m l) σ₂ S₂))
  exact congrArg some (secondPhase_stepAux tm1 tm2 decodeOut encodeIn (tm2.m l) σ₁ σ₂ S₁ aux S₂)

theorem liftFirstCfg_step {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₂ : tm2.σ) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k))
    (l : tm1.Λ) (var : tm1.σ) (stk : ∀ k, List (tm1.Γ k)) :
    TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m
      (liftFirstCfg tm1 tm2 decodeOut encodeIn σ₂ aux S₂ ⟨some l, var, stk⟩) =
      some (liftFirstCfg tm1 tm2 decodeOut encodeIn σ₂ aux S₂
        (TM2.stepAux (tm1.m l) var stk)) := by
  simpa [liftFirstCfg] using
    seqComp_step_first tm1 tm2 decodeOut encodeIn l var σ₂ stk aux S₂

theorem option_bind_iterate_none {σ : Type} (f : σ → Option σ) :
    ∀ n, (flip bind f)^[n] (none : Option σ) = none
  | 0 => rfl
  | n + 1 => by
      simp only [Function.iterate_succ_apply, flip]
      exact option_bind_iterate_none f n

theorem liftFirstCfg_iterate {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₂ : tm2.σ) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k))
    (n : ℕ) (c c' : tm1.Cfg)
    (h : (flip bind tm1.step)^[n] (some c) = some c') :
    (flip bind (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m))^[n]
      (some (liftFirstCfg tm1 tm2 decodeOut encodeIn σ₂ aux S₂ c)) =
      some (liftFirstCfg tm1 tm2 decodeOut encodeIn σ₂ aux S₂ c') := by
  induction n generalizing c with
  | zero =>
      injection h with h'
      exact congrArg some (congrArg _ h')
  | succ n ih =>
      have h1 : (flip bind tm1.step)^[n] (tm1.step c) = some c' := by
        simpa [Function.iterate_succ_apply, flip, Option.bind] using h
      rcases c with ⟨lOpt, var, stk⟩
      cases lOpt with
      | none =>
          have : (flip bind tm1.step)^[n] (none : Option tm1.Cfg) = some c' := by
            simpa [FinTM2.step, TM2.step] using h1
          rw [option_bind_iterate_none] at this
          cases this
      | some l =>
          have hc : tm1.step ⟨some l, var, stk⟩ =
              some (TM2.stepAux (tm1.m l) var stk) := by
            simp [FinTM2.step, TM2.step]
          have hstep :=
            liftFirstCfg_step tm1 tm2 decodeOut encodeIn σ₂ aux S₂ l var stk
          have h1' : (flip bind tm1.step)^[n]
              (some (TM2.stepAux (tm1.m l) var stk)) = some c' := by
            simpa [hc] using h1
          have ih' := ih (TM2.stepAux (tm1.m l) var stk) h1'
          simpa [Function.iterate_succ_apply, flip, Option.bind, hstep] using ih'

/-- One product step lifts one second-machine step when the label is active. -/
theorem liftSecondCfg_step {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₁ : tm1.σ) (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ)
    (l : tm2.Λ) (var : tm2.σ) (stk : ∀ k, List (tm2.Γ k)) :
    TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m
      (liftSecondCfg tm1 tm2 decodeOut encodeIn σ₁ S₁ aux ⟨some l, var, stk⟩) =
      some (liftSecondCfg tm1 tm2 decodeOut encodeIn σ₁ S₁ aux
        (TM2.stepAux (tm2.m l) var stk)) := by
  simpa [liftSecondCfg] using
    seqComp_step_second tm1 tm2 decodeOut encodeIn l σ₁ var S₁ aux stk

/-- Multi-step second-phase lift (halt stays halt). -/
theorem liftSecondCfg_iterate {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₁ : tm1.σ) (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ)
    (n : ℕ) (c c' : tm2.Cfg)
    (h : (flip bind tm2.step)^[n] (some c) = some c') :
    (flip bind (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m))^[n]
      (some (liftSecondCfg tm1 tm2 decodeOut encodeIn σ₁ S₁ aux c)) =
      some (liftSecondCfg tm1 tm2 decodeOut encodeIn σ₁ S₁ aux c') := by
  induction n generalizing c with
  | zero =>
      injection h with h'
      exact congrArg some (congrArg _ h')
  | succ n ih =>
      have h1 : (flip bind tm2.step)^[n] (tm2.step c) = some c' := by
        simpa [Function.iterate_succ_apply, flip, Option.bind] using h
      rcases c with ⟨lOpt, var, stk⟩
      cases lOpt with
      | none =>
          have : (flip bind tm2.step)^[n] (none : Option tm2.Cfg) = some c' := by
            simpa [FinTM2.step, TM2.step] using h1
          rw [option_bind_iterate_none] at this
          cases this
      | some l =>
          have hc : tm2.step ⟨some l, var, stk⟩ =
              some (TM2.stepAux (tm2.m l) var stk) := by
            simp [FinTM2.step, TM2.step]
          have hstep :=
            liftSecondCfg_step tm1 tm2 decodeOut encodeIn σ₁ S₁ aux l var stk
          have h1' : (flip bind tm2.step)^[n]
              (some (TM2.stepAux (tm2.m l) var stk)) = some c' := by
            simpa [hc] using h1
          have ih' := ih (TM2.stepAux (tm2.m l) var stk) h1'
          simpa [Function.iterate_succ_apply, flip, Option.bind, hstep] using ih'

/-- Package `EvalsToInTime` for a first-machine run into a product first-phase run. -/
noncomputable def seqComp_evals_first {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₂ : tm2.σ) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k))
    (c c' : tm1.Cfg) (m : ℕ)
    (h : EvalsToInTime tm1.step c (some c') m) :
    EvalsToInTime
      (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m)
      (liftFirstCfg tm1 tm2 decodeOut encodeIn σ₂ aux S₂ c)
      (some (liftFirstCfg tm1 tm2 decodeOut encodeIn σ₂ aux S₂ c')) m where
  steps := h.steps
  steps_le_m := h.steps_le_m
  evals_in_steps := by
    -- Coerce configs to `some` for the bind iterate.
    simpa using
      liftFirstCfg_iterate tm1 tm2 decodeOut encodeIn σ₂ aux S₂ h.steps c c'
        (by simpa using h.evals_in_steps)

/-- Package `EvalsToInTime` for a second-machine run into a product second-phase run. -/
noncomputable def seqComp_evals_second {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₁ : tm1.σ) (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ)
    (c c' : tm2.Cfg) (m : ℕ)
    (h : EvalsToInTime tm2.step c (some c') m) :
    EvalsToInTime
      (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m)
      (liftSecondCfg tm1 tm2 decodeOut encodeIn σ₁ S₁ aux c)
      (some (liftSecondCfg tm1 tm2 decodeOut encodeIn σ₁ S₁ aux c')) m where
  steps := h.steps
  steps_le_m := h.steps_le_m
  evals_in_steps := by
    simpa using
      liftSecondCfg_iterate tm1 tm2 decodeOut encodeIn σ₁ S₁ aux h.steps c c'
        (by simpa using h.evals_in_steps)

/-! ### Order preserving copy phase (list transfer) -/

/-- One out→aux symbol: pop then push (2 steps). -/
def seqComp_evals_copyToAux_one {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₁ : tm1.σ) (σ₂ : tm2.σ)
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k))
    (x : tm1.Γ tm1.k₁) (xs : List (tm1.Γ tm1.k₁))
    (hOut : S₁ tm1.k₁ = x :: xs) :
    EvalsToInTime
      (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m)
      (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPop)
        (σ₁, σ₂, none) S₁ aux S₂)
      (some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPop)
        (σ₁, σ₂, none) (Function.update S₁ tm1.k₁ xs) (decodeOut x :: aux) S₂))
      2 where
  steps := 2
  steps_le_m := by decide
  evals_in_steps := by
    change
      ((some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPop)
          (σ₁, σ₂, none) S₁ aux S₂)).bind
        (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m)).bind
        (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m) =
      some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPop)
        (σ₁, σ₂, none) (Function.update S₁ tm1.k₁ xs) (decodeOut x :: aux) S₂)
    rw [Option.bind, seqComp_step_copyToAuxPop_cons tm1 tm2 decodeOut encodeIn
      σ₁ σ₂ S₁ aux S₂ x xs hOut]
    change TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m
        (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPush)
          (σ₁, σ₂, some (decodeOut x)) (Function.update S₁ tm1.k₁ xs) aux S₂) =
      some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPop)
        (σ₁, σ₂, none) (Function.update S₁ tm1.k₁ xs) (decodeOut x :: aux) S₂)
    exact seqComp_step_copyToAuxPush tm1 tm2 decodeOut encodeIn σ₁ σ₂
      (Function.update S₁ tm1.k₁ xs) aux S₂ (decodeOut x)

/-- Empty out→aux pop jumps to aux→in (1 step). -/
def seqComp_evals_copyToAux_nil {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₁ : tm1.σ) (σ₂ : tm2.σ)
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k))
    (hOut : S₁ tm1.k₁ = []) :
    EvalsToInTime
      (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m)
      (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPop)
        (σ₁, σ₂, none) S₁ aux S₂)
      (some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
        (σ₁, σ₂, none) S₁ aux S₂))
      1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPop)
        (σ₁, σ₂, none) S₁ aux S₂)).bind
        (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m) =
      some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
        (σ₁, σ₂, none) S₁ aux S₂)
    exact seqComp_step_copyToAuxPop_nil tm1 tm2 decodeOut encodeIn σ₁ σ₂ S₁ aux S₂ hOut

/-- One aux→in symbol: pop then push (2 steps). -/
def seqComp_evals_copyToIn_one {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₁ : tm1.σ) (σ₂ : tm2.σ)
    (S₁ : ∀ k, List (tm1.Γ k)) (b : βΓ) (bs : List βΓ) (S₂ : ∀ k, List (tm2.Γ k)) :
    EvalsToInTime
      (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m)
      (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
        (σ₁, σ₂, none) S₁ (b :: bs) S₂)
      (some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
        (σ₁, σ₂, none) S₁ bs
        (Function.update S₂ tm2.k₀ (encodeIn b :: S₂ tm2.k₀))))
      2 where
  steps := 2
  steps_le_m := by decide
  evals_in_steps := by
    change
      ((some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
          (σ₁, σ₂, none) S₁ (b :: bs) S₂)).bind
        (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m)).bind
        (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m) =
      some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
        (σ₁, σ₂, none) S₁ bs
        (Function.update S₂ tm2.k₀ (encodeIn b :: S₂ tm2.k₀)))
    rw [Option.bind, seqComp_step_copyToInPop_cons tm1 tm2 decodeOut encodeIn
      σ₁ σ₂ S₁ b bs S₂]
    exact seqComp_step_copyToInPush tm1 tm2 decodeOut encodeIn σ₁ σ₂ S₁ bs S₂ b

/-- Empty aux→in pop jumps to second main (1 step). -/
def seqComp_evals_copyToIn_nil {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₁ : tm1.σ) (σ₂ : tm2.σ)
    (S₁ : ∀ k, List (tm1.Γ k)) (S₂ : ∀ k, List (tm2.Γ k)) :
    EvalsToInTime
      (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m)
      (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
        (σ₁, σ₂, none) S₁ [] S₂)
      (some (seqCompCfg tm1 tm2 decodeOut encodeIn (some (.second tm2.main))
        (σ₁, σ₂, none) S₁ [] S₂))
      1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
        (σ₁, σ₂, none) S₁ [] S₂)).bind
        (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m) =
      some (seqCompCfg tm1 tm2 decodeOut encodeIn (some (.second tm2.main))
        (σ₁, σ₂, none) S₁ [] S₂)
    exact seqComp_step_copyToInPop_nil tm1 tm2 decodeOut encodeIn σ₁ σ₂ S₁ S₂

/-- Rewrite the ending configuration of an `EvalsToInTime` proof. -/
def evalsToInTime_congr_end {σ} {f : σ → Option σ} {a : σ} {b b' : Option σ} {m : ℕ}
    (h : EvalsToInTime f a b m) (heq : b = b') : EvalsToInTime f a b' m := by
  rwa [← heq]

/-- Transfer the whole first out stack onto aux (reversed decode), then enter aux→in.
Cost `2 * length + 1`. -/
noncomputable def seqComp_evals_copyToAux {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₁ : tm1.σ) (σ₂ : tm2.σ)
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k))
    (xs : List (tm1.Γ tm1.k₁))
    (hOut : S₁ tm1.k₁ = xs) :
    EvalsToInTime
      (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m)
      (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPop)
        (σ₁, σ₂, none) S₁ aux S₂)
      (some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
        (σ₁, σ₂, none) (Function.update S₁ tm1.k₁ [])
        ((xs.map decodeOut).reverse ++ aux) S₂))
      (2 * xs.length + 1) := by
  induction xs generalizing S₁ aux with
  | nil =>
      have h := seqComp_evals_copyToAux_nil tm1 tm2 decodeOut encodeIn σ₁ σ₂ S₁ aux S₂ hOut
      have hS : Function.update S₁ tm1.k₁ [] = S₁ := by
        letI : DecidableEq tm1.K := tm1.kDecidableEq
        exact update_self_of_eq_nil S₁ tm1.k₁ hOut
      simpa [hS, List.map, List.reverse_nil, List.nil_append, Nat.mul_zero] using h
  | cons x xs ih =>
      have h1 := seqComp_evals_copyToAux_one tm1 tm2 decodeOut encodeIn σ₁ σ₂
        S₁ aux S₂ x xs hOut
      have h2 := ih (Function.update S₁ tm1.k₁ xs) (decodeOut x :: aux)
        (by simp [Function.update])
      have h := EvalsToInTime.trans
        (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m)
        2 (2 * xs.length + 1) _ _ _ h1 h2
      have hupd :
          Function.update (Function.update S₁ tm1.k₁ xs) tm1.k₁ [] =
            Function.update S₁ tm1.k₁ [] := by
        letI : DecidableEq tm1.K := tm1.kDecidableEq
        funext k
        by_cases hk : k = tm1.k₁ <;> simp [Function.update, hk]
      have hstack :
          (xs.map decodeOut).reverse ++ decodeOut x :: aux =
            ((x :: xs).map decodeOut).reverse ++ aux := by
        simp [List.map_cons, List.reverse_cons, List.append_assoc]
      have hend :
          seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
              (σ₁, σ₂, none)
              (Function.update (Function.update S₁ tm1.k₁ xs) tm1.k₁ [])
              ((xs.map decodeOut).reverse ++ decodeOut x :: aux) S₂ =
            seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
              (σ₁, σ₂, none) (Function.update S₁ tm1.k₁ [])
              (((x :: xs).map decodeOut).reverse ++ aux) S₂ := by
        simp only [hupd, hstack]
      have h' := evalsToInTime_congr_end h (congrArg some hend)
      exact evalsToInTime_le_mono h' (by simp [List.length_cons]; omega)

/-- Transfer the whole aux stack onto second input (reversed encode), then enter second main.
Cost `2 * length + 1`. -/
noncomputable def seqComp_evals_copyToIn {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (σ₁ : tm1.σ) (σ₂ : tm2.σ)
    (S₁ : ∀ k, List (tm1.Γ k)) (aux : List βΓ) (S₂ : ∀ k, List (tm2.Γ k)) :
    EvalsToInTime
      (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m)
      (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
        (σ₁, σ₂, none) S₁ aux S₂)
      (some (seqCompCfg tm1 tm2 decodeOut encodeIn (some (.second tm2.main))
        (σ₁, σ₂, none) S₁ []
        (Function.update S₂ tm2.k₀ ((aux.map encodeIn).reverse ++ S₂ tm2.k₀))))
      (2 * aux.length + 1) := by
  induction aux generalizing S₂ with
  | nil =>
      have h := seqComp_evals_copyToIn_nil tm1 tm2 decodeOut encodeIn σ₁ σ₂ S₁ S₂
      have hS : Function.update S₂ tm2.k₀ (S₂ tm2.k₀) = S₂ := by
        letI : DecidableEq tm2.K := tm2.kDecidableEq
        funext k
        by_cases hk : k = tm2.k₀
        · subst hk; rw [Function.update_self]
        · rw [Function.update_of_ne hk]
      simpa [List.map, List.reverse_nil, List.nil_append, Nat.mul_zero, hS] using h
  | cons b bs ih =>
      have h1 := seqComp_evals_copyToIn_one tm1 tm2 decodeOut encodeIn σ₁ σ₂ S₁ b bs S₂
      have h2 := ih (Function.update S₂ tm2.k₀ (encodeIn b :: S₂ tm2.k₀))
      have h := EvalsToInTime.trans
        (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m)
        2 (2 * bs.length + 1) _ _ _ h1 h2
      have hmid :
          (Function.update S₂ tm2.k₀ (encodeIn b :: S₂ tm2.k₀)) tm2.k₀ =
            encodeIn b :: S₂ tm2.k₀ := by
        letI : DecidableEq tm2.K := tm2.kDecidableEq
        simp [Function.update]
      have hupd :
          Function.update (Function.update S₂ tm2.k₀ (encodeIn b :: S₂ tm2.k₀)) tm2.k₀
              ((bs.map encodeIn).reverse ++ encodeIn b :: S₂ tm2.k₀) =
            Function.update S₂ tm2.k₀
              ((bs.map encodeIn).reverse ++ encodeIn b :: S₂ tm2.k₀) := by
        letI : DecidableEq tm2.K := tm2.kDecidableEq
        funext k
        by_cases hk : k = tm2.k₀ <;> simp [Function.update, hk]
      have hstack :
          (bs.map encodeIn).reverse ++ encodeIn b :: S₂ tm2.k₀ =
            ((b :: bs).map encodeIn).reverse ++ S₂ tm2.k₀ := by
        simp [List.map_cons, List.reverse_cons, List.append_assoc]
      have hend :
          seqCompCfg tm1 tm2 decodeOut encodeIn (some (.second tm2.main))
              (σ₁, σ₂, none) S₁ []
              (Function.update (Function.update S₂ tm2.k₀ (encodeIn b :: S₂ tm2.k₀)) tm2.k₀
                ((bs.map encodeIn).reverse ++
                  (Function.update S₂ tm2.k₀ (encodeIn b :: S₂ tm2.k₀)) tm2.k₀)) =
            seqCompCfg tm1 tm2 decodeOut encodeIn (some (.second tm2.main))
              (σ₁, σ₂, none) S₁ []
              (Function.update S₂ tm2.k₀ (((b :: bs).map encodeIn).reverse ++ S₂ tm2.k₀)) := by
        simp only [hmid]
        rw [hupd, hstack]
      have h' := evalsToInTime_congr_end h (congrArg some hend)
      exact evalsToInTime_le_mono h' (by simp [List.length_cons]; omega)

/-! ### Packaging: product initList / haltList as phase lifts -/

theorem initList_stk_k₀ (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    (initList tm s).stk tm.k₀ = s := by
  simp [initList]

theorem initList_stk_of_ne (tm : FinTM2) (s : List (tm.Γ tm.k₀)) (k : tm.K)
    (hne : k ≠ tm.k₀) : (initList tm s).stk k = [] := by
  simp [initList, hne]

theorem haltList_stk_k₁ (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    (haltList tm s).stk tm.k₁ = s := by
  simp [haltList]

theorem haltList_stk_of_ne (tm : FinTM2) (s : List (tm.Γ tm.k₁)) (k : tm.K)
    (hne : k ≠ tm.k₁) : (haltList tm s).stk k = [] := by
  simp [haltList, hne]

theorem seqComp_initList {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (s : List (tm1.Γ tm1.k₀)) :
    initList (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn) s =
      liftFirstCfg tm1 tm2 decodeOut encodeIn tm2.initialState [] emptyStk
        (initList tm1 s) := by
  let tm := seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn
  letI : DecidableEq tm1.K := tm1.kDecidableEq
  letI : DecidableEq tm2.K := tm2.kDecidableEq
  letI : DecidableEq (CompK tm1.K tm2.K) := tm.kDecidableEq
  have hlift :
      liftFirstCfg tm1 tm2 decodeOut encodeIn tm2.initialState [] emptyStk (initList tm1 s) =
        seqCompCfg tm1 tm2 decodeOut encodeIn (some (.first tm1.main))
          (tm1.initialState, tm2.initialState, none) (initList tm1 s).stk [] emptyStk := by
    simp [liftFirstCfg, initList, seqCompCfg]
  rw [hlift]
  have hcfg :
      initList tm s =
        (⟨some (CompLabel.first tm1.main), (tm1.initialState, tm2.initialState, none),
          (initList tm s).stk⟩ : tm.Cfg) := by
    simp [initList, tm, seqCompComputer]
  rw [hcfg]
  refine congrArg (fun stk : ∀ k, List (tm.Γ k) =>
      (⟨some (CompLabel.first tm1.main), (tm1.initialState, tm2.initialState, none), stk⟩ :
        tm.Cfg)) ?_
  funext k
  change (initList tm s).stk k =
    seqCompStk (initList tm1 s).stk ([] : List βΓ) emptyStk k
  cases k with
  | inl k1 =>
      simp only [seqCompStk]
      by_cases hk : k1 = tm1.k₀
      · subst hk
        -- Unfold tm so product k₀ is definitionally Sum.inl tm1.k₀
            -- (propositional rw on stk keys fails: Γ is key-dependent).
        simp only [tm, seqCompComputer]
        exact (initList_stk_k₀ (seqCompComputer tm1 tm2 decodeOut encodeIn) s).trans
          (initList_stk_k₀ tm1 s).symm
      · have hneL : (Sum.inl k1 : CompK tm1.K tm2.K) ≠ tm.k₀ := by
          simp only [tm, seqCompComputer]
          exact fun h => hk (Sum.inl.inj h)
        rw [initList_stk_of_ne tm s _ hneL, initList_stk_of_ne tm1 s k1 hk]
        rfl
  | inr u =>
      cases u with
      | inl v =>
          cases v
          simp only [seqCompStk]
          have hne : (Sum.inr (Sum.inl ()) : CompK tm1.K tm2.K) ≠ tm.k₀ := by
            simp only [tm, seqCompComputer]
            intro h; cases h
          exact initList_stk_of_ne tm s _ hne
      | inr k2 =>
          simp only [seqCompStk]
          have hne : (Sum.inr (Sum.inr k2) : CompK tm1.K tm2.K) ≠ tm.k₀ := by
            simp only [tm, seqCompComputer]
            intro h; cases h
          exact initList_stk_of_ne tm s _ hne

theorem seqComp_haltList {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (s : List (tm2.Γ tm2.k₁)) :
    haltList (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn) s =
      liftSecondCfg tm1 tm2 decodeOut encodeIn tm1.initialState emptyStk []
        (haltList tm2 s) := by
  let tm := seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn
  letI : DecidableEq tm1.K := tm1.kDecidableEq
  letI : DecidableEq tm2.K := tm2.kDecidableEq
  letI : DecidableEq (CompK tm1.K tm2.K) := tm.kDecidableEq
  have hlift :
      liftSecondCfg tm1 tm2 decodeOut encodeIn tm1.initialState emptyStk [] (haltList tm2 s) =
        seqCompCfg tm1 tm2 decodeOut encodeIn none
          (tm1.initialState, tm2.initialState, none) emptyStk [] (haltList tm2 s).stk := by
    simp [liftSecondCfg, haltList, seqCompCfg]
  rw [hlift]
  have hcfg :
      haltList tm s =
        (⟨(none : Option (CompLabel tm1.Λ tm2.Λ)),
          (tm1.initialState, tm2.initialState, none), (haltList tm s).stk⟩ : tm.Cfg) := by
    simp [haltList, tm, seqCompComputer]
  rw [hcfg]
  refine congrArg (fun stk : ∀ k, List (tm.Γ k) =>
      (⟨(none : Option (CompLabel tm1.Λ tm2.Λ)),
        (tm1.initialState, tm2.initialState, none), stk⟩ : tm.Cfg)) ?_
  funext k
  change (haltList tm s).stk k =
    seqCompStk (emptyStk : ∀ k, List (tm1.Γ k)) ([] : List βΓ) (haltList tm2 s).stk k
  cases k with
  | inl k1 =>
      simp only [seqCompStk, emptyStk]
      have hne : (Sum.inl k1 : CompK tm1.K tm2.K) ≠ tm.k₁ := by
        simp only [tm, seqCompComputer]
        intro h; cases h
      exact haltList_stk_of_ne tm s _ hne
  | inr u =>
      cases u with
      | inl v =>
          cases v
          simp only [seqCompStk]
          have hne : (Sum.inr (Sum.inl ()) : CompK tm1.K tm2.K) ≠ tm.k₁ := by
            simp only [tm, seqCompComputer]
            intro h; cases h
          exact haltList_stk_of_ne tm s _ hne
      | inr k2 =>
          simp only [seqCompStk]
          by_cases hk : k2 = tm2.k₁
          · subst hk
        -- Unfold tm so product k₁ is definitionally Sum.inr (Sum.inr tm2.k₁)
            -- (propositional rw on stk keys fails: Γ is key-dependent).
            simp only [tm, seqCompComputer]
            exact (haltList_stk_k₁ (seqCompComputer tm1 tm2 decodeOut encodeIn) s).trans
              (haltList_stk_k₁ tm2 s).symm
          · have hne : (Sum.inr (Sum.inr k2) : CompK tm1.K tm2.K) ≠ tm.k₁ := by
              simp only [tm, seqCompComputer]
              exact fun h => hk (by cases h; rfl)
            rw [haltList_stk_of_ne tm s _ hne, haltList_stk_of_ne tm2 s k2 hk]
            rfl

/-! ### Full sequential evaluation (first, copy, second) -/

theorem haltList_stk_cleared (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    Function.update (haltList tm s).stk tm.k₁ [] = emptyStk := by
  letI : DecidableEq tm.K := tm.kDecidableEq
  funext k
  by_cases hk : k = tm.k₁
  · subst hk
    rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne hk, emptyStk, haltList_stk_of_ne tm s k hk]

/-- initList stacks equal update of empty at the input key. -/
theorem initList_stk_eq_update_empty (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    (initList tm s).stk = Function.update (emptyStk : ∀ k, List (tm.Γ k)) tm.k₀ s := by
  letI : DecidableEq tm.K := tm.kDecidableEq
  funext k
  by_cases hk : k = tm.k₀
  · subst hk
    rw [Function.update_self, initList_stk_k₀]
  · rw [Function.update_of_ne hk, emptyStk, initList_stk_of_ne tm s k hk]

/-- Double reverse of mapped mid recovers the composed encoding. -/
theorem map_encode_decode_reverse_cancel {α β γ : Type}
    (decodeOut : α → β) (encodeIn : β → γ) (mid : List α) :
    ((mid.map decodeOut).reverse.map encodeIn).reverse =
      mid.map (encodeIn ∘ decodeOut) := by
  simp [List.map_reverse, List.reverse_reverse, List.map_map]

/-- Full sequential evaluation: first run, out→aux→in copy, second run. -/
noncomputable def seqComp_evals_compose {βΓ : Type}
    [Inhabited βΓ] [Fintype βΓ] [DecidableEq βΓ]
    (tm1 tm2 : FinTM2)
    (decodeOut : tm1.Γ tm1.k₁ → βΓ) (encodeIn : βΓ → tm2.Γ tm2.k₀)
    (inp : List (tm1.Γ tm1.k₀))
    (mid : List (tm1.Γ tm1.k₁))
    (out : List (tm2.Γ tm2.k₁))
    (m1 m2 : ℕ)
    (h1 : EvalsToInTime tm1.step (initList tm1 inp) (some (haltList tm1 mid)) m1)
    (h2 : EvalsToInTime tm2.step
      (initList tm2 (mid.map (encodeIn ∘ decodeOut)))
      (some (haltList tm2 out)) m2) :
    EvalsToInTime
      (TM2.step (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn).m)
      (initList (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn) inp)
      (some (haltList (seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn) out))
      (m1 + (2 * mid.length + 1) + (2 * mid.length + 1) + m2) := by
  let tm := seqCompComputer (βΓ := βΓ) tm1 tm2 decodeOut encodeIn
  letI : DecidableEq tm1.K := tm1.kDecidableEq
  letI : DecidableEq tm2.K := tm2.kDecidableEq
  have hInit :
      initList tm inp =
        liftFirstCfg tm1 tm2 decodeOut encodeIn tm2.initialState [] emptyStk
          (initList tm1 inp) :=
    seqComp_initList tm1 tm2 decodeOut encodeIn inp
  have hFirst :=
    seqComp_evals_first tm1 tm2 decodeOut encodeIn tm2.initialState [] emptyStk
      (initList tm1 inp) (haltList tm1 mid) m1 h1
  have hLiftHalt :
      liftFirstCfg tm1 tm2 decodeOut encodeIn tm2.initialState [] emptyStk
          (haltList tm1 mid) =
        seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPop)
          ((haltList tm1 mid).var, tm2.initialState, none)
          (haltList tm1 mid).stk [] emptyStk := by
    simp [liftFirstCfg, haltList]
  have hCopyAux :=
    seqComp_evals_copyToAux tm1 tm2 decodeOut encodeIn
      (haltList tm1 mid).var tm2.initialState
      (haltList tm1 mid).stk [] emptyStk mid
      (haltList_stk_k₁ tm1 mid)
  have hMid1 :
      seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
          ((haltList tm1 mid).var, tm2.initialState, none)
          (Function.update (haltList tm1 mid).stk tm1.k₁ [])
          ((mid.map decodeOut).reverse ++ ([] : List βΓ)) emptyStk =
        seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
          (tm1.initialState, tm2.initialState, none)
          emptyStk (mid.map decodeOut).reverse emptyStk := by
    have hv : (haltList tm1 mid).var = tm1.initialState := by simp [haltList]
    have hs := haltList_stk_cleared tm1 mid
    simp [hv, hs]
  have hCopyAux' :=
    evalsToInTime_congr_end hCopyAux (congrArg some hMid1)
  -- Align copyAux time from reverse length to mid.length
  have hlen : (mid.map decodeOut).reverse.length = mid.length := by
    simp [List.length_reverse, List.length_map]
  have hCopyAux'' :
      EvalsToInTime (TM2.step tm.m)
        (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToAuxPop)
          ((haltList tm1 mid).var, tm2.initialState, none)
          (haltList tm1 mid).stk [] emptyStk)
        (some (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
          (tm1.initialState, tm2.initialState, none)
          emptyStk (mid.map decodeOut).reverse emptyStk))
        (2 * mid.length + 1) := by
    -- hCopyAux' has time 2 * mid.length + 1 already (xs = mid)
    exact hCopyAux'
  have hCopyIn :=
    seqComp_evals_copyToIn tm1 tm2 decodeOut encodeIn
      tm1.initialState tm2.initialState emptyStk (mid.map decodeOut).reverse emptyStk
  have hEnc := map_encode_decode_reverse_cancel decodeOut encodeIn mid
  have hInit2Stk := initList_stk_eq_update_empty tm2 (mid.map (encodeIn ∘ decodeOut))
  have hMid2 :
      seqCompCfg tm1 tm2 decodeOut encodeIn (some (.second tm2.main))
          (tm1.initialState, tm2.initialState, none) emptyStk []
          (Function.update (emptyStk : ∀ k, List (tm2.Γ k)) tm2.k₀
            (((mid.map decodeOut).reverse.map encodeIn).reverse ++ emptyStk tm2.k₀)) =
        liftSecondCfg tm1 tm2 decodeOut encodeIn tm1.initialState emptyStk []
          (initList tm2 (mid.map (encodeIn ∘ decodeOut))) := by
    have hstk :
        Function.update (emptyStk : ∀ k, List (tm2.Γ k)) tm2.k₀
            (((mid.map decodeOut).reverse.map encodeIn).reverse ++ emptyStk tm2.k₀) =
          (initList tm2 (mid.map (encodeIn ∘ decodeOut))).stk := by
      simp only [emptyStk, List.append_nil, hEnc]
      exact hInit2Stk.symm
    simp only [liftSecondCfg, initList]
    exact congrArg (fun S₂ : ∀ k, List (tm2.Γ k) =>
      seqCompCfg tm1 tm2 decodeOut encodeIn (some (.second tm2.main))
        (tm1.initialState, tm2.initialState, none) emptyStk [] S₂) hstk
  have hCopyIn' :=
    evalsToInTime_congr_end hCopyIn (congrArg some hMid2)
  have hCopyIn'' :
      EvalsToInTime (TM2.step tm.m)
        (seqCompCfg tm1 tm2 decodeOut encodeIn (some .copyToInPop)
          (tm1.initialState, tm2.initialState, none)
          emptyStk (mid.map decodeOut).reverse emptyStk)
        (some (liftSecondCfg tm1 tm2 decodeOut encodeIn tm1.initialState emptyStk []
          (initList tm2 (mid.map (encodeIn ∘ decodeOut)))))
        (2 * mid.length + 1) := by
    have h := hCopyIn'
    -- time is 2 * reverse.length + 1
    simpa [hlen] using h
  have hSecond :=
    seqComp_evals_second tm1 tm2 decodeOut encodeIn tm1.initialState emptyStk []
      (initList tm2 (mid.map (encodeIn ∘ decodeOut))) (haltList tm2 out) m2 h2
  have hHalt :
      liftSecondCfg tm1 tm2 decodeOut encodeIn tm1.initialState emptyStk []
          (haltList tm2 out) =
        haltList tm out :=
    (seqComp_haltList tm1 tm2 decodeOut encodeIn out).symm
  have hSecond' :=
    evalsToInTime_congr_end hSecond (congrArg some hHalt)
  have hFirst' :
      EvalsToInTime (TM2.step tm.m)
        (initList tm inp)
        (some (liftFirstCfg tm1 tm2 decodeOut encodeIn tm2.initialState [] emptyStk
          (haltList tm1 mid))) m1 := by
    simpa [hInit] using hFirst
  have hFirst'' :=
    evalsToInTime_congr_end hFirst' (congrArg some hLiftHalt)
  -- EvalsToInTime.trans yields (m₂ + m₁); chain and reassociate at the end.
  have t1 :=
    EvalsToInTime.trans (TM2.step tm.m) m1 (2 * mid.length + 1) _ _ _
      hFirst'' hCopyAux''
  have t2 :=
    EvalsToInTime.trans (TM2.step tm.m)
      ((2 * mid.length + 1) + m1) (2 * mid.length + 1) _ _ _ t1 hCopyIn''
  have t3 :=
    EvalsToInTime.trans (TM2.step tm.m)
      ((2 * mid.length + 1) + ((2 * mid.length + 1) + m1)) m2 _ _ _ t2 hSecond'
  exact evalsToInTime_le_mono t3 (by omega)

/-! ### P ⊆ NP via projFirst then characteristic -/

theorem poly_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  simp only [Polynomial.eval_eq_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

noncomputable def compose_projFirst_bitEnc {χ : List Bool → Bool}
    (hχ : TM2ComputableInPolyTime idBitEnc bitEnc χ) :
    TM2ComputableInPolyTime encodePair bitEnc (fun pw => χ pw.1) := by
  let decodeOut : Bool → Bool := id
  let encodeIn : Bool → hχ.tm.Γ hχ.tm.k₀ := hχ.inputAlphabet.symm
  let tm :=
    seqCompComputer (βΓ := Bool) projFirstComputer hχ.tm decodeOut encodeIn
  let inA : tm.Γ tm.k₀ ≃ Bool := by
    simpa [tm, seqCompComputer, CompΓ] using (Equiv.refl Bool)
  let outA : tm.Γ tm.k₁ ≃ Bool := by
    let e : tm.Γ tm.k₁ ≃ hχ.tm.Γ hχ.tm.k₁ := by
      simpa [tm, seqCompComputer, CompΓ, CompK] using
        (Equiv.refl (hχ.tm.Γ hχ.tm.k₁))
    exact e.trans hχ.outputAlphabet
  refine
    { tm := tm
      inputAlphabet := inA
      outputAlphabet := outA
      time := seqCompTime projFirstTime hχ.time
      outputsFun := ?out }
  case out =>
    intro pw
    rcases pw with ⟨x, w⟩
    change TM2OutputsInTime tm (List.map inA.invFun (encodePair (x, w)))
      (some (List.map outA.invFun (bitEnc (χ x))))
      ((seqCompTime projFirstTime hχ.time).eval (encodePair (x, w)).length)
    have hin :
        List.map inA.invFun (encodePair (x, w)) = encodePair (x, w) := by
      -- inA reduces to Equiv.refl Bool
      change List.map (Equiv.refl Bool).symm (encodePair (x, w)) = encodePair (x, w)
      simp [List.map_id]
    have hout :
        List.map outA.invFun (bitEnc (χ x)) =
          List.map hχ.outputAlphabet.invFun (bitEnc (χ x)) := by
      -- outputAlphabet.invFun : Bool → tm.Γ tm.k₁ embeds the bit encoding
      apply congrArg (fun f : Bool → tm.Γ tm.k₁ => List.map f (bitEnc (χ x)))
      funext b
      simp only [outA]
      -- (refl.trans e).symm b = e.symm (refl.symm b) = e.symm b
      change (Equiv.refl _).symm (hχ.outputAlphabet.symm b) = hχ.outputAlphabet.symm b
      rfl
    have h1 := projFirst_evals x w
    have hmid :
        x.map (encodeIn ∘ decodeOut) =
          List.map hχ.inputAlphabet.invFun (idBitEnc x) := by
      simp [decodeOut, encodeIn, idBitEnc]
    have h2 : EvalsToInTime hχ.tm.step
        (initList hχ.tm (x.map (encodeIn ∘ decodeOut)))
        (some (haltList hχ.tm (List.map hχ.outputAlphabet.invFun (bitEnc (χ x)))))
        (hχ.time.eval (idBitEnc x).length) := by
      simpa [hmid] using hχ.outputsFun x
    have heval :=
      seqComp_evals_compose (βΓ := Bool) projFirstComputer hχ.tm
        decodeOut encodeIn (encodePair (x, w)) x
        (List.map hχ.outputAlphabet.invFun (bitEnc (χ x)))
        (3 * x.length + w.length + 3)
        (hχ.time.eval (idBitEnc x).length) h1 h2
    -- Rewrite endpoints to alphabet-mapped lists
    have heval' :
        EvalsToInTime (TM2.step tm.m)
          (initList tm (List.map inA.invFun (encodePair (x, w))))
          (some (haltList tm (List.map outA.invFun (bitEnc (χ x)))))
          (3 * x.length + w.length + 3 + (2 * x.length + 1) + (2 * x.length + 1) +
            hχ.time.eval (idBitEnc x).length) := by
      rw [hin, hout]
      exact heval
    -- Time into seqCompTime.eval
    set n := (encodePair (x, w)).length with hn_def
    have hxlen : x.length ≤ n := by
      simp [hn_def, length_encodePair]; omega
    have h1le : 3 * x.length + w.length + 3 ≤ projFirstTime.eval n := by
      simpa [hn_def] using projFirstTime_bound x w
    have h2le : hχ.time.eval (idBitEnc x).length ≤ hχ.time.eval n := by
      simpa [idBitEnc] using poly_eval_mono (hχ.time) hxlen
    have hcopy : (2 * x.length + 1) + (2 * x.length + 1) ≤ 4 * (n + 1) := by
      have : 4 * (x.length + 1) ≤ 4 * (n + 1) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_right hxlen 1)
      omega
    have hbound :
        3 * x.length + w.length + 3 + (2 * x.length + 1) + (2 * x.length + 1) +
            hχ.time.eval (idBitEnc x).length ≤
          (seqCompTime projFirstTime hχ.time).eval n := by
      rw [seqCompTime_eval]
      have hsum := Nat.add_le_add (Nat.add_le_add h1le hcopy) h2le
      simpa [Nat.add_assoc] using hsum
    simpa [hn_def] using evalsToInTime_le_mono heval' hbound

/-- Every language in P is in NP (ignore the witness). -/
theorem InP_implies_InNP (L : Language) (h : InP L) : InNP L := by
  rcases h with ⟨χ, hχ, hdec⟩
  refine ⟨zeroWitnessBound, ignoreWitness χ, ?_, ignoreWitness_zero_correct L χ hdec⟩
  simpa [ignoreWitness] using compose_projFirst_bitEnc hχ

/-! ### P closed under complement and bridge theorem 2 -/

/-- Flip one input bit onto the shared output stack: pop, push negation, reset state. -/
def notBitComputer : FinTM2 where
  K := Unit
  k₀ := ⟨⟩
  k₁ := ⟨⟩
  Γ _ := Bool
  Λ := Bool
  main := false
  σ := Bool
  initialState := false
  m
    | false =>
        TM2.Stmt.pop ⟨⟩ (fun _ o => Option.getD o false) <|
          TM2.Stmt.goto fun _ => true
    | true =>
        TM2.Stmt.push ⟨⟩ (fun s => !s) <|
          TM2.Stmt.load (fun _ => false) TM2.Stmt.halt

def notBitCfg (l : Option Bool) (v : Bool) (s : List Bool) : notBitComputer.Cfg :=
  ⟨l, v, fun _ => s⟩

theorem update_notBit_stk (s t : List Bool) :
    Function.update (fun _ : Unit => s) PUnit.unit t = fun _ => t := by
  funext k; cases k; simp [Function.update]

theorem notBit_step_read (b : Bool) :
    TM2.step notBitComputer.m (notBitCfg (some false) false [b]) =
      some (notBitCfg (some true) b []) := by
  simp [notBitComputer, notBitCfg, TM2.step, TM2.stepAux]
  exact congrArg some <|
    congrArg (fun stk => (⟨some true, b, stk⟩ : notBitComputer.Cfg))
      (update_notBit_stk [b] [])

theorem notBit_step_write (b : Bool) :
    TM2.step notBitComputer.m (notBitCfg (some true) b []) =
      some (notBitCfg none false [!b]) := by
  simp [notBitComputer, notBitCfg, TM2.step, TM2.stepAux]
  exact congrArg some <|
    congrArg (fun stk => (⟨none, false, stk⟩ : notBitComputer.Cfg))
      (update_notBit_stk [] [!b])

theorem notBit_initList (s : List Bool) :
    initList notBitComputer s = notBitCfg (some false) false s := by
  simp [initList, notBitComputer, notBitCfg]

theorem notBit_haltList (b : Bool) :
    haltList notBitComputer [!b] = notBitCfg none false [!b] := by
  simp [haltList, notBitComputer, notBitCfg]

def notBit_evals_one (b : Bool) :
    EvalsToInTime notBitComputer.step
      (initList notBitComputer [b])
      (some (haltList notBitComputer [!b])) 2 where
  steps := 2
  steps_le_m := le_rfl
  evals_in_steps := by
    change ((some (initList notBitComputer [b])).bind notBitComputer.step).bind
        notBitComputer.step =
      some (haltList notBitComputer [!b])
    simp only [FinTM2.step, notBit_initList, notBit_haltList]
    change (TM2.step notBitComputer.m (notBitCfg (some false) false [b])).bind
        (TM2.step notBitComputer.m) =
      some (notBitCfg none false [!b])
    rw [notBit_step_read b]
    exact notBit_step_write b

noncomputable def notBitTime : Polynomial ℕ := 2

theorem notBitTime_eval (n : ℕ) : notBitTime.eval n = 2 := by
  simp [notBitTime]

/-- Boolean negation under `bitEnc`. -/
noncomputable def notBitComputableInPolyTime :
    TM2ComputableInPolyTime bitEnc bitEnc (fun b => !b) where
  tm := notBitComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := notBitTime
  outputsFun a := by
    change TM2OutputsInTime notBitComputer (List.map id (bitEnc a))
      (some (List.map id (bitEnc (!a)))) (notBitTime.eval (bitEnc a).length)
    simp only [bitEnc, List.map_id, notBitTime_eval]
    exact notBit_evals_one a

/-- Negate an InP characteristic after its bit output. -/
noncomputable def compose_notAfter {χ : List Bool → Bool}
    (hχ : TM2ComputableInPolyTime idBitEnc bitEnc χ) :
    TM2ComputableInPolyTime idBitEnc bitEnc (fun x => !(χ x)) := by
  let decodeOut : hχ.tm.Γ hχ.tm.k₁ → Bool := hχ.outputAlphabet
  let encodeIn : Bool → notBitComputer.Γ notBitComputer.k₀ := id
  let tm :=
    seqCompComputer (βΓ := Bool) hχ.tm notBitComputer decodeOut encodeIn
  let inA : tm.Γ tm.k₀ ≃ Bool := by
    let e : tm.Γ tm.k₀ ≃ hχ.tm.Γ hχ.tm.k₀ := by
      simpa [tm, seqCompComputer, CompΓ, CompK] using
        (Equiv.refl (hχ.tm.Γ hχ.tm.k₀))
    exact e.trans hχ.inputAlphabet
  let outA : tm.Γ tm.k₁ ≃ Bool := by
    simpa [tm, seqCompComputer, CompΓ, CompK] using (Equiv.refl Bool)
  refine
    { tm := tm
      inputAlphabet := inA
      outputAlphabet := outA
      -- Copy cost is 8 for a length-1 mid; seqCompTime at n=0 only budgets 6,
      -- so add a constant 2 slack (still a polynomial).
      time := seqCompTime hχ.time notBitTime + 2
      outputsFun := ?out }
  case out =>
    intro x
    change TM2OutputsInTime tm (List.map inA.invFun (idBitEnc x))
      (some (List.map outA.invFun (bitEnc (!(χ x)))))
      ((seqCompTime hχ.time notBitTime + 2).eval (idBitEnc x).length)
    have hin :
        List.map inA.invFun (idBitEnc x) =
          List.map hχ.inputAlphabet.invFun (idBitEnc x) := by
      apply congrArg (fun f : Bool → tm.Γ tm.k₀ => List.map f (idBitEnc x))
      funext b
      simp only [inA]
      change (Equiv.refl _).symm (hχ.inputAlphabet.symm b) = hχ.inputAlphabet.symm b
      rfl
    have hout :
        List.map outA.invFun (bitEnc (!(χ x))) = [!(χ x)] := by
      change List.map (Equiv.refl Bool).symm (bitEnc (!(χ x))) = [!(χ x)]
      simp [bitEnc]
    have h1 := hχ.outputsFun x
    have hmid :
        (List.map hχ.outputAlphabet.invFun (bitEnc (χ x))).map (encodeIn ∘ decodeOut) =
          [χ x] := by
      simp [bitEnc, encodeIn, decodeOut]
      rfl
    have h2 : EvalsToInTime notBitComputer.step
        (initList notBitComputer
          ((List.map hχ.outputAlphabet.invFun (bitEnc (χ x))).map (encodeIn ∘ decodeOut)))
        (some (haltList notBitComputer [!(χ x)])) 2 := by
      rw [hmid]
      exact notBit_evals_one (χ x)
    have heval :=
      seqComp_evals_compose (βΓ := Bool) hχ.tm notBitComputer decodeOut encodeIn
        (List.map hχ.inputAlphabet.invFun (idBitEnc x))
        (List.map hχ.outputAlphabet.invFun (bitEnc (χ x)))
        [!(χ x)]
        (hχ.time.eval (idBitEnc x).length) 2 h1 h2
    -- mid has length 1, so compose time is time.eval + 3 + 3 + 2
    have heval' :
        EvalsToInTime (TM2.step tm.m)
          (initList tm (List.map inA.invFun (idBitEnc x)))
          (some (haltList tm (List.map outA.invFun (bitEnc (!(χ x))))))
          (hχ.time.eval (idBitEnc x).length + 3 + 3 + 2) := by
      have hlen :
          (List.map hχ.outputAlphabet.invFun (bitEnc (χ x))).length = 1 := by
        simp [bitEnc]
      have h := heval
      simp only [hlen, Nat.mul_one] at h
      -- h : Evals ... (initList tm (map hχ.invFun ...)) (some (haltList tm [!χx])) (t+3+3+2)
      rw [hin, hout]
      exact h
    have hbound :
        hχ.time.eval (idBitEnc x).length + 3 + 3 + 2 ≤
          (seqCompTime hχ.time notBitTime + 2).eval (idBitEnc x).length := by
      simp only [seqCompTime_eval, notBitTime_eval, idBitEnc, Polynomial.eval_add,
        Polynomial.eval_ofNat]
      omega
    exact evalsToInTime_le_mono heval' hbound


/-- Negated characteristic decides the language complement. -/
theorem not_chi_decides_complement (L : Language) (χ : List Bool → Bool)
    (hdec : ∀ x, χ x = true ↔ L x) :
    ∀ x, Bool.not (χ x) = true ↔ complement L x := by
  intro x
  cases hχx : χ x with
  | false =>
      have hL : ¬ L x := by
        intro hL
        have := (hdec x).mpr hL
        exact Bool.noConfusion (hχx.symm.trans this)
      simpa [complement] using hL
  | true =>
      have hL : L x := (hdec x).mp hχx
      simp [complement, hL]

/-- Deterministic poly time is closed under complement (flip the output bit). -/
theorem InP_complement (L : Language) (h : InP L) : InP (complement L) := by
  rcases h with ⟨χ, hχ, hdec⟩
  refine ⟨fun x => Bool.not (χ x), compose_notAfter hχ, not_chi_decides_complement L χ hdec⟩

/-- Bridge theorem 2: P = NP implies NP = coNP. -/
theorem classP_eq_classNP_implies_NP_eq_coNP
    (h : ClassP_eq_ClassNP) : ClassNP_eq_ClassCoNP := by
  intro L
  constructor
  · intro hNP
    have hP : InP L := (h L).mpr hNP
    exact InP_implies_InNP (complement L) (InP_complement L hP)
  · intro hCo
    have hPc : InP (complement L) := (h (complement L)).mpr (by simpa [InCoNP] using hCo)
    have hP : InP L := by
      simpa [complement_complement] using InP_complement (complement L) hPc
    exact (h L).mp hP

end SATurday.Bridge

/-! ## Frontier

Cook Reckhow class equalities `InP_implies_InNP` and
`classP_eq_classNP_implies_NP_eq_coNP` are accepted. Remaining R5 work is
outside this module (FormulaEncoding / proof system pin). -/
