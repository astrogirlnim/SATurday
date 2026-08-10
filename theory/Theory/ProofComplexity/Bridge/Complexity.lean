import Theory.ProofComplexity.Bridge.Encoding
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

/-!
# Complexity classes over TM2 poly time (Ladder Rung R5)

Pinned class predicates `InP`, `InNP`, `InCoNP` using mathlib's
`Turing.TM2ComputableInPolyTime`. Class equality propositions match the
Cook Reckhow bridge pin. Constant bit InP nonvacuity and `encodePair`
projection (`projFirstComputableInPolyTime`) are certified. Closing
`InP_implies_InNP` still needs poly time composition with an arbitrary
InP witness (mathlib `TM2ComputableInPolyTime.comp` is `proof_wanted`).

LOG: R5 Bridge Complexity module (InP InNP InCoNP, encodePair projFirst)
-/

open Turing
open TM2.Stmt
open StateTransition
open scoped Polynomial

namespace SATurday.Bridge

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


end SATurday.Bridge

/-! ## Frontier: P ⊆ NP and bridge theorem 2

`projFirstComputableInPolyTime` and `ignoreWitness_under_fst` are certified.
Remaining for `InP_implies_InNP`: compose those two into one
`TM2ComputableInPolyTime encodePair bitEnc (fun pw => χ pw.1)` (mathlib
`TM2ComputableInPolyTime.comp` is still `proof_wanted`). Bridge theorem 2
still needs P closed under complement. -/

namespace SATurday.Bridge.BridgeFrontier

open SATurday.Bridge

/-- Every language in P is in NP (ignore the witness).
Blocked on poly time composition of `projFirstComputableInPolyTime` with the
InP witness (`ignoreWitness_under_fst`). -/
theorem InP_implies_InNP (L : Language) (h : InP L) : InNP L := by
  sorry

/-- Bridge theorem 2: P = NP implies NP = coNP. -/
theorem classP_eq_classNP_implies_NP_eq_coNP :
    ClassP_eq_ClassNP → ClassNP_eq_ClassCoNP := by
  sorry

end SATurday.Bridge.BridgeFrontier
