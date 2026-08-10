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
composition (`seqCompComputer`), and Bool right-constant composition
(`comp_const_right`, NP nonvacuity) are certified. Closing
`InP_implies_InNP` still needs the sequential simulation proof for
`compose_projFirst_bitEnc` (mathlib `TM2ComputableInPolyTime.comp` is
`proof_wanted`).

LOG: R5 Bridge Complexity module (InP InNP composition surgery NP nonvacuity)
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

/-- Lift stack indices through `Sum.inl`, keeping the same labels and state. -/
def stmtLiftInl {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {Γ₂ : K₂ → Type} {Λ σ : Type} :
    TM2.Stmt Γ₁ Λ σ → TM2.Stmt (Sum.elim Γ₁ Γ₂) Λ σ
  | .push k f q => .push (Sum.inl k) f (stmtLiftInl q)
  | .peek k f q => .peek (Sum.inl k) f (stmtLiftInl q)
  | .pop k f q => .pop (Sum.inl k) f (stmtLiftInl q)
  | .load f q => .load f (stmtLiftInl q)
  | .branch p q₁ q₂ => .branch p (stmtLiftInl q₁) (stmtLiftInl q₂)
  | .goto f => .goto f
  | .halt => .halt

/-- Lift stack indices through `Sum.inr`. -/
def stmtLiftInr {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {Γ₂ : K₂ → Type} {Λ σ : Type} :
    TM2.Stmt Γ₂ Λ σ → TM2.Stmt (Sum.elim Γ₁ Γ₂) Λ σ
  | .push k f q => .push (Sum.inr k) f (stmtLiftInr q)
  | .peek k f q => .peek (Sum.inr k) f (stmtLiftInr q)
  | .pop k f q => .pop (Sum.inr k) f (stmtLiftInr q)
  | .load f q => .load f (stmtLiftInr q)
  | .branch p q₁ q₂ => .branch p (stmtLiftInr q₁) (stmtLiftInr q₂)
  | .goto f => .goto f
  | .halt => .halt

/-- Labels for the sequential product: run first TM, copy out→in, run second. -/
inductive CompLabel (Λ₁ Λ₂ : Type) where
  | first : Λ₁ → CompLabel Λ₁ Λ₂
  | copyPop : CompLabel Λ₁ Λ₂
  | copyPush : CompLabel Λ₁ Λ₂
  | second : Λ₂ → CompLabel Λ₁ Λ₂
  deriving Repr

/-- Equivalence packing composition labels as a sum (gives Fintype for free). -/
def equivCompLabel (Λ₁ Λ₂ : Type) : CompLabel Λ₁ Λ₂ ≃ Λ₁ ⊕ Bool ⊕ Λ₂ where
  toFun
    | .first l => .inl l
    | .copyPop => .inr (.inl false)
    | .copyPush => .inr (.inl true)
    | .second l => .inr (.inr l)
  invFun
    | .inl l => .first l
    | .inr (.inl false) => .copyPop
    | .inr (.inl true) => .copyPush
    | .inr (.inr l) => .second l
  left_inv
    | .first _ | .copyPop | .copyPush | .second _ => rfl
  right_inv
    | .inl _ | .inr (.inl false) | .inr (.inl true) | .inr (.inr _) => rfl

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

/-- Stack family of the sequential product. -/
def compΓ {K₁ K₂ : Type} (Γ₁ : K₁ → Type) (Γ₂ : K₂ → Type) :
    K₁ ⊕ K₂ → Type :=
  Sum.elim Γ₁ Γ₂

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

/-- Copy pop: read one symbol from the first output stack into the buffer;
if empty, jump to the second machine's main label. -/
def copyPopStmt {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {Γ₂ : K₂ → Type}
    {Λ₁ Λ₂ σ₁ σ₂ βΓ : Type} [Inhabited βΓ] [DecidableEq βΓ]
    (kOut : K₁) (decodeOut : Γ₁ kOut → βΓ) (secondMain : Λ₂) :
    TM2.Stmt (Sum.elim Γ₁ Γ₂) (CompLabel Λ₁ Λ₂) (Compσ σ₁ σ₂ βΓ) :=
  .pop (Sum.inl kOut)
    (fun st o =>
      match o with
      | none => (st.1, st.2.1, none)
      | some x => (st.1, st.2.1, some (decodeOut x))) <|
    .branch (fun st => decide (st.2.2 = none))
      (.goto fun _ => CompLabel.second secondMain)
      (.goto fun _ => CompLabel.copyPush)

/-- Copy push: write the buffered symbol onto the second input stack and loop. -/
def copyPushStmt {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {Γ₂ : K₂ → Type}
    {Λ₁ Λ₂ σ₁ σ₂ βΓ : Type} [Inhabited βΓ]
    (kIn : K₂) (encodeIn : βΓ → Γ₂ kIn) :
    TM2.Stmt (Sum.elim Γ₁ Γ₂) (CompLabel Λ₁ Λ₂) (Compσ σ₁ σ₂ βΓ) :=
  .push (Sum.inr kIn) (fun st => encodeIn (st.2.2.getD default)) <|
    .load (fun st => (st.1, st.2.1, none)) <|
      .goto fun _ => CompLabel.copyPop

/-- First-phase program: lift stacks and state, remap labels into `CompLabel.first`,
and send former `halt` to `copyPop`. -/
def firstPhaseStmt {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {Γ₂ : K₂ → Type}
    {Λ₁ Λ₂ σ₁ σ₂ βΓ : Type}
    (q : TM2.Stmt Γ₁ Λ₁ σ₁) :
    TM2.Stmt (Sum.elim Γ₁ Γ₂) (CompLabel Λ₁ Λ₂) (Compσ σ₁ σ₂ βΓ) :=
  stmtRemap CompLabel.first (fun _ => CompLabel.copyPop)
    (stmtLiftInl (stmtLiftState₁ q : TM2.Stmt Γ₁ Λ₁ (Compσ σ₁ σ₂ βΓ)))

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

/-- Second-phase program: lift stacks and state, remap labels into
`CompLabel.second`, preserve genuine `halt`. -/
def secondPhaseStmt {K₁ K₂ : Type} {Γ₁ : K₁ → Type} {Γ₂ : K₂ → Type}
    {Λ₁ Λ₂ σ₁ σ₂ βΓ : Type}
    (q : TM2.Stmt Γ₂ Λ₂ σ₂) :
    TM2.Stmt (Sum.elim Γ₁ Γ₂) (CompLabel Λ₁ Λ₂) (Compσ σ₁ σ₂ βΓ) :=
  stmtRemapGoto CompLabel.second
    (stmtLiftInr (stmtLiftState₂ q : TM2.Stmt Γ₂ Λ₂ (Compσ σ₁ σ₂ βΓ)))

/-- Sequential product FinTM2: run `tm1`, copy output tape to `tm2` input tape
(via `decodeOut` / `encodeIn` through the middle alphabet), then run `tm2`. -/
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
  letI : Fintype (Sum.elim tm1.Γ tm2.Γ (Sum.inl tm1.k₀)) := by
    change Fintype (tm1.Γ tm1.k₀)
    exact tm1.Γk₀Fin
  exact
    { K := tm1.K ⊕ tm2.K
      k₀ := Sum.inl tm1.k₀
      k₁ := Sum.inr tm2.k₁
      Γ := Sum.elim tm1.Γ tm2.Γ
      Λ := CompLabel tm1.Λ tm2.Λ
      main := CompLabel.first tm1.main
      σ := Compσ tm1.σ tm2.σ βΓ
      initialState := (tm1.initialState, tm2.initialState, none)
      m
        | .first l => firstPhaseStmt (tm1.m l)
        | .copyPop => copyPopStmt tm1.k₁ decodeOut tm2.main
        | .copyPush => copyPushStmt tm2.k₀ encodeIn
        | .second l => secondPhaseStmt (tm2.m l) }

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

/-- Time bound skeleton for sequential composition: first run, copy at most
`n + 1` symbols, then second run. Used by the Frontier composition obligation. -/
noncomputable def seqCompTime (p q : Polynomial ℕ) : Polynomial ℕ :=
  p + (Polynomial.X + 1) + q

theorem seqCompTime_eval (p q : Polynomial ℕ) (n : ℕ) :
    (seqCompTime p q).eval n = p.eval n + (n + 1) + q.eval n := by
  simp [seqCompTime, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]

end SATurday.Bridge

/-! ## Frontier: P ⊆ NP and bridge theorem 2

Accepted this cycle: statement surgery (`stmtRemap`, lifts, `seqCompComputer`),
local Bool composition `comp_const_right` / `constBit_encodePair`, and NP
nonvacuity (`emptyLanguage_in_NP`, `fullLanguage_in_NP`).

Remaining for `InP_implies_InNP`: prove `outputsFun` for
`seqCompComputer projFirstComputer h.tm` (mathlib-style sequential simulation),
i.e. local `encodePair → idBitEnc → bitEnc` composition for an arbitrary InP
witness. Bridge theorem 2 still needs P closed under complement. -/

namespace SATurday.Bridge.BridgeFrontier

open SATurday.Bridge

/-- Local composition target: project the pair then run an InP characteristic.
Machine skeleton is `seqCompComputer`; the evaluation proof is the remaining
obligation (same content as mathlib `TM2ComputableInPolyTime.comp` specialized
to Bool pair encodings). -/
noncomputable def compose_projFirst_bitEnc {χ : List Bool → Bool}
    (hχ : TM2ComputableInPolyTime idBitEnc bitEnc χ) :
    TM2ComputableInPolyTime encodePair bitEnc (fun pw => χ pw.1) := by
  let tm :=
    seqCompComputer (βΓ := Bool) projFirstComputer hχ.tm
      (fun b : Bool => b)
      (fun b : Bool => hχ.inputAlphabet.symm b)
  refine
    { tm := tm
      inputAlphabet := ?inA
      outputAlphabet := ?outA
      time := seqCompTime projFirstTime hχ.time
      outputsFun := fun _ => by sorry }
  case inA =>
    -- Input stack is left injection of projFirst's Bool input stack.
    simpa [tm, seqCompComputer] using (Equiv.refl Bool)
  case outA =>
    -- Output stack is right injection of hχ's output stack.
    let e : tm.Γ tm.k₁ ≃ hχ.tm.Γ hχ.tm.k₁ := by
      simpa [tm, seqCompComputer] using (Equiv.refl (hχ.tm.Γ hχ.tm.k₁))
    exact e.trans hχ.outputAlphabet

/-- Every language in P is in NP (ignore the witness).
Blocked on `compose_projFirst_bitEnc.outputsFun` (sequential simulation). -/
theorem InP_implies_InNP (L : Language) (h : InP L) : InNP L := by
  rcases h with ⟨χ, hχ, hdec⟩
  refine ⟨zeroWitnessBound, ignoreWitness χ, ?_, ignoreWitness_zero_correct L χ hdec⟩
  -- Need compose_projFirst_bitEnc hχ after transport ignoreWitness = χ ∘ fst.
  sorry

/-- Bridge theorem 2: P = NP implies NP = coNP. -/
theorem classP_eq_classNP_implies_NP_eq_coNP :
    ClassP_eq_ClassNP → ClassNP_eq_ClassCoNP := by
  sorry

end SATurday.Bridge.BridgeFrontier
