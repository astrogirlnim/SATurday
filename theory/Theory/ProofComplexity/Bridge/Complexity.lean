import Theory.ProofComplexity.Bridge.Encoding
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

/-!
# Complexity classes over TM2 poly time (Ladder Rung R5)

Pinned class predicates `InP`, `InNP`, `InCoNP` using mathlib's
`Turing.TM2ComputableInPolyTime`. Class equality propositions match the
Cook Reckhow bridge pin. Constant bit nonvacuity is certified; P ⊆ NP and
bridge theorem 2 remain in `BridgeFrontier`.

LOG: R5 Bridge Complexity module (InP InNP InCoNP)
-/

open Turing
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

end SATurday.Bridge

/-! ## Frontier: P ⊆ NP and bridge theorem 2

Needs: pairing verifier TM for `InP_implies_InNP`; close P under complement for
bridge theorem 2. Mathlib leaves `TM2ComputableInPolyTime.comp` as
`proof_wanted`. Constant bit nonvacuity is certified above. -/

namespace SATurday.Bridge.BridgeFrontier

open SATurday.Bridge

/-- Every language in P is in NP (ignore the witness; needs pairing TM). -/
theorem InP_implies_InNP (L : Language) (h : InP L) : InNP L := by
  sorry

/-- Bridge theorem 2: P = NP implies NP = coNP. -/
theorem classP_eq_classNP_implies_NP_eq_coNP :
    ClassP_eq_ClassNP → ClassNP_eq_ClassCoNP := by
  sorry

end SATurday.Bridge.BridgeFrontier
