import Theory.ProofComplexity.Bridge.FormulaEncoding
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic

/-!
# Propositional proof systems (Ladder Rung R5)

Cook Reckhow proof systems over `TAUT`: a poly time function whose image is
exactly the language of encoded tautologies, plus the polynomially bounded
predicate.

Cluster 1 (2026-08-21): structure definitions, finite truth table machinery,
and the semantic truth table proof map (sound and complete for `TAUT`).
The TM2 poly time witness for that map, and the exponential size lower bound,
remain Frontier.

LOG: R5 Bridge ProofSystem cluster 1 (defs and TT semantic map)
-/

open Turing
open scoped Polynomial

namespace SATurday.Bridge

/-! ## Proof system predicates -/

/-- A propositional proof system: poly time `f` with image exactly `TAUT`.
Bundled as a Type (the poly time witness is data, not a bare Prop). -/
structure IsPropProofSystem (f : List Bool → List Bool) where
  /-- `f` is computable in deterministic polynomial time on bit strings. -/
  poly : TM2ComputableInPolyTime idBitEnc idBitEnc f
  /-- Soundness: every output of `f` is an encoded tautology. -/
  sound : ∀ π, TAUT (f π)
  /-- Completeness: every encoded tautology is hit by some proof. -/
  complete : ∀ φ, TAUT φ → ∃ π, f π = φ

/-- Polynomially bounded: every tautology has a proof of poly length in `|φ|`. -/
def PolynomiallyBounded (f : List Bool → List Bool) : Prop :=
  ∃ q : Polynomial ℕ, ∀ φ, TAUT φ → ∃ π, f π = φ ∧ π.length ≤ q.eval φ.length

/-! ## Finite assignment evaluation -/

/-- Largest variable index occurring in a formula. -/
def PropFormula.maxVar : PropFormula → ℕ
  | var i => i
  | not φ => φ.maxVar
  | and φ ψ => max φ.maxVar ψ.maxVar
  | or φ ψ => max φ.maxVar ψ.maxVar

/-- Evaluate under a finite assignment list (`getD` defaults missing vars to false). -/
def PropFormula.evalOn (σ : List Bool) : PropFormula → Bool
  | var i => σ.getD i false
  | not φ => !(evalOn σ φ)
  | and φ ψ => evalOn σ φ && evalOn σ ψ
  | or φ ψ => evalOn σ φ || evalOn σ ψ

/-- `evalOn` matches reading the list as a pointwise assignment. -/
theorem evalOn_eq_eval_getD (φ : PropFormula) (σ : List Bool) :
    φ.evalOn σ = φ.eval (fun i => σ.getD i false) := by
  induction φ with
  | var i => simp [PropFormula.eval, PropFormula.evalOn]
  | not φ ih => simp [PropFormula.eval, PropFormula.evalOn, ih]
  | and φ ψ ihφ ihψ => simp [PropFormula.eval, PropFormula.evalOn, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [PropFormula.eval, PropFormula.evalOn, ihφ, ihψ]

/-- Evaluation depends only on assignments to variables at most `maxVar`. -/
theorem eval_eq_of_agree (φ : PropFormula) (σ τ : ℕ → Bool)
    (h : ∀ i ≤ φ.maxVar, σ i = τ i) :
    φ.eval σ = φ.eval τ := by
  induction φ with
  | var i =>
      simp [PropFormula.eval]
      exact h i (by simp [PropFormula.maxVar])
  | not φ ih =>
      simp [PropFormula.eval]
      rw [ih fun i hi => h i (by simp [PropFormula.maxVar]; omega)]
  | and φ ψ ihφ ihψ =>
      simp [PropFormula.eval]
      have hφ : ∀ i ≤ φ.maxVar, σ i = τ i := fun i hi =>
        h i (by simp [PropFormula.maxVar]; omega)
      have hψ : ∀ i ≤ ψ.maxVar, σ i = τ i := fun i hi =>
        h i (by simp [PropFormula.maxVar]; omega)
      rw [ihφ hφ, ihψ hψ]
  | or φ ψ ihφ ihψ =>
      simp [PropFormula.eval]
      have hφ : ∀ i ≤ φ.maxVar, σ i = τ i := fun i hi =>
        h i (by simp [PropFormula.maxVar]; omega)
      have hψ : ∀ i ≤ ψ.maxVar, σ i = τ i := fun i hi =>
        h i (by simp [PropFormula.maxVar]; omega)
      rw [ihφ hφ, ihψ hψ]

/-- Semantic eval agrees with finite `evalOn` on the prefix `0 .. maxVar`. -/
theorem eval_eq_evalOn (φ : PropFormula) (σ : ℕ → Bool) :
    φ.eval σ = φ.evalOn ((List.range (φ.maxVar + 1)).map σ) := by
  rw [evalOn_eq_eval_getD]
  refine eval_eq_of_agree φ σ _ ?_
  intro i hi
  have hi' : i < φ.maxVar + 1 := Nat.lt_succ_of_le hi
  have hlen : ((List.range (φ.maxVar + 1)).map σ).length = φ.maxVar + 1 := by
    simp
  simp [List.getD_eq_getElem?_getD, hi', hlen]

/-! ## Truth tables -/

/-- All bit strings of a fixed length (length `2^n`, each entry length `n`). -/
def allBitstrings : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBitstrings n).flatMap fun t => [false :: t, true :: t]

theorem length_allBitstrings (n : ℕ) : (allBitstrings n).length = 2 ^ n := by
  induction n with
  | zero => simp [allBitstrings]
  | succ n ih =>
      simp [allBitstrings, List.length_flatMap, ih]
      ring

theorem length_mem_allBitstrings (n : ℕ) (s : List Bool) (hs : s ∈ allBitstrings n) :
    s.length = n := by
  induction n generalizing s with
  | zero =>
      simp [allBitstrings] at hs
      subst hs; rfl
  | succ n ih =>
      simp [allBitstrings, List.mem_flatMap] at hs
      rcases hs with ⟨t, ht, hcases⟩
      rcases hcases with h | h <;> subst h <;> simp [ih t ht]

/-- Every length `n` string appears in `allBitstrings n`. -/
theorem mem_allBitstrings_of_length (s : List Bool) :
    s ∈ allBitstrings s.length := by
  induction s with
  | nil => simp [allBitstrings]
  | cons b s ih =>
      simp [allBitstrings, List.mem_flatMap]
      refine ⟨s, ih, ?_⟩
      cases b <;> simp

/-- Truth table of `φ` on all assignments to variables `0 .. maxVar`. -/
def truthTableOf (φ : PropFormula) : List Bool :=
  (allBitstrings (φ.maxVar + 1)).map (fun σ => φ.evalOn σ)

/-- Check that `table` is exactly the all true truth table of `φ`. -/
def validatesTautology (φ : PropFormula) (table : List Bool) : Prop :=
  table = truthTableOf φ ∧ ∀ b ∈ truthTableOf φ, b = true

instance (φ : PropFormula) (table : List Bool) :
    Decidable (validatesTautology φ table) := by
  unfold validatesTautology
  infer_instance

theorem validatesTautology_truthTableOf_of_tautology (φ : PropFormula)
    (h : φ.Tautology) :
    validatesTautology φ (truthTableOf φ) := by
  refine ⟨rfl, ?_⟩
  intro b hb
  simp [truthTableOf, List.mem_map] at hb
  rcases hb with ⟨σ, hσ, rfl⟩
  have : φ.eval (fun i => σ.getD i false) = true := h _
  simpa [evalOn_eq_eval_getD] using this

theorem tautology_of_validatesTautology (φ : PropFormula) (table : List Bool)
    (h : validatesTautology φ table) : φ.Tautology := by
  rcases h with ⟨rfl, hall⟩
  intro σ
  let τ : List Bool := (List.range (φ.maxVar + 1)).map σ
  have hlen : τ.length = φ.maxVar + 1 := by simp [τ]
  have hmem : τ ∈ allBitstrings (φ.maxVar + 1) := by
    simpa [hlen] using mem_allBitstrings_of_length τ
  have heq := eval_eq_evalOn φ σ
  have hτ : φ.evalOn τ = true := by
    apply hall
    simp [truthTableOf, List.mem_map]
    exact ⟨τ, hmem, rfl⟩
  simpa [heq, τ] using hτ

/-! ## Truth table proof map (semantic Cook Reckhow witness) -/

/-- Truth table proof system map: proofs are `encodePair (φCode, table)`.
If the table validates `φCode` as a tautology, output `φCode`; otherwise output
the seed tautology encoding (keeps the map total and sound). -/
def truthTableProofSystem (π : List Bool) : List Bool :=
  match decodePair π with
  | none => encodeFormula tautSeed
  | some (φCode, table) =>
      match decodeFormula φCode with
      | none => encodeFormula tautSeed
      | some φ =>
          if validatesTautology φ table then φCode else encodeFormula tautSeed

theorem truthTableProofSystem_sound (π : List Bool) :
    TAUT (truthTableProofSystem π) := by
  unfold truthTableProofSystem
  cases hpair : decodePair π with
  | none =>
      simp [hpair]
      exact tautSeed_mem_TAUT
  | some pw =>
      rcases pw with ⟨φCode, table⟩
      simp [hpair]
      cases hφ : decodeFormula φCode with
      | none =>
          simp [hφ]
          exact tautSeed_mem_TAUT
      | some φ =>
          simp [hφ]
          split_ifs with hval
          · exact ⟨φ, hφ, tautology_of_validatesTautology φ table hval⟩
          · exact tautSeed_mem_TAUT

theorem truthTableProofSystem_complete :
    ∀ φ, TAUT φ → ∃ π, truthTableProofSystem π = φ := by
  intro φ hTAUT
  rcases hTAUT with ⟨ψ, hdec, htaut⟩
  refine ⟨encodePair (φ, truthTableOf ψ), ?_⟩
  have hval := validatesTautology_truthTableOf_of_tautology ψ htaut
  simp [truthTableProofSystem, decodePair_encodePair, hdec, hval]

/-- Semantic half of the truth table witness (poly time still Frontier). -/
theorem truthTableProofSystem_sound_and_complete :
    (∀ π, TAUT (truthTableProofSystem π)) ∧
      (∀ φ, TAUT φ → ∃ π, truthTableProofSystem π = φ) :=
  ⟨truthTableProofSystem_sound, truthTableProofSystem_complete⟩

namespace ProofSystemFrontier

/-- Full `IsPropProofSystem` instance once a TM2 poly time witness for
`truthTableProofSystem` is certified (verification is poly in the proof length). -/
theorem truthTable_is_prop_proof_system :
    Nonempty (IsPropProofSystem truthTableProofSystem) := by
  sorry

/-- Truth table proofs are exponential in formula size, so not poly bounded. -/
theorem truthTable_not_poly_bounded :
    ¬ PolynomiallyBounded truthTableProofSystem := by
  sorry

end ProofSystemFrontier

end SATurday.Bridge
