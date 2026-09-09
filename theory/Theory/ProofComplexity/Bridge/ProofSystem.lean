import Theory.ProofComplexity.Bridge.FormulaEncoding
import Theory.ProofComplexity.Bridge.Complexity
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Nat.Bits
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

/-! ## Index ordered assignments (`assignmentAt`)

The i-th element of `allBitstrings n` in the fixed flatMap order used by
`truthTableOf`. Cluster C2 index loop validation reads assignments by index. -/

/-- i-th assignment in `allBitstrings n` (meaningful when `i < 2 ^ n`). -/
def assignmentAt : ℕ → ℕ → List Bool
  | 0, 0 => []
  | 0, _ + 1 => []
  | n + 1, i =>
      if i % 2 = 0 then
        false :: assignmentAt n (i / 2)
      else
        true :: assignmentAt n (i / 2)

theorem assignmentAt_zero (i : ℕ) : assignmentAt 0 i = [] := by
  cases i <;> rfl

theorem assignmentAt_length (n i : ℕ) (hi : i < 2 ^ n) :
    (assignmentAt n i).length = n := by
  induction n generalizing i with
  | zero =>
      simp [allBitstrings] at hi
      match i with
      | 0 => simp [assignmentAt]
  | succ n ih =>
      simp only [assignmentAt, Nat.pow_succ] at hi ⊢
      by_cases h : i % 2 = 0
      · simp [h, ih (i / 2) (by omega)]
      · simp [h, ih (i / 2) (by omega)]

theorem assignmentAt_mem (n i : ℕ) (hi : i < 2 ^ n) :
    assignmentAt n i ∈ allBitstrings n := by
  induction n generalizing i with
  | zero =>
      simp [allBitstrings] at hi ⊢
      match i with
      | 0 => simp [assignmentAt]
  | succ n ih =>
      simp only [assignmentAt, allBitstrings, List.mem_flatMap, List.mem_map]
      by_cases h : i % 2 = 0
      · refine ⟨assignmentAt n (i / 2), ih (i / 2) (by omega), ?_⟩
        simp [List.mem_cons, assignmentAt, h]
      · refine ⟨assignmentAt n (i / 2), ih (i / 2) (by omega), ?_⟩
        simp [List.mem_cons, assignmentAt, h]

/-! ## Mutual list: `assignmentAtList` equals `allBitstrings`

Index loop validation needs `(allBitstrings n)[i] = assignmentAt n i`. Direct
induction on `get` over `flatMap` stalled; instead build the list of all
`assignmentAt` values and prove it coincides with `allBitstrings`. -/

/-- All assignments in flatMap index order via `assignmentAt`. -/
def assignmentAtList (n : ℕ) : List (List Bool) :=
  (List.range (2 ^ n)).map (assignmentAt n)

theorem length_assignmentAtList (n : ℕ) :
    (assignmentAtList n).length = 2 ^ n := by
  simp [assignmentAtList]

/-- Even index at depth `n+1` prepends `false` to the parent assignment. -/
theorem assignmentAt_succ_mul_two (n k : ℕ) :
    assignmentAt (n + 1) (2 * k) = false :: assignmentAt n k := by
  have hmod : (2 * k) % 2 = 0 := Nat.mul_mod_right 2 k
  have hdiv : (2 * k) / 2 = k := by omega
  simp [assignmentAt, hmod, hdiv]

/-- Odd index at depth `n+1` prepends `true` to the parent assignment. -/
theorem assignmentAt_succ_mul_two_add_one (n k : ℕ) :
    assignmentAt (n + 1) (2 * k + 1) = true :: assignmentAt n k := by
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  have hdiv : (2 * k + 1) / 2 = k := by omega
  simp [assignmentAt, hmod, hdiv]

/-- `List.range (2 * m)` maps as interleaved pairs `[f(2k), f(2k+1)]`. -/
theorem map_range_two_mul {α : Type*} (m : ℕ) (f : ℕ → α) :
    (List.range (2 * m)).map f =
      (List.range m).flatMap (fun k => [f (2 * k), f (2 * k + 1)]) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hlen : 2 * (m + 1) = 2 * m + 2 := by omega
      rw [hlen, List.range_succ, List.range_succ, List.map_append, List.map_append,
        List.map_cons, List.map_nil, List.map_cons, List.map_nil, ih,
        List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil]
      simp [Nat.add_comm]

/-- `assignmentAtList` reproduces the recursive flatMap order of `allBitstrings`. -/
theorem assignmentAtList_eq_allBitstrings (n : ℕ) :
    assignmentAtList n = allBitstrings n := by
  induction n with
  | zero =>
      simp [assignmentAtList, allBitstrings, assignmentAt]
  | succ n ih =>
      -- Expand both sides; rewrite parent list via IH.
      simp only [assignmentAtList, allBitstrings, Nat.pow_succ]
      -- `2 ^ n * 2 = 2 * 2 ^ n` for the range length.
      have hpow : 2 ^ n * 2 = 2 * 2 ^ n := by omega
      rw [hpow, map_range_two_mul]
      -- Convert pair map into flatMap over parent assignments.
      have hpair :
          (List.range (2 ^ n)).flatMap
              (fun k =>
                [assignmentAt (n + 1) (2 * k), assignmentAt (n + 1) (2 * k + 1)]) =
            (List.range (2 ^ n)).flatMap
              (fun k =>
                [false :: assignmentAt n k, true :: assignmentAt n k]) := by
        congr 1
        funext k
        simp [assignmentAt_succ_mul_two, assignmentAt_succ_mul_two_add_one]
      rw [hpair]
      -- `(range.map assignmentAt).flatMap g = range.flatMap (g ∘ assignmentAt)`.
      have hswap :
          (List.range (2 ^ n)).flatMap
              (fun k => [false :: assignmentAt n k, true :: assignmentAt n k]) =
            ((List.range (2 ^ n)).map (assignmentAt n)).flatMap
              (fun t => [false :: t, true :: t]) := by
        symm
        exact List.flatMap_map (assignmentAt n) (fun t => [false :: t, true :: t])
          (List.range (2 ^ n))
      rw [hswap, ← ih]
      simp [assignmentAtList]

/-- Index `i` of `allBitstrings n` is exactly `assignmentAt n i`. -/
theorem allBitstrings_get_eq_assignmentAt (n i : ℕ)
    (hi : i < (allBitstrings n).length) :
    (allBitstrings n)[i] = assignmentAt n i := by
  have hi' : i < (assignmentAtList n).length := by
    simpa [assignmentAtList_eq_allBitstrings, length_assignmentAtList,
      length_allBitstrings] using hi
  calc
    (allBitstrings n)[i]
        = (assignmentAtList n)[i] := by
            simp [assignmentAtList_eq_allBitstrings]
      _ = assignmentAt n i := by
            simp [assignmentAtList, List.getElem_range]

/-- Truth table of `φ` on all assignments to variables `0 .. maxVar`. -/
def truthTableOf (φ : PropFormula) : List Bool :=
  (allBitstrings (φ.maxVar + 1)).map (fun σ => φ.evalOn σ)

/-- Truth table bit at index `i` is evaluation on `assignmentAt`. -/
theorem truthTableOf_get_eq_evalOn (φ : PropFormula) (i : ℕ)
    (hi : i < (truthTableOf φ).length) :
    (truthTableOf φ)[i] =
      φ.evalOn (assignmentAt (φ.maxVar + 1) i) := by
  unfold truthTableOf at hi ⊢
  have hi' : i < (allBitstrings (φ.maxVar + 1)).length := by
    simpa using hi
  simp [List.getElem_map, allBitstrings_get_eq_assignmentAt _ _ hi']

/-- Truth table length is always `2 ^ (maxVar + 1)`. -/
theorem length_truthTableOf (φ : PropFormula) :
    (truthTableOf φ).length = 2 ^ (φ.maxVar + 1) := by
  simp [truthTableOf, length_allBitstrings]

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

/-! ## Cluster C2: `validatesTautology_by_index` (index loop form)

Index loop FinTM2 plan: length gate `table.length = 2^(maxVar+1)`, then for each
`i < table.length` require `table[i] = evalOn (assignmentAt ... i)` and
`table[i] = true`. Equivalent to list form `validatesTautology`. -/

/-- Index loop validation: length gate plus per index eval and all true. -/
def validatesTautology_by_index (φ : PropFormula) (table : List Bool) : Prop :=
  table.length = 2 ^ (φ.maxVar + 1) ∧
    ∀ (i : ℕ) (hi : i < table.length),
      table[i] = φ.evalOn (assignmentAt (φ.maxVar + 1) i) ∧ table[i] = true

instance (φ : PropFormula) (table : List Bool) :
    Decidable (validatesTautology_by_index φ table) := by
  unfold validatesTautology_by_index
  infer_instance

/-- List form implies index loop form. -/
theorem validatesTautology_by_index_of_validatesTautology (φ : PropFormula)
    (table : List Bool) (h : validatesTautology φ table) :
    validatesTautology_by_index φ table := by
  rcases h with ⟨htbl, hall⟩
  refine ⟨?hlen, ?hidx⟩
  · -- Length gate from truth table length.
    simpa [htbl, length_truthTableOf] using rfl
  · intro i hi
    -- Rewrite table to truthTableOf for get and membership.
    have hi' : i < (truthTableOf φ).length := by simpa [htbl] using hi
    have hget : table[i] = (truthTableOf φ)[i] := by simp [htbl]
    have heval := truthTableOf_get_eq_evalOn φ i hi'
    have htrue : table[i] = true := by
      have hmem : table[i] ∈ truthTableOf φ := by
        simpa [htbl] using List.getElem_mem hi'
      exact hall _ hmem
    exact ⟨hget.trans heval, htrue⟩

/-- Index loop form implies list form. -/
theorem validatesTautology_of_by_index (φ : PropFormula) (table : List Bool)
    (h : validatesTautology_by_index φ table) :
    validatesTautology φ table := by
  rcases h with ⟨hlen, hidx⟩
  have hlen' : table.length = (truthTableOf φ).length := by
    simpa [length_truthTableOf] using hlen
  -- Pointwise get equality yields list equality.
  have htbl : table = truthTableOf φ := by
    apply List.ext_getElem hlen'
    intro i hi_table hi_tt
    have hpair := hidx i hi_table
    have heval := truthTableOf_get_eq_evalOn φ i hi_tt
    exact hpair.1.trans heval.symm
  refine ⟨htbl, ?_⟩
  intro b hb
  -- Every member is some `table[i]` after rewriting.
  have hb' : b ∈ table := by simpa [htbl] using hb
  rcases List.mem_iff_getElem.mp hb' with ⟨i, hi, rfl⟩
  exact (hidx i hi).2

/-- Certified equivalence: list validation iff index loop validation. -/
theorem validatesTautology_iff_by_index (φ : PropFormula) (table : List Bool) :
    validatesTautology φ table ↔ validatesTautology_by_index φ table :=
  ⟨validatesTautology_by_index_of_validatesTautology φ table,
    validatesTautology_of_by_index φ table⟩

/-! ## Cluster C2 length gate (FinTM2 reject path)

Index loop FinTM2 step 3: if `table.length ≠ 2^(maxVar+1)`, reject with `[true]`
without entering the per index loop. This is the first machine oriented gate. -/

/-- Length gate Bool the FinTM2 branches on before the index loop. -/
def lengthGateOk (φ : PropFormula) (table : List Bool) : Bool :=
  decide (table.length = 2 ^ (φ.maxVar + 1))

theorem lengthGateOk_iff (φ : PropFormula) (table : List Bool) :
    lengthGateOk φ table = true ↔ table.length = 2 ^ (φ.maxVar + 1) := by
  simp [lengthGateOk]

/-- Length gate holds on every accepting index loop witness. -/
theorem lengthGateOk_of_validatesTautology_by_index (φ : PropFormula)
    (table : List Bool) (h : validatesTautology_by_index φ table) :
    lengthGateOk φ table = true := by
  have hlen := h.1
  simp [lengthGateOk, hlen]

/-- Failed length gate falsifies the index loop form. -/
theorem not_validatesTautology_by_index_of_lengthGateFail (φ : PropFormula)
    (table : List Bool) (h : lengthGateOk φ table = false) :
    ¬ validatesTautology_by_index φ table := by
  intro hval
  have htrue := lengthGateOk_of_validatesTautology_by_index φ table hval
  exact Bool.false_ne_true (h.symm.trans htrue)

/-- Failed length gate falsifies the list form (via certified equivalence). -/
theorem not_validatesTautology_of_lengthGateFail (φ : PropFormula)
    (table : List Bool) (h : lengthGateOk φ table = false) :
    ¬ validatesTautology φ table := by
  intro hval
  exact not_validatesTautology_by_index_of_lengthGateFail φ table h
    (validatesTautology_by_index_of_validatesTautology φ table hval)

/-! ## Cluster C2 length compare scaffolding (binary of `2^n`)

FinTM2 length gate needs a poly size witness for `2^(maxVar+1)`: little endian
bits `false^n ++ [true]`, not a unary tape of length `2^n`. The machine below
writes those bits from unary `encodeNat n` (push order yields the reverse). -/

/-- Little endian bits of `2 ^ n`: `n` zeros then a one. -/
def pow2BitsLE (n : ℕ) : List Bool :=
  List.replicate n false ++ [true]

theorem length_pow2BitsLE (n : ℕ) : (pow2BitsLE n).length = n + 1 := by
  simp [pow2BitsLE]

/-- Numeric value of a little endian bit list (head is least significant). -/
def bitsLEValue : List Bool → ℕ
  | [] => 0
  | b :: bs => (bif b then 1 else 0) + 2 * bitsLEValue bs

theorem bitsLEValue_pow2BitsLE (n : ℕ) :
    bitsLEValue (pow2BitsLE n) = 2 ^ n := by
  induction n with
  | zero => simp [pow2BitsLE, bitsLEValue]
  | succ n ih =>
      have hform : pow2BitsLE (n + 1) = false :: pow2BitsLE n := by
        simp [pow2BitsLE, List.replicate_succ]
      rw [hform, bitsLEValue, ih]
      simp [Nat.pow_succ, Nat.mul_comm]

/-- Length equals a power of two (FinTM2 compare target on Nat). -/
def lengthEqPow2 (n : ℕ) (table : List Bool) : Bool :=
  decide (table.length = 2 ^ n)

theorem lengthEqPow2_iff (n : ℕ) (table : List Bool) :
    lengthEqPow2 n table = true ↔ table.length = 2 ^ n := by
  simp [lengthEqPow2]

theorem lengthEqPow2_iff_bits (n : ℕ) (table : List Bool) :
    lengthEqPow2 n table = true ↔
      table.length = bitsLEValue (pow2BitsLE n) := by
  rw [lengthEqPow2_iff, bitsLEValue_pow2BitsLE]

/-- Length gate is lengthEqPow2 at bit width `maxVar + 1`. -/
theorem lengthGateOk_eq_lengthEqPow2 (φ : PropFormula) (table : List Bool) :
    lengthGateOk φ table = lengthEqPow2 (φ.maxVar + 1) table := by
  simp [lengthGateOk, lengthEqPow2]

theorem lengthGateOk_iff_bits (φ : PropFormula) (table : List Bool) :
    lengthGateOk φ table = true ↔
      table.length = bitsLEValue (pow2BitsLE (φ.maxVar + 1)) := by
  rw [lengthGateOk_eq_lengthEqPow2, lengthEqPow2_iff_bits]

/-- Push order of `writePow2BitsComputer`: one then `n` zeros. -/
def pow2BitsWriteOrder (n : ℕ) : List Bool :=
  true :: List.replicate n false

theorem pow2BitsWriteOrder_eq_reverse (n : ℕ) :
    pow2BitsWriteOrder n = (pow2BitsLE n).reverse := by
  simp [pow2BitsWriteOrder, pow2BitsLE, List.reverse_append, List.reverse_cons,
    List.reverse_replicate]

/-- Moving one false across a false block: used by writePow2 accumulator step. -/
theorem replicate_false_append_cons (n : ℕ) (out : List Bool) :
    List.replicate n false ++ false :: out =
      false :: List.replicate n false ++ out := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [List.replicate_succ, List.cons_append] using
        congrArg (fun t => false :: t) ih

open TM2.Stmt

inductive WritePow2Stack where
  | inp | out
  deriving DecidableEq, Repr

instance : Fintype WritePow2Stack where
  elems := {.inp, .out}
  complete s := by cases s <;> simp

/-- Read unary `encodeNat n`, push `false` per `true`, then push `true` on the
terminator and halt. Output is `pow2BitsWriteOrder n`. -/
inductive WritePow2Label where
  | loop
  deriving DecidableEq, Repr

instance : Fintype WritePow2Label where
  elems := {.loop}
  complete s := by cases s <;> simp

/-- FinTM2 Stmt scaffolding: unary width `n` to binary bits of `2^n`. -/
def writePow2BitsComputer : FinTM2 where
  K := WritePow2Stack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := WritePow2Label
  main := .loop
  σ := Option Bool
  initialState := none
  m
    | .loop =>
        pop WritePow2Stack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) halt)
            (branch (fun s => decide (s = some true))
              (push WritePow2Stack.out (fun _ => false) <|
                load (fun _ => none) <|
                  goto fun _ => WritePow2Label.loop)
              (push WritePow2Stack.out (fun _ => true) <|
                load (fun _ => none) halt))

def writePow2Stk (inp out : List Bool) : WritePow2Stack → List Bool
  | .inp => inp
  | .out => out

def writePow2Cfg (l : Option WritePow2Label) (v : Option Bool)
    (inp out : List Bool) : writePow2BitsComputer.Cfg :=
  ⟨l, v, writePow2Stk inp out⟩

theorem writePow2_step_true (xs out : List Bool) :
    TM2.step writePow2BitsComputer.m
      (writePow2Cfg (some .loop) none (true :: xs) out) =
      some (writePow2Cfg (some .loop) none xs (false :: out)) := by
  simp [writePow2BitsComputer, writePow2Cfg, writePow2Stk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some WritePow2Label.loop, none, stk⟩ : writePow2BitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, writePow2Stk]

theorem writePow2_step_false (out : List Bool) :
    TM2.step writePow2BitsComputer.m
      (writePow2Cfg (some .loop) none [false] out) =
      some (writePow2Cfg none none [] (true :: out)) := by
  simp [writePow2BitsComputer, writePow2Cfg, writePow2Stk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option WritePow2Label), none, stk⟩ : writePow2BitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, writePow2Stk]

theorem writePow2_step_nil (out : List Bool) :
    TM2.step writePow2BitsComputer.m
      (writePow2Cfg (some .loop) none [] out) =
      some (writePow2Cfg none none [] out) := by
  simp [writePow2BitsComputer, writePow2Cfg, writePow2Stk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option WritePow2Label), none, stk⟩ : writePow2BitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, writePow2Stk]

theorem writePow2Bits_initList (s : List Bool) :
    initList writePow2BitsComputer s =
      writePow2Cfg (some .loop) none s [] := by
  refine congrArg (fun stk =>
      (⟨some WritePow2Label.loop, none, stk⟩ : writePow2BitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [writePow2BitsComputer, writePow2Stk]

theorem writePow2Bits_haltList (out : List Bool) :
    haltList writePow2BitsComputer out =
      writePow2Cfg none none [] out := by
  refine congrArg (fun stk =>
      (⟨(none : Option WritePow2Label), none, stk⟩ : writePow2BitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [writePow2BitsComputer, writePow2Stk]

open StateTransition

def writePow2_evals_true (xs out : List Bool) :
    EvalsToInTime writePow2BitsComputer.step
      (writePow2Cfg (some .loop) none (true :: xs) out)
      (some (writePow2Cfg (some .loop) none xs (false :: out))) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (writePow2Cfg (some .loop) none (true :: xs) out)).bind
        writePow2BitsComputer.step =
      some (writePow2Cfg (some .loop) none xs (false :: out))
    simp only [FinTM2.step]
    exact writePow2_step_true xs out

def writePow2_evals_false (out : List Bool) :
    EvalsToInTime writePow2BitsComputer.step
      (writePow2Cfg (some .loop) none [false] out)
      (some (writePow2Cfg none none [] (true :: out))) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (writePow2Cfg (some .loop) none [false] out)).bind
        writePow2BitsComputer.step =
      some (writePow2Cfg none none [] (true :: out))
    simp only [FinTM2.step]
    exact writePow2_step_false out

/-- From `encodeNat n` on inp and arbitrary out accumulator, halt with
`pow2BitsWriteOrder n ++ out` after `n + 1` steps. -/
noncomputable def writePow2Bits_evals_from (n : ℕ) (out : List Bool) :
    EvalsToInTime writePow2BitsComputer.step
      (writePow2Cfg (some .loop) none (encodeNat n) out)
      (some (writePow2Cfg none none [] (pow2BitsWriteOrder n ++ out)))
      (n + 1) := by
  induction n generalizing out with
  | zero =>
      simp only [encodeNat, pow2BitsWriteOrder, List.replicate_zero]
      have h := writePow2_evals_false out
      simpa [List.singleton_append] using h
  | succ n ih =>
      have hform : encodeNat (n + 1) = true :: encodeNat n := by
        simp [encodeNat, List.replicate_succ]
      rw [hform]
      have h1 := writePow2_evals_true (encodeNat n) out
      have hrest := ih (false :: out)
      have htrans :=
        EvalsToInTime.trans writePow2BitsComputer.step 1 (n + 1) _ _ _ h1 hrest
      have hout :
          pow2BitsWriteOrder n ++ false :: out =
            pow2BitsWriteOrder (n + 1) ++ out := by
        simp only [pow2BitsWriteOrder, List.replicate_succ, List.cons_append]
        exact congrArg (fun t => true :: t) (replicate_false_append_cons n out)
      simpa [hout, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htrans

/-- On `encodeNat n`, the machine writes `pow2BitsWriteOrder n` in `n + 1` steps. -/
noncomputable def writePow2Bits_evals (n : ℕ) :
    TM2OutputsInTime writePow2BitsComputer (encodeNat n)
      (some (pow2BitsWriteOrder n)) (n + 1) := by
  have h : EvalsToInTime writePow2BitsComputer.step
      (initList writePow2BitsComputer (encodeNat n))
      (some (haltList writePow2BitsComputer (pow2BitsWriteOrder n))) (n + 1) := by
    rw [writePow2Bits_initList, writePow2Bits_haltList]
    simpa [List.append_nil] using writePow2Bits_evals_from n []
  exact h

noncomputable def writePow2BitsTime : Polynomial ℕ := Polynomial.X

theorem writePow2BitsTime_eval (n : ℕ) :
    writePow2BitsTime.eval n = n := by
  simp [writePow2BitsTime]

/-- Writing little endian bits of `2^n` (in push order) is poly time in `|encodeNat n|`. -/
noncomputable def writePow2BitsComputableInPolyTime :
    TM2ComputableInPolyTime encodeNat idBitEnc pow2BitsWriteOrder where
  tm := writePow2BitsComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := writePow2BitsTime
  outputsFun n := by
    change TM2OutputsInTime writePow2BitsComputer
      (List.map id (encodeNat n))
      (some (List.map id (idBitEnc (pow2BitsWriteOrder n))))
      (writePow2BitsTime.eval (encodeNat n).length)
    simp only [idBitEnc, List.map_id, id_eq, writePow2BitsTime_eval]
    have hlen : (encodeNat n).length = n + 1 := by
      simp [encodeNat]
    simpa [hlen] using writePow2Bits_evals n

theorem writePow2Bits_computableInPolyTime :
    Nonempty (TM2ComputableInPolyTime encodeNat idBitEnc pow2BitsWriteOrder) :=
  ⟨writePow2BitsComputableInPolyTime⟩

/-! ## Cluster C2 count table length to bits (compare to `pow2BitsLE`)

Length gate machine path: emit little endian bits of `table.length`, then
compare structurally to `pow2BitsLE (maxVar+1)`. Unary length is not poly;
`natBitsLE` (mathlib `Nat.bits`) is the FinTM2 counter output. -/

/-- Canonical little endian bits of `n` (empty for `0`; head is LSB). -/
def natBitsLE (n : ℕ) : List Bool := Nat.bits n

theorem natBitsLE_zero : natBitsLE 0 = [] := by
  simp [natBitsLE]

theorem natBitsLE_one : natBitsLE 1 = [true] := by
  simp [natBitsLE]

theorem natBitsLE_bit (b : Bool) (n : ℕ) (hn : n = 0 → b = true) :
    natBitsLE (Nat.bit b n) = b :: natBitsLE n := by
  simpa [natBitsLE] using Nat.bits_append_bit n b hn

theorem natBitsLE_mul_two {n : ℕ} (hn : n ≠ 0) :
    natBitsLE (2 * n) = false :: natBitsLE n := by
  simpa [natBitsLE] using Nat.bit0_bits n hn

theorem natBitsLE_mul_two_add_one (n : ℕ) :
    natBitsLE (2 * n + 1) = true :: natBitsLE n := by
  simpa [natBitsLE] using Nat.bit1_bits n

theorem bitsLEValue_nil : bitsLEValue [] = 0 := rfl

theorem bitsLEValue_cons (b : Bool) (rest : List Bool) :
    bitsLEValue (b :: rest) =
      (bif b then 1 else 0) + 2 * bitsLEValue rest := rfl

theorem bitsLEValue_natBitsLE (n : ℕ) :
    bitsLEValue (natBitsLE n) = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [natBitsLE, bitsLEValue]
  | bit b n h ih =>
      rw [natBitsLE_bit b n h, bitsLEValue_cons, ih, Nat.bit_val]
      cases b <;> simp [Bool.toNat] <;> omega

/-- Powers of two have the expected little endian shape. -/
theorem natBitsLE_pow2 (n : ℕ) : natBitsLE (2 ^ n) = pow2BitsLE n := by
  induction n with
  | zero => simpa [pow2BitsLE, Nat.pow_zero] using natBitsLE_one
  | succ n ih =>
      have hne : 2 ^ n ≠ 0 := (Nat.pow_pos (by decide : 0 < (2 : ℕ))).ne'
      have hform : 2 ^ (n + 1) = 2 * (2 ^ n) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      rw [hform, natBitsLE_mul_two hne, ih]
      simp [pow2BitsLE, List.replicate_succ]

/-- Length equals `2^n` iff its canonical bits equal `pow2BitsLE n`. -/
theorem lengthEqPow2_iff_natBits (n : ℕ) (table : List Bool) :
    lengthEqPow2 n table = true ↔
      natBitsLE table.length = pow2BitsLE n := by
  rw [lengthEqPow2_iff]
  constructor
  · intro h
    rw [h, natBitsLE_pow2]
  · intro h
    have := congrArg bitsLEValue h
    simpa [bitsLEValue_natBitsLE, bitsLEValue_pow2BitsLE] using this

/-- FinTM2 length gate Bool: compare counted length bits to `pow2BitsLE`. -/
def lengthBitsEqPow2 (n : ℕ) (table : List Bool) : Bool :=
  decide (natBitsLE table.length = pow2BitsLE n)

theorem lengthBitsEqPow2_iff (n : ℕ) (table : List Bool) :
    lengthBitsEqPow2 n table = true ↔
      natBitsLE table.length = pow2BitsLE n := by
  simp [lengthBitsEqPow2]

theorem lengthEqPow2_eq_lengthBitsEqPow2 (n : ℕ) (table : List Bool) :
    lengthEqPow2 n table = lengthBitsEqPow2 n table := by
  refine Bool.eq_iff_iff.mpr ?_
  rw [lengthEqPow2_iff_natBits, lengthBitsEqPow2_iff]

theorem lengthGateOk_eq_lengthBitsEqPow2 (φ : PropFormula) (table : List Bool) :
    lengthGateOk φ table = lengthBitsEqPow2 (φ.maxVar + 1) table := by
  simp [lengthGateOk_eq_lengthEqPow2, lengthEqPow2_eq_lengthBitsEqPow2]

theorem lengthGateOk_iff_natBits (φ : PropFormula) (table : List Bool) :
    lengthGateOk φ table = true ↔
      natBitsLE table.length = pow2BitsLE (φ.maxVar + 1) := by
  rw [lengthGateOk_eq_lengthBitsEqPow2, lengthBitsEqPow2_iff]

/-- Counted length bits of a table (semantic FinTM2 output). -/
def lengthBitsLE (table : List Bool) : List Bool :=
  natBitsLE table.length

theorem lengthBitsLE_eq_pow2BitsLE_iff (n : ℕ) (table : List Bool) :
    lengthBitsLE table = pow2BitsLE n ↔ table.length = 2 ^ n := by
  constructor
  · intro h
    have := congrArg bitsLEValue h
    simpa [lengthBitsLE, bitsLEValue_natBitsLE, bitsLEValue_pow2BitsLE] using this
  · intro h
    simp [lengthBitsLE, h, natBitsLE_pow2]

/-! ## Cluster C2 FinTM2: count input length into little endian bits

Stmt scaffolding and single step lemmas. Full `EvalsToInTime` / poly time
witness for `lengthBitsLE` is the next formalize slice (carry restore fuel). -/

open TM2.Stmt

inductive CountLenStack where
  | inp | bits | aux
  deriving DecidableEq, Repr

instance : Fintype CountLenStack where
  elems := {.inp, .bits, .aux}
  complete s := by cases s <;> simp

/-- `loop` consumes one input symbol; `inc`/`restore` binary increment bits. -/
inductive CountLenLabel where
  | loop | inc | restore
  deriving DecidableEq, Repr

instance : Fintype CountLenLabel where
  elems := {.loop, .inc, .restore}
  complete s := by cases s <;> simp

/-- FinTM2: read table from `inp`, intended halt with `natBitsLE table.length` on `bits`. -/
def countLengthBitsComputer : FinTM2 where
  K := CountLenStack
  k₀ := .inp
  k₁ := .bits
  Γ _ := Bool
  Λ := CountLenLabel
  main := .loop
  σ := Option Bool
  initialState := none
  m
    | .loop =>
        pop CountLenStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            halt
            (load (fun _ => none) <| goto fun _ => CountLenLabel.inc)
    | .inc =>
        pop CountLenStack.bits (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push CountLenStack.bits (fun _ => true) <|
              load (fun _ => none) <| goto fun _ => CountLenLabel.restore)
            (branch (fun s => decide (s = some false))
              (push CountLenStack.bits (fun _ => true) <|
                load (fun _ => none) <| goto fun _ => CountLenLabel.restore)
              (push CountLenStack.aux (fun _ => false) <|
                load (fun _ => none) <| goto fun _ => CountLenLabel.inc))
    | .restore =>
        pop CountLenStack.aux (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => CountLenLabel.loop)
            (push CountLenStack.bits (fun s => Option.getD s false) <|
              load (fun _ => none) <| goto fun _ => CountLenLabel.restore)

def countLenStk (inp bits aux : List Bool) : CountLenStack → List Bool
  | .inp => inp
  | .bits => bits
  | .aux => aux

def countLenCfg (l : Option CountLenLabel) (v : Option Bool)
    (inp bits aux : List Bool) : countLengthBitsComputer.Cfg :=
  ⟨l, v, countLenStk inp bits aux⟩

theorem countLen_step_loop_cons (b : Bool) (xs bits aux : List Bool) :
    TM2.step countLengthBitsComputer.m
      (countLenCfg (some .loop) none (b :: xs) bits aux) =
      some (countLenCfg (some .inc) none xs bits aux) := by
  simp [countLengthBitsComputer, countLenCfg, countLenStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some CountLenLabel.inc, none, stk⟩ : countLengthBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, countLenStk]

theorem countLen_step_loop_nil (bits aux : List Bool) :
    TM2.step countLengthBitsComputer.m
      (countLenCfg (some .loop) none [] bits aux) =
      some (countLenCfg none none [] bits aux) := by
  simp [countLengthBitsComputer, countLenCfg, countLenStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option CountLenLabel), none, stk⟩ : countLengthBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, countLenStk]

theorem countLen_step_inc_nil (inp aux : List Bool) :
    TM2.step countLengthBitsComputer.m
      (countLenCfg (some .inc) none inp [] aux) =
      some (countLenCfg (some .restore) none inp [true] aux) := by
  simp [countLengthBitsComputer, countLenCfg, countLenStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some CountLenLabel.restore, none, stk⟩ : countLengthBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, countLenStk]

theorem countLen_step_inc_false (inp rest aux : List Bool) :
    TM2.step countLengthBitsComputer.m
      (countLenCfg (some .inc) none inp (false :: rest) aux) =
      some (countLenCfg (some .restore) none inp (true :: rest) aux) := by
  simp [countLengthBitsComputer, countLenCfg, countLenStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some CountLenLabel.restore, none, stk⟩ : countLengthBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, countLenStk]

theorem countLen_step_inc_true (inp rest aux : List Bool) :
    TM2.step countLengthBitsComputer.m
      (countLenCfg (some .inc) none inp (true :: rest) aux) =
      some (countLenCfg (some .inc) none inp rest (false :: aux)) := by
  simp [countLengthBitsComputer, countLenCfg, countLenStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some CountLenLabel.inc, none, stk⟩ : countLengthBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, countLenStk]

theorem countLen_step_restore_nil (inp bits : List Bool) :
    TM2.step countLengthBitsComputer.m
      (countLenCfg (some .restore) none inp bits []) =
      some (countLenCfg (some .loop) none inp bits []) := by
  simp [countLengthBitsComputer, countLenCfg, countLenStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some CountLenLabel.loop, none, stk⟩ : countLengthBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, countLenStk]

theorem countLen_step_restore_cons (inp : List Bool) (b : Bool) (aux bits : List Bool) :
    TM2.step countLengthBitsComputer.m
      (countLenCfg (some .restore) none inp bits (b :: aux)) =
      some (countLenCfg (some .restore) none inp (b :: bits) aux) := by
  simp [countLengthBitsComputer, countLenCfg, countLenStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some CountLenLabel.restore, none, stk⟩ : countLengthBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, countLenStk]

theorem countLengthBits_initList (s : List Bool) :
    initList countLengthBitsComputer s =
      countLenCfg (some .loop) none s [] [] := by
  refine congrArg (fun stk =>
      (⟨some CountLenLabel.loop, none, stk⟩ : countLengthBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [countLengthBitsComputer, countLenStk]

theorem countLengthBits_haltList (out : List Bool) :
    haltList countLengthBitsComputer out =
      countLenCfg none none [] out [] := by
  refine congrArg (fun stk =>
      (⟨(none : Option CountLenLabel), none, stk⟩ : countLengthBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [countLengthBitsComputer, countLenStk]

/-! ### Cluster C2: countLengthBits EvalsToInTime and polyTime -/

/-- Semantic binary increment matching the FinTM2 carry or restore loop. -/
def bitsInc : List Bool → List Bool
  | [] => [true]
  | false :: rest => true :: rest
  | true :: rest => false :: bitsInc rest

theorem length_natBitsLE_le (n : ℕ) : (natBitsLE n).length ≤ n := by
  induction n using Nat.binaryRec' with
  | zero => simp [natBitsLE]
  | bit b n hn ih =>
      rw [natBitsLE_bit b n hn, List.length_cons]
      have hle : (natBitsLE n).length + 1 ≤ n + 1 := Nat.succ_le_succ ih
      cases b with
      | false =>
          have hn0 : n ≠ 0 := fun h => by cases hn h
          have : n + 1 ≤ Nat.bit false n := by
            simp [Nat.bit_val]; omega
          exact le_trans hle this
      | true =>
          have : n + 1 ≤ Nat.bit true n := by
            simp [Nat.bit_val]; omega
          exact le_trans hle this

/-- Incrementing little endian bits of `n` yields bits of `n + 1`. -/
theorem bitsInc_natBitsLE (n : ℕ) :
    bitsInc (natBitsLE n) = natBitsLE (n + 1) := by
  induction n using Nat.binaryRec' with
  | zero =>
      simp [bitsInc, natBitsLE]
  | bit b n hn ih =>
      cases b with
      | false =>
          rw [natBitsLE_bit false n hn]
          simp only [bitsInc]
          have hbit : Nat.bit false n + 1 = Nat.bit true n := by
            simp [Nat.bit_val]
          rw [hbit, natBitsLE_bit true n (fun _ => rfl)]
      | true =>
          rw [natBitsLE_bit true n (fun _ => rfl)]
          simp only [bitsInc]
          rw [ih]
          have hbit : Nat.bit true n + 1 = Nat.bit false (n + 1) := by
            simp [Nat.bit_val]; omega
          rw [hbit, natBitsLE_bit false (n + 1) (fun h => (Nat.succ_ne_zero n h).elim)]

open StateTransition

def countLen_evals_loop_cons (b : Bool) (xs bits aux : List Bool) :
    EvalsToInTime countLengthBitsComputer.step
      (countLenCfg (some .loop) none (b :: xs) bits aux)
      (some (countLenCfg (some .inc) none xs bits aux)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (countLenCfg (some .loop) none (b :: xs) bits aux)).bind
        countLengthBitsComputer.step =
      some (countLenCfg (some .inc) none xs bits aux)
    simp only [FinTM2.step]
    exact countLen_step_loop_cons b xs bits aux

def countLen_evals_loop_nil (bits aux : List Bool) :
    EvalsToInTime countLengthBitsComputer.step
      (countLenCfg (some .loop) none [] bits aux)
      (some (countLenCfg none none [] bits aux)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (countLenCfg (some .loop) none [] bits aux)).bind
        countLengthBitsComputer.step =
      some (countLenCfg none none [] bits aux)
    simp only [FinTM2.step]
    exact countLen_step_loop_nil bits aux

def countLen_evals_inc_nil (inp aux : List Bool) :
    EvalsToInTime countLengthBitsComputer.step
      (countLenCfg (some .inc) none inp [] aux)
      (some (countLenCfg (some .restore) none inp [true] aux)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (countLenCfg (some .inc) none inp [] aux)).bind
        countLengthBitsComputer.step =
      some (countLenCfg (some .restore) none inp [true] aux)
    simp only [FinTM2.step]
    exact countLen_step_inc_nil inp aux

def countLen_evals_inc_false (inp rest aux : List Bool) :
    EvalsToInTime countLengthBitsComputer.step
      (countLenCfg (some .inc) none inp (false :: rest) aux)
      (some (countLenCfg (some .restore) none inp (true :: rest) aux)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (countLenCfg (some .inc) none inp (false :: rest) aux)).bind
        countLengthBitsComputer.step =
      some (countLenCfg (some .restore) none inp (true :: rest) aux)
    simp only [FinTM2.step]
    exact countLen_step_inc_false inp rest aux

def countLen_evals_inc_true (inp rest aux : List Bool) :
    EvalsToInTime countLengthBitsComputer.step
      (countLenCfg (some .inc) none inp (true :: rest) aux)
      (some (countLenCfg (some .inc) none inp rest (false :: aux))) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (countLenCfg (some .inc) none inp (true :: rest) aux)).bind
        countLengthBitsComputer.step =
      some (countLenCfg (some .inc) none inp rest (false :: aux))
    simp only [FinTM2.step]
    exact countLen_step_inc_true inp rest aux

def countLen_evals_restore_nil (inp bits : List Bool) :
    EvalsToInTime countLengthBitsComputer.step
      (countLenCfg (some .restore) none inp bits [])
      (some (countLenCfg (some .loop) none inp bits [])) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (countLenCfg (some .restore) none inp bits [])).bind
        countLengthBitsComputer.step =
      some (countLenCfg (some .loop) none inp bits [])
    simp only [FinTM2.step]
    exact countLen_step_restore_nil inp bits

def countLen_evals_restore_cons (inp : List Bool) (b : Bool) (aux bits : List Bool) :
    EvalsToInTime countLengthBitsComputer.step
      (countLenCfg (some .restore) none inp bits (b :: aux))
      (some (countLenCfg (some .restore) none inp (b :: bits) aux)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (countLenCfg (some .restore) none inp bits (b :: aux))).bind
        countLengthBitsComputer.step =
      some (countLenCfg (some .restore) none inp (b :: bits) aux)
    simp only [FinTM2.step]
    exact countLen_step_restore_cons inp b aux bits

/-- Restore empties `aux` onto `bits` (LIFO), then returns to `loop`. -/
noncomputable def countLen_evals_restore (inp bits aux : List Bool) :
    EvalsToInTime countLengthBitsComputer.step
      (countLenCfg (some .restore) none inp bits aux)
      (some (countLenCfg (some .loop) none inp (aux.reverse ++ bits) []))
      (aux.length + 1) := by
  induction aux generalizing bits with
  | nil =>
      simpa using countLen_evals_restore_nil inp bits
  | cons a rest ih =>
      have h1 := countLen_evals_restore_cons inp a rest bits
      have h2 := ih (a :: bits)
      have h :=
        EvalsToInTime.trans countLengthBitsComputer.step 1 (rest.length + 1) _ _ _ h1 h2
      have heq : rest.reverse ++ (a :: bits) = (a :: rest).reverse ++ bits := by
        simp [List.reverse_cons, List.append_assoc]
      refine ⟨⟨h.steps, ?_⟩, ?_⟩
      · simpa [← heq] using h.evals_in_steps
      · have : h.steps ≤ (a :: rest).length + 1 := by
          simp [List.length_cons]
          exact le_trans h.steps_le_m (by omega)
        exact this

/-- From `inc` with carry stack `aux`, return to `loop` with
`aux.reverse ++ bitsInc bits` (input tape `inp` preserved). -/
noncomputable def countLen_evals_inc (inp bits aux : List Bool) :
    EvalsToInTime countLengthBitsComputer.step
      (countLenCfg (some .inc) none inp bits aux)
      (some (countLenCfg (some .loop) none inp (aux.reverse ++ bitsInc bits) []))
      (2 * bits.length + aux.length + 2) := by
  induction bits generalizing aux with
  | nil =>
      have h1 := countLen_evals_inc_nil inp aux
      have h2 := countLen_evals_restore inp [true] aux
      have h :=
        EvalsToInTime.trans countLengthBitsComputer.step 1 (aux.length + 1) _ _ _ h1 h2
      refine ⟨⟨h.steps, ?_⟩, ?_⟩
      · simpa [bitsInc] using h.evals_in_steps
      · have : h.steps ≤ 2 * ([] : List Bool).length + aux.length + 2 :=
          le_trans h.steps_le_m (by omega)
        exact this
  | cons b rest ih =>
      cases b with
      | false =>
          have h1 := countLen_evals_inc_false inp rest aux
          have h2 := countLen_evals_restore inp (true :: rest) aux
          have h :=
            EvalsToInTime.trans countLengthBitsComputer.step 1 (aux.length + 1) _ _ _ h1 h2
          refine ⟨⟨h.steps, ?_⟩, ?_⟩
          · simpa [bitsInc] using h.evals_in_steps
          · refine le_trans h.steps_le_m ?_
            simp [List.length_cons]
      | true =>
          have h1 := countLen_evals_inc_true inp rest aux
          have h2 := ih (false :: aux)
          have h :=
            EvalsToInTime.trans countLengthBitsComputer.step 1
              (2 * rest.length + (false :: aux).length + 2) _ _ _ h1 h2
          have heq :
              (false :: aux).reverse ++ bitsInc rest =
                aux.reverse ++ bitsInc (true :: rest) := by
            simp [bitsInc, List.reverse_cons, List.append_assoc]
          refine ⟨⟨h.steps, ?_⟩, ?_⟩
          · simpa [← heq] using h.evals_in_steps
          · refine le_trans h.steps_le_m ?_
            simp [List.length_cons]; omega

/-- Consume one input symbol and binary increment the bit counter. -/
noncomputable def countLen_evals_one (b : Bool) (xs bits : List Bool) :
    EvalsToInTime countLengthBitsComputer.step
      (countLenCfg (some .loop) none (b :: xs) bits [])
      (some (countLenCfg (some .loop) none xs (bitsInc bits) []))
      (2 * bits.length + 3) := by
  have h1 := countLen_evals_loop_cons b xs bits []
  have h2 := countLen_evals_inc xs bits []
  have h :=
    EvalsToInTime.trans countLengthBitsComputer.step 1
      (2 * bits.length + [].length + 2) _ _ _ h1 h2
  refine ⟨⟨h.steps, ?_⟩, ?_⟩
  · simpa using h.evals_in_steps
  · refine le_trans h.steps_le_m ?_
    simp

/-- From `loop` with counter `natBitsLE n`, process all of `inp`. -/
noncomputable def countLen_evals_from (inp : List Bool) (n : ℕ) :
    EvalsToInTime countLengthBitsComputer.step
      (countLenCfg (some .loop) none inp (natBitsLE n) [])
      (some (countLenCfg (some .loop) none [] (natBitsLE (n + inp.length)) []))
      (inp.length * (2 * (n + inp.length) + 3)) := by
  induction inp generalizing n with
  | nil =>
      simpa using EvalsToInTime.refl countLengthBitsComputer.step
        (countLenCfg (some .loop) none [] (natBitsLE n) [])
  | cons b xs ih =>
      have h1 := countLen_evals_one b xs (natBitsLE n)
      have h1w :
          EvalsToInTime countLengthBitsComputer.step
            (countLenCfg (some .loop) none (b :: xs) (natBitsLE n) [])
            (some (countLenCfg (some .loop) none xs (bitsInc (natBitsLE n)) []))
            (2 * (n + xs.length + 1) + 3) :=
        ⟨h1.toEvalsTo, le_trans h1.steps_le_m (by
          have := length_natBitsLE_le n; omega)⟩
      have h1' :
          EvalsToInTime countLengthBitsComputer.step
            (countLenCfg (some .loop) none (b :: xs) (natBitsLE n) [])
            (some (countLenCfg (some .loop) none xs (natBitsLE (n + 1)) []))
            (2 * (n + xs.length + 1) + 3) := by
        simpa [bitsInc_natBitsLE n] using h1w
      have h2 := ih (n + 1)
      have h :=
        EvalsToInTime.trans countLengthBitsComputer.step
          (2 * (n + xs.length + 1) + 3)
          (xs.length * (2 * (n + 1 + xs.length) + 3)) _ _ _ h1' h2
      have hlen : n + 1 + xs.length = n + (b :: xs).length := by
        simp [List.length_cons]; ring
      refine ⟨⟨h.steps, ?_⟩, ?_⟩
      · simpa [hlen] using h.evals_in_steps
      · refine le_trans h.steps_le_m ?_
        simp [List.length_cons]; ring_nf; omega

/-- On table `s`, halt with `lengthBitsLE s` in quadratic steps. -/
noncomputable def countLengthBits_evals (s : List Bool) :
    TM2OutputsInTime countLengthBitsComputer s (some (lengthBitsLE s))
      (s.length * (2 * s.length + 3) + 1) := by
  have hfrom := countLen_evals_from s 0
  have hfrom' :
      EvalsToInTime countLengthBitsComputer.step
        (countLenCfg (some .loop) none s [] [])
        (some (countLenCfg (some .loop) none [] (natBitsLE s.length) []))
        (s.length * (2 * s.length + 3)) := by
    simpa [natBitsLE_zero] using hfrom
  have hhalt := countLen_evals_loop_nil (natBitsLE s.length) []
  have h :=
    EvalsToInTime.trans countLengthBitsComputer.step
      (s.length * (2 * s.length + 3)) 1 _ _ _ hfrom' hhalt
  have hbound :
      EvalsToInTime countLengthBitsComputer.step
        (initList countLengthBitsComputer s)
        (some (haltList countLengthBitsComputer (lengthBitsLE s)))
        (s.length * (2 * s.length + 3) + 1) := by
    rw [countLengthBits_initList, countLengthBits_haltList]
    refine ⟨?_, ?_⟩
    · simpa [lengthBitsLE] using h.toEvalsTo
    · simpa [Nat.add_comm] using h.steps_le_m
  exact hbound

noncomputable def countLengthBitsTime : Polynomial ℕ :=
  2 * Polynomial.X ^ 2 + 3 * Polynomial.X + 1

theorem countLengthBitsTime_eval (n : ℕ) :
    countLengthBitsTime.eval n = 2 * n ^ 2 + 3 * n + 1 := by
  simp [countLengthBitsTime, pow_two, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat]

/-- Counting table length into little endian bits is poly time. -/
noncomputable def countLengthBitsComputableInPolyTime :
    TM2ComputableInPolyTime idBitEnc idBitEnc lengthBitsLE where
  tm := countLengthBitsComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := countLengthBitsTime
  outputsFun s := by
    change TM2OutputsInTime countLengthBitsComputer (List.map id (idBitEnc s))
      (some (List.map id (idBitEnc (lengthBitsLE s))))
      (countLengthBitsTime.eval (idBitEnc s).length)
    simp only [idBitEnc, List.map_id, id_eq, countLengthBitsTime_eval]
    have hcost : s.length * (2 * s.length + 3) + 1 = 2 * s.length ^ 2 + 3 * s.length + 1 := by
      ring
    simpa [hcost] using countLengthBits_evals s

theorem countLengthBits_computableInPolyTime :
    Nonempty (TM2ComputableInPolyTime idBitEnc idBitEnc lengthBitsLE) :=
  ⟨countLengthBitsComputableInPolyTime⟩

/-! ## Cluster C2 bit list equality (compare glue to `pow2BitsLE`)

Length gate machine path after counting: decide structural equality of
`lengthBitsLE table` and `pow2BitsLE (maxVar+1)`. Semantic `bitsEqual` plus a
zipper FinTM2 on two preloaded stacks; encodePair loading remains next. -/

/-- Structural bit list equality (FinTM2 compare target). -/
def bitsEqual (xs ys : List Bool) : Bool :=
  decide (xs = ys)

theorem bitsEqual_iff (xs ys : List Bool) :
    bitsEqual xs ys = true ↔ xs = ys := by
  simp [bitsEqual]

/-- Zipper form matching FinTM2 dual pop (heads compared pairwise). -/
def bitsEqualZip : List Bool → List Bool → Bool
  | [], [] => true
  | x :: xs, y :: ys => (decide (x = y) && bitsEqualZip xs ys)
  | _, _ => false

theorem bitsEqualZip_nil_nil : bitsEqualZip [] [] = true := rfl

theorem bitsEqualZip_nil_cons (y : Bool) (ys : List Bool) :
    bitsEqualZip [] (y :: ys) = false := rfl

theorem bitsEqualZip_cons_nil (x : Bool) (xs : List Bool) :
    bitsEqualZip (x :: xs) [] = false := rfl

theorem bitsEqualZip_cons_cons (x y : Bool) (xs ys : List Bool) :
    bitsEqualZip (x :: xs) (y :: ys) =
      (decide (x = y) && bitsEqualZip xs ys) := rfl

theorem bitsEqual_eq_bitsEqualZip (xs ys : List Bool) :
    bitsEqual xs ys = bitsEqualZip xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => simp [bitsEqual, bitsEqualZip]
      | cons y ys => simp [bitsEqual, bitsEqualZip]
  | cons x xs ih =>
      cases ys with
      | nil => simp [bitsEqual, bitsEqualZip]
      | cons y ys =>
          by_cases hxy : x = y
          · subst hxy
            simpa [bitsEqual, bitsEqualZip] using ih ys
          · simp [bitsEqual, bitsEqualZip, hxy]

theorem lengthBitsEqPow2_eq_bitsEqual (n : ℕ) (table : List Bool) :
    lengthBitsEqPow2 n table =
      bitsEqual (lengthBitsLE table) (pow2BitsLE n) := by
  simp [lengthBitsEqPow2, lengthBitsLE, bitsEqual]

theorem lengthGateOk_eq_bitsEqual (φ : PropFormula) (table : List Bool) :
    lengthGateOk φ table =
      bitsEqual (lengthBitsLE table) (pow2BitsLE (φ.maxVar + 1)) := by
  rw [lengthGateOk_eq_lengthBitsEqPow2, lengthBitsEqPow2_eq_bitsEqual]

theorem bitsEqual_lengthBitsLE_pow2BitsLE (n : ℕ) (table : List Bool) :
    bitsEqual (lengthBitsLE table) (pow2BitsLE n) = true ↔
      table.length = 2 ^ n := by
  rw [bitsEqual_iff, lengthBitsLE_eq_pow2BitsLE_iff]

/-! ## Cluster C2 FinTM2: zip compare two bit stacks

Preloaded `left`/`right` stacks; halt with `[true]` or `[false]` on `out`.
Loading from `encodePair` is deferred to the next formalize slice. -/

inductive BitsEqStack where
  | left | right | out
  deriving DecidableEq, Repr

instance : Fintype BitsEqStack where
  elems := {.left, .right, .out}
  complete s := by cases s <;> simp

/-- `loop` pops left; `expectTrue`/`expectFalse` match right; `checkRight`
accepts when right is empty; `reject`/`drainRight` clear leftovers then write
`false` so the final config matches `haltList`. -/
inductive BitsEqLabel where
  | loop | expectTrue | expectFalse | checkRight | reject | drainRight
  deriving DecidableEq, Repr

instance : Fintype BitsEqLabel where
  elems := {.loop, .expectTrue, .expectFalse, .checkRight, .reject, .drainRight}
  complete s := by cases s <;> simp

/-- FinTM2: compare `left` to `right`, write equality bit on `out`.
Reject paths drain leftover stacks before halt so `haltList` is reachable. -/
def bitsEqualComputer : FinTM2 where
  K := BitsEqStack
  k₀ := .left
  k₁ := .out
  Γ _ := Bool
  Λ := BitsEqLabel
  main := .loop
  σ := Option Bool
  initialState := none
  m
    | .loop =>
        pop BitsEqStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => BitsEqLabel.checkRight)
            (branch (fun s => decide (s = some true))
              (load (fun _ => none) <| goto fun _ => BitsEqLabel.expectTrue)
              (load (fun _ => none) <| goto fun _ => BitsEqLabel.expectFalse))
    | .expectTrue =>
        pop BitsEqStack.right (fun _ o => o) <|
          branch (fun s => decide (s = some true))
            (load (fun _ => none) <| goto fun _ => BitsEqLabel.loop)
            (load (fun _ => none) <| goto fun _ => BitsEqLabel.reject)
    | .expectFalse =>
        pop BitsEqStack.right (fun _ o => o) <|
          branch (fun s => decide (s = some false))
            (load (fun _ => none) <| goto fun _ => BitsEqLabel.loop)
            (load (fun _ => none) <| goto fun _ => BitsEqLabel.reject)
    | .checkRight =>
        pop BitsEqStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push BitsEqStack.out (fun _ => true) <|
              load (fun _ => none) halt)
            (load (fun _ => none) <| goto fun _ => BitsEqLabel.reject)
    | .reject =>
        pop BitsEqStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => BitsEqLabel.drainRight)
            (load (fun _ => none) <| goto fun _ => BitsEqLabel.reject)
    | .drainRight =>
        pop BitsEqStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push BitsEqStack.out (fun _ => false) <|
              load (fun _ => none) halt)
            (load (fun _ => none) <| goto fun _ => BitsEqLabel.drainRight)

def bitsEqStk (left right out : List Bool) : BitsEqStack → List Bool
  | .left => left
  | .right => right
  | .out => out

def bitsEqCfg (l : Option BitsEqLabel) (v : Option Bool)
    (left right out : List Bool) : bitsEqualComputer.Cfg :=
  ⟨l, v, bitsEqStk left right out⟩

theorem bitsEq_step_loop_nil (right out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfg (some .loop) none [] right out) =
      some (bitsEqCfg (some .checkRight) none [] right out) := by
  simp [bitsEqualComputer, bitsEqCfg, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.checkRight, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_loop_true (xs right out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfg (some .loop) none (true :: xs) right out) =
      some (bitsEqCfg (some .expectTrue) none xs right out) := by
  simp [bitsEqualComputer, bitsEqCfg, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.expectTrue, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_loop_false (xs right out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfg (some .loop) none (false :: xs) right out) =
      some (bitsEqCfg (some .expectFalse) none xs right out) := by
  simp [bitsEqualComputer, bitsEqCfg, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.expectFalse, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_expectTrue_true (left ys out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfg (some .expectTrue) none left (true :: ys) out) =
      some (bitsEqCfg (some .loop) none left ys out) := by
  simp [bitsEqualComputer, bitsEqCfg, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.loop, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_expectTrue_false (left ys out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfg (some .expectTrue) none left (false :: ys) out) =
      some (bitsEqCfg (some .reject) none left ys out) := by
  simp [bitsEqualComputer, bitsEqCfg, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.reject, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_expectTrue_nil (left out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfg (some .expectTrue) none left [] out) =
      some (bitsEqCfg (some .reject) none left [] out) := by
  simp [bitsEqualComputer, bitsEqCfg, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.reject, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_expectFalse_false (left ys out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfg (some .expectFalse) none left (false :: ys) out) =
      some (bitsEqCfg (some .loop) none left ys out) := by
  simp [bitsEqualComputer, bitsEqCfg, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.loop, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_expectFalse_true (left ys out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfg (some .expectFalse) none left (true :: ys) out) =
      some (bitsEqCfg (some .reject) none left ys out) := by
  simp [bitsEqualComputer, bitsEqCfg, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.reject, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_expectFalse_nil (left out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfg (some .expectFalse) none left [] out) =
      some (bitsEqCfg (some .reject) none left [] out) := by
  simp [bitsEqualComputer, bitsEqCfg, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.reject, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_checkRight_nil (left out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfg (some .checkRight) none left [] out) =
      some (bitsEqCfg none none left [] (true :: out)) := by
  simp [bitsEqualComputer, bitsEqCfg, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option BitsEqLabel), none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_checkRight_cons (left : List Bool) (y : Bool) (ys out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfg (some .checkRight) none left (y :: ys) out) =
      some (bitsEqCfg (some .reject) none left ys out) := by
  simp [bitsEqualComputer, bitsEqCfg, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.reject, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_reject_nil (right out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfg (some .reject) none [] right out) =
      some (bitsEqCfg (some .drainRight) none [] right out) := by
  simp [bitsEqualComputer, bitsEqCfg, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.drainRight, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_reject_cons (x : Bool) (xs right out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfg (some .reject) none (x :: xs) right out) =
      some (bitsEqCfg (some .reject) none xs right out) := by
  simp [bitsEqualComputer, bitsEqCfg, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.reject, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_drainRight_nil (left out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfg (some .drainRight) none left [] out) =
      some (bitsEqCfg none none left [] (false :: out)) := by
  simp [bitsEqualComputer, bitsEqCfg, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option BitsEqLabel), none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_drainRight_cons (left : List Bool) (y : Bool) (ys out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfg (some .drainRight) none left (y :: ys) out) =
      some (bitsEqCfg (some .drainRight) none left ys out) := by
  simp [bitsEqualComputer, bitsEqCfg, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.drainRight, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEqual_initList (s : List Bool) :
    initList bitsEqualComputer s =
      bitsEqCfg (some .loop) none s [] [] := by
  refine congrArg (fun stk =>
      (⟨some BitsEqLabel.loop, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [bitsEqualComputer, bitsEqStk]

theorem bitsEqual_haltList (out : List Bool) :
    haltList bitsEqualComputer out =
      bitsEqCfg none none [] [] out := by
  refine congrArg (fun stk =>
      (⟨(none : Option BitsEqLabel), none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [bitsEqualComputer, bitsEqStk]

/-- Semantic output of the zip machine on preloaded stacks. -/
def bitsEqualPair (p : List Bool × List Bool) : Bool :=
  bitsEqual p.1 p.2

theorem bitsEqualPair_eq (xs ys : List Bool) :
    bitsEqualPair (xs, ys) = bitsEqual xs ys := rfl

theorem bitsEqualPair_iff_lengthGate (n : ℕ) (table : List Bool) :
    bitsEqualPair (lengthBitsLE table, pow2BitsLE n) = true ↔
      table.length = 2 ^ n := by
  simpa [bitsEqualPair] using bitsEqual_lengthBitsLE_pow2BitsLE n table

/-! ### Cluster C2: bitsEqual leftover drain and EvalsToInTime -/

open StateTransition

def bitsEq_evals_reject_cons (x : Bool) (xs right out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .reject) none (x :: xs) right out)
      (some (bitsEqCfg (some .reject) none xs right out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfg (some .reject) none (x :: xs) right out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfg (some .reject) none xs right out)
    simp only [FinTM2.step]
    exact bitsEq_step_reject_cons x xs right out

def bitsEq_evals_reject_nil (right out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .reject) none [] right out)
      (some (bitsEqCfg (some .drainRight) none [] right out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfg (some .reject) none [] right out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfg (some .drainRight) none [] right out)
    simp only [FinTM2.step]
    exact bitsEq_step_reject_nil right out

def bitsEq_evals_drainRight_cons (left : List Bool) (y : Bool) (ys out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .drainRight) none left (y :: ys) out)
      (some (bitsEqCfg (some .drainRight) none left ys out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfg (some .drainRight) none left (y :: ys) out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfg (some .drainRight) none left ys out)
    simp only [FinTM2.step]
    exact bitsEq_step_drainRight_cons left y ys out

def bitsEq_evals_drainRight_nil (left out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .drainRight) none left [] out)
      (some (bitsEqCfg none none left [] (false :: out))) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfg (some .drainRight) none left [] out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfg none none left [] (false :: out))
    simp only [FinTM2.step]
    exact bitsEq_step_drainRight_nil left out

/-- Empty `right`, then write `false` and halt (left already empty for haltList). -/
noncomputable def bitsEq_evals_drainRight (right out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .drainRight) none [] right out)
      (some (bitsEqCfg none none [] [] (false :: out)))
      (right.length + 1) := by
  induction right with
  | nil =>
      simpa using bitsEq_evals_drainRight_nil [] out
  | cons y ys ih =>
      have h1 := bitsEq_evals_drainRight_cons [] y ys out
      have h :=
        EvalsToInTime.trans bitsEqualComputer.step 1 (ys.length + 1) _ _ _ h1 ih
      refine ⟨⟨h.steps, h.evals_in_steps⟩, ?_⟩
      refine le_trans h.steps_le_m ?_
      simp [List.length_cons]

/-- Drain leftover `left` then `right`, halt with `false :: out` (= haltList when out=[]). -/
noncomputable def bitsEq_evals_reject (left right out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .reject) none left right out)
      (some (bitsEqCfg none none [] [] (false :: out)))
      (left.length + right.length + 2) := by
  induction left generalizing right with
  | nil =>
      have h1 := bitsEq_evals_reject_nil right out
      have h2 := bitsEq_evals_drainRight right out
      have h :=
        EvalsToInTime.trans bitsEqualComputer.step 1 (right.length + 1) _ _ _ h1 h2
      refine ⟨⟨h.steps, h.evals_in_steps⟩, ?_⟩
      refine le_trans h.steps_le_m ?_
      simp
  | cons x xs ih =>
      have h1 := bitsEq_evals_reject_cons x xs right out
      have h2 := ih right
      have h :=
        EvalsToInTime.trans bitsEqualComputer.step 1
          (xs.length + right.length + 2) _ _ _ h1 h2
      refine ⟨⟨h.steps, h.evals_in_steps⟩, ?_⟩
      refine le_trans h.steps_le_m ?_
      simp [List.length_cons]

def bitsEq_evals_loop_nil (right out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .loop) none [] right out)
      (some (bitsEqCfg (some .checkRight) none [] right out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfg (some .loop) none [] right out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfg (some .checkRight) none [] right out)
    simp only [FinTM2.step]
    exact bitsEq_step_loop_nil right out

def bitsEq_evals_loop_true (xs right out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .loop) none (true :: xs) right out)
      (some (bitsEqCfg (some .expectTrue) none xs right out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfg (some .loop) none (true :: xs) right out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfg (some .expectTrue) none xs right out)
    simp only [FinTM2.step]
    exact bitsEq_step_loop_true xs right out

def bitsEq_evals_loop_false (xs right out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .loop) none (false :: xs) right out)
      (some (bitsEqCfg (some .expectFalse) none xs right out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfg (some .loop) none (false :: xs) right out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfg (some .expectFalse) none xs right out)
    simp only [FinTM2.step]
    exact bitsEq_step_loop_false xs right out

def bitsEq_evals_expectTrue_true (left ys out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .expectTrue) none left (true :: ys) out)
      (some (bitsEqCfg (some .loop) none left ys out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfg (some .expectTrue) none left (true :: ys) out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfg (some .loop) none left ys out)
    simp only [FinTM2.step]
    exact bitsEq_step_expectTrue_true left ys out

def bitsEq_evals_expectFalse_false (left ys out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .expectFalse) none left (false :: ys) out)
      (some (bitsEqCfg (some .loop) none left ys out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfg (some .expectFalse) none left (false :: ys) out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfg (some .loop) none left ys out)
    simp only [FinTM2.step]
    exact bitsEq_step_expectFalse_false left ys out

def bitsEq_evals_checkRight_nil (left out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .checkRight) none left [] out)
      (some (bitsEqCfg none none left [] (true :: out))) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfg (some .checkRight) none left [] out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfg none none left [] (true :: out))
    simp only [FinTM2.step]
    exact bitsEq_step_checkRight_nil left out

def bitsEq_evals_checkRight_cons (left : List Bool) (y : Bool) (ys out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .checkRight) none left (y :: ys) out)
      (some (bitsEqCfg (some .reject) none left ys out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfg (some .checkRight) none left (y :: ys) out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfg (some .reject) none left ys out)
    simp only [FinTM2.step]
    exact bitsEq_step_checkRight_cons left y ys out

/-- Accept path: empty left and empty right write `true` and match haltList. -/
noncomputable def bitsEq_evals_accept (out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .loop) none [] [] out)
      (some (bitsEqCfg none none [] [] (true :: out))) 2 := by
  have h1 := bitsEq_evals_loop_nil [] out
  have h2 := bitsEq_evals_checkRight_nil [] out
  exact EvalsToInTime.trans bitsEqualComputer.step 1 1 _ _ _ h1 h2

/-- Equal zippers: from `loop` with identical stacks, halt with `[true]`. -/
noncomputable def bitsEq_evals_equal (xs : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .loop) none xs xs [])
      (some (haltList bitsEqualComputer [true]))
      (2 * xs.length + 2) := by
  induction xs with
  | nil =>
      have h := bitsEq_evals_accept []
      simpa [bitsEqual_haltList] using h
  | cons x xs ih =>
      cases x with
      | true =>
          have h1 := bitsEq_evals_loop_true xs (true :: xs) []
          have h2 := bitsEq_evals_expectTrue_true xs xs []
          have h12 :=
            EvalsToInTime.trans bitsEqualComputer.step 1 1 _ _ _ h1 h2
          have h :=
            EvalsToInTime.trans bitsEqualComputer.step 2 (2 * xs.length + 2)
              _ _ _ h12 ih
          refine ⟨⟨h.steps, ?_⟩, ?_⟩
          · simpa [bitsEqual_haltList] using h.evals_in_steps
          · refine le_trans h.steps_le_m ?_
            simp [List.length_cons]; omega
      | false =>
          have h1 := bitsEq_evals_loop_false xs (false :: xs) []
          have h2 := bitsEq_evals_expectFalse_false xs xs []
          have h12 :=
            EvalsToInTime.trans bitsEqualComputer.step 1 1 _ _ _ h1 h2
          have h :=
            EvalsToInTime.trans bitsEqualComputer.step 2 (2 * xs.length + 2)
              _ _ _ h12 ih
          refine ⟨⟨h.steps, ?_⟩, ?_⟩
          · simpa [bitsEqual_haltList] using h.evals_in_steps
          · refine le_trans h.steps_le_m ?_
            simp [List.length_cons]; omega

/-- Left empty, right leftover: checkRight rejects, drain, haltList `[false]`. -/
noncomputable def bitsEq_evals_left_nil_right_cons (y : Bool) (ys : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .loop) none [] (y :: ys) [])
      (some (haltList bitsEqualComputer [false]))
      (ys.length + 4) := by
  have h1 := bitsEq_evals_loop_nil (y :: ys) []
  have h2 := bitsEq_evals_checkRight_cons [] y ys []
  have h12 :=
    EvalsToInTime.trans bitsEqualComputer.step 1 1 _ _ _ h1 h2
  have h3 := bitsEq_evals_reject [] ys []
  have h :=
    EvalsToInTime.trans bitsEqualComputer.step 2 (0 + ys.length + 2) _ _ _ h12 h3
  refine ⟨⟨h.steps, ?_⟩, ?_⟩
  · simpa [bitsEqual_haltList] using h.evals_in_steps
  · refine le_trans h.steps_le_m ?_
    simp [List.length_cons]

/-- Reject from `reject` label drains to haltList `[false]`. -/
noncomputable def bitsEq_evals_reject_to_halt (left right : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .reject) none left right [])
      (some (haltList bitsEqualComputer [false]))
      (left.length + right.length + 2) := by
  have h := bitsEq_evals_reject left right []
  simpa [bitsEqual_haltList] using h

/-! ## Truth table proof map (semantic Cook Reckhow witness) -/
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

/-! ## Exponential proof size lower bound (toward not poly bounded) -/

/-- Variable indexed seed tautology `p_k ∨ ¬p_k`. -/
def tautSeedAt (k : ℕ) : PropFormula :=
  .or (.var k) (.not (.var k))

theorem tautSeedAt_tautology (k : ℕ) : (tautSeedAt k).Tautology := by
  intro σ
  simp [tautSeedAt, PropFormula.eval, Bool.or_not_self]

theorem tautSeedAt_maxVar (k : ℕ) : (tautSeedAt k).maxVar = k := by
  simp [tautSeedAt, PropFormula.maxVar]

theorem length_truthTableOf_tautSeedAt (k : ℕ) :
    (truthTableOf (tautSeedAt k)).length = 2 ^ (k + 1) := by
  simp [truthTableOf, tautSeedAt_maxVar, length_allBitstrings]

theorem length_encodeFormula_tautSeedAt (k : ℕ) :
    (encodeFormula (tautSeedAt k)).length = 2 * k + 10 := by
  simp [tautSeedAt, encodeFormula, encodeNat]
  omega

theorem tautSeedAt_mem_TAUT (k : ℕ) : TAUT (encodeFormula (tautSeedAt k)) :=
  ⟨tautSeedAt k, decodeFormula_encodeFormula _, tautSeedAt_tautology k⟩

theorem encodeFormula_tautSeedAt_ne_tautSeed (k : ℕ) (hk : 1 ≤ k) :
    encodeFormula (tautSeedAt k) ≠ encodeFormula tautSeed := by
  intro h
  have := encodeFormula_injective h
  simp [tautSeedAt, tautSeed] at this
  omega

/-- Any proof that outputs `encodeFormula (tautSeedAt k)` (for `k ≥ 1`) must
carry a full truth table of length `2^(k+1)`. -/
theorem truthTableProofSystem_length_ge (π : List Bool) (k : ℕ) (hk : 1 ≤ k)
    (h : truthTableProofSystem π = encodeFormula (tautSeedAt k)) :
    2 ^ (k + 1) ≤ π.length := by
  have hne := encodeFormula_tautSeedAt_ne_tautSeed k hk
  unfold truthTableProofSystem at h
  cases hpair : decodePair π with
  | none =>
      simp [hpair] at h
      exact (hne h.symm).elim
  | some pw =>
      rcases pw with ⟨φCode, table⟩
      simp [hpair] at h
      cases hφ : decodeFormula φCode with
      | none =>
          simp [hφ] at h
          exact (hne h.symm).elim
      | some φ =>
          simp [hφ] at h
          split_ifs at h with hval
          · have hφcode : φCode = encodeFormula (tautSeedAt k) := h
            subst hφcode
            rcases hval with ⟨htable, _⟩
            have hφeq : φ = tautSeedAt k := by
              have hdec := decodeFormula_encodeFormula (tautSeedAt k)
              rw [hφ] at hdec
              exact Option.some_injective _ hdec
            subst hφeq
            have hsnd := length_ge_snd_of_decodePair (x := encodeFormula (tautSeedAt k))
              (w := table) hpair
            have htlen := length_truthTableOf_tautSeedAt k
            rw [htable] at hsnd
            omega
          · exact (hne h.symm).elim


/-! ## Polynomial versus exponential (closes not poly bounded) -/

/-- Squares fall below powers of two for `m ≥ 5`. -/
theorem sq_lt_two_pow (m : ℕ) (hm : 5 ≤ m) : m ^ 2 < 2 ^ m := by
  have hlin : ∀ n ≥ 5, 2 * n + 1 ≤ 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => decide
    | succ n hn ih =>
        calc
          2 * (n + 1) + 1 = 2 * n + 1 + 2 := by ring
          _ ≤ 2 ^ n + 2 := by omega
          _ ≤ 2 ^ n + 2 ^ n := by
            have : (2 : ℕ) ≤ 2 ^ n :=
              Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ n)
            omega
          _ = 2 ^ (n + 1) := by ring
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
      calc
        (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
        _ < 2 ^ m + 2 * m + 1 := by omega
        _ ≤ 2 ^ m + 2 ^ m := by
          have := hlin m hm
          omega
        _ = 2 ^ (m + 1) := by ring

/-- Linear versus exponential: `k * m` is eventually below `2^m`. -/
theorem exists_const_mul_lt_two_pow (k : ℕ) :
    ∃ m0 : ℕ, ∀ m ≥ m0, k * m < 2 ^ m := by
  refine ⟨max 5 (2 * k + 1), ?_⟩
  intro m hm
  have hm5 : 5 ≤ m := by omega
  have hk : k ≤ m := by omega
  calc
    k * m ≤ m * m := by gcongr
    _ = m ^ 2 := by ring
    _ < 2 ^ m := sq_lt_two_pow m hm5

/-- `k * log 2 n` is eventually strictly below `n`. -/
theorem exists_log_mul_lt (k : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, k * Nat.log 2 n < n := by
  obtain ⟨m0, hm0⟩ := exists_const_mul_lt_two_pow k
  refine ⟨2 ^ m0, ?_⟩
  intro n hn
  have hn0 : n ≠ 0 :=
    (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (Nat.two_pow_pos m0) hn))
  have hm : m0 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by decide : 1 < 2) hn
  have hpow : k * Nat.log 2 n < 2 ^ Nat.log 2 n := hm0 _ hm
  exact lt_of_lt_of_le hpow (Nat.pow_log_le_self 2 hn0)

/-- Nat log of a product: at most the sum of logs plus one. -/
theorem log_mul_le_add_one (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b + 1 := by
  have ha' : a < 2 ^ (Nat.log 2 a + 1) :=
    Nat.lt_pow_of_log_lt (by decide : 1 < 2) (Nat.lt_succ_self _)
  have hb' : b < 2 ^ (Nat.log 2 b + 1) :=
    Nat.lt_pow_of_log_lt (by decide : 1 < 2) (Nat.lt_succ_self _)
  have hmul : a * b < 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by
    have h1 : a * b < 2 ^ (Nat.log 2 a + 1) * b :=
      Nat.mul_lt_mul_of_pos_right ha' hb
    have h2 : 2 ^ (Nat.log 2 a + 1) * b <
        2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) :=
      Nat.mul_lt_mul_of_pos_left hb' (Nat.two_pow_pos _)
    calc
      a * b < 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) := lt_trans h1 h2
      _ = 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by rw [← pow_add]; ring
  have : Nat.log 2 (a * b) < Nat.log 2 a + Nat.log 2 b + 2 :=
    Nat.log_lt_of_lt_pow (mul_ne_zero ha.ne' hb.ne') hmul
  omega

/-- `log 2 (n ^ d) ≤ d * log 2 n + d`. -/
theorem log_pow_le_add (n d : ℕ) (hn : 0 < n) :
    Nat.log 2 (n ^ d) ≤ d * Nat.log 2 n + d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ]
      have hnd : 0 < n ^ d := pow_pos hn _
      calc
        Nat.log 2 (n ^ d * n) ≤ Nat.log 2 (n ^ d) + Nat.log 2 n + 1 :=
          log_mul_le_add_one _ _ hnd hn
        _ ≤ d * Nat.log 2 n + d + Nat.log 2 n + 1 := by omega
        _ = (d + 1) * Nat.log 2 n + (d + 1) := by ring

/-- `A * n^d` is eventually strictly below `2^n`. -/
theorem exists_const_mul_pow_lt_two_pow (A d : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, A * n ^ d < 2 ^ n := by
  obtain ⟨N1, h1⟩ := exists_log_mul_lt (2 * (d + 1))
  refine ⟨max N1 (max A (2 * (d + 1) + 1)), ?_⟩
  intro n hn
  by_cases hA0 : A = 0
  · simp [hA0]
  · have hn0 : 0 < n := by omega
    have hAn : A ≤ n := by omega
    have hle : A * n ^ d ≤ n ^ (d + 1) := by
      calc
        A * n ^ d ≤ n * n ^ d := by gcongr
        _ = n ^ (d + 1) := by rw [pow_succ']
    have hne : n ^ (d + 1) ≠ 0 := (pow_pos hn0 _).ne'
    have hlog : Nat.log 2 (n ^ (d + 1)) ≤ (d + 1) * Nat.log 2 n + (d + 1) :=
      log_pow_le_add n (d + 1) hn0
    have hroom : (d + 1) * Nat.log 2 n + (d + 1) < n := by
      have h2 : 2 * ((d + 1) * Nat.log 2 n) < n := by
        simpa [mul_assoc] using h1 n (le_trans (le_max_left _ _) hn)
      have h2d : 2 * (d + 1) ≤ n := by omega
      omega
    have : Nat.log 2 (n ^ (d + 1)) < n := lt_of_le_of_lt hlog hroom
    have hpow : n ^ (d + 1) < 2 ^ n :=
      (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) hne).1 this
    omega

/-- Polynomial evaluation bound: `q.eval n ≤ C * n^deg` for `n ≥ 1`. -/
theorem Polynomial.eval_le_sum_coeff_mul_pow (q : Polynomial ℕ) {n : ℕ}
    (hn : 1 ≤ n) :
    q.eval n ≤ (∑ i ∈ q.support, q.coeff i) * n ^ q.natDegree := by
  classical
  simp only [Polynomial.eval_eq_sum, Polynomial.sum]
  have hle :
      (∑ i ∈ q.support, q.coeff i * n ^ i) ≤
        ∑ i ∈ q.support, q.coeff i * n ^ q.natDegree := by
    refine Finset.sum_le_sum fun i hi => ?_
    exact Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right hn (Polynomial.le_natDegree_of_mem_supp i hi))
  have hmul :
      (∑ i ∈ q.support, q.coeff i * n ^ q.natDegree) =
        (∑ i ∈ q.support, q.coeff i) * n ^ q.natDegree := by
    rw [← Finset.sum_mul]
  exact hle.trans (le_of_eq hmul)

/-- Polynomials fall below `2^(k+1)` along the line `2k+10`. -/
theorem Polynomial.exists_eval_two_k_ten_lt_two_pow (q : Polynomial ℕ) :
    ∃ k : ℕ, 1 ≤ k ∧ q.eval (2 * k + 10) < 2 ^ (k + 1) := by
  classical
  let C : ℕ := ∑ i ∈ q.support, q.coeff i
  let d : ℕ := q.natDegree
  obtain ⟨N, hN⟩ := exists_const_mul_pow_lt_two_pow (C * 3 ^ d) d
  refine ⟨max N 10, le_trans (by decide : 1 ≤ 10) (le_max_right _ _), ?_⟩
  set k := max N 10
  have hEv : C * 3 ^ d * (k + 1) ^ d < 2 ^ (k + 1) := by
    simpa [mul_assoc] using hN (k + 1) (by omega)
  have hC : C * (2 * k + 10) ^ d ≤ C * 3 ^ d * (k + 1) ^ d := by
    have hbase : 2 * k + 10 ≤ 3 * (k + 1) := by omega
    calc
      C * (2 * k + 10) ^ d ≤ C * (3 * (k + 1)) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _)
      _ = C * (3 ^ d * (k + 1) ^ d) := by rw [Nat.mul_pow]
      _ = C * 3 ^ d * (k + 1) ^ d := by ac_rfl
  have hbound : q.eval (2 * k + 10) ≤ C * (2 * k + 10) ^ d := by
    simpa [C, d] using
      Polynomial.eval_le_sum_coeff_mul_pow q (n := 2 * k + 10) (by omega)
  omega

theorem truthTable_not_poly_bounded :
    ¬ PolynomiallyBounded truthTableProofSystem := by
  intro h
  rcases h with ⟨q, hq⟩
  obtain ⟨k, hk1, hklt⟩ := Polynomial.exists_eval_two_k_ten_lt_two_pow q
  obtain ⟨π, hπ, hlen⟩ := hq (encodeFormula (tautSeedAt k)) (tautSeedAt_mem_TAUT k)
  have hge := truthTableProofSystem_length_ge π k hk1 hπ
  have hle : π.length ≤ q.eval (2 * k + 10) := by
    simpa [length_encodeFormula_tautSeedAt k] using hlen
  omega

namespace ProofSystemFrontier

/-- Full `IsPropProofSystem` instance once a TM2 poly time witness for
`truthTableProofSystem` is certified (verification is poly in the proof length). -/
theorem truthTable_is_prop_proof_system :
    Nonempty (IsPropProofSystem truthTableProofSystem) := by
  sorry

end ProofSystemFrontier

/-! ## Cluster C/D prep: emit fixed `encodeFormula tautSeed` (TT fail branches) -/

open TM2.Stmt

theorem length_encodeFormula_tautSeed :
    (encodeFormula tautSeed).length = 10 := by
  simp [encodeFormula_tautSeed]

inductive EmitSeedStack where
  | inp | out
  deriving DecidableEq, Repr

instance : Fintype EmitSeedStack where
  elems := {.inp, .out}
  complete s := by cases s <;> simp

/-- Clear input, then ten write labels for the fixed seed bits (high index first). -/
inductive EmitSeedLabel where
  | clear
  | e0 | e1 | e2 | e3 | e4 | e5 | e6 | e7 | e8 | e9
  deriving DecidableEq, Repr

instance : Fintype EmitSeedLabel where
  elems :=
    {.clear, .e0, .e1, .e2, .e3, .e4, .e5, .e6, .e7, .e8, .e9}
  complete s := by cases s <;> simp

/-- Clears the input and writes `encodeFormula tautSeed` (length 10). -/
def emitTautSeedComputer : FinTM2 where
  K := EmitSeedStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := EmitSeedLabel
  main := .clear
  σ := Bool
  initialState := false
  m
    | .clear =>
        pop EmitSeedStack.inp (fun _ o => decide (o = none)) <|
          branch id
            (goto fun _ => EmitSeedLabel.e0)
            (goto fun _ => EmitSeedLabel.clear)
    | .e0 =>
        push EmitSeedStack.out (fun _ =>
            (encodeFormula tautSeed).getD 9 false) <|
          goto fun _ => EmitSeedLabel.e1
    | .e1 =>
        push EmitSeedStack.out (fun _ =>
            (encodeFormula tautSeed).getD 8 false) <|
          goto fun _ => EmitSeedLabel.e2
    | .e2 =>
        push EmitSeedStack.out (fun _ =>
            (encodeFormula tautSeed).getD 7 false) <|
          goto fun _ => EmitSeedLabel.e3
    | .e3 =>
        push EmitSeedStack.out (fun _ =>
            (encodeFormula tautSeed).getD 6 false) <|
          goto fun _ => EmitSeedLabel.e4
    | .e4 =>
        push EmitSeedStack.out (fun _ =>
            (encodeFormula tautSeed).getD 5 false) <|
          goto fun _ => EmitSeedLabel.e5
    | .e5 =>
        push EmitSeedStack.out (fun _ =>
            (encodeFormula tautSeed).getD 4 false) <|
          goto fun _ => EmitSeedLabel.e6
    | .e6 =>
        push EmitSeedStack.out (fun _ =>
            (encodeFormula tautSeed).getD 3 false) <|
          goto fun _ => EmitSeedLabel.e7
    | .e7 =>
        push EmitSeedStack.out (fun _ =>
            (encodeFormula tautSeed).getD 2 false) <|
          goto fun _ => EmitSeedLabel.e8
    | .e8 =>
        push EmitSeedStack.out (fun _ =>
            (encodeFormula tautSeed).getD 1 false) <|
          goto fun _ => EmitSeedLabel.e9
    | .e9 =>
        push EmitSeedStack.out (fun _ =>
            (encodeFormula tautSeed).getD 0 false) <|
          load (fun _ => false) halt

def emitSeedStk (inp out : List Bool) : EmitSeedStack → List Bool
  | .inp => inp
  | .out => out

def emitSeedCfg (l : Option EmitSeedLabel) (v : Bool)
    (inp out : List Bool) : emitTautSeedComputer.Cfg :=
  ⟨l, v, emitSeedStk inp out⟩

theorem emitSeed_step_clear_cons (x : Bool) (xs out : List Bool) :
    TM2.step emitTautSeedComputer.m
      (emitSeedCfg (some .clear) false (x :: xs) out) =
      some (emitSeedCfg (some .clear) false xs out) := by
  simp [emitTautSeedComputer, emitSeedCfg, emitSeedStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EmitSeedLabel.clear, false, stk⟩ : emitTautSeedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, emitSeedStk]

theorem emitSeed_step_clear_nil (out : List Bool) :
    TM2.step emitTautSeedComputer.m
      (emitSeedCfg (some .clear) false [] out) =
      some (emitSeedCfg (some .e0) true [] out) := by
  simp [emitTautSeedComputer, emitSeedCfg, emitSeedStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EmitSeedLabel.e0, true, stk⟩ : emitTautSeedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, emitSeedStk]

theorem emitSeed_step_e0 (inp out : List Bool) (v : Bool) :
    TM2.step emitTautSeedComputer.m
      (emitSeedCfg (some .e0) v inp out) =
      some (emitSeedCfg (some .e1) v inp
        ((encodeFormula tautSeed).getD 9 false :: out)) := by
  simp [emitTautSeedComputer, emitSeedCfg, emitSeedStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EmitSeedLabel.e1, v, stk⟩ : emitTautSeedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, emitSeedStk]

theorem emitSeed_step_e1 (inp out : List Bool) (v : Bool) :
    TM2.step emitTautSeedComputer.m
      (emitSeedCfg (some .e1) v inp out) =
      some (emitSeedCfg (some .e2) v inp
        ((encodeFormula tautSeed).getD 8 false :: out)) := by
  simp [emitTautSeedComputer, emitSeedCfg, emitSeedStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EmitSeedLabel.e2, v, stk⟩ : emitTautSeedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, emitSeedStk]

theorem emitSeed_step_e2 (inp out : List Bool) (v : Bool) :
    TM2.step emitTautSeedComputer.m
      (emitSeedCfg (some .e2) v inp out) =
      some (emitSeedCfg (some .e3) v inp
        ((encodeFormula tautSeed).getD 7 false :: out)) := by
  simp [emitTautSeedComputer, emitSeedCfg, emitSeedStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EmitSeedLabel.e3, v, stk⟩ : emitTautSeedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, emitSeedStk]

theorem emitSeed_step_e3 (inp out : List Bool) (v : Bool) :
    TM2.step emitTautSeedComputer.m
      (emitSeedCfg (some .e3) v inp out) =
      some (emitSeedCfg (some .e4) v inp
        ((encodeFormula tautSeed).getD 6 false :: out)) := by
  simp [emitTautSeedComputer, emitSeedCfg, emitSeedStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EmitSeedLabel.e4, v, stk⟩ : emitTautSeedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, emitSeedStk]

theorem emitSeed_step_e4 (inp out : List Bool) (v : Bool) :
    TM2.step emitTautSeedComputer.m
      (emitSeedCfg (some .e4) v inp out) =
      some (emitSeedCfg (some .e5) v inp
        ((encodeFormula tautSeed).getD 5 false :: out)) := by
  simp [emitTautSeedComputer, emitSeedCfg, emitSeedStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EmitSeedLabel.e5, v, stk⟩ : emitTautSeedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, emitSeedStk]

theorem emitSeed_step_e5 (inp out : List Bool) (v : Bool) :
    TM2.step emitTautSeedComputer.m
      (emitSeedCfg (some .e5) v inp out) =
      some (emitSeedCfg (some .e6) v inp
        ((encodeFormula tautSeed).getD 4 false :: out)) := by
  simp [emitTautSeedComputer, emitSeedCfg, emitSeedStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EmitSeedLabel.e6, v, stk⟩ : emitTautSeedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, emitSeedStk]

theorem emitSeed_step_e6 (inp out : List Bool) (v : Bool) :
    TM2.step emitTautSeedComputer.m
      (emitSeedCfg (some .e6) v inp out) =
      some (emitSeedCfg (some .e7) v inp
        ((encodeFormula tautSeed).getD 3 false :: out)) := by
  simp [emitTautSeedComputer, emitSeedCfg, emitSeedStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EmitSeedLabel.e7, v, stk⟩ : emitTautSeedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, emitSeedStk]

theorem emitSeed_step_e7 (inp out : List Bool) (v : Bool) :
    TM2.step emitTautSeedComputer.m
      (emitSeedCfg (some .e7) v inp out) =
      some (emitSeedCfg (some .e8) v inp
        ((encodeFormula tautSeed).getD 2 false :: out)) := by
  simp [emitTautSeedComputer, emitSeedCfg, emitSeedStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EmitSeedLabel.e8, v, stk⟩ : emitTautSeedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, emitSeedStk]

theorem emitSeed_step_e8 (inp out : List Bool) (v : Bool) :
    TM2.step emitTautSeedComputer.m
      (emitSeedCfg (some .e8) v inp out) =
      some (emitSeedCfg (some .e9) v inp
        ((encodeFormula tautSeed).getD 1 false :: out)) := by
  simp [emitTautSeedComputer, emitSeedCfg, emitSeedStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EmitSeedLabel.e9, v, stk⟩ : emitTautSeedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, emitSeedStk]

theorem emitSeed_step_e9 (inp out : List Bool) (v : Bool) :
    TM2.step emitTautSeedComputer.m
      (emitSeedCfg (some .e9) v inp out) =
      some (emitSeedCfg none false inp
        ((encodeFormula tautSeed).getD 0 false :: out)) := by
  simp [emitTautSeedComputer, emitSeedCfg, emitSeedStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option EmitSeedLabel), false, stk⟩ : emitTautSeedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, emitSeedStk]

theorem emitTautSeed_initList (s : List Bool) :
    initList emitTautSeedComputer s =
      emitSeedCfg (some .clear) false s [] := by
  refine congrArg (fun stk =>
      (⟨some EmitSeedLabel.clear, false, stk⟩ : emitTautSeedComputer.Cfg)) ?_
  funext k; cases k <;> simp [emitTautSeedComputer, emitSeedStk]

theorem emitTautSeed_haltList :
    haltList emitTautSeedComputer (encodeFormula tautSeed) =
      emitSeedCfg none false [] (encodeFormula tautSeed) := by
  refine congrArg (fun stk =>
      (⟨(none : Option EmitSeedLabel), false, stk⟩ : emitTautSeedComputer.Cfg)) ?_
  funext k; cases k <;> simp [emitTautSeedComputer, emitSeedStk]

open StateTransition

set_option maxHeartbeats 2000000

def emitSeed_evals_clear_one (x : Bool) (xs out : List Bool) :
    EvalsToInTime emitTautSeedComputer.step
      (emitSeedCfg (some .clear) false (x :: xs) out)
      (some (emitSeedCfg (some .clear) false xs out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (emitSeedCfg (some .clear) false (x :: xs) out)).bind
        emitTautSeedComputer.step =
      some (emitSeedCfg (some .clear) false xs out)
    simp only [FinTM2.step]
    exact emitSeed_step_clear_cons x xs out

def emitSeed_evals_clear_nil (out : List Bool) :
    EvalsToInTime emitTautSeedComputer.step
      (emitSeedCfg (some .clear) false [] out)
      (some (emitSeedCfg (some .e0) true [] out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (emitSeedCfg (some .clear) false [] out)).bind
        emitTautSeedComputer.step =
      some (emitSeedCfg (some .e0) true [] out)
    simp only [FinTM2.step]
    exact emitSeed_step_clear_nil out

noncomputable def emitSeed_evals_clear (s out : List Bool) :
    EvalsToInTime emitTautSeedComputer.step
      (emitSeedCfg (some .clear) false s out)
      (some (emitSeedCfg (some .clear) false [] out))
      s.length := by
  induction s with
  | nil =>
      simpa using EvalsToInTime.refl emitTautSeedComputer.step
        (emitSeedCfg (some .clear) false [] out)
  | cons x xs ih =>
      have h1 := emitSeed_evals_clear_one x xs out
      have h2 := ih
      have h := EvalsToInTime.trans emitTautSeedComputer.step 1 xs.length
        _ _ _ h1 h2
      simpa [Nat.add_comm] using h

def emitSeed_evals_ei (lab next : EmitSeedLabel) (bit : Bool)
    (hstep : ∀ inp out v,
      TM2.step emitTautSeedComputer.m (emitSeedCfg (some lab) v inp out) =
        some (emitSeedCfg (some next) v inp (bit :: out)))
    (inp out : List Bool) (v : Bool) :
    EvalsToInTime emitTautSeedComputer.step
      (emitSeedCfg (some lab) v inp out)
      (some (emitSeedCfg (some next) v inp (bit :: out))) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (emitSeedCfg (some lab) v inp out)).bind
        emitTautSeedComputer.step =
      some (emitSeedCfg (some next) v inp (bit :: out))
    simp only [FinTM2.step]
    exact hstep inp out v

def emitSeed_evals_e9 (inp out : List Bool) (v : Bool) :
    EvalsToInTime emitTautSeedComputer.step
      (emitSeedCfg (some .e9) v inp out)
      (some (emitSeedCfg none false inp
        ((encodeFormula tautSeed).getD 0 false :: out))) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (emitSeedCfg (some .e9) v inp out)).bind
        emitTautSeedComputer.step =
      some (emitSeedCfg none false inp
        ((encodeFormula tautSeed).getD 0 false :: out))
    simp only [FinTM2.step]
    exact emitSeed_step_e9 inp out v

/-- Emit all 10 seed bits then halt. -/
noncomputable def emitSeed_evals_emit (inp : List Bool) (v : Bool) :
    EvalsToInTime emitTautSeedComputer.step
      (emitSeedCfg (some .e0) v inp [])
      (some (emitSeedCfg none false inp (encodeFormula tautSeed)))
      10 := by
  simp only [encodeFormula_tautSeed]
  have s0 := emitSeed_evals_ei .e0 .e1 false emitSeed_step_e0 inp [] v
  have s1 := emitSeed_evals_ei .e1 .e2 false emitSeed_step_e1 inp [false] v
  have t1 := EvalsToInTime.trans emitTautSeedComputer.step 1 1 _ _ _ s0
    (by simpa [encodeFormula_tautSeed] using s1)
  have s2 := emitSeed_evals_ei .e2 .e3 false emitSeed_step_e2 inp
    [false, false] v
  have t2 := EvalsToInTime.trans emitTautSeedComputer.step 2 1 _ _ _ t1
    (by simpa [encodeFormula_tautSeed] using s2)
  have s3 := emitSeed_evals_ei .e3 .e4 true emitSeed_step_e3 inp
    [false, false, false] v
  have t3 := EvalsToInTime.trans emitTautSeedComputer.step 3 1 _ _ _ t2
    (by simpa [encodeFormula_tautSeed] using s3)
  have s4 := emitSeed_evals_ei .e4 .e5 false emitSeed_step_e4 inp
    [true, false, false, false] v
  have t4 := EvalsToInTime.trans emitTautSeedComputer.step 4 1 _ _ _ t3
    (by simpa [encodeFormula_tautSeed] using s4)
  have s5 := emitSeed_evals_ei .e5 .e6 false emitSeed_step_e5 inp
    [false, true, false, false, false] v
  have t5 := EvalsToInTime.trans emitTautSeedComputer.step 5 1 _ _ _ t4
    (by simpa [encodeFormula_tautSeed] using s5)
  have s6 := emitSeed_evals_ei .e6 .e7 false emitSeed_step_e6 inp
    [false, false, true, false, false, false] v
  have t6 := EvalsToInTime.trans emitTautSeedComputer.step 6 1 _ _ _ t5
    (by simpa [encodeFormula_tautSeed] using s6)
  have s7 := emitSeed_evals_ei .e7 .e8 false emitSeed_step_e7 inp
    [false, false, false, true, false, false, false] v
  have t7 := EvalsToInTime.trans emitTautSeedComputer.step 7 1 _ _ _ t6
    (by simpa [encodeFormula_tautSeed] using s7)
  have s8 := emitSeed_evals_ei .e8 .e9 true emitSeed_step_e8 inp
    [false, false, false, false, true, false, false, false] v
  have t8 := EvalsToInTime.trans emitTautSeedComputer.step 8 1 _ _ _ t7
    (by simpa [encodeFormula_tautSeed] using s8)
  have s9 := emitSeed_evals_e9 inp
    [true, false, false, false, false, true, false, false, false] v
  have t9 := EvalsToInTime.trans emitTautSeedComputer.step 9 1 _ _ _ t8
    (by simpa [encodeFormula_tautSeed] using s9)
  simpa [encodeFormula_tautSeed] using t9

/-- Full run: clear input, emit seed encoding. -/
noncomputable def emitTautSeed_evals (s : List Bool) :
    TM2OutputsInTime emitTautSeedComputer s (some (encodeFormula tautSeed))
      (s.length + 11) := by
  have hclear := emitSeed_evals_clear s []
  have hnil := emitSeed_evals_clear_nil []
  have h1 := EvalsToInTime.trans emitTautSeedComputer.step s.length 1
    _ _ _ hclear hnil
  have hemit := emitSeed_evals_emit [] true
  have h1' : EvalsToInTime emitTautSeedComputer.step
      (emitSeedCfg (some .clear) false s [])
      (some (emitSeedCfg (some .e0) true [] []))
      (s.length + 1) := by
    have heq : 1 + s.length = s.length + 1 := by omega
    exact heq ▸ h1
  have h2 := EvalsToInTime.trans emitTautSeedComputer.step (s.length + 1) 10
    _ _ _ h1' hemit
  have hbound : EvalsToInTime emitTautSeedComputer.step
      (initList emitTautSeedComputer s)
      (some (haltList emitTautSeedComputer (encodeFormula tautSeed)))
      (s.length + 11) := by
    rw [emitTautSeed_initList, emitTautSeed_haltList]
    exact ⟨h2.toEvalsTo, le_trans h2.steps_le_m (by omega)⟩
  exact hbound

noncomputable def emitTautSeedTime : Polynomial ℕ := Polynomial.X + 11

theorem emitTautSeedTime_eval (n : ℕ) :
    emitTautSeedTime.eval n = n + 11 := by
  simp [emitTautSeedTime, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_ofNat]

/-- Emitting `encodeFormula tautSeed` is poly time (TT map fail branches). -/
noncomputable def emitTautSeedComputableInPolyTime :
    TM2ComputableInPolyTime idBitEnc idBitEnc
      (fun _ : List Bool => encodeFormula tautSeed) where
  tm := emitTautSeedComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := emitTautSeedTime
  outputsFun s := by
    change TM2OutputsInTime emitTautSeedComputer (List.map id (idBitEnc s))
      (some (List.map id (idBitEnc (encodeFormula tautSeed))))
      (emitTautSeedTime.eval (idBitEnc s).length)
    simp only [idBitEnc, List.map_id, id_eq, emitTautSeedTime_eval]
    exact emitTautSeed_evals s

/-- Cluster A complete: `decodePairResult` is poly time via the branching FinTM2. -/
theorem decodePairResult_computableInPolyTime :
    Nonempty (TM2ComputableInPolyTime idBitEnc idBitEnc decodePairResult) :=
  ⟨decodePairResultComputableInPolyTime⟩

/-! ## Cluster B success slice: `decodeFormulaResult` on `encodeFormula` inputs -/

/-- On well formed formula encodings, `prefixFalseCopyComputer` realizes
`decodeFormulaResult ∘ encodeFormula`. -/
noncomputable def decodeFormulaResult_on_encodeFormula_computableInPolyTime :
    TM2ComputableInPolyTime encodeFormula idBitEnc
      (fun φ => decodeFormulaResult (encodeFormula φ)) where
  tm := prefixFalseCopyComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := prefixFalseCopyTime
  outputsFun φ := by
    change TM2OutputsInTime prefixFalseCopyComputer
      (List.map id (encodeFormula φ))
      (some (List.map id (idBitEnc (decodeFormulaResult (encodeFormula φ)))))
      (prefixFalseCopyTime.eval (encodeFormula φ).length)
    simp only [idBitEnc, List.map_id, id_eq, decodeFormulaResult_encodeFormula,
      prefixFalseCopyTime_eval]
    exact prefixFalseCopy_evals (encodeFormula φ)

/-- Same success rewrite under identity encodings: well formed inputs are exactly
`encodeFormula` images, and `decodeFormulaResult` is `false :: ·` on those. -/
theorem decodeFormulaResult_on_encodeFormula_eq (φ : PropFormula) :
    decodeFormulaResult (encodeFormula φ) = false :: encodeFormula φ :=
  decodeFormulaResult_encodeFormula φ

/-! ## Cluster B branching FinTM2 (formula prefix validator)

Duplicate the input, validate that the copy is a full `encodeFormula` image via
recursive descent (tag bits, unary nat, marker stack for not and binary nodes),
then either prefix false copy or emit `[true]`. Marker bit `true` means parse one
more sibling; `false` means not parent, continue `afterSub`. -/

open TM2.Stmt

inductive DFRStack where
  | inp | aux | work | out
  deriving DecidableEq, Repr

instance : Fintype DFRStack where
  elems := {.inp, .aux, .work, .out}
  complete s := by cases s <;> simp

inductive DFRLabel where
  | dupToAux | split
  | parseTag0 | parseTag1F | parseTag1T
  | parseNat | afterSub | checkWork
  | writeFalse | copy | rev
  | clearInpFail | clearWorkFail | clearAuxFail | writeTrue
  deriving DecidableEq, Repr

instance : Fintype DFRLabel where
  elems := {.dupToAux, .split, .parseTag0, .parseTag1F, .parseTag1T, .parseNat,
    .afterSub, .checkWork, .writeFalse, .copy, .rev, .clearInpFail, .clearWorkFail,
    .clearAuxFail, .writeTrue}
  complete s := by cases s <;> simp

/-- Branching machine realizing `decodeFormulaResult`. -/
def decodeFormulaResultComputer : FinTM2 where
  K := DFRStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := DFRLabel
  main := .dupToAux
  σ := Option Bool
  initialState := none
  m
    | .dupToAux =>
        pop DFRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => DFRLabel.split)
            (push DFRStack.aux (fun s => s.getD false) <|
              load (fun _ => none) <|
                goto fun _ => DFRLabel.dupToAux)
    | .split =>
        pop DFRStack.aux (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => DFRLabel.parseTag0)
            (push DFRStack.inp (fun s => s.getD false) <|
              push DFRStack.work (fun s => s.getD false) <|
                load (fun _ => none) <|
                  goto fun _ => DFRLabel.split)
    | .parseTag0 =>
        pop DFRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => DFRLabel.clearInpFail)
            (branch (fun s => decide (s = some false))
              (goto fun _ => DFRLabel.parseTag1F)
              (goto fun _ => DFRLabel.parseTag1T))
    | .parseTag1F =>
        pop DFRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => DFRLabel.clearInpFail)
            (branch (fun s => decide (s = some false))
              (goto fun _ => DFRLabel.parseNat)
              (push DFRStack.aux (fun _ => false) <|
                load (fun _ => none) <|
                  goto fun _ => DFRLabel.parseTag0))
    | .parseTag1T =>
        pop DFRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => DFRLabel.clearInpFail)
            (push DFRStack.aux (fun _ => true) <|
              load (fun _ => none) <|
                goto fun _ => DFRLabel.parseTag0)
    | .parseNat =>
        pop DFRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => DFRLabel.clearInpFail)
            (branch (fun s => decide (s = some true))
              (load (fun _ => none) <|
                goto fun _ => DFRLabel.parseNat)
              (load (fun _ => none) <|
                goto fun _ => DFRLabel.afterSub))
    | .afterSub =>
        pop DFRStack.aux (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => DFRLabel.checkWork)
            (branch (fun s => decide (s = some true))
              (load (fun _ => none) <|
                goto fun _ => DFRLabel.parseTag0)
              (load (fun _ => none) <|
                goto fun _ => DFRLabel.afterSub))
    | .checkWork =>
        pop DFRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => DFRLabel.writeFalse)
            (goto fun _ => DFRLabel.clearInpFail)
    | .writeFalse =>
        push DFRStack.work (fun _ => false) <|
          load (fun _ => none) <|
            goto fun _ => DFRLabel.copy
    | .copy =>
        pop DFRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => DFRLabel.rev)
            (push DFRStack.work (fun s => s.getD false) <|
              load (fun _ => none) <|
                goto fun _ => DFRLabel.copy)
    | .rev =>
        pop DFRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            halt
            (push DFRStack.out (fun s => s.getD false) <|
              load (fun _ => none) <|
                goto fun _ => DFRLabel.rev)
    | .clearInpFail =>
        pop DFRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => DFRLabel.clearWorkFail)
            (goto fun _ => DFRLabel.clearInpFail)
    | .clearWorkFail =>
        pop DFRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => DFRLabel.clearAuxFail)
            (goto fun _ => DFRLabel.clearWorkFail)
    | .clearAuxFail =>
        pop DFRStack.aux (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (goto fun _ => DFRLabel.writeTrue)
            (goto fun _ => DFRLabel.clearAuxFail)
    | .writeTrue =>
        push DFRStack.out (fun _ => true) <|
          load (fun _ => none) <|
            halt

def dfrStk (inp aux work out : List Bool) : DFRStack → List Bool
  | .inp => inp
  | .aux => aux
  | .work => work
  | .out => out

def dfrCfg (l : Option DFRLabel) (v : Option Bool)
    (inp aux work out : List Bool) : decodeFormulaResultComputer.Cfg :=
  ⟨l, v, dfrStk inp aux work out⟩

theorem dfr_step_dup_cons (b : Bool) (rest aux work out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .dupToAux) none (b :: rest) aux work out) =
      some (dfrCfg (some .dupToAux) none rest (b :: aux) work out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.dupToAux, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_dup_nil (aux work out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .dupToAux) none [] aux work out) =
      some (dfrCfg (some .split) none [] aux work out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.split, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_split_cons (b : Bool) (rest inp work out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .split) none inp (b :: rest) work out) =
      some (dfrCfg (some .split) none (b :: inp) rest (b :: work) out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.split, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_split_nil (inp work out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .split) none inp [] work out) =
      some (dfrCfg (some .parseTag0) none inp [] work out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.parseTag0, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_parseTag0_nil (inp aux out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .parseTag0) none inp aux [] out) =
      some (dfrCfg (some .clearInpFail) none inp aux [] out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.clearInpFail, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_parseTag0_false (rest inp aux out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .parseTag0) none inp aux (false :: rest) out) =
      some (dfrCfg (some .parseTag1F) (some false) inp aux rest out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.parseTag1F, some false, stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_parseTag0_true (rest inp aux out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .parseTag0) none inp aux (true :: rest) out) =
      some (dfrCfg (some .parseTag1T) (some true) inp aux rest out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.parseTag1T, some true, stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_parseTag1F_nil (inp aux out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .parseTag1F) (some false) inp aux [] out) =
      some (dfrCfg (some .clearInpFail) none inp aux [] out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.clearInpFail, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_parseTag1F_var (rest inp aux out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .parseTag1F) (some false) inp aux (false :: rest) out) =
      some (dfrCfg (some .parseNat) (some false) inp aux rest out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.parseNat, some false, stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_parseTag1F_not (rest inp aux out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .parseTag1F) (some false) inp aux (true :: rest) out) =
      some (dfrCfg (some .parseTag0) none inp (false :: aux) rest out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.parseTag0, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_parseTag1T_nil (inp aux out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .parseTag1T) (some true) inp aux [] out) =
      some (dfrCfg (some .clearInpFail) none inp aux [] out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.clearInpFail, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_parseTag1T_bin (b : Bool) (rest inp aux out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .parseTag1T) (some true) inp aux (b :: rest) out) =
      some (dfrCfg (some .parseTag0) none inp (true :: aux) rest out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.parseTag0, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_parseNat_nil (v : Option Bool) (inp aux out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .parseNat) v inp aux [] out) =
      some (dfrCfg (some .clearInpFail) none inp aux [] out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.clearInpFail, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_parseNat_true (v : Option Bool) (rest inp aux out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .parseNat) v inp aux (true :: rest) out) =
      some (dfrCfg (some .parseNat) none inp aux rest out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.parseNat, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_parseNat_false (v : Option Bool) (rest inp aux out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .parseNat) v inp aux (false :: rest) out) =
      some (dfrCfg (some .afterSub) none inp aux rest out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.afterSub, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_afterSub_root (inp work out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .afterSub) none inp [] work out) =
      some (dfrCfg (some .checkWork) none inp [] work out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.checkWork, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_afterSub_sibling (rest inp work out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .afterSub) none inp (true :: rest) work out) =
      some (dfrCfg (some .parseTag0) none inp rest work out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.parseTag0, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_afterSub_not (rest inp work out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .afterSub) none inp (false :: rest) work out) =
      some (dfrCfg (some .afterSub) none inp rest work out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.afterSub, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_checkWork_empty (inp aux out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .checkWork) none inp aux [] out) =
      some (dfrCfg (some .writeFalse) none inp aux [] out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.writeFalse, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_checkWork_junk (b : Bool) (rest inp aux out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .checkWork) none inp aux (b :: rest) out) =
      some (dfrCfg (some .clearInpFail) (some b) inp aux rest out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.clearInpFail, some b, stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_writeFalse (inp aux out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .writeFalse) none inp aux [] out) =
      some (dfrCfg (some .copy) none inp aux [false] out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.copy, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_copy_cons (b : Bool) (rest aux work out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .copy) none (b :: rest) aux work out) =
      some (dfrCfg (some .copy) none rest aux (b :: work) out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.copy, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_copy_nil (aux work out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .copy) none [] aux work out) =
      some (dfrCfg (some .rev) none [] aux work out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.rev, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_rev_cons (b : Bool) (rest inp aux out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .rev) none inp aux (b :: rest) out) =
      some (dfrCfg (some .rev) none inp aux rest (b :: out)) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.rev, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_rev_nil (inp aux out : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .rev) none inp aux [] out) =
      some (dfrCfg none none inp aux [] out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option DFRLabel), (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_clearInpFail_cons (b : Bool) (rest aux work out : List Bool)
    (v : Option Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .clearInpFail) v (b :: rest) aux work out) =
      some (dfrCfg (some .clearInpFail) (some b) rest aux work out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.clearInpFail, some b, stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_clearInpFail_nil (aux work out : List Bool) (v : Option Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .clearInpFail) v [] aux work out) =
      some (dfrCfg (some .clearWorkFail) none [] aux work out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.clearWorkFail, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_clearWorkFail_cons (b : Bool) (rest inp aux out : List Bool)
    (v : Option Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .clearWorkFail) v inp aux (b :: rest) out) =
      some (dfrCfg (some .clearWorkFail) (some b) inp aux rest out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.clearWorkFail, some b, stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_clearWorkFail_nil (inp aux out : List Bool) (v : Option Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .clearWorkFail) v inp aux [] out) =
      some (dfrCfg (some .clearAuxFail) none inp aux [] out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.clearAuxFail, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_clearAuxFail_cons (b : Bool) (rest inp work out : List Bool)
    (v : Option Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .clearAuxFail) v inp (b :: rest) work out) =
      some (dfrCfg (some .clearAuxFail) (some b) inp rest work out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.clearAuxFail, some b, stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_clearAuxFail_nil (inp work out : List Bool) (v : Option Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .clearAuxFail) v inp [] work out) =
      some (dfrCfg (some .writeTrue) none inp [] work out) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some DFRLabel.writeTrue, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem dfr_step_writeTrue (inp aux work : List Bool) :
    TM2.step decodeFormulaResultComputer.m
      (dfrCfg (some .writeTrue) none inp aux work []) =
      some (dfrCfg none none inp aux work [true]) := by
  simp [decodeFormulaResultComputer, dfrCfg, dfrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option DFRLabel), (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, dfrStk]

theorem decodeFormulaResult_initList (s : List Bool) :
    initList decodeFormulaResultComputer s =
      dfrCfg (some .dupToAux) none s [] [] [] := by
  refine congrArg (fun stk =>
      (⟨some DFRLabel.dupToAux, (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [decodeFormulaResultComputer, dfrStk]

theorem decodeFormulaResult_haltList (s : List Bool) :
    haltList decodeFormulaResultComputer s =
      dfrCfg none none [] [] [] s := by
  refine congrArg (fun stk =>
      (⟨(none : Option DFRLabel), (none : Option Bool), stk⟩ :
        decodeFormulaResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [decodeFormulaResultComputer, dfrStk]

/-! ## Cluster B multi-step evals (success scaffolding and formula parse) -/

open StateTransition

set_option maxHeartbeats 4000000

def dfr_evals_dup_one (b : Bool) (rest aux work out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .dupToAux) none (b :: rest) aux work out)
      (some (dfrCfg (some .dupToAux) none rest (b :: aux) work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .dupToAux) none (b :: rest) aux work out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .dupToAux) none rest (b :: aux) work out)
    simp only [FinTM2.step]
    exact dfr_step_dup_cons b rest aux work out

noncomputable def dfr_evals_dup (s aux work out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .dupToAux) none s aux work out)
      (some (dfrCfg (some .dupToAux) none [] (s.reverse ++ aux) work out))
      s.length := by
  induction s generalizing aux with
  | nil =>
      simpa using EvalsToInTime.refl decodeFormulaResultComputer.step
        (dfrCfg (some .dupToAux) none [] aux work out)
  | cons b bs ih =>
      have h1 := dfr_evals_dup_one b bs aux work out
      have h2 := ih (b :: aux)
      have h := EvalsToInTime.trans decodeFormulaResultComputer.step 1 bs.length
        _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

def dfr_evals_dup_nil (aux work out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .dupToAux) none [] aux work out)
      (some (dfrCfg (some .split) none [] aux work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .dupToAux) none [] aux work out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .split) none [] aux work out)
    simp only [FinTM2.step]
    exact dfr_step_dup_nil aux work out

def dfr_evals_split_one (b : Bool) (rest inp work out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .split) none inp (b :: rest) work out)
      (some (dfrCfg (some .split) none (b :: inp) rest (b :: work) out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .split) none inp (b :: rest) work out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .split) none (b :: inp) rest (b :: work) out)
    simp only [FinTM2.step]
    exact dfr_step_split_cons b rest inp work out

noncomputable def dfr_evals_split (t inp work out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .split) none inp t work out)
      (some (dfrCfg (some .split) none (t.reverse ++ inp) [] (t.reverse ++ work) out))
      t.length := by
  induction t generalizing inp work with
  | nil =>
      simpa using EvalsToInTime.refl decodeFormulaResultComputer.step
        (dfrCfg (some .split) none inp [] work out)
  | cons b bs ih =>
      have h1 := dfr_evals_split_one b bs inp work out
      have h2 := ih (b :: inp) (b :: work)
      have h := EvalsToInTime.trans decodeFormulaResultComputer.step 1 bs.length
        _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

def dfr_evals_split_nil (inp work out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .split) none inp [] work out)
      (some (dfrCfg (some .parseTag0) none inp [] work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .split) none inp [] work out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .parseTag0) none inp [] work out)
    simp only [FinTM2.step]
    exact dfr_step_split_nil inp work out

/-- Duplicate phase: reach `parseTag0` with both `inp` and `work` holding `s`. -/
noncomputable def dfr_evals_to_parse (s : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .dupToAux) none s [] [] [])
      (some (dfrCfg (some .parseTag0) none s [] s []))
      (2 * s.length + 2) := by
  have hdup := dfr_evals_dup s [] [] []
  have hdup' : EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .dupToAux) none s [] [] [])
      (some (dfrCfg (some .dupToAux) none [] s.reverse [] [])) s.length := by
    simpa using hdup
  have htoSplit := dfr_evals_dup_nil s.reverse [] []
  have h1 := EvalsToInTime.trans decodeFormulaResultComputer.step s.length 1
    _ _ _ hdup' htoSplit
  have hsplit := dfr_evals_split s.reverse [] [] []
  have hsplit' : EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .split) none [] s.reverse [] [])
      (some (dfrCfg (some .split) none s [] s [])) s.reverse.length := by
    simpa [List.reverse_reverse] using hsplit
  have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step (1 + s.length)
    s.reverse.length _ _ _ h1 hsplit'
  have htoParse := dfr_evals_split_nil s s []
  have h3 := EvalsToInTime.trans decodeFormulaResultComputer.step
    (s.reverse.length + (1 + s.length)) 1 _ _ _ h2 htoParse
  refine ⟨h3.toEvalsTo, le_trans h3.steps_le_m ?_⟩
  simp [List.length_reverse]; omega

def dfr_evals_writeFalse (inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .writeFalse) none inp aux [] out)
      (some (dfrCfg (some .copy) none inp aux [false] out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .writeFalse) none inp aux [] out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .copy) none inp aux [false] out)
    simp only [FinTM2.step]
    exact dfr_step_writeFalse inp aux out

def dfr_evals_copy_one (b : Bool) (rest aux work out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .copy) none (b :: rest) aux work out)
      (some (dfrCfg (some .copy) none rest aux (b :: work) out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .copy) none (b :: rest) aux work out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .copy) none rest aux (b :: work) out)
    simp only [FinTM2.step]
    exact dfr_step_copy_cons b rest aux work out

def dfr_evals_copy_nil (aux work out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .copy) none [] aux work out)
      (some (dfrCfg (some .rev) none [] aux work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .copy) none [] aux work out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .rev) none [] aux work out)
    simp only [FinTM2.step]
    exact dfr_step_copy_nil aux work out

noncomputable def dfr_evals_copy (inp aux work out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .copy) none inp aux work out)
      (some (dfrCfg (some .rev) none [] aux (inp.reverse ++ work) out))
      (inp.length + 1) := by
  induction inp generalizing work with
  | nil =>
      simpa using dfr_evals_copy_nil aux work out
  | cons b bs ih =>
      have h1 := dfr_evals_copy_one b bs aux work out
      have h2 := ih (b :: work)
      have h := EvalsToInTime.trans decodeFormulaResultComputer.step 1 (bs.length + 1)
        _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

def dfr_evals_rev_one (b : Bool) (rest inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .rev) none inp aux (b :: rest) out)
      (some (dfrCfg (some .rev) none inp aux rest (b :: out))) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .rev) none inp aux (b :: rest) out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .rev) none inp aux rest (b :: out))
    simp only [FinTM2.step]
    exact dfr_step_rev_cons b rest inp aux out

def dfr_evals_rev_nil (inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .rev) none inp aux [] out)
      (some (dfrCfg none none inp aux [] out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .rev) none inp aux [] out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg none none inp aux [] out)
    simp only [FinTM2.step]
    exact dfr_step_rev_nil inp aux out

noncomputable def dfr_evals_rev (work inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .rev) none inp aux work out)
      (some (dfrCfg none none inp aux [] (work.reverse ++ out)))
      (work.length + 1) := by
  induction work generalizing out with
  | nil =>
      simpa using dfr_evals_rev_nil inp aux out
  | cons b bs ih =>
      have h1 := dfr_evals_rev_one b bs inp aux out
      have h2 := ih (b :: out)
      have h := EvalsToInTime.trans decodeFormulaResultComputer.step 1 (bs.length + 1)
        _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

/-- Success finisher from writeFalse: output `false :: s`. -/
noncomputable def dfr_evals_success_from_writeFalse (s : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .writeFalse) none s [] [] [])
      (some (dfrCfg none none [] [] [] (false :: s)))
      (2 * s.length + 4) := by
  have h0 := dfr_evals_writeFalse s [] []
  have hcopy := dfr_evals_copy s [] [false] []
  have h1 := EvalsToInTime.trans decodeFormulaResultComputer.step 1 (s.length + 1)
    _ _ _ h0 hcopy
  have hrev := dfr_evals_rev (s.reverse ++ [false]) [] [] []
  have hrev' : EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .rev) none [] [] (s.reverse ++ [false]) [])
      (some (dfrCfg none none [] [] [] (false :: s)))
      ((s.reverse ++ [false]).length + 1) := by
    simpa [List.reverse_append, List.reverse_cons, List.reverse_reverse, List.reverse_nil]
      using hrev
  have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step ((s.length + 1) + 1)
    ((s.reverse ++ [false]).length + 1) _ _ _ h1 hrev'
  refine ⟨h2.toEvalsTo, le_trans h2.steps_le_m ?_⟩
  simp [List.length_append, List.length_reverse]; omega

def dfr_evals_clearInp_one (b : Bool) (rest aux work out : List Bool) (v : Option Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .clearInpFail) v (b :: rest) aux work out)
      (some (dfrCfg (some .clearInpFail) (some b) rest aux work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .clearInpFail) v (b :: rest) aux work out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .clearInpFail) (some b) rest aux work out)
    simp only [FinTM2.step]
    exact dfr_step_clearInpFail_cons b rest aux work out v

def dfr_evals_clearInp_nil (aux work out : List Bool) (v : Option Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .clearInpFail) v [] aux work out)
      (some (dfrCfg (some .clearWorkFail) none [] aux work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .clearInpFail) v [] aux work out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .clearWorkFail) none [] aux work out)
    simp only [FinTM2.step]
    exact dfr_step_clearInpFail_nil aux work out v

noncomputable def dfr_evals_clearInp (inp aux work out : List Bool) (v : Option Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .clearInpFail) v inp aux work out)
      (some (dfrCfg (some .clearWorkFail) none [] aux work out))
      (inp.length + 1) := by
  induction inp generalizing v with
  | nil =>
      simpa using dfr_evals_clearInp_nil aux work out v
  | cons b bs ih =>
      have h := EvalsToInTime.trans decodeFormulaResultComputer.step 1 (bs.length + 1)
        _ _ _ (dfr_evals_clearInp_one b bs aux work out v) (ih (some b))
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

def dfr_evals_clearWorkFail_one (b : Bool) (rest inp aux out : List Bool)
    (v : Option Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .clearWorkFail) v inp aux (b :: rest) out)
      (some (dfrCfg (some .clearWorkFail) (some b) inp aux rest out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .clearWorkFail) v inp aux (b :: rest) out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .clearWorkFail) (some b) inp aux rest out)
    simp only [FinTM2.step]
    exact dfr_step_clearWorkFail_cons b rest inp aux out v

def dfr_evals_clearWorkFail_nil (inp aux out : List Bool) (v : Option Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .clearWorkFail) v inp aux [] out)
      (some (dfrCfg (some .clearAuxFail) none inp aux [] out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .clearWorkFail) v inp aux [] out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .clearAuxFail) none inp aux [] out)
    simp only [FinTM2.step]
    exact dfr_step_clearWorkFail_nil inp aux out v

noncomputable def dfr_evals_clearWorkFail (work inp aux out : List Bool)
    (v : Option Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .clearWorkFail) v inp aux work out)
      (some (dfrCfg (some .clearAuxFail) none inp aux [] out))
      (work.length + 1) := by
  induction work generalizing v with
  | nil =>
      simpa using dfr_evals_clearWorkFail_nil inp aux out v
  | cons b bs ih =>
      have h := EvalsToInTime.trans decodeFormulaResultComputer.step 1 (bs.length + 1)
        _ _ _ (dfr_evals_clearWorkFail_one b bs inp aux out v) (ih (some b))
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

def dfr_evals_clearAuxFail_one (b : Bool) (rest inp work out : List Bool)
    (v : Option Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .clearAuxFail) v inp (b :: rest) work out)
      (some (dfrCfg (some .clearAuxFail) (some b) inp rest work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .clearAuxFail) v inp (b :: rest) work out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .clearAuxFail) (some b) inp rest work out)
    simp only [FinTM2.step]
    exact dfr_step_clearAuxFail_cons b rest inp work out v

def dfr_evals_clearAuxFail_nil (inp work out : List Bool) (v : Option Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .clearAuxFail) v inp [] work out)
      (some (dfrCfg (some .writeTrue) none inp [] work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .clearAuxFail) v inp [] work out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .writeTrue) none inp [] work out)
    simp only [FinTM2.step]
    exact dfr_step_clearAuxFail_nil inp work out v

noncomputable def dfr_evals_clearAuxFail (aux inp work out : List Bool)
    (v : Option Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .clearAuxFail) v inp aux work out)
      (some (dfrCfg (some .writeTrue) none inp [] work out))
      (aux.length + 1) := by
  induction aux generalizing v with
  | nil =>
      simpa using dfr_evals_clearAuxFail_nil inp work out v
  | cons b bs ih =>
      have h := EvalsToInTime.trans decodeFormulaResultComputer.step 1 (bs.length + 1)
        _ _ _ (dfr_evals_clearAuxFail_one b bs inp work out v) (ih (some b))
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

def dfr_evals_writeTrue (inp aux work : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .writeTrue) none inp aux work [])
      (some (dfrCfg none none inp aux work [true])) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .writeTrue) none inp aux work [])).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg none none inp aux work [true])
    simp only [FinTM2.step]
    exact dfr_step_writeTrue inp aux work

/-- Failure finisher from clearInpFail: clear inp, work, and aux, then emit `[true]`. -/
noncomputable def dfr_evals_fail_from_clearInp (s work aux : List Bool)
    (v : Option Bool := none) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .clearInpFail) v s aux work [])
      (some (dfrCfg none none [] [] [] [true]))
      (s.length + work.length + aux.length + 4) := by
  have h1 := dfr_evals_clearInp s aux work [] v
  have h2 := dfr_evals_clearWorkFail work [] aux [] none
  have h12 := EvalsToInTime.trans decodeFormulaResultComputer.step (s.length + 1)
    (work.length + 1) _ _ _ h1 h2
  have h3 := dfr_evals_clearAuxFail aux [] [] [] none
  have h123 := EvalsToInTime.trans decodeFormulaResultComputer.step
    ((work.length + 1) + (s.length + 1)) (aux.length + 1) _ _ _ h12 h3
  have h4 := dfr_evals_writeTrue [] [] []
  have h := EvalsToInTime.trans decodeFormulaResultComputer.step
    ((aux.length + 1) + ((work.length + 1) + (s.length + 1))) 1 _ _ _ h123 h4
  refine ⟨h.toEvalsTo, le_trans h.steps_le_m ?_⟩
  omega

/-- Step cost to parse one encoded formula from `parseTag0` to `afterSub`. -/
def dfrParseCost : PropFormula → ℕ
  | .var n => n + 3
  | .not φ => dfrParseCost φ + 3
  | .and φ ψ => dfrParseCost φ + dfrParseCost ψ + 3
  | .or φ ψ => dfrParseCost φ + dfrParseCost ψ + 3

def dfr_evals_parseNat_true_one (v : Option Bool) (rest inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseNat) v inp aux (true :: rest) out)
      (some (dfrCfg (some .parseNat) none inp aux rest out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .parseNat) v inp aux (true :: rest) out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .parseNat) none inp aux rest out)
    simp only [FinTM2.step]
    exact dfr_step_parseNat_true v rest inp aux out

def dfr_evals_parseNat_false_one (v : Option Bool) (rest inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseNat) v inp aux (false :: rest) out)
      (some (dfrCfg (some .afterSub) none inp aux rest out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .parseNat) v inp aux (false :: rest) out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .afterSub) none inp aux rest out)
    simp only [FinTM2.step]
    exact dfr_step_parseNat_false v rest inp aux out

/-- Consume `encodeNat n ++ rest` from `parseNat` into `afterSub`. -/
noncomputable def dfr_evals_parseNat (n : ℕ) (rest inp aux out : List Bool)
    (v : Option Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseNat) v inp aux (encodeNat n ++ rest) out)
      (some (dfrCfg (some .afterSub) none inp aux rest out))
      (n + 1) := by
  induction n generalizing v with
  | zero =>
      change EvalsToInTime _ (dfrCfg _ v inp aux (false :: rest) out) _ 1
      simpa [encodeNat] using dfr_evals_parseNat_false_one v rest inp aux out
  | succ n ih =>
      have hbits : encodeNat (n + 1) ++ rest = true :: (encodeNat n ++ rest) := by
        simp [encodeNat, List.replicate_succ]
      rw [hbits]
      have h1 := dfr_evals_parseNat_true_one v (encodeNat n ++ rest) inp aux out
      have h2 := ih none
      have h := EvalsToInTime.trans decodeFormulaResultComputer.step 1 (n + 1)
        _ _ _ h1 h2
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

def dfr_evals_parseTag0_false_one (rest inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseTag0) none inp aux (false :: rest) out)
      (some (dfrCfg (some .parseTag1F) (some false) inp aux rest out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .parseTag0) none inp aux (false :: rest) out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .parseTag1F) (some false) inp aux rest out)
    simp only [FinTM2.step]
    exact dfr_step_parseTag0_false rest inp aux out

def dfr_evals_parseTag0_true_one (rest inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseTag0) none inp aux (true :: rest) out)
      (some (dfrCfg (some .parseTag1T) (some true) inp aux rest out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .parseTag0) none inp aux (true :: rest) out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .parseTag1T) (some true) inp aux rest out)
    simp only [FinTM2.step]
    exact dfr_step_parseTag0_true rest inp aux out

def dfr_evals_parseTag1F_var_one (rest inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseTag1F) (some false) inp aux (false :: rest) out)
      (some (dfrCfg (some .parseNat) (some false) inp aux rest out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .parseTag1F) (some false) inp aux (false :: rest) out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .parseNat) (some false) inp aux rest out)
    simp only [FinTM2.step]
    exact dfr_step_parseTag1F_var rest inp aux out

def dfr_evals_parseTag1F_not_one (rest inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseTag1F) (some false) inp aux (true :: rest) out)
      (some (dfrCfg (some .parseTag0) none inp (false :: aux) rest out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .parseTag1F) (some false) inp aux (true :: rest) out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .parseTag0) none inp (false :: aux) rest out)
    simp only [FinTM2.step]
    exact dfr_step_parseTag1F_not rest inp aux out

def dfr_evals_parseTag1T_bin_one (b : Bool) (rest inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseTag1T) (some true) inp aux (b :: rest) out)
      (some (dfrCfg (some .parseTag0) none inp (true :: aux) rest out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .parseTag1T) (some true) inp aux (b :: rest) out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .parseTag0) none inp (true :: aux) rest out)
    simp only [FinTM2.step]
    exact dfr_step_parseTag1T_bin b rest inp aux out

def dfr_evals_afterSub_not_one (rest inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .afterSub) none inp (false :: aux) rest out)
      (some (dfrCfg (some .afterSub) none inp aux rest out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .afterSub) none inp (false :: aux) rest out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .afterSub) none inp aux rest out)
    simp only [FinTM2.step]
    exact dfr_step_afterSub_not aux inp rest out

def dfr_evals_afterSub_sibling_one (rest inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .afterSub) none inp (true :: aux) rest out)
      (some (dfrCfg (some .parseTag0) none inp aux rest out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .afterSub) none inp (true :: aux) rest out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .parseTag0) none inp aux rest out)
    simp only [FinTM2.step]
    exact dfr_step_afterSub_sibling aux inp rest out

def dfr_evals_afterSub_root_one (inp work out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .afterSub) none inp [] work out)
      (some (dfrCfg (some .checkWork) none inp [] work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .afterSub) none inp [] work out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .checkWork) none inp [] work out)
    simp only [FinTM2.step]
    exact dfr_step_afterSub_root inp work out

def dfr_evals_checkWork_empty_one (inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .checkWork) none inp aux [] out)
      (some (dfrCfg (some .writeFalse) none inp aux [] out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .checkWork) none inp aux [] out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .writeFalse) none inp aux [] out)
    simp only [FinTM2.step]
    exact dfr_step_checkWork_empty inp aux out

def dfr_evals_parseTag0_nil_one (inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseTag0) none inp aux [] out)
      (some (dfrCfg (some .clearInpFail) none inp aux [] out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .parseTag0) none inp aux [] out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .clearInpFail) none inp aux [] out)
    simp only [FinTM2.step]
    exact dfr_step_parseTag0_nil inp aux out

/-- From `parseTag0`, parse `encodeFormula φ ++ rest` down to `afterSub`. -/
noncomputable def dfr_evals_parse_formula (φ : PropFormula) (rest inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseTag0) none inp aux (encodeFormula φ ++ rest) out)
      (some (dfrCfg (some .afterSub) none inp aux rest out))
      (dfrParseCost φ) := by
  induction φ generalizing rest aux with
  | var n =>
      have hbits : encodeFormula (.var n) ++ rest =
          false :: false :: (encodeNat n ++ rest) := by
        simp [encodeFormula]
      rw [hbits]
      have h0 := dfr_evals_parseTag0_false_one (false :: (encodeNat n ++ rest)) inp aux out
      have h1 := dfr_evals_parseTag1F_var_one (encodeNat n ++ rest) inp aux out
      have h01 := EvalsToInTime.trans decodeFormulaResultComputer.step 1 1
        _ _ _ h0 h1
      have hnat := dfr_evals_parseNat n rest inp aux out (some false)
      have h := EvalsToInTime.trans decodeFormulaResultComputer.step 2 (n + 1)
        _ _ _ h01 hnat
      simpa [dfrParseCost, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  | not φ ih =>
      have hbits : encodeFormula (.not φ) ++ rest =
          false :: true :: (encodeFormula φ ++ rest) := by
        simp [encodeFormula]
      rw [hbits]
      have h0 := dfr_evals_parseTag0_false_one (true :: (encodeFormula φ ++ rest)) inp aux out
      have h1 := dfr_evals_parseTag1F_not_one (encodeFormula φ ++ rest) inp aux out
      have h01 := EvalsToInTime.trans decodeFormulaResultComputer.step 1 1
        _ _ _ h0 h1
      have hφ := ih rest (false :: aux)
      have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step 2 (dfrParseCost φ)
        _ _ _ h01 hφ
      have hpop := dfr_evals_afterSub_not_one rest inp aux out
      have h := EvalsToInTime.trans decodeFormulaResultComputer.step
        (dfrParseCost φ + 2) 1 _ _ _ h2 hpop
      have heq : 1 + (dfrParseCost φ + 2) = dfrParseCost (.not φ) := by
        simp [dfrParseCost]; omega
      exact heq ▸ h
  | and φ ψ ihφ ihψ =>
      have hbits : encodeFormula (.and φ ψ) ++ rest =
          true :: false :: (encodeFormula φ ++ (encodeFormula ψ ++ rest)) := by
        simp [encodeFormula, List.append_assoc]
      rw [hbits]
      have h0 :=
        dfr_evals_parseTag0_true_one
          (false :: (encodeFormula φ ++ (encodeFormula ψ ++ rest))) inp aux out
      have h1 :=
        dfr_evals_parseTag1T_bin_one false
          (encodeFormula φ ++ (encodeFormula ψ ++ rest)) inp aux out
      have h01 := EvalsToInTime.trans decodeFormulaResultComputer.step 1 1
        _ _ _ h0 h1
      have hφ := ihφ (encodeFormula ψ ++ rest) (true :: aux)
      have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step 2 (dfrParseCost φ)
        _ _ _ h01 hφ
      have hsib :=
        dfr_evals_afterSub_sibling_one (encodeFormula ψ ++ rest) inp aux out
      have h3 := EvalsToInTime.trans decodeFormulaResultComputer.step
        (dfrParseCost φ + 2) 1 _ _ _ h2 hsib
      have hψ := ihψ rest aux
      have h := EvalsToInTime.trans decodeFormulaResultComputer.step
        (1 + (dfrParseCost φ + 2)) (dfrParseCost ψ) _ _ _ h3 hψ
      have heq :
          dfrParseCost ψ + (1 + (dfrParseCost φ + 2)) =
            dfrParseCost (.and φ ψ) := by
        simp [dfrParseCost]; omega
      exact heq ▸ h
  | or φ ψ ihφ ihψ =>
      have hbits : encodeFormula (.or φ ψ) ++ rest =
          true :: true :: (encodeFormula φ ++ (encodeFormula ψ ++ rest)) := by
        simp [encodeFormula, List.append_assoc]
      rw [hbits]
      have h0 :=
        dfr_evals_parseTag0_true_one
          (true :: (encodeFormula φ ++ (encodeFormula ψ ++ rest))) inp aux out
      have h1 :=
        dfr_evals_parseTag1T_bin_one true
          (encodeFormula φ ++ (encodeFormula ψ ++ rest)) inp aux out
      have h01 := EvalsToInTime.trans decodeFormulaResultComputer.step 1 1
        _ _ _ h0 h1
      have hφ := ihφ (encodeFormula ψ ++ rest) (true :: aux)
      have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step 2 (dfrParseCost φ)
        _ _ _ h01 hφ
      have hsib :=
        dfr_evals_afterSub_sibling_one (encodeFormula ψ ++ rest) inp aux out
      have h3 := EvalsToInTime.trans decodeFormulaResultComputer.step
        (dfrParseCost φ + 2) 1 _ _ _ h2 hsib
      have hψ := ihψ rest aux
      have h := EvalsToInTime.trans decodeFormulaResultComputer.step
        (1 + (dfrParseCost φ + 2)) (dfrParseCost ψ) _ _ _ h3 hψ
      have heq :
          dfrParseCost ψ + (1 + (dfrParseCost φ + 2)) =
            dfrParseCost (.or φ ψ) := by
        simp [dfrParseCost]; omega
      exact heq ▸ h

/-- From parse of a full `encodeFormula φ`, reach writeFalse. -/
noncomputable def dfr_evals_parse_encodeFormula (φ : PropFormula) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseTag0) none (encodeFormula φ) [] (encodeFormula φ) [])
      (some (dfrCfg (some .writeFalse) none (encodeFormula φ) [] [] []))
      (dfrParseCost φ + 2) := by
  have hparse := dfr_evals_parse_formula φ [] (encodeFormula φ) [] []
  have hparse' : EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseTag0) none (encodeFormula φ) [] (encodeFormula φ) [])
      (some (dfrCfg (some .afterSub) none (encodeFormula φ) [] [] []))
      (dfrParseCost φ) := by
    simpa using hparse
  have hroot := dfr_evals_afterSub_root_one (encodeFormula φ) [] []
  have h1 := EvalsToInTime.trans decodeFormulaResultComputer.step (dfrParseCost φ) 1
    _ _ _ hparse' hroot
  have hcheck := dfr_evals_checkWork_empty_one (encodeFormula φ) [] []
  have h := EvalsToInTime.trans decodeFormulaResultComputer.step
    (1 + dfrParseCost φ) 1 _ _ _ h1 hcheck
  have heq : 1 + (1 + dfrParseCost φ) = dfrParseCost φ + 2 := by omega
  exact heq ▸ h

/-- Full success run on `encodeFormula φ`. -/
noncomputable def dfr_evals_on_encodeFormula (φ : PropFormula) :
    TM2OutputsInTime decodeFormulaResultComputer (encodeFormula φ)
      (some (false :: encodeFormula φ))
      (4 * (encodeFormula φ).length + dfrParseCost φ + 8) := by
  let s := encodeFormula φ
  have hto := dfr_evals_to_parse s
  have hparse := dfr_evals_parse_encodeFormula φ
  have h1 := EvalsToInTime.trans decodeFormulaResultComputer.step (2 * s.length + 2)
    (dfrParseCost φ + 2) _ _ _ hto hparse
  have hsucc := dfr_evals_success_from_writeFalse s
  have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step
    ((dfrParseCost φ + 2) + (2 * s.length + 2)) (2 * s.length + 4)
    _ _ _ h1 hsucc
  have hbound : EvalsToInTime decodeFormulaResultComputer.step
      (initList decodeFormulaResultComputer s)
      (some (haltList decodeFormulaResultComputer (false :: s)))
      (4 * s.length + dfrParseCost φ + 8) := by
    rw [decodeFormulaResult_initList, decodeFormulaResult_haltList]
    -- trans yields (2*s.length+4) + ((dfrParseCost+2)+(2*s.length+2))
    exact ⟨h2.toEvalsTo, le_trans h2.steps_le_m (by omega)⟩
  exact hbound

/-- Empty input fails at parseTag0 and emits `[true]`. -/
noncomputable def dfr_evals_on_nil :
    TM2OutputsInTime decodeFormulaResultComputer [] (some [true]) 7 := by
  have hto := dfr_evals_to_parse []
  have hfail0 := dfr_evals_parseTag0_nil_one [] [] []
  have h1 := EvalsToInTime.trans decodeFormulaResultComputer.step 2 1
    _ _ _ hto hfail0
  have hfail := dfr_evals_fail_from_clearInp [] [] []
  have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step 3 4
    _ _ _ h1 hfail
  have hbound : EvalsToInTime decodeFormulaResultComputer.step
      (initList decodeFormulaResultComputer [])
      (some (haltList decodeFormulaResultComputer [true])) 7 := by
    rw [decodeFormulaResult_initList, decodeFormulaResult_haltList]
    exact ⟨h2.toEvalsTo, le_trans h2.steps_le_m (by omega)⟩
  exact hbound

def dfr_evals_checkWork_junk_one (b : Bool) (rest inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .checkWork) none inp aux (b :: rest) out)
      (some (dfrCfg (some .clearInpFail) (some b) inp aux rest out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .checkWork) none inp aux (b :: rest) out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .clearInpFail) (some b) inp aux rest out)
    simp only [FinTM2.step]
    exact dfr_step_checkWork_junk b rest inp aux out

/-- When a full formula prefix is followed by junk, fail at checkWork. -/
noncomputable def dfr_evals_on_encodeFormula_junk (φ : PropFormula) (junk : List Bool)
    (hjunk : junk ≠ []) :
    TM2OutputsInTime decodeFormulaResultComputer (encodeFormula φ ++ junk)
      (some [true])
      (4 * (encodeFormula φ ++ junk).length + dfrParseCost φ + 10) := by
  let s := encodeFormula φ ++ junk
  have hto := dfr_evals_to_parse s
  have hparse := dfr_evals_parse_formula φ junk s [] []
  have hparse' : EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseTag0) none s [] s [])
      (some (dfrCfg (some .afterSub) none s [] junk []))
      (dfrParseCost φ) := by
    simpa [s] using hparse
  have h1 := EvalsToInTime.trans decodeFormulaResultComputer.step (2 * s.length + 2)
    (dfrParseCost φ) _ _ _ hto hparse'
  have hroot := dfr_evals_afterSub_root_one s junk []
  have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step
    (dfrParseCost φ + (2 * s.length + 2)) 1 _ _ _
    (by simpa [Nat.add_comm] using h1) hroot
  cases junk with
  | nil => exact (hjunk rfl).elim
  | cons b rest =>
      have hjunk1 := dfr_evals_checkWork_junk_one b rest s [] []
      have h3 := EvalsToInTime.trans decodeFormulaResultComputer.step
        (1 + (dfrParseCost φ + (2 * s.length + 2))) 1 _ _ _ h2 hjunk1
      have hfail := dfr_evals_fail_from_clearInp s rest [] (some b)
      have h4 := EvalsToInTime.trans decodeFormulaResultComputer.step
        (1 + (1 + (dfrParseCost φ + (2 * s.length + 2))))
        (s.length + rest.length + 4) _ _ _ h3 hfail
      have hbound : EvalsToInTime decodeFormulaResultComputer.step
          (initList decodeFormulaResultComputer s)
          (some (haltList decodeFormulaResultComputer [true]))
          (4 * s.length + dfrParseCost φ + 10) := by
        rw [decodeFormulaResult_initList, decodeFormulaResult_haltList]
        exact ⟨h4.toEvalsTo, le_trans h4.steps_le_m (by
          simp [s, List.length_append]; omega)⟩
      exact hbound

/-- Full failure when `decodeFormula s = none` via leftover suffix after a valid
prefix. -/
noncomputable def dfr_evals_on_none_of_junk {s : List Bool} {φ : PropFormula}
    {rest : List Bool}
    (hpref : decodeFormulaPrefixFuel (s.length + 1) s = some (φ, rest))
    (hne : rest ≠ []) :
    TM2OutputsInTime decodeFormulaResultComputer s (some [true])
      (4 * s.length + dfrParseCost φ + 10) := by
  have hs : s = encodeFormula φ ++ rest :=
    encodeFormula_append_of_decodeFormulaPrefixFuel _ hpref
  subst hs
  exact dfr_evals_on_encodeFormula_junk φ rest hne

/-! ## Cluster B prefix-none failure and full poly time witness -/

theorem dfrParseCost_le (φ : PropFormula) :
    dfrParseCost φ ≤ 2 * (encodeFormula φ).length := by
  induction φ with
  | var n =>
      simp [dfrParseCost, encodeFormula, encodeNat, List.length_append,
        List.length_replicate]
  | not φ ih =>
      simp only [dfrParseCost, length_encodeFormula_not]
      omega
  | and φ ψ ihφ ihψ =>
      simp only [dfrParseCost, length_encodeFormula_and]
      omega
  | or φ ψ ihφ ihψ =>
      simp only [dfrParseCost, length_encodeFormula_or]
      omega

def dfr_evals_parseTag1F_nil_one (inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseTag1F) (some false) inp aux [] out)
      (some (dfrCfg (some .clearInpFail) none inp aux [] out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .parseTag1F) (some false) inp aux [] out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .clearInpFail) none inp aux [] out)
    simp only [FinTM2.step]
    exact dfr_step_parseTag1F_nil inp aux out

def dfr_evals_parseTag1T_nil_one (inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseTag1T) (some true) inp aux [] out)
      (some (dfrCfg (some .clearInpFail) none inp aux [] out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .parseTag1T) (some true) inp aux [] out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .clearInpFail) none inp aux [] out)
    simp only [FinTM2.step]
    exact dfr_step_parseTag1T_nil inp aux out

def dfr_evals_parseNat_nil_one (v : Option Bool) (inp aux out : List Bool) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseNat) v inp aux [] out)
      (some (dfrCfg (some .clearInpFail) none inp aux [] out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (dfrCfg (some .parseNat) v inp aux [] out)).bind
        decodeFormulaResultComputer.step =
      some (dfrCfg (some .clearInpFail) none inp aux [] out)
    simp only [FinTM2.step]
    exact dfr_step_parseNat_nil v inp aux out

/-- `decodeNat` fails exactly when the work tape is all `true`; consume it. -/
noncomputable def dfr_evals_parseNat_fail (work inp aux out : List Bool)
    (v : Option Bool) (h : decodeNat work = none) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseNat) v inp aux work out)
      (some (dfrCfg (some .clearInpFail) none inp aux [] out))
      (work.length + 1) := by
  have hall : ∀ b ∈ work, b = true := (decodeNat_eq_none_iff work).mp h
  induction work generalizing v with
  | nil =>
      simpa using dfr_evals_parseNat_nil_one v inp aux out
  | cons b rest ih =>
      have hb : b = true := hall b (List.Mem.head (a := b) (as := rest))
      subst hb
      have hrest : decodeNat rest = none :=
        (decodeNat_eq_none_iff rest).mpr fun b hb =>
          hall b (List.Mem.tail (a := b) (b := true) hb)
      have h1 := dfr_evals_parseNat_true_one v rest inp aux out
      have h2 := ih none hrest fun b hb =>
        hall b (List.Mem.tail (a := b) (b := true) hb)
      have h := EvalsToInTime.trans decodeFormulaResultComputer.step 1
        (rest.length + 1) _ _ _ h1 h2
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- From `parseTag0`, fail whenever fuelled prefix decode returns none.
Requires `work.length < fuel` so recursive children keep a usable fuel budget.
Ends at halt with `[true]` after clearing inp, work, and aux (including markers). -/
noncomputable def dfr_evals_parse_fail (work inp aux : List Bool) (fuel : ℕ)
    (hfuel : work.length < fuel)
    (h : decodeFormulaPrefixFuel fuel work = none) :
    EvalsToInTime decodeFormulaResultComputer.step
      (dfrCfg (some .parseTag0) none inp aux work [])
      (some (dfrCfg none none [] [] [] [true]))
      (3 * work.length + inp.length + aux.length + 5) := by
  induction fuel generalizing work aux with
  | zero =>
      exact (Nat.not_lt_zero _ hfuel).elim
  | succ f ih =>
      match work with
      | [] =>
          have h1 := dfr_evals_parseTag0_nil_one inp aux []
          have hfail := dfr_evals_fail_from_clearInp inp [] aux none
          have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step 1
            (inp.length + aux.length + 4) _ _ _ h1 hfail
          refine ⟨h2.toEvalsTo, le_trans h2.steps_le_m (by
            simp [List.length_cons, List.length_nil] <;> omega)⟩
      | [false] =>
          have h0 := dfr_evals_parseTag0_false_one [] inp aux []
          have h1 := dfr_evals_parseTag1F_nil_one inp aux []
          have h01 := EvalsToInTime.trans decodeFormulaResultComputer.step 1 1
            _ _ _ h0 h1
          have hfail := dfr_evals_fail_from_clearInp inp [] aux none
          have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step 2
            (inp.length + aux.length + 4) _ _ _ h01 hfail
          refine ⟨h2.toEvalsTo, le_trans h2.steps_le_m (by
            simp [List.length_cons, List.length_nil] <;> omega)⟩
      | [true] =>
          have h0 := dfr_evals_parseTag0_true_one [] inp aux []
          have h1 := dfr_evals_parseTag1T_nil_one inp aux []
          have h01 := EvalsToInTime.trans decodeFormulaResultComputer.step 1 1
            _ _ _ h0 h1
          have hfail := dfr_evals_fail_from_clearInp inp [] aux none
          have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step 2
            (inp.length + aux.length + 4) _ _ _ h01 hfail
          refine ⟨h2.toEvalsTo, le_trans h2.steps_le_m (by
            simp [List.length_cons, List.length_nil] <;> omega)⟩
      | false :: false :: rest =>
          have hnat : decodeNat rest = none := by
            simp only [decodeFormulaPrefixFuel] at h
            cases hn : decodeNat rest with
            | none => rfl
            | some _ => simp [hn] at h
          have h0 :=
            dfr_evals_parseTag0_false_one (false :: rest) inp aux []
          have h1 := dfr_evals_parseTag1F_var_one rest inp aux []
          have h01 := EvalsToInTime.trans decodeFormulaResultComputer.step 1 1
            _ _ _ h0 h1
          have hnatfail :=
            dfr_evals_parseNat_fail rest inp aux [] (some false) hnat
          have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step 2
            (rest.length + 1) _ _ _ h01 hnatfail
          have hfail := dfr_evals_fail_from_clearInp inp [] aux none
          have h3 := EvalsToInTime.trans decodeFormulaResultComputer.step
            ((rest.length + 1) + 2) (inp.length + aux.length + 4) _ _ _ h2 hfail
          refine ⟨h3.toEvalsTo, le_trans h3.steps_le_m (by
            simp [List.length_cons, List.length_nil] <;> omega)⟩
      | false :: true :: rest =>
          have hchild : decodeFormulaPrefixFuel f rest = none := by
            simp only [decodeFormulaPrefixFuel] at h
            cases hc : decodeFormulaPrefixFuel f rest with
            | none => rfl
            | some _ => simp [hc] at h
          have hrest : rest.length < f := by
            simp only [List.length_cons] at hfuel
            omega
          have h0 :=
            dfr_evals_parseTag0_false_one (true :: rest) inp aux []
          have h1 := dfr_evals_parseTag1F_not_one rest inp aux []
          have h01 := EvalsToInTime.trans decodeFormulaResultComputer.step 1 1
            _ _ _ h0 h1
          have hfail := ih rest (false :: aux) hrest hchild
          have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step 2
            (3 * rest.length + inp.length + (false :: aux).length + 5)
            _ _ _ h01 hfail
          refine ⟨h2.toEvalsTo, le_trans h2.steps_le_m (by
            simp [List.length_cons, List.length_nil] <;> omega)⟩
      | true :: false :: rest =>
          have h0 :=
            dfr_evals_parseTag0_true_one (false :: rest) inp aux []
          have h1 :=
            dfr_evals_parseTag1T_bin_one false rest inp aux []
          have h01 := EvalsToInTime.trans decodeFormulaResultComputer.step 1 1
            _ _ _ h0 h1
          have hrest : rest.length < f := by
            simp only [List.length_cons] at hfuel
            omega
          cases hφ : decodeFormulaPrefixFuel f rest with
          | none =>
              have hfail := ih rest (true :: aux) hrest hφ
              have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step 2
                (3 * rest.length + inp.length + (true :: aux).length + 5)
                _ _ _ h01 hfail
              refine ⟨h2.toEvalsTo, le_trans h2.steps_le_m (by
                simp [List.length_cons, List.length_nil] <;> omega)⟩
          | some pr =>
              rcases pr with ⟨φ, rest₁⟩
              have hψ : decodeFormulaPrefixFuel f rest₁ = none := by
                simp only [decodeFormulaPrefixFuel, hφ] at h
                cases hs : decodeFormulaPrefixFuel f rest₁ with
                | none => rfl
                | some _ => simp [hs] at h
              have hs : rest = encodeFormula φ ++ rest₁ :=
                encodeFormula_append_of_decodeFormulaPrefixFuel _ hφ
              have hrest₁ : rest₁.length < f := by
                have : rest₁.length ≤ rest.length := by
                  simp [hs, List.length_append] <;> omega
                omega
              subst hs
              have hparse :=
                dfr_evals_parse_formula φ rest₁ inp (true :: aux) []
              have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step 2
                (dfrParseCost φ) _ _ _ h01 hparse
              have hsib :=
                dfr_evals_afterSub_sibling_one rest₁ inp aux []
              have h3 := EvalsToInTime.trans decodeFormulaResultComputer.step
                (dfrParseCost φ + 2) 1 _ _ _ h2 hsib
              have hfail := ih rest₁ aux hrest₁ hψ
              have h4 := EvalsToInTime.trans decodeFormulaResultComputer.step
                (1 + (dfrParseCost φ + 2))
                (3 * rest₁.length + inp.length + aux.length + 5) _ _ _ h3 hfail
              have hcost := dfrParseCost_le φ
              refine ⟨h4.toEvalsTo, le_trans h4.steps_le_m (by
                simp [List.length_append, List.length_cons] at hcost ⊢ <;> omega)⟩
      | true :: true :: rest =>
          have h0 :=
            dfr_evals_parseTag0_true_one (true :: rest) inp aux []
          have h1 :=
            dfr_evals_parseTag1T_bin_one true rest inp aux []
          have h01 := EvalsToInTime.trans decodeFormulaResultComputer.step 1 1
            _ _ _ h0 h1
          have hrest : rest.length < f := by
            simp only [List.length_cons] at hfuel
            omega
          cases hφ : decodeFormulaPrefixFuel f rest with
          | none =>
              have hfail := ih rest (true :: aux) hrest hφ
              have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step 2
                (3 * rest.length + inp.length + (true :: aux).length + 5)
                _ _ _ h01 hfail
              refine ⟨h2.toEvalsTo, le_trans h2.steps_le_m (by
                simp [List.length_cons, List.length_nil] <;> omega)⟩
          | some pr =>
              rcases pr with ⟨φ, rest₁⟩
              have hψ : decodeFormulaPrefixFuel f rest₁ = none := by
                simp only [decodeFormulaPrefixFuel, hφ] at h
                cases hs : decodeFormulaPrefixFuel f rest₁ with
                | none => rfl
                | some _ => simp [hs] at h
              have hs : rest = encodeFormula φ ++ rest₁ :=
                encodeFormula_append_of_decodeFormulaPrefixFuel _ hφ
              have hrest₁ : rest₁.length < f := by
                have : rest₁.length ≤ rest.length := by
                  simp [hs, List.length_append] <;> omega
                omega
              subst hs
              have hparse :=
                dfr_evals_parse_formula φ rest₁ inp (true :: aux) []
              have h2 := EvalsToInTime.trans decodeFormulaResultComputer.step 2
                (dfrParseCost φ) _ _ _ h01 hparse
              have hsib :=
                dfr_evals_afterSub_sibling_one rest₁ inp aux []
              have h3 := EvalsToInTime.trans decodeFormulaResultComputer.step
                (dfrParseCost φ + 2) 1 _ _ _ h2 hsib
              have hfail := ih rest₁ aux hrest₁ hψ
              have h4 := EvalsToInTime.trans decodeFormulaResultComputer.step
                (1 + (dfrParseCost φ + 2))
                (3 * rest₁.length + inp.length + aux.length + 5) _ _ _ h3 hfail
              have hcost := dfrParseCost_le φ
              refine ⟨h4.toEvalsTo, le_trans h4.steps_le_m (by
                simp [List.length_append, List.length_cons] at hcost ⊢ <;> omega)⟩

/-- Full failure when the fuelled prefix decode returns none. -/
noncomputable def dfr_evals_on_none_of_prefix (s : List Bool)
    (h : decodeFormulaPrefixFuel (s.length + 1) s = none) :
    TM2OutputsInTime decodeFormulaResultComputer s (some [true])
      (6 * s.length + 7) := by
  have hto := dfr_evals_to_parse s
  have hfuel : s.length < s.length + 1 := Nat.lt_succ_self _
  have hparse := dfr_evals_parse_fail s s [] (s.length + 1) hfuel h
  have h1 := EvalsToInTime.trans decodeFormulaResultComputer.step (2 * s.length + 2)
    (3 * s.length + s.length + 5) _ _ _ hto hparse
  have hbound : EvalsToInTime decodeFormulaResultComputer.step
      (initList decodeFormulaResultComputer s)
      (some (haltList decodeFormulaResultComputer [true]))
      (6 * s.length + 7) := by
    rw [decodeFormulaResult_initList, decodeFormulaResult_haltList]
    exact ⟨h1.toEvalsTo, le_trans h1.steps_le_m (by omega)⟩
  exact hbound

/-- Full failure for any `decodeFormula s = none`. -/
noncomputable def dfr_evals_on_none (s : List Bool) (h : decodeFormula s = none) :
    TM2OutputsInTime decodeFormulaResultComputer s (some [true])
      (7 * s.length + 10) := by
  cases hpref : decodeFormulaPrefixFuel (s.length + 1) s with
  | none =>
      have hout := dfr_evals_on_none_of_prefix s hpref
      exact ⟨hout.toEvalsTo, le_trans hout.steps_le_m (by omega)⟩
  | some pr =>
      rcases pr with ⟨φ, rest⟩
      have hne : rest ≠ [] := by
        unfold decodeFormula decodeFormulaPrefix at h
        simp only [hpref] at h
        intro hnil
        subst hnil
        simp at h
      have hout := dfr_evals_on_none_of_junk hpref hne
      have hcost := dfrParseCost_le φ
      have hs : s = encodeFormula φ ++ rest :=
        encodeFormula_append_of_decodeFormulaPrefixFuel _ hpref
      exact ⟨hout.toEvalsTo, le_trans hout.steps_le_m (by
        simp [hs, List.length_append] at hcost ⊢ <;> omega)⟩

noncomputable def decodeFormulaResultTime : Polynomial ℕ := 10 * Polynomial.X + 10

theorem decodeFormulaResultTime_eval (n : ℕ) :
    decodeFormulaResultTime.eval n = 10 * n + 10 := by
  simp [decodeFormulaResultTime, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat]

/-- Full `decodeFormulaResult` is poly time via the branching FinTM2. -/
noncomputable def decodeFormulaResultComputableInPolyTime :
    TM2ComputableInPolyTime idBitEnc idBitEnc decodeFormulaResult where
  tm := decodeFormulaResultComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := decodeFormulaResultTime
  outputsFun s := by
    change TM2OutputsInTime decodeFormulaResultComputer (List.map id (idBitEnc s))
      (some (List.map id (idBitEnc (decodeFormulaResult s))))
      (decodeFormulaResultTime.eval (idBitEnc s).length)
    simp only [idBitEnc, List.map_id, id_eq, decodeFormulaResultTime_eval]
    cases h : decodeFormula s with
    | none =>
        have hout := dfr_evals_on_none s h
        rw [decodeFormulaResult_of_none h]
        exact ⟨hout.toEvalsTo, le_trans hout.steps_le_m (by omega)⟩
    | some φ =>
        have hs : encodeFormula φ = s := encodeFormula_of_decodeFormula h
        subst hs
        have hout := dfr_evals_on_encodeFormula φ
        rw [decodeFormulaResult_encodeFormula]
        have hcost := dfrParseCost_le φ
        exact ⟨hout.toEvalsTo, le_trans hout.steps_le_m (by omega)⟩

/-- Cluster B complete: `decodeFormulaResult` is poly time via the branching FinTM2. -/
theorem decodeFormulaResult_computableInPolyTime :
    Nonempty (TM2ComputableInPolyTime idBitEnc idBitEnc decodeFormulaResult) :=
  ⟨decodeFormulaResultComputableInPolyTime⟩

/-! ## Cluster C prep: `validatesTautologyResult` (functional layer before FinTM2)

Branching FinTM2 for `validatesTautology` follows the same tape convention as
`decodePairResult` and `decodeFormulaResult`: `[true]` means reject (emit seed),
`false :: φCode` means accept and copy the formula encoding. -/

/-- Linear cost model for validation: O(|φCode| · |table|) in the prove pin. -/
def validatesTautologyCost (φCode table : List Bool) : ℕ :=
  φCode.length * (table.length + 1) + table.length + 1

theorem validatesTautologyCost_eq (φCode table : List Bool) :
    validatesTautologyCost φCode table =
      (φCode.length + 1) * (table.length + 1) := by
  unfold validatesTautologyCost
  ring

theorem validatesTautologyCost_le (φCode table : List Bool) :
    validatesTautologyCost φCode table ≤
      (φCode.length + 1) * (table.length + 1) :=
  le_of_eq (validatesTautologyCost_eq φCode table)

/-- Pure function the eventual FinTM2 must realize on decoded `(φCode, table)`. -/
def validatesTautologyResult (φCode table : List Bool) : List Bool :=
  match decodeFormula φCode with
  | none => [true]
  | some φ =>
      if validatesTautology φ table then false :: φCode else [true]

theorem validatesTautologyResult_of_valid {φCode : List Bool} {φ : PropFormula}
    {table : List Bool} (hdec : decodeFormula φCode = some φ)
    (hval : validatesTautology φ table) :
    validatesTautologyResult φCode table = false :: φCode := by
  simp [validatesTautologyResult, hdec, hval]

theorem validatesTautologyResult_of_decode_fail {φCode table : List Bool}
    (h : decodeFormula φCode = none) :
    validatesTautologyResult φCode table = [true] := by
  simp [validatesTautologyResult, h]

theorem validatesTautologyResult_of_invalid_table {φCode : List Bool}
    {φ : PropFormula} {table : List Bool} (hdec : decodeFormula φCode = some φ)
    (hval : ¬ validatesTautology φ table) :
    validatesTautologyResult φCode table = [true] := by
  simp [validatesTautologyResult, hdec, hval]

theorem validatesTautologyResult_eq (φCode table : List Bool) :
    validatesTautologyResult φCode table =
      match decodeFormula φCode with
      | none => [true]
      | some φ =>
          if validatesTautology φ table then false :: φCode else [true] := by
  cases h : decodeFormula φCode with
  | none => simp [validatesTautologyResult, h]
  | some φ =>
      by_cases hval : validatesTautology φ table <;>
        simp [validatesTautologyResult, h, hval]

/-- Same case split with the certified index loop predicate (FinTM2 target form). -/
theorem validatesTautologyResult_eq_by_index (φCode table : List Bool) :
    validatesTautologyResult φCode table =
      match decodeFormula φCode with
      | none => [true]
      | some φ =>
          if validatesTautology_by_index φ table then false :: φCode
          else [true] := by
  cases h : decodeFormula φCode with
  | none => simp [validatesTautologyResult, h]
  | some φ =>
      by_cases hval : validatesTautology φ table
      · have hidx := validatesTautology_by_index_of_validatesTautology φ table hval
        simp [validatesTautologyResult, h, hval, hidx]
      · have hidx : ¬ validatesTautology_by_index φ table := by
          intro hby
          exact hval (validatesTautology_of_by_index φ table hby)
        simp [validatesTautologyResult, h, hval, hidx]

/-- Length gate fail after a successful decode rejects with `[true]`. -/
theorem validatesTautologyResult_of_lengthGateFail {φCode : List Bool}
    {φ : PropFormula} {table : List Bool}
    (hdec : decodeFormula φCode = some φ)
    (hlen : lengthGateOk φ table = false) :
    validatesTautologyResult φCode table = [true] := by
  have hval := not_validatesTautology_of_lengthGateFail φ table hlen
  simp [validatesTautologyResult, hdec, hval]

theorem length_validatesTautologyResult_le (φCode table : List Bool) :
    (validatesTautologyResult φCode table).length ≤ φCode.length + 1 := by
  simp only [validatesTautologyResult]
  cases h : decodeFormula φCode with
  | none => simp
  | some φ =>
      by_cases hval : validatesTautology φ table
      · simp [hval]
      · simp [hval]

/-- On the TT map success branch, output is `φCode` iff validation accepts. -/
theorem truthTableProofSystem_output_φCode {π φCode table : List Bool} {φ : PropFormula}
    (hpair : decodePair π = some (φCode, table))
    (hφ : decodeFormula φCode = some φ) (hval : validatesTautology φ table) :
    truthTableProofSystem π = φCode := by
  unfold truthTableProofSystem
  simp [hpair, hφ, hval]

/-! ## Cluster C pair tape: `validatesTautologyResult` on `encodePair` inputs

After Cluster A decodePair, the TT map holds `(φCode, table)` on the tape.
The FinTM2 target is the composed map below (Cluster C machine input format). -/

/-- Pair input for validation: `encodePair (φCode, table)`. -/
def validatesTautologyPairInput (φCode table : List Bool) : List Bool :=
  encodePair (φCode, table)

/-- Validation after pair decode; rejects malformed pair encodings with `[true]`. -/
def validatesTautologyResult_on_pair (π : List Bool) : List Bool :=
  match decodePair π with
  | none => [true]
  | some (φCode, table) => validatesTautologyResult φCode table

theorem validatesTautologyResult_on_pair_eq (π : List Bool) :
    validatesTautologyResult_on_pair π =
      match decodePair π with
      | none => [true]
      | some (φCode, table) => validatesTautologyResult φCode table := by
  rfl

theorem validatesTautologyResult_on_pair_of_some {π φCode table : List Bool}
    (h : decodePair π = some (φCode, table)) :
    validatesTautologyResult_on_pair π =
      validatesTautologyResult φCode table := by
  simp [validatesTautologyResult_on_pair, h]

theorem validatesTautologyResult_on_pair_encodePair (φCode table : List Bool) :
    validatesTautologyResult_on_pair (encodePair (φCode, table)) =
      validatesTautologyResult φCode table := by
  simp [validatesTautologyResult_on_pair, decodePair_encodePair]

theorem length_validatesTautologyResult_on_pair_le (π : List Bool) :
    (validatesTautologyResult_on_pair π).length ≤ π.length + 1 := by
  simp only [validatesTautologyResult_on_pair]
  cases h : decodePair π with
  | none => simp
  | some pw =>
      rcases pw with ⟨φCode, table⟩
      have hout := length_validatesTautologyResult_le φCode table
      have hfst := length_fst_le_of_decodePair h
      exact Nat.le_trans hout (Nat.add_le_add_right hfst 1)

/-- Malformed pair encoding rejects immediately with `[true]`. -/
theorem validatesTautologyResult_on_pair_of_none {π : List Bool}
    (h : decodePair π = none) :
    validatesTautologyResult_on_pair π = [true] := by
  simp [validatesTautologyResult_on_pair, h]

/-- Canonical table validates iff the formula is a tautology. -/
theorem validatesTautology_truthTableOf_iff (φ : PropFormula) :
    validatesTautology φ (truthTableOf φ) ↔ φ.Tautology :=
  ⟨tautology_of_validatesTautology φ (truthTableOf φ),
    validatesTautology_truthTableOf_of_tautology φ⟩

/-- On `encodeFormula φ` with its own truth table, validation is exactly the
tautology test, and accept copies `false :: encodeFormula φ`. -/
theorem validatesTautologyResult_truthTableOf (φ : PropFormula) :
    validatesTautologyResult (encodeFormula φ) (truthTableOf φ) =
      if validatesTautology φ (truthTableOf φ) then false :: encodeFormula φ
      else [true] := by
  simp [validatesTautologyResult, decodeFormula_encodeFormula]

theorem validatesTautologyResult_truthTableOf_of_tautology (φ : PropFormula)
    (h : φ.Tautology) :
    validatesTautologyResult (encodeFormula φ) (truthTableOf φ) =
      false :: encodeFormula φ := by
  have hval := validatesTautology_truthTableOf_of_tautology φ h
  simpa [validatesTautologyResult_truthTableOf, hval]

theorem validatesTautologyResult_on_pair_truthTableOf_of_tautology (φ : PropFormula)
    (h : φ.Tautology) :
    validatesTautologyResult_on_pair
        (encodePair (encodeFormula φ, truthTableOf φ)) =
      false :: encodeFormula φ := by
  simp [validatesTautologyResult_on_pair_encodePair,
    validatesTautologyResult_truthTableOf_of_tautology φ h]

/-- Reject branch of Cluster C: constant `[true]` is already poly time. -/
theorem validatesTautologyResult_reject_computableInPolyTime :
    Nonempty (TM2ComputableInPolyTime idBitEnc idBitEnc
      (fun _ : List Bool => ([true] : List Bool))) :=
  ⟨constTrueListComputableInPolyTime⟩

/-- Accept slice of Cluster C: on tautologies with the canonical table, the map
reduces to `false :: encodeFormula φ`, realized by `prefixFalseCopyComputer`. -/
noncomputable def validatesTautologyResult_tautologySliceComputableInPolyTime :
    TM2ComputableInPolyTime encodeFormula idBitEnc
      (fun φ => false :: encodeFormula φ) where
  tm := prefixFalseCopyComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := prefixFalseCopyTime
  outputsFun φ := by
    change TM2OutputsInTime prefixFalseCopyComputer
      (List.map id (encodeFormula φ))
      (some (List.map id (idBitEnc (false :: encodeFormula φ))))
      (prefixFalseCopyTime.eval (encodeFormula φ).length)
    simp only [idBitEnc, List.map_id, id_eq, prefixFalseCopyTime_eval]
    exact prefixFalseCopy_evals (encodeFormula φ)

theorem validatesTautologyResult_tautologySlice_computableInPolyTime :
    Nonempty (TM2ComputableInPolyTime encodeFormula idBitEnc
      (fun φ => false :: encodeFormula φ)) :=
  ⟨validatesTautologyResult_tautologySliceComputableInPolyTime⟩

/-! ## Cluster C cost model for branching FinTM2 glue

The eventual machine branches on `decodePair`, then either runs the certified
reject slice (`constTrueList`, cost `n + 2`) or the inner validation path. -/

/-- Step budget for `validatesTautologyResult_on_pair` at input `π`. -/
def validatesTautologyResult_on_pairCost (π : List Bool) : ℕ :=
  match decodePair π with
  | none => π.length + 2
  | some (φCode, table) =>
      decodePairCost π + validatesTautologyCost φCode table

theorem validatesTautologyResult_on_pairCost_le (π : List Bool) :
    validatesTautologyResult_on_pairCost π ≤
      (π.length + 1) * (π.length + 2) := by
  unfold validatesTautologyResult_on_pairCost
  cases h : decodePair π with
  | none =>
      have h1 : 1 ≤ π.length + 1 := by omega
      calc
        π.length + 2 = 1 * (π.length + 2) := by ring
        _ ≤ (π.length + 1) * (π.length + 2) := Nat.mul_le_mul_right _ h1
  | some pw =>
      rcases pw with ⟨φCode, table⟩
      have hpair := decodePairCost_le π
      have hval := validatesTautologyCost_le φCode table
      have hfst := length_fst_le_of_decodePair h
      have htable := length_ge_snd_of_decodePair h
      have hinner : validatesTautologyCost φCode table ≤ (π.length + 1) * (π.length + 1) :=
        calc
          validatesTautologyCost φCode table ≤
              (φCode.length + 1) * (table.length + 1) := hval
          _ ≤ (π.length + 1) * (π.length + 1) := by
            gcongr <;> omega
      calc
        decodePairCost π + validatesTautologyCost φCode table ≤
            π.length + 1 + (π.length + 1) * (π.length + 1) := by omega
        _ ≤ (π.length + 1) * (π.length + 2) := by
          have heq : π.length + 1 + (π.length + 1) * (π.length + 1) =
              (π.length + 1) * (π.length + 2) := by ring
          rw [heq]

noncomputable def validatesTautologyResult_on_pairTime : Polynomial ℕ :=
  (Polynomial.X + 1) * (Polynomial.X + 2)

theorem validatesTautologyResult_on_pairTime_eval (n : ℕ) :
    validatesTautologyResult_on_pairTime.eval n = (n + 1) * (n + 2) := by
  simp [validatesTautologyResult_on_pairTime, Polynomial.eval_mul,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]

theorem validatesTautologyResult_on_pairCost_le_time_eval (π : List Bool) :
    validatesTautologyResult_on_pairCost π ≤
      validatesTautologyResult_on_pairTime.eval π.length := by
  have h := validatesTautologyResult_on_pairCost_le π
  simp [validatesTautologyResult_on_pairTime_eval]
  exact h

/-- Pair decode failure agrees with Cluster A reject tape `[true]`. -/
theorem validatesTautologyResult_on_pair_eq_decodePairResult_on_fail {π : List Bool}
    (h : decodePair π = none) :
    validatesTautologyResult_on_pair π = decodePairResult π := by
  rw [validatesTautologyResult_on_pair_of_none h, decodePairResult_of_none h]

/-- Successful pair decode reduces to inner validation on the components. -/
theorem validatesTautologyResult_on_pair_eq_inner {π φCode table : List Bool}
    (h : decodePair π = some (φCode, table)) :
    validatesTautologyResult_on_pair π =
      validatesTautologyResult φCode table := by
  simp [validatesTautologyResult_on_pair, h]

namespace ProofSystemFrontier

/-- Full FinTM2 for `validatesTautologyResult_on_pair`: decode pair, decode
formula, length gate `table.length = 2^(maxVar+1)`, then index loop under
`|table|` fuel, then branch to the reject or accept slices above.

Certified: length gate Bool, reject lemmas, `pow2BitsLE` plus writePow2Bits
FinTM2, `natBitsLE`/`lengthBitsEqPow2` compare, `countLengthBits` polyTime,
`bitsEqual`/`bitsEqualZip` lengthGate rewrites, `bitsEqualComputer` Stmt,
leftover drain, and EvalsToInTime to haltList on equal and reject paths.
Remaining: encodePair load glue, full unequal zipper Evals, then per index
eval loop. -/
theorem validatesTautologyResult_computableInPolyTime :
    Nonempty (TM2ComputableInPolyTime idBitEnc idBitEnc
      validatesTautologyResult_on_pair) := by
  sorry

end ProofSystemFrontier

end SATurday.Bridge
