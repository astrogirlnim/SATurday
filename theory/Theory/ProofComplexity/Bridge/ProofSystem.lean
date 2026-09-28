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

/-- Encoded interpretive eval agrees with `evalOn` on `encodeFormula` images. -/
theorem evalEncoded_encodeFormula_evalOn (φ : PropFormula) (σ : List Bool) :
    evalEncoded σ (encodeFormula φ) = some (φ.evalOn σ) := by
  simpa [evalOn_eq_eval_getD] using evalEncoded_encodeFormula φ σ

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

theorem pow2BitsLE_ne_nil (n : ℕ) : pow2BitsLE n ≠ [] := by
  simp [pow2BitsLE]

theorem pow2BitsLE_zero : pow2BitsLE 0 = [true] := by
  simp [pow2BitsLE]

theorem pow2BitsLE_succ (n : ℕ) :
    pow2BitsLE (n + 1) = false :: pow2BitsLE n := by
  simp [pow2BitsLE, List.replicate_succ]

theorem replicate_false_concat (n : ℕ) (acc : List Bool) :
    List.replicate n false ++ false :: acc =
      List.replicate (n + 1) false ++ acc := by
  rw [List.replicate_succ', List.append_assoc]
  rfl

theorem pow2BitsLE_injective {n m : ℕ} (h : pow2BitsLE n = pow2BitsLE m) :
    n = m := by
  have : n + 1 = m + 1 := by
    simpa [length_pow2BitsLE] using congrArg List.length h
  omega

/-- Target bit string for the length gate after a successful pow2 shape check:
`pow2BitsLE (maxVar + 1)`. -/
def maxVarSuccBits (φ : PropFormula) : List Bool :=
  pow2BitsLE (φ.maxVar + 1)

theorem maxVarSuccBits_eq (φ : PropFormula) :
    maxVarSuccBits φ = pow2BitsLE (φ.maxVar + 1) := rfl

/-- Decode then read `maxVar`; `none` means the tape is not a formula. -/
def maxVarOfCode (φCode : List Bool) : Option ℕ :=
  match decodeFormula φCode with
  | some φ => some φ.maxVar
  | none => none

theorem maxVarOfCode_some {φCode : List Bool} {φ : PropFormula}
    (h : decodeFormula φCode = some φ) :
    maxVarOfCode φCode = some φ.maxVar := by
  simp [maxVarOfCode, h]

theorem maxVarOfCode_none {φCode : List Bool}
    (h : decodeFormula φCode = none) :
    maxVarOfCode φCode = none := by
  simp [maxVarOfCode, h]

theorem maxVarOfCode_encodeFormula (φ : PropFormula) :
    maxVarOfCode (encodeFormula φ) = some φ.maxVar := by
  simp [maxVarOfCode, decodeFormula_encodeFormula]

/-- Emit `maxVarSuccBits` from a code tape, or `none` on decode fail. -/
def maxVarSuccBitsOfCode (φCode : List Bool) : Option (List Bool) :=
  match decodeFormula φCode with
  | some φ => some (maxVarSuccBits φ)
  | none => none

theorem maxVarSuccBitsOfCode_some {φCode : List Bool} {φ : PropFormula}
    (h : decodeFormula φCode = some φ) :
    maxVarSuccBitsOfCode φCode = some (maxVarSuccBits φ) := by
  simp [maxVarSuccBitsOfCode, h]

theorem maxVarSuccBitsOfCode_none {φCode : List Bool}
    (h : decodeFormula φCode = none) :
    maxVarSuccBitsOfCode φCode = none := by
  simp [maxVarSuccBitsOfCode, h]

theorem maxVarSuccBitsOfCode_encodeFormula (φ : PropFormula) :
    maxVarSuccBitsOfCode (encodeFormula φ) = some (maxVarSuccBits φ) := by
  simp [maxVarSuccBitsOfCode, decodeFormula_encodeFormula]

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

/-- Iterate `bitsInc` `t` times. Counting `|table|` symbols from `[]` yields
`natBitsLE t`. -/
def bitsIncIter : ℕ → List Bool → List Bool
  | 0, acc => acc
  | t + 1, acc => bitsIncIter t (bitsInc acc)

theorem bitsIncIter_zero (acc : List Bool) : bitsIncIter 0 acc = acc := rfl

theorem bitsIncIter_succ (t : ℕ) (acc : List Bool) :
    bitsIncIter (t + 1) acc = bitsIncIter t (bitsInc acc) := rfl

theorem bitsIncIter_natBitsLE (t w : ℕ) :
    bitsIncIter t (natBitsLE w) = natBitsLE (w + t) := by
  induction t generalizing w with
  | zero => simp [bitsIncIter]
  | succ t ih =>
      rw [bitsIncIter_succ, bitsInc_natBitsLE, ih]
      ac_rfl

theorem bitsIncIter_nil (t : ℕ) : bitsIncIter t [] = natBitsLE t := by
  have h1 : bitsIncIter 0 [] = natBitsLE 0 := by simp [bitsIncIter, natBitsLE_zero]
  have h2 : bitsInc [] = natBitsLE 1 := by simp [bitsInc, natBitsLE_one]
  cases t with
  | zero => exact h1
  | succ t =>
      rw [bitsIncIter_succ, h2, bitsIncIter_natBitsLE, Nat.one_add]

theorem natBitsLE_eq_pow2BitsLE_iff (t n : ℕ) :
    natBitsLE t = pow2BitsLE n ↔ t = 2 ^ n := by
  constructor
  · intro h
    have := congrArg bitsLEValue h
    simpa [bitsLEValue_natBitsLE, bitsLEValue_pow2BitsLE] using this
  · intro h
    simp [h, natBitsLE_pow2]

theorem bitsIncIter_nil_eq_pow2BitsLE_iff (t n : ℕ) :
    bitsIncIter t [] = pow2BitsLE n ↔ t = 2 ^ n := by
  rw [bitsIncIter_nil, natBitsLE_eq_pow2BitsLE_iff]

/-! ## Cluster C2 index assignment = padded `natBitsLE`

Index loop needs `assignmentAt n i` as a FinTM2 tape. When `i < 2^n`, that
assignment is exactly the little endian bits of `i` padded with `false` to
length `n`. The pad FinTM2 below realizes this from `encodePair (encodeNat n, bs)`. -/

/-- Pad little endian bits to length `n` (truncate if longer). -/
def padBitsLE (n : ℕ) (bs : List Bool) : List Bool :=
  (bs ++ List.replicate n false).take n

theorem length_padBitsLE (n : ℕ) (bs : List Bool) :
    (padBitsLE n bs).length = n := by
  simp [padBitsLE]

theorem padBitsLE_of_length_le (n : ℕ) (bs : List Bool) (hle : bs.length ≤ n) :
    padBitsLE n bs = bs ++ List.replicate (n - bs.length) false := by
  simp only [padBitsLE]
  rw [List.take_append, List.take_of_length_le hle, List.take_replicate,
    min_eq_left (Nat.sub_le _ _)]

/-- Canonical bit length of `i` is at most `n` whenever `i < 2^n`. -/
theorem length_natBitsLE_of_lt_pow : ∀ {i n : ℕ}, i < 2 ^ n →
    (natBitsLE i).length ≤ n := by
  intro i n h
  induction n generalizing i with
  | zero =>
      have : i = 0 := by simpa using h
      subst this
      simp [natBitsLE]
  | succ n ih =>
      by_cases hi : i = 0
      · subst hi
        simp [natBitsLE]
      · have hdiv : i / 2 < 2 ^ n := by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ, Nat.mul_comm]
          have : i < 2 * 2 ^ n := by simpa [hpow] using h
          omega
        have hlen := ih hdiv
        by_cases he : i % 2 = 0
        · have hk0 : i / 2 ≠ 0 := by
            intro hz
            have : i = 0 := by omega
            exact hi this
          have hbits : natBitsLE i = false :: natBitsLE (i / 2) := by
            calc
              natBitsLE i = natBitsLE (2 * (i / 2)) := by congr 1; omega
              _ = false :: natBitsLE (i / 2) := natBitsLE_mul_two hk0
          rw [hbits, List.length_cons]
          exact Nat.succ_le_succ hlen
        · have hbits : natBitsLE i = true :: natBitsLE (i / 2) := by
            calc
              natBitsLE i = natBitsLE (2 * (i / 2) + 1) := by congr 1; omega
              _ = true :: natBitsLE (i / 2) := natBitsLE_mul_two_add_one _
          rw [hbits, List.length_cons]
          exact Nat.succ_le_succ hlen

/-- Index assignment is padded little endian bits of the index. -/
theorem assignmentAt_eq_padBitsLE : ∀ {n i : ℕ}, i < 2 ^ n →
    assignmentAt n i = padBitsLE n (natBitsLE i) := by
  intro n i hi
  induction n generalizing i with
  | zero =>
      have : i = 0 := by simpa using hi
      subst this
      simp [assignmentAt, padBitsLE, natBitsLE]
  | succ n ih =>
      by_cases hi0 : i = 0
      · subst hi0
        have ih0 := ih (Nat.pow_pos (by decide : 0 < (2 : ℕ)))
        have happ : assignmentAt (n + 1) 0 = false :: assignmentAt n 0 := by
          simp [assignmentAt]
        have hpad : padBitsLE (n + 1) (natBitsLE 0) =
            false :: padBitsLE n (natBitsLE 0) := by
          simp [padBitsLE, natBitsLE, List.replicate_succ]
        rw [happ, ih0, hpad]
      · have hdiv : i / 2 < 2 ^ n := by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ, Nat.mul_comm]
          have : i < 2 * 2 ^ n := by simpa [hpow] using hi
          omega
        have ih' := ih hdiv
        have hlen2 : (natBitsLE (i / 2)).length ≤ n :=
          length_natBitsLE_of_lt_pow hdiv
        by_cases he : i % 2 = 0
        · have hk0 : i / 2 ≠ 0 := by
            intro hz
            have : i = 0 := by omega
            exact hi0 this
          have hbits : natBitsLE i = false :: natBitsLE (i / 2) := by
            calc
              natBitsLE i = natBitsLE (2 * (i / 2)) := by congr 1; omega
              _ = false :: natBitsLE (i / 2) := natBitsLE_mul_two hk0
          have happ : assignmentAt (n + 1) i =
              false :: assignmentAt n (i / 2) := by
            calc
              assignmentAt (n + 1) i
                  = assignmentAt (n + 1) (2 * (i / 2)) := by congr 2; omega
              _ = false :: assignmentAt n (i / 2) :=
                assignmentAt_succ_mul_two n (i / 2)
          have hpad : padBitsLE (n + 1) (false :: natBitsLE (i / 2)) =
              false :: padBitsLE n (natBitsLE (i / 2)) := by
            have hlen_cons : (false :: natBitsLE (i / 2)).length ≤ n + 1 := by
              simpa [List.length_cons] using Nat.succ_le_succ hlen2
            rw [padBitsLE_of_length_le _ _ hlen_cons,
              padBitsLE_of_length_le _ _ hlen2]
            -- `n + 1 - (|bs|+1) = n - |bs|`
            simp [List.length_cons, Nat.succ_sub_succ_eq_sub]
          rw [happ, ih', hbits, hpad]
        · have hbits : natBitsLE i = true :: natBitsLE (i / 2) := by
            calc
              natBitsLE i = natBitsLE (2 * (i / 2) + 1) := by congr 1; omega
              _ = true :: natBitsLE (i / 2) := natBitsLE_mul_two_add_one _
          have happ : assignmentAt (n + 1) i =
              true :: assignmentAt n (i / 2) := by
            calc
              assignmentAt (n + 1) i
                  = assignmentAt (n + 1) (2 * (i / 2) + 1) := by congr 2; omega
              _ = true :: assignmentAt n (i / 2) :=
                assignmentAt_succ_mul_two_add_one n (i / 2)
          have hpad : padBitsLE (n + 1) (true :: natBitsLE (i / 2)) =
              true :: padBitsLE n (natBitsLE (i / 2)) := by
            have hlen_cons : (true :: natBitsLE (i / 2)).length ≤ n + 1 := by
              simpa [List.length_cons] using Nat.succ_le_succ hlen2
            rw [padBitsLE_of_length_le _ _ hlen_cons,
              padBitsLE_of_length_le _ _ hlen2]
            simp [List.length_cons, Nat.succ_sub_succ_eq_sub]
          rw [happ, ih', hbits, hpad]

/-- Semantic target of the pad FinTM2 on well formed pair tapes. -/
def padBitsFromPair (p : List Bool × List Bool) : List Bool :=
  match decodeNat p.1 with
  | some (n, []) => padBitsLE n p.2
  | _ => []

theorem padBitsFromPair_encodeNat (n : ℕ) (bs : List Bool) :
    padBitsFromPair (encodeNat n, bs) = padBitsLE n bs := by
  simp [padBitsFromPair, decodeNat_encodeNat]

/-- When `i < 2^n`, padded bits of `i` recover `assignmentAt`. -/
theorem assignmentAt_eq_padBitsFromPair (n i : ℕ) (hi : i < 2 ^ n) :
    assignmentAt n i = padBitsFromPair (encodeNat n, natBitsLE i) := by
  rw [padBitsFromPair_encodeNat, assignmentAt_eq_padBitsLE hi]

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
zipper FinTM2 that loads `encodePair` then compares. -/

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

theorem bitsEqual_pow2BitsLE_iff (n m : ℕ) :
    bitsEqual (pow2BitsLE n) (pow2BitsLE m) = true ↔ n = m := by
  rw [bitsEqual_iff]
  constructor
  · exact pow2BitsLE_injective
  · intro h; simp [h]

/-- Parked width `pow2BitsLE n` matches `maxVarSuccBits φ` iff `n = maxVar+1`. -/
theorem bitsEqual_pow2BitsLE_maxVarSuccBits (n : ℕ) (φ : PropFormula) :
    bitsEqual (pow2BitsLE n) (maxVarSuccBits φ) = true ↔
      n = φ.maxVar + 1 := by
  simpa [maxVarSuccBits] using bitsEqual_pow2BitsLE_iff n (φ.maxVar + 1)

/-- After a successful decode, the length gate is the parked-width compare. -/
theorem lengthGateOk_iff_bitsEqual_parked (φ : PropFormula) (table : List Bool)
    (n : ℕ) (hlen : table.length = 2 ^ n) :
    lengthGateOk φ table = true ↔
      bitsEqual (pow2BitsLE n) (maxVarSuccBits φ) = true := by
  rw [lengthGateOk_iff, bitsEqual_pow2BitsLE_maxVarSuccBits]
  constructor
  · intro hgate
    have : 2 ^ n = 2 ^ (φ.maxVar + 1) := by simpa [hlen] using hgate
    exact Nat.pow_right_injective (by decide : (1 : ℕ) < 2) this
  · intro hn
    simpa [hlen, hn]

theorem lengthGateOk_iff_bitsEqual_maxVarSuccBits (φ : PropFormula)
    (table : List Bool) :
    lengthGateOk φ table = true ↔
      bitsEqual (lengthBitsLE table) (maxVarSuccBits φ) = true := by
  simp [lengthGateOk_eq_bitsEqual, maxVarSuccBits, bitsEqual_iff]

/-! ## Cluster C2 FinTM2: encodePair load then zip compare

`inp` holds `encodePair (xs, ys)`. Load parses the self delimiting prefix into
`left = xs.reverse` and `right = ys.reverse` (reversals cancel for equality),
then the zipper compare writes `[true]`/`[false]` on `out`. -/

inductive BitsEqStack where
  | inp | left | right | out
  deriving DecidableEq, Repr

instance : Fintype BitsEqStack where
  elems := {.inp, .left, .right, .out}
  complete s := by cases s <;> simp

/-- `parse`/`expectBit` unpack the first component; `loadRight` copies the
second; then `loop`..`drainRight` compare as before. -/
inductive BitsEqLabel where
  | parse | expectBit | loadRight
  | loop | expectTrue | expectFalse | checkRight | reject | drainRight
  deriving DecidableEq, Repr

instance : Fintype BitsEqLabel where
  elems := {.parse, .expectBit, .loadRight, .loop, .expectTrue, .expectFalse,
    .checkRight, .reject, .drainRight}
  complete s := by cases s <;> simp

/-- FinTM2: load `encodePair` from `inp` into compare stacks, write equality bit.
Reject paths drain leftover compare stacks before halt so `haltList` is reachable. -/
def bitsEqualComputer : FinTM2 where
  K := BitsEqStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := BitsEqLabel
  main := .parse
  σ := Option Bool
  initialState := none
  m
    | .parse =>
        pop BitsEqStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => BitsEqLabel.reject)
            (branch (fun s => decide (s = some false))
              (load (fun _ => none) <| goto fun _ => BitsEqLabel.loadRight)
              (load (fun _ => none) <| goto fun _ => BitsEqLabel.expectBit))
    | .expectBit =>
        pop BitsEqStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => BitsEqLabel.reject)
            (push BitsEqStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => BitsEqLabel.parse)
    | .loadRight =>
        pop BitsEqStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => BitsEqLabel.loop)
            (push BitsEqStack.right (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => BitsEqLabel.loadRight)
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

/-- Stack map; compare phase lemmas keep `inp = []`. -/
def bitsEqStk (inp left right out : List Bool) : BitsEqStack → List Bool
  | .inp => inp
  | .left => left
  | .right => right
  | .out => out

/-- Compare phase config (`inp` empty after successful load). -/
def bitsEqCfg (l : Option BitsEqLabel) (v : Option Bool)
    (left right out : List Bool) : bitsEqualComputer.Cfg :=
  ⟨l, v, bitsEqStk [] left right out⟩

/-- Full config including residual `inp` (load phase). -/
def bitsEqCfgInp (l : Option BitsEqLabel) (v : Option Bool)
    (inp left right out : List Bool) : bitsEqualComputer.Cfg :=
  ⟨l, v, bitsEqStk inp left right out⟩

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

/-! ### encodePair load steps (parse first component, copy second) -/

theorem bitsEq_step_parse_false (rest left right out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfgInp (some .parse) none (false :: rest) left right out) =
      some (bitsEqCfgInp (some .loadRight) none rest left right out) := by
  simp [bitsEqualComputer, bitsEqCfgInp, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.loadRight, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_parse_true (b : Bool) (rest left right out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfgInp (some .parse) none (true :: b :: rest) left right out) =
      some (bitsEqCfgInp (some .expectBit) none (b :: rest) left right out) := by
  simp [bitsEqualComputer, bitsEqCfgInp, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.expectBit, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_parse_nil (left right out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfgInp (some .parse) none [] left right out) =
      some (bitsEqCfgInp (some .reject) none [] left right out) := by
  simp [bitsEqualComputer, bitsEqCfgInp, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.reject, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_expectBit (b : Bool) (rest left right out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfgInp (some .expectBit) none (b :: rest) left right out) =
      some (bitsEqCfgInp (some .parse) none rest (b :: left) right out) := by
  simp [bitsEqualComputer, bitsEqCfgInp, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.parse, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_expectBit_nil (left right out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfgInp (some .expectBit) none [] left right out) =
      some (bitsEqCfgInp (some .reject) none [] left right out) := by
  simp [bitsEqualComputer, bitsEqCfgInp, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.reject, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_loadRight_cons (b : Bool) (rest left right out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfgInp (some .loadRight) none (b :: rest) left right out) =
      some (bitsEqCfgInp (some .loadRight) none rest left (b :: right) out) := by
  simp [bitsEqualComputer, bitsEqCfgInp, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.loadRight, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEq_step_loadRight_nil (left right out : List Bool) :
    TM2.step bitsEqualComputer.m
      (bitsEqCfgInp (some .loadRight) none [] left right out) =
      some (bitsEqCfg (some .loop) none left right out) := by
  simp [bitsEqualComputer, bitsEqCfgInp, bitsEqCfg, bitsEqStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some BitsEqLabel.loop, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, bitsEqStk]

theorem bitsEqual_initList (s : List Bool) :
    initList bitsEqualComputer s =
      bitsEqCfgInp (some .parse) none s [] [] [] := by
  refine congrArg (fun stk =>
      (⟨some BitsEqLabel.parse, none, stk⟩ : bitsEqualComputer.Cfg)) ?_
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

/-! ### Cluster C2: encodePair load EvalsToInTime into compare loop -/

def bitsEq_evals_parse_false (rest left right out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfgInp (some .parse) none (false :: rest) left right out)
      (some (bitsEqCfgInp (some .loadRight) none rest left right out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfgInp (some .parse) none (false :: rest) left right out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfgInp (some .loadRight) none rest left right out)
    simp only [FinTM2.step]
    exact bitsEq_step_parse_false rest left right out

def bitsEq_evals_one_bit (b : Bool) (rest left right out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfgInp (some .parse) none (true :: b :: rest) left right out)
      (some (bitsEqCfgInp (some .parse) none rest (b :: left) right out)) 2 where
  steps := 2
  steps_le_m := by decide
  evals_in_steps := by
    change ((some (bitsEqCfgInp (some .parse) none (true :: b :: rest) left right out)).bind
        bitsEqualComputer.step).bind bitsEqualComputer.step =
      some (bitsEqCfgInp (some .parse) none rest (b :: left) right out)
    simp only [FinTM2.step]
    change ((TM2.step bitsEqualComputer.m
        (bitsEqCfgInp (some .parse) none (true :: b :: rest) left right out)).bind
        (TM2.step bitsEqualComputer.m)) =
      some (bitsEqCfgInp (some .parse) none rest (b :: left) right out)
    rw [bitsEq_step_parse_true]
    exact bitsEq_step_expectBit b rest left right out

noncomputable def bitsEq_evals_parse_first (x rest left right out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfgInp (some .parse) none
        ((x.flatMap fun b => [true, b]) ++ rest) left right out)
      (some (bitsEqCfgInp (some .parse) none rest (x.reverse ++ left) right out))
      (2 * x.length) := by
  induction x generalizing left with
  | nil =>
      simpa using EvalsToInTime.refl bitsEqualComputer.step
        (bitsEqCfgInp (some .parse) none rest left right out)
  | cons b xs ih =>
      have h1 :=
        bitsEq_evals_one_bit b ((xs.flatMap fun b => [true, b]) ++ rest) left right out
      have h2 := ih (b :: left)
      have h :=
        EvalsToInTime.trans bitsEqualComputer.step 2 (2 * xs.length)
          (bitsEqCfgInp (some .parse) none
            ((b :: xs).flatMap (fun b => [true, b]) ++ rest) left right out)
          (bitsEqCfgInp (some .parse) none
            ((xs.flatMap fun b => [true, b]) ++ rest) (b :: left) right out)
          (some (bitsEqCfgInp (some .parse) none rest
            (xs.reverse ++ (b :: left)) right out))
          (by simpa [List.flatMap] using h1) h2
      simpa [List.flatMap, List.reverse_cons, List.append_assoc, Nat.mul_succ,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, two_mul] using h

def bitsEq_evals_loadRight_cons (b : Bool) (rest left right out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfgInp (some .loadRight) none (b :: rest) left right out)
      (some (bitsEqCfgInp (some .loadRight) none rest left (b :: right) out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfgInp (some .loadRight) none (b :: rest) left right out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfgInp (some .loadRight) none rest left (b :: right) out)
    simp only [FinTM2.step]
    exact bitsEq_step_loadRight_cons b rest left right out

def bitsEq_evals_loadRight_nil (left right out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfgInp (some .loadRight) none [] left right out)
      (some (bitsEqCfg (some .loop) none left right out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfgInp (some .loadRight) none [] left right out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfg (some .loop) none left right out)
    simp only [FinTM2.step]
    exact bitsEq_step_loadRight_nil left right out

noncomputable def bitsEq_evals_loadRight (ys left right out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfgInp (some .loadRight) none ys left right out)
      (some (bitsEqCfg (some .loop) none left (ys.reverse ++ right) out))
      (ys.length + 1) := by
  induction ys generalizing right with
  | nil =>
      simpa using bitsEq_evals_loadRight_nil left right out
  | cons y ys ih =>
      have h1 := bitsEq_evals_loadRight_cons y ys left right out
      have h2 := ih (y :: right)
      have h :=
        EvalsToInTime.trans bitsEqualComputer.step 1 (ys.length + 1) _ _ _ h1 h2
      refine ⟨⟨h.steps, ?_⟩, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using h.evals_in_steps
      · refine le_trans h.steps_le_m ?_
        simp [List.length_cons]

/-- Load `encodePair (xs, ys)` from `inp` into compare stacks (reversed). -/
noncomputable def bitsEq_evals_load_encodePair (xs ys : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfgInp (some .parse) none (encodePair (xs, ys)) [] [] [])
      (some (bitsEqCfg (some .loop) none xs.reverse ys.reverse []))
      (2 * xs.length + ys.length + 2) := by
  have hparse :=
    bitsEq_evals_parse_first xs (false :: ys) [] [] []
  have htoLoad :=
    bitsEq_evals_parse_false ys xs.reverse [] []
  have hload :=
    bitsEq_evals_loadRight ys xs.reverse [] []
  have h1 : EvalsToInTime bitsEqualComputer.step
      (bitsEqCfgInp (some .parse) none (encodePair (xs, ys)) [] [] [])
      (some (bitsEqCfgInp (some .parse) none (false :: ys) xs.reverse [] []))
      (2 * xs.length) := by
    simpa [encodePair, List.append_assoc] using hparse
  have h12 :=
    EvalsToInTime.trans bitsEqualComputer.step (2 * xs.length) 1 _ _ _ h1 htoLoad
  have h12' : EvalsToInTime bitsEqualComputer.step
      (bitsEqCfgInp (some .parse) none (encodePair (xs, ys)) [] [] [])
      (some (bitsEqCfgInp (some .loadRight) none ys xs.reverse [] []))
      (2 * xs.length + 1) := by
    simpa [Nat.add_comm] using h12
  have h :=
    EvalsToInTime.trans bitsEqualComputer.step (2 * xs.length + 1) (ys.length + 1)
      _ _ _ h12' hload
  refine ⟨⟨h.steps, ?_⟩, ?_⟩
  · simpa [List.append_nil] using h.evals_in_steps
  · refine le_trans h.steps_le_m ?_
    omega

theorem bitsEqual_reverse (xs ys : List Bool) :
    bitsEqual xs.reverse ys.reverse = bitsEqual xs ys := by
  simp [bitsEqual, List.reverse_inj]

/-- Equal pair from `initList (encodePair (xs, xs))` to haltList `[true]`. -/
noncomputable def bitsEq_evals_encodePair_equal (xs : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (initList bitsEqualComputer (encodePair (xs, xs)))
      (some (haltList bitsEqualComputer [true]))
      (2 * xs.length + xs.length + 2 + (2 * xs.length + 2)) := by
  have hload := bitsEq_evals_load_encodePair xs xs
  have hcmp0 := bitsEq_evals_equal xs.reverse
  have hcmp : EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .loop) none xs.reverse xs.reverse [])
      (some (haltList bitsEqualComputer [true]))
      (2 * xs.length + 2) := by
    simpa [List.length_reverse] using hcmp0
  have h1 : EvalsToInTime bitsEqualComputer.step
      (initList bitsEqualComputer (encodePair (xs, xs)))
      (some (bitsEqCfg (some .loop) none xs.reverse xs.reverse []))
      (2 * xs.length + xs.length + 2) := by
    simpa [bitsEqual_initList] using hload
  have h :=
    EvalsToInTime.trans bitsEqualComputer.step
      (2 * xs.length + xs.length + 2) (2 * xs.length + 2) _ _ _ h1 hcmp
  refine ⟨⟨h.steps, h.evals_in_steps⟩, ?_⟩
  refine le_trans h.steps_le_m ?_
  omega

/-! ### Cluster C2: unequal zipper Evals and bitsEqualPair polyTime -/

def bitsEq_evals_expectTrue_false (left ys out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .expectTrue) none left (false :: ys) out)
      (some (bitsEqCfg (some .reject) none left ys out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfg (some .expectTrue) none left (false :: ys) out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfg (some .reject) none left ys out)
    simp only [FinTM2.step]
    exact bitsEq_step_expectTrue_false left ys out

def bitsEq_evals_expectTrue_nil (left out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .expectTrue) none left [] out)
      (some (bitsEqCfg (some .reject) none left [] out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfg (some .expectTrue) none left [] out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfg (some .reject) none left [] out)
    simp only [FinTM2.step]
    exact bitsEq_step_expectTrue_nil left out

def bitsEq_evals_expectFalse_true (left ys out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .expectFalse) none left (true :: ys) out)
      (some (bitsEqCfg (some .reject) none left ys out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfg (some .expectFalse) none left (true :: ys) out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfg (some .reject) none left ys out)
    simp only [FinTM2.step]
    exact bitsEq_step_expectFalse_true left ys out

def bitsEq_evals_expectFalse_nil (left out : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .expectFalse) none left [] out)
      (some (bitsEqCfg (some .reject) none left [] out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (bitsEqCfg (some .expectFalse) none left [] out)).bind
        bitsEqualComputer.step =
      some (bitsEqCfg (some .reject) none left [] out)
    simp only [FinTM2.step]
    exact bitsEq_step_expectFalse_nil left out

/-- Right empty, left nonempty: expect mismatch on nil, drain left, halt `[false]`. -/
noncomputable def bitsEq_evals_left_cons_right_nil (x : Bool) (xs : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .loop) none (x :: xs) [] [])
      (some (haltList bitsEqualComputer [false]))
      (xs.length + 4) := by
  cases x with
  | true =>
      have h1 := bitsEq_evals_loop_true xs [] []
      have h2 := bitsEq_evals_expectTrue_nil xs []
      have h12 :=
        EvalsToInTime.trans bitsEqualComputer.step 1 1 _ _ _ h1 h2
      have h3 := bitsEq_evals_reject_to_halt xs []
      have h :=
        EvalsToInTime.trans bitsEqualComputer.step 2 (xs.length + 2) _ _ _ h12 h3
      refine ⟨⟨h.steps, ?_⟩, ?_⟩
      · simpa [bitsEqual_haltList] using h.evals_in_steps
      · refine le_trans h.steps_le_m ?_
        simp [List.length_cons]
  | false =>
      have h1 := bitsEq_evals_loop_false xs [] []
      have h2 := bitsEq_evals_expectFalse_nil xs []
      have h12 :=
        EvalsToInTime.trans bitsEqualComputer.step 1 1 _ _ _ h1 h2
      have h3 := bitsEq_evals_reject_to_halt xs []
      have h :=
        EvalsToInTime.trans bitsEqualComputer.step 2 (xs.length + 2) _ _ _ h12 h3
      refine ⟨⟨h.steps, ?_⟩, ?_⟩
      · simpa [bitsEqual_haltList] using h.evals_in_steps
      · refine le_trans h.steps_le_m ?_
        simp [List.length_cons]

/-- Bit mismatch at heads: two steps to `reject`, then drain to halt `[false]`. -/
noncomputable def bitsEq_evals_mismatch (x y : Bool) (xs ys : List Bool)
    (hne : x ≠ y) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .loop) none (x :: xs) (y :: ys) [])
      (some (haltList bitsEqualComputer [false]))
      (xs.length + ys.length + 4) := by
  cases x with
  | true =>
      cases y with
      | true => exact (hne rfl).elim
      | false =>
          have h1 := bitsEq_evals_loop_true xs (false :: ys) []
          have h2 := bitsEq_evals_expectTrue_false xs ys []
          have h12 :=
            EvalsToInTime.trans bitsEqualComputer.step 1 1 _ _ _ h1 h2
          have h3 := bitsEq_evals_reject_to_halt xs ys
          have h :=
            EvalsToInTime.trans bitsEqualComputer.step 2
              (xs.length + ys.length + 2) _ _ _ h12 h3
          refine ⟨⟨h.steps, ?_⟩, ?_⟩
          · simpa [bitsEqual_haltList] using h.evals_in_steps
          · refine le_trans h.steps_le_m ?_
            simp [List.length_cons]
  | false =>
      cases y with
      | false => exact (hne rfl).elim
      | true =>
          have h1 := bitsEq_evals_loop_false xs (true :: ys) []
          have h2 := bitsEq_evals_expectFalse_true xs ys []
          have h12 :=
            EvalsToInTime.trans bitsEqualComputer.step 1 1 _ _ _ h1 h2
          have h3 := bitsEq_evals_reject_to_halt xs ys
          have h :=
            EvalsToInTime.trans bitsEqualComputer.step 2
              (xs.length + ys.length + 2) _ _ _ h12 h3
          refine ⟨⟨h.steps, ?_⟩, ?_⟩
          · simpa [bitsEqual_haltList] using h.evals_in_steps
          · refine le_trans h.steps_le_m ?_
            simp [List.length_cons]

/-- Unequal stacks from `loop` halt with `[false]` (zipper reject paths). -/
noncomputable def bitsEq_evals_unequal (xs ys : List Bool) (hne : xs ≠ ys) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .loop) none xs ys [])
      (some (haltList bitsEqualComputer [false]))
      (2 * xs.length + ys.length + 4) := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact (hne rfl).elim
      | cons y ys =>
          have h := bitsEq_evals_left_nil_right_cons y ys
          refine ⟨⟨h.steps, h.evals_in_steps⟩, ?_⟩
          refine le_trans h.steps_le_m ?_
          simp [List.length_cons]
  | cons x xs ih =>
      cases ys with
      | nil =>
          have h := bitsEq_evals_left_cons_right_nil x xs
          refine ⟨⟨h.steps, h.evals_in_steps⟩, ?_⟩
          refine le_trans h.steps_le_m ?_
          simp [List.length_cons]; omega
      | cons y ys =>
          by_cases hxy : x = y
          · subst hxy
            have hne' : xs ≠ ys := by
              intro heq; exact hne (congrArg (List.cons x) heq)
            have h1 : EvalsToInTime bitsEqualComputer.step
                (bitsEqCfg (some .loop) none (x :: xs) (x :: ys) [])
                (some (bitsEqCfg (some .loop) none xs ys [])) 2 := by
              cases x with
              | true =>
                  exact EvalsToInTime.trans bitsEqualComputer.step 1 1 _ _ _
                    (bitsEq_evals_loop_true xs (true :: ys) [])
                    (bitsEq_evals_expectTrue_true xs ys [])
              | false =>
                  exact EvalsToInTime.trans bitsEqualComputer.step 1 1 _ _ _
                    (bitsEq_evals_loop_false xs (false :: ys) [])
                    (bitsEq_evals_expectFalse_false xs ys [])
            have h2 := ih ys hne'
            have h :=
              EvalsToInTime.trans bitsEqualComputer.step 2
                (2 * xs.length + ys.length + 4) _ _ _ h1 h2
            refine ⟨⟨h.steps, h.evals_in_steps⟩, ?_⟩
            refine le_trans h.steps_le_m ?_
            simp [List.length_cons]; omega
          · have h := bitsEq_evals_mismatch x y xs ys hxy
            refine ⟨⟨h.steps, h.evals_in_steps⟩, ?_⟩
            refine le_trans h.steps_le_m ?_
            simp [List.length_cons]; omega

/-- Zipper from `loop` to haltList carrying `bitsEqual` (equal or unequal). -/
noncomputable def bitsEq_evals_zip (xs ys : List Bool) :
    EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .loop) none xs ys [])
      (some (haltList bitsEqualComputer [bitsEqual xs ys]))
      (2 * xs.length + ys.length + 4) := by
  by_cases heq : xs = ys
  · subst heq
    have h := bitsEq_evals_equal xs
    refine ⟨⟨h.steps, ?_⟩, ?_⟩
    · simpa [bitsEqual, decide_eq_true (Eq.refl xs)] using h.evals_in_steps
    · refine le_trans h.steps_le_m ?_
      omega
  · have h := bitsEq_evals_unequal xs ys heq
    have hbits : bitsEqual xs ys = false := by
      simp [bitsEqual, decide_eq_false heq]
    refine ⟨⟨h.steps, ?_⟩, h.steps_le_m⟩
    simpa [hbits] using h.evals_in_steps

/-- Unequal pair from `initList (encodePair (xs, ys))` to haltList `[false]`. -/
noncomputable def bitsEq_evals_encodePair_unequal (xs ys : List Bool)
    (hne : xs ≠ ys) :
    EvalsToInTime bitsEqualComputer.step
      (initList bitsEqualComputer (encodePair (xs, ys)))
      (some (haltList bitsEqualComputer [false]))
      (2 * xs.length + ys.length + 2 + (2 * xs.length + ys.length + 4)) := by
  have hload := bitsEq_evals_load_encodePair xs ys
  have hne' : xs.reverse ≠ ys.reverse := by
    intro h; exact hne (List.reverse_injective h)
  have hcmp0 := bitsEq_evals_unequal xs.reverse ys.reverse hne'
  have hcmp : EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .loop) none xs.reverse ys.reverse [])
      (some (haltList bitsEqualComputer [false]))
      (2 * xs.length + ys.length + 4) := by
    simpa [List.length_reverse] using hcmp0
  have h1 : EvalsToInTime bitsEqualComputer.step
      (initList bitsEqualComputer (encodePair (xs, ys)))
      (some (bitsEqCfg (some .loop) none xs.reverse ys.reverse []))
      (2 * xs.length + ys.length + 2) := by
    simpa [bitsEqual_initList] using hload
  have h :=
    EvalsToInTime.trans bitsEqualComputer.step
      (2 * xs.length + ys.length + 2) (2 * xs.length + ys.length + 4)
      _ _ _ h1 hcmp
  refine ⟨⟨h.steps, h.evals_in_steps⟩, ?_⟩
  refine le_trans h.steps_le_m ?_
  omega

/-- Full `encodePair` run: output `[bitsEqualPair p]` in linear tape length. -/
noncomputable def bitsEqualPair_evals (p : List Bool × List Bool) :
    TM2OutputsInTime bitsEqualComputer (encodePair p)
      (some (bitEnc (bitsEqualPair p)))
      (4 * (encodePair p).length + 6) := by
  rcases p with ⟨xs, ys⟩
  have hload := bitsEq_evals_load_encodePair xs ys
  have hzip0 := bitsEq_evals_zip xs.reverse ys.reverse
  have hzip : EvalsToInTime bitsEqualComputer.step
      (bitsEqCfg (some .loop) none xs.reverse ys.reverse [])
      (some (haltList bitsEqualComputer [bitsEqualPair (xs, ys)]))
      (2 * xs.length + ys.length + 4) := by
    have hrev := bitsEqual_reverse xs ys
    simpa [List.length_reverse, bitsEqualPair, hrev] using hzip0
  have h1 : EvalsToInTime bitsEqualComputer.step
      (initList bitsEqualComputer (encodePair (xs, ys)))
      (some (bitsEqCfg (some .loop) none xs.reverse ys.reverse []))
      (2 * xs.length + ys.length + 2) := by
    simpa [bitsEqual_initList] using hload
  have h :=
    EvalsToInTime.trans bitsEqualComputer.step
      (2 * xs.length + ys.length + 2) (2 * xs.length + ys.length + 4)
      _ _ _ h1 hzip
  refine ⟨⟨h.steps, ?_⟩, ?_⟩
  · simpa [bitEnc, bitsEqualPair] using h.evals_in_steps
  · refine le_trans h.steps_le_m ?_
    simp [length_encodePair]; omega

noncomputable def bitsEqualPairTime : Polynomial ℕ := 4 * Polynomial.X + 6

theorem bitsEqualPairTime_eval (n : ℕ) :
    bitsEqualPairTime.eval n = 4 * n + 6 := by
  simp [bitsEqualPairTime, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat]

/-- Pairwise bit equality under `encodePair` is poly time (Bool output). -/
noncomputable def bitsEqualPairComputableInPolyTime :
    TM2ComputableInPolyTime encodePair bitEnc bitsEqualPair where
  tm := bitsEqualComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := bitsEqualPairTime
  outputsFun p := by
    change TM2OutputsInTime bitsEqualComputer (List.map id (encodePair p))
      (some (List.map id (bitEnc (bitsEqualPair p))))
      (bitsEqualPairTime.eval (encodePair p).length)
    simp only [List.map_id, id_eq, bitsEqualPairTime_eval]
    exact bitsEqualPair_evals p

theorem bitsEqualPair_computableInPolyTime :
    Nonempty (TM2ComputableInPolyTime encodePair bitEnc bitsEqualPair) :=
  ⟨bitsEqualPairComputableInPolyTime⟩

/-! ## Cluster C2 FinTM2: pad bits to length `n`

Input `encodePair (encodeNat n, bs)`. Load (as in `bitsEqualComputer`) yields
`fuel = reverse (encodeNat n) = false :: true^n` and `bits = reverse bs`.
`revBits` moves `bits` onto `inp`, producing forward `bs` on `inp`. Sync pops
the fuel terminator; each `true` writes one bit into `work` from `inp` (or
`false`). That leaves `work = reverse (padBitsLE n bs)`. Final `revOut` copies
`work` onto `out`, then `drainInp` discards any leftover `inp` bits so the
halt configuration matches `haltList` when `|bs| > n`. -/

open TM2.Stmt

inductive PadBitsStack where
  | inp | fuel | bits | work | out
  deriving DecidableEq, Repr

instance : Fintype PadBitsStack where
  elems := {.inp, .fuel, .bits, .work, .out}
  complete s := by cases s <;> simp

inductive PadBitsLabel where
  | parse | expectBit | loadBits | revBits | sync | loop | takeBit | revOut
  | drainInp
  deriving DecidableEq, Repr

instance : Fintype PadBitsLabel where
  elems :=
    {.parse, .expectBit, .loadBits, .revBits, .sync, .loop, .takeBit, .revOut,
      .drainInp}
  complete s := by cases s <;> simp

/-- FinTM2 realizing `padBitsLE n bs` on `encodePair (encodeNat n, bs)`. -/
def padBitsComputer : FinTM2 where
  K := PadBitsStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := PadBitsLabel
  main := .parse
  σ := Option Bool
  initialState := none
  m
    | .parse =>
        pop PadBitsStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => PadBitsLabel.revOut)
            (branch (fun s => decide (s = some false))
              (load (fun _ => none) <| goto fun _ => PadBitsLabel.loadBits)
              (load (fun _ => none) <| goto fun _ => PadBitsLabel.expectBit))
    | .expectBit =>
        pop PadBitsStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => PadBitsLabel.revOut)
            (push PadBitsStack.fuel (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => PadBitsLabel.parse)
    | .loadBits =>
        pop PadBitsStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => PadBitsLabel.revBits)
            (push PadBitsStack.bits (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => PadBitsLabel.loadBits)
    | .revBits =>
        pop PadBitsStack.bits (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => PadBitsLabel.sync)
            (push PadBitsStack.inp (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => PadBitsLabel.revBits)
    | .sync =>
        pop PadBitsStack.fuel (fun _ o => o) <|
          branch (fun s => decide (s = some false))
            (load (fun _ => none) <| goto fun _ => PadBitsLabel.loop)
            (load (fun _ => none) <| goto fun _ => PadBitsLabel.revOut)
    | .loop =>
        pop PadBitsStack.fuel (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => PadBitsLabel.revOut)
            (branch (fun s => decide (s = some true))
              (load (fun _ => none) <| goto fun _ => PadBitsLabel.takeBit)
              (load (fun _ => none) <| goto fun _ => PadBitsLabel.revOut))
    | .takeBit =>
        pop PadBitsStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push PadBitsStack.work (fun _ => false) <|
              load (fun _ => none) <| goto fun _ => PadBitsLabel.loop)
            (push PadBitsStack.work (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => PadBitsLabel.loop)
    | .revOut =>
        pop PadBitsStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => PadBitsLabel.drainInp)
            (push PadBitsStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => PadBitsLabel.revOut)
    | .drainInp =>
        pop PadBitsStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) halt)
            (load (fun _ => none) <| goto fun _ => PadBitsLabel.drainInp)

def padBitsStk (inp fuel bits work out : List Bool) : PadBitsStack → List Bool
  | .inp => inp
  | .fuel => fuel
  | .bits => bits
  | .work => work
  | .out => out

def padBitsCfg (l : Option PadBitsLabel) (v : Option Bool)
    (inp fuel bits work out : List Bool) : padBitsComputer.Cfg :=
  ⟨l, v, padBitsStk inp fuel bits work out⟩

theorem padBits_initList (s : List Bool) :
    initList padBitsComputer s =
      padBitsCfg (some .parse) none s [] [] [] [] := by
  refine congrArg (fun stk =>
      (⟨some PadBitsLabel.parse, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [padBitsComputer, padBitsStk]

theorem padBits_haltList (out : List Bool) :
    haltList padBitsComputer out =
      padBitsCfg none none [] [] [] [] out := by
  refine congrArg (fun stk =>
      (⟨(none : Option PadBitsLabel), none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [padBitsComputer, padBitsStk]

/-! ### padBitsComputer step lemmas -/

open StateTransition

theorem padBits_step_parse_false (rest fuel bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .parse) none (false :: rest) fuel bits work out) =
      some (padBitsCfg (some .loadBits) none rest fuel bits work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.loadBits, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_parse_true (b : Bool) (rest fuel bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .parse) none (true :: b :: rest) fuel bits work out) =
      some (padBitsCfg (some .expectBit) none (b :: rest) fuel bits work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.expectBit, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_parse_nil (fuel bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .parse) none [] fuel bits work out) =
      some (padBitsCfg (some .revOut) none [] fuel bits work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.revOut, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_expectBit (b : Bool) (rest fuel bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .expectBit) none (b :: rest) fuel bits work out) =
      some (padBitsCfg (some .parse) none rest (b :: fuel) bits work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.parse, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_loadBits_cons (b : Bool) (rest fuel bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .loadBits) none (b :: rest) fuel bits work out) =
      some (padBitsCfg (some .loadBits) none rest fuel (b :: bits) work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.loadBits, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_loadBits_nil (fuel bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .loadBits) none [] fuel bits work out) =
      some (padBitsCfg (some .revBits) none [] fuel bits work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.revBits, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_revBits_cons (b : Bool) (inp fuel bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .revBits) none inp fuel (b :: bits) work out) =
      some (padBitsCfg (some .revBits) none (b :: inp) fuel bits work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.revBits, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_revBits_nil (inp fuel work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .revBits) none inp fuel [] work out) =
      some (padBitsCfg (some .sync) none inp fuel [] work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.sync, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_sync_false (fuel bits work out : List Bool) (inp : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .sync) none inp (false :: fuel) bits work out) =
      some (padBitsCfg (some .loop) none inp fuel bits work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.loop, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_loop_nil (inp bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .loop) none inp [] bits work out) =
      some (padBitsCfg (some .revOut) none inp [] bits work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.revOut, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_loop_true (inp fuel bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .loop) none inp (true :: fuel) bits work out) =
      some (padBitsCfg (some .takeBit) none inp fuel bits work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.takeBit, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_takeBit_cons (b : Bool) (inp fuel bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .takeBit) none (b :: inp) fuel bits work out) =
      some (padBitsCfg (some .loop) none inp fuel bits (b :: work) out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.loop, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_takeBit_nil (fuel bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .takeBit) none [] fuel bits work out) =
      some (padBitsCfg (some .loop) none [] fuel bits (false :: work) out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.loop, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_revOut_cons (b : Bool) (inp fuel bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .revOut) none inp fuel bits (b :: work) out) =
      some (padBitsCfg (some .revOut) none inp fuel bits work (b :: out)) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.revOut, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_revOut_nil (inp fuel bits out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .revOut) none inp fuel bits [] out) =
      some (padBitsCfg (some .drainInp) none inp fuel bits [] out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.drainInp, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_drainInp_cons (b : Bool) (rest fuel bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .drainInp) none (b :: rest) fuel bits work out) =
      some (padBitsCfg (some .drainInp) none rest fuel bits work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.drainInp, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_drainInp_nil (fuel bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .drainInp) none [] fuel bits work out) =
      some (padBitsCfg none none [] fuel bits work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option PadBitsLabel), none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_expectBit_nil (fuel bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .expectBit) none [] fuel bits work out) =
      some (padBitsCfg (some .revOut) none [] fuel bits work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.revOut, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_sync_true (rest inp bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .sync) none inp (true :: rest) bits work out) =
      some (padBitsCfg (some .revOut) none inp rest bits work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.revOut, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_sync_nil (inp bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .sync) none inp [] bits work out) =
      some (padBitsCfg (some .revOut) none inp [] bits work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.revOut, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

theorem padBits_step_loop_false (rest inp bits work out : List Bool) :
    TM2.step padBitsComputer.m
      (padBitsCfg (some .loop) none inp (false :: rest) bits work out) =
      some (padBitsCfg (some .revOut) none inp rest bits work out) := by
  simp [padBitsComputer, padBitsCfg, padBitsStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some PadBitsLabel.revOut, none, stk⟩ : padBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, padBitsStk]

/-! ### padBitsComputer EvalsToInTime (happy path pieces) -/

def padBits_evals_parse_false (rest fuel bits work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .parse) none (false :: rest) fuel bits work out)
      (some (padBitsCfg (some .loadBits) none rest fuel bits work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (padBitsCfg (some .parse) none (false :: rest) fuel bits work out)).bind
        padBitsComputer.step =
      some (padBitsCfg (some .loadBits) none rest fuel bits work out)
    simp only [FinTM2.step]
    exact padBits_step_parse_false rest fuel bits work out

def padBits_evals_expectBit (b : Bool) (rest fuel bits work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .expectBit) none (b :: rest) fuel bits work out)
      (some (padBitsCfg (some .parse) none rest (b :: fuel) bits work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (padBitsCfg (some .expectBit) none (b :: rest) fuel bits work out)).bind
        padBitsComputer.step =
      some (padBitsCfg (some .parse) none rest (b :: fuel) bits work out)
    simp only [FinTM2.step]
    exact padBits_step_expectBit b rest fuel bits work out

def padBits_evals_parse_true (b : Bool) (rest fuel bits work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .parse) none (true :: b :: rest) fuel bits work out)
      (some (padBitsCfg (some .expectBit) none (b :: rest) fuel bits work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (padBitsCfg (some .parse) none (true :: b :: rest) fuel bits work out)).bind
        padBitsComputer.step =
      some (padBitsCfg (some .expectBit) none (b :: rest) fuel bits work out)
    simp only [FinTM2.step]
    exact padBits_step_parse_true b rest fuel bits work out

/-- Parse one self delimiting first-component bit (`true :: b`) into fuel. -/
noncomputable def padBits_evals_parse_one (b : Bool) (rest fuel bits work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .parse) none (true :: b :: rest) fuel bits work out)
      (some (padBitsCfg (some .parse) none rest (b :: fuel) bits work out)) 2 := by
  have h1 := padBits_evals_parse_true b rest fuel bits work out
  have h2 := padBits_evals_expectBit b rest fuel bits work out
  exact EvalsToInTime.trans padBitsComputer.step 1 1 _ _ _ h1 h2

/-- Parse the full first component of `encodePair`, leaving separator on inp. -/
noncomputable def padBits_evals_parse_first (xs : List Bool)
    (rest fuel bits work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .parse) none
        (xs.flatMap (fun b => [true, b]) ++ rest) fuel bits work out)
      (some (padBitsCfg (some .parse) none rest (xs.reverse ++ fuel) bits work out))
      (2 * xs.length) := by
  induction xs generalizing fuel with
  | nil =>
      simpa using
        (EvalsToInTime.refl padBitsComputer.step
          (padBitsCfg (some .parse) none rest fuel bits work out) :
          EvalsToInTime padBitsComputer.step _ _ 0)
  | cons b xs ih =>
      have h1 :=
        padBits_evals_parse_one b (xs.flatMap (fun b => [true, b]) ++ rest)
          fuel bits work out
      have h2 := ih (b :: fuel)
      have h :=
        EvalsToInTime.trans padBitsComputer.step 2 (2 * xs.length) _ _ _ h1 h2
      simpa [List.flatMap_cons, List.reverse_cons, List.append_assoc,
        Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

def padBits_evals_loadBits_nil (fuel bits work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .loadBits) none [] fuel bits work out)
      (some (padBitsCfg (some .revBits) none [] fuel bits work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (padBitsCfg (some .loadBits) none [] fuel bits work out)).bind
        padBitsComputer.step =
      some (padBitsCfg (some .revBits) none [] fuel bits work out)
    simp only [FinTM2.step]
    exact padBits_step_loadBits_nil fuel bits work out

def padBits_evals_loadBits_cons (b : Bool) (ys fuel bits work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .loadBits) none (b :: ys) fuel bits work out)
      (some (padBitsCfg (some .loadBits) none ys fuel (b :: bits) work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (padBitsCfg (some .loadBits) none (b :: ys) fuel bits work out)).bind
        padBitsComputer.step =
      some (padBitsCfg (some .loadBits) none ys fuel (b :: bits) work out)
    simp only [FinTM2.step]
    exact padBits_step_loadBits_cons b ys fuel bits work out

noncomputable def padBits_evals_loadBits (ys fuel bits work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .loadBits) none ys fuel bits work out)
      (some (padBitsCfg (some .revBits) none [] fuel (ys.reverse ++ bits) work out))
      (ys.length + 1) := by
  induction ys generalizing bits with
  | nil =>
      simpa using padBits_evals_loadBits_nil fuel bits work out
  | cons b ys ih =>
      have h :=
        EvalsToInTime.trans padBitsComputer.step 1 (ys.length + 1) _ _ _
          (padBits_evals_loadBits_cons b ys fuel bits work out) (ih (b :: bits))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

def padBits_evals_revBits_nil (inp fuel work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .revBits) none inp fuel [] work out)
      (some (padBitsCfg (some .sync) none inp fuel [] work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (padBitsCfg (some .revBits) none inp fuel [] work out)).bind
        padBitsComputer.step =
      some (padBitsCfg (some .sync) none inp fuel [] work out)
    simp only [FinTM2.step]
    exact padBits_step_revBits_nil inp fuel work out

def padBits_evals_revBits_cons (b : Bool) (bits inp fuel work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .revBits) none inp fuel (b :: bits) work out)
      (some (padBitsCfg (some .revBits) none (b :: inp) fuel bits work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (padBitsCfg (some .revBits) none inp fuel (b :: bits) work out)).bind
        padBitsComputer.step =
      some (padBitsCfg (some .revBits) none (b :: inp) fuel bits work out)
    simp only [FinTM2.step]
    exact padBits_step_revBits_cons b inp fuel bits work out

noncomputable def padBits_evals_revBits (bits inp fuel work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .revBits) none inp fuel bits work out)
      (some (padBitsCfg (some .sync) none (bits.reverse ++ inp) fuel [] work out))
      (bits.length + 1) := by
  induction bits generalizing inp with
  | nil =>
      simpa using padBits_evals_revBits_nil inp fuel work out
  | cons b bits ih =>
      have h :=
        EvalsToInTime.trans padBitsComputer.step 1 (bits.length + 1) _ _ _
          (padBits_evals_revBits_cons b bits inp fuel work out) (ih (b :: inp))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

/-- Load `encodePair (xs, ys)` into reversed fuel/bits, then enter `revBits`. -/
noncomputable def padBits_evals_load_encodePair (xs ys : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .parse) none (encodePair (xs, ys)) [] [] [] [])
      (some (padBitsCfg (some .revBits) none [] xs.reverse ys.reverse [] []))
      (2 * xs.length + ys.length + 2) := by
  have hparse :=
    padBits_evals_parse_first xs (false :: ys) [] [] [] []
  have htoLoad :=
    padBits_evals_parse_false ys xs.reverse [] [] []
  have hload :=
    padBits_evals_loadBits ys xs.reverse [] [] []
  have h1 : EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .parse) none (encodePair (xs, ys)) [] [] [] [])
      (some (padBitsCfg (some .parse) none (false :: ys) xs.reverse [] [] []))
      (2 * xs.length) := by
    simpa [encodePair, List.append_assoc] using hparse
  have h12 :=
    EvalsToInTime.trans padBitsComputer.step (2 * xs.length) 1 _ _ _ h1 htoLoad
  have h12' : EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .parse) none (encodePair (xs, ys)) [] [] [] [])
      (some (padBitsCfg (some .loadBits) none ys xs.reverse [] [] []))
      (2 * xs.length + 1) := by
    simpa [Nat.add_comm] using h12
  have h :=
    EvalsToInTime.trans padBitsComputer.step (2 * xs.length + 1) (ys.length + 1)
      _ _ _ h12' hload
  refine ⟨⟨h.steps, ?_⟩, ?_⟩
  · simpa [List.append_nil] using h.evals_in_steps
  · refine le_trans h.steps_le_m ?_
    omega

def padBits_evals_sync_false (rest inp bits work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .sync) none inp (false :: rest) bits work out)
      (some (padBitsCfg (some .loop) none inp rest bits work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (padBitsCfg (some .sync) none inp (false :: rest) bits work out)).bind
        padBitsComputer.step =
      some (padBitsCfg (some .loop) none inp rest bits work out)
    simp only [FinTM2.step]
    exact padBits_step_sync_false rest bits work out inp

def padBits_evals_loop_nil (inp bits work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .loop) none inp [] bits work out)
      (some (padBitsCfg (some .revOut) none inp [] bits work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (padBitsCfg (some .loop) none inp [] bits work out)).bind
        padBitsComputer.step =
      some (padBitsCfg (some .revOut) none inp [] bits work out)
    simp only [FinTM2.step]
    exact padBits_step_loop_nil inp bits work out

def padBits_evals_loop_true (rest inp bits work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .loop) none inp (true :: rest) bits work out)
      (some (padBitsCfg (some .takeBit) none inp rest bits work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (padBitsCfg (some .loop) none inp (true :: rest) bits work out)).bind
        padBitsComputer.step =
      some (padBitsCfg (some .takeBit) none inp rest bits work out)
    simp only [FinTM2.step]
    exact padBits_step_loop_true inp rest bits work out

def padBits_evals_takeBit_cons (b : Bool) (rest fuel bits work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .takeBit) none (b :: rest) fuel bits work out)
      (some (padBitsCfg (some .loop) none rest fuel bits (b :: work) out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (padBitsCfg (some .takeBit) none (b :: rest) fuel bits work out)).bind
        padBitsComputer.step =
      some (padBitsCfg (some .loop) none rest fuel bits (b :: work) out)
    simp only [FinTM2.step]
    exact padBits_step_takeBit_cons b rest fuel bits work out

def padBits_evals_takeBit_nil (fuel bits work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .takeBit) none [] fuel bits work out)
      (some (padBitsCfg (some .loop) none [] fuel bits (false :: work) out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (padBitsCfg (some .takeBit) none [] fuel bits work out)).bind
        padBitsComputer.step =
      some (padBitsCfg (some .loop) none [] fuel bits (false :: work) out)
    simp only [FinTM2.step]
    exact padBits_step_takeBit_nil fuel bits work out

theorem take_append_replicate_false_succ (m : ℕ) (l : List Bool) :
    (l ++ List.replicate (m + 1) false).take m =
      (l ++ List.replicate m false).take m := by
  have hlen : m ≤ (l ++ List.replicate m false).length := by
    simp
  have hrep : List.replicate (m + 1) false =
      List.replicate m false ++ [false] := by
    simpa [List.replicate_one] using List.replicate_add m 1 false
  calc
    (l ++ List.replicate (m + 1) false).take m
        = (l ++ (List.replicate m false ++ [false])).take m := by rw [hrep]
    _ = ((l ++ List.replicate m false) ++ [false]).take m := by
          rw [List.append_assoc]
    _ = (l ++ List.replicate m false).take m :=
          List.take_append_of_le_length hlen

theorem padBitsLE_cons (n : ℕ) (b : Bool) (bs : List Bool) :
    padBitsLE (n + 1) (b :: bs) = b :: padBitsLE n bs := by
  simp only [padBitsLE, List.cons_append]
  change b :: (bs ++ List.replicate (n + 1) false).take n =
    b :: (bs ++ List.replicate n false).take n
  rw [take_append_replicate_false_succ]

theorem padBitsLE_nil (n : ℕ) :
    padBitsLE n ([] : List Bool) = List.replicate n false := by
  simp [padBitsLE]

theorem encodeNat_reverse (n : ℕ) :
    (encodeNat n).reverse = false :: List.replicate n true := by
  simp [encodeNat, List.reverse_append, List.reverse_replicate]

/-- Pad loop: `fuel = true^n` writes `reverse (padBitsLE n inp)` onto work. -/
noncomputable def padBits_evals_loop (n : ℕ) (inp work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .loop) none inp (List.replicate n true) [] work out)
      (some (padBitsCfg (some .revOut) none (inp.drop n) [] []
        ((padBitsLE n inp).reverse ++ work) out))
      (2 * n + 1) := by
  induction n generalizing inp work with
  | zero =>
      simpa [padBitsLE, List.drop] using padBits_evals_loop_nil inp [] work out
  | succ n ih =>
      have hfuel : List.replicate (n + 1) true = true :: List.replicate n true := by
        simp [List.replicate_succ]
      rw [hfuel]
      have h1 := padBits_evals_loop_true (List.replicate n true) inp [] work out
      cases inp with
      | nil =>
          have h2 := padBits_evals_takeBit_nil (List.replicate n true) [] work out
          have h12 :=
            EvalsToInTime.trans padBitsComputer.step 1 1 _ _ _ h1 h2
          have h3 := ih [] (false :: work)
          have h :=
            EvalsToInTime.trans padBitsComputer.step 2 (2 * n + 1) _ _ _ h12 h3
          have hpad :
              (padBitsLE n []).reverse ++ false :: work =
                (padBitsLE (n + 1) []).reverse ++ work := by
            simp [padBitsLE_nil, List.reverse_replicate, List.replicate_succ]
          refine ⟨⟨h.steps, ?_⟩, ?_⟩
          · simpa [List.drop, hpad, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using h.evals_in_steps
          · refine le_trans h.steps_le_m ?_
            omega
      | cons b bs =>
          have h2 :=
            padBits_evals_takeBit_cons b bs (List.replicate n true) [] work out
          have h12 :=
            EvalsToInTime.trans padBitsComputer.step 1 1 _ _ _ h1 h2
          have h3 := ih bs (b :: work)
          have h :=
            EvalsToInTime.trans padBitsComputer.step 2 (2 * n + 1) _ _ _ h12 h3
          have hpad :
              (padBitsLE n bs).reverse ++ b :: work =
                (padBitsLE (n + 1) (b :: bs)).reverse ++ work := by
            simp [padBitsLE_cons, List.reverse_cons]
          refine ⟨⟨h.steps, ?_⟩, ?_⟩
          · simpa [List.drop_succ_cons, hpad, Nat.mul_succ, Nat.add_comm,
              Nat.add_left_comm, Nat.add_assoc] using h.evals_in_steps
          · refine le_trans h.steps_le_m ?_
            omega

def padBits_evals_revOut_one (b : Bool) (rest inp fuel bits out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .revOut) none inp fuel bits (b :: rest) out)
      (some (padBitsCfg (some .revOut) none inp fuel bits rest (b :: out))) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (padBitsCfg (some .revOut) none inp fuel bits (b :: rest) out)).bind
        padBitsComputer.step =
      some (padBitsCfg (some .revOut) none inp fuel bits rest (b :: out))
    simp only [FinTM2.step]
    exact padBits_step_revOut_cons b inp fuel bits rest out

def padBits_evals_revOut_nil (inp fuel bits out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .revOut) none inp fuel bits [] out)
      (some (padBitsCfg (some .drainInp) none inp fuel bits [] out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (padBitsCfg (some .revOut) none inp fuel bits [] out)).bind
        padBitsComputer.step =
      some (padBitsCfg (some .drainInp) none inp fuel bits [] out)
    simp only [FinTM2.step]
    exact padBits_step_revOut_nil inp fuel bits out

noncomputable def padBits_evals_revOut (work inp fuel bits out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .revOut) none inp fuel bits work out)
      (some (padBitsCfg (some .drainInp) none inp fuel bits []
        (work.reverse ++ out)))
      (work.length + 1) := by
  induction work generalizing out with
  | nil =>
      simpa using padBits_evals_revOut_nil inp fuel bits out
  | cons b bs ih =>
      have h1 := padBits_evals_revOut_one b bs inp fuel bits out
      have h2 := ih (b :: out)
      have h :=
        EvalsToInTime.trans padBitsComputer.step 1 (bs.length + 1) _ _ _ h1 h2
      refine ⟨⟨h.steps, ?_⟩, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using h.evals_in_steps
      · refine le_trans h.steps_le_m ?_
        simp [List.length_cons]

def padBits_evals_drainInp_one (b : Bool) (rest fuel bits work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .drainInp) none (b :: rest) fuel bits work out)
      (some (padBitsCfg (some .drainInp) none rest fuel bits work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (padBitsCfg (some .drainInp) none (b :: rest) fuel bits work out)).bind
        padBitsComputer.step =
      some (padBitsCfg (some .drainInp) none rest fuel bits work out)
    simp only [FinTM2.step]
    exact padBits_step_drainInp_cons b rest fuel bits work out

def padBits_evals_drainInp_nil (fuel bits work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .drainInp) none [] fuel bits work out)
      (some (padBitsCfg none none [] fuel bits work out)) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (padBitsCfg (some .drainInp) none [] fuel bits work out)).bind
        padBitsComputer.step =
      some (padBitsCfg none none [] fuel bits work out)
    simp only [FinTM2.step]
    exact padBits_step_drainInp_nil fuel bits work out

noncomputable def padBits_evals_drainInp (inp fuel bits work out : List Bool) :
    EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .drainInp) none inp fuel bits work out)
      (some (padBitsCfg none none [] fuel bits work out))
      (inp.length + 1) := by
  induction inp with
  | nil =>
      simpa using padBits_evals_drainInp_nil fuel bits work out
  | cons b bs ih =>
      have h1 := padBits_evals_drainInp_one b bs fuel bits work out
      have h2 := ih
      have h :=
        EvalsToInTime.trans padBitsComputer.step 1 (bs.length + 1) _ _ _ h1 h2
      refine ⟨⟨h.steps, h.evals_in_steps⟩, ?_⟩
      refine le_trans h.steps_le_m ?_
      simp [List.length_cons]

/-- Full run: `encodePair (encodeNat n, bs)` yields `padBitsLE n bs`. -/
noncomputable def padBits_evals (n : ℕ) (bs : List Bool) :
    TM2OutputsInTime padBitsComputer (encodePair (encodeNat n, bs))
      (some (padBitsLE n bs))
      (5 * n + 3 * bs.length + 9) := by
  have hencLen : (encodeNat n).length = n + 1 := by simp [encodeNat]
  have hload0 := padBits_evals_load_encodePair (encodeNat n) bs
  have hrev0 :=
    padBits_evals_revBits bs.reverse [] (encodeNat n).reverse [] []
  have hsync0 :=
    padBits_evals_sync_false (List.replicate n true) bs [] [] []
  have hloop0 := padBits_evals_loop n bs [] []
  have hrevOut0 :=
    padBits_evals_revOut ((padBitsLE n bs).reverse) (bs.drop n) [] [] []
  have hdrain0 :=
    padBits_evals_drainInp (bs.drop n) [] [] [] (padBitsLE n bs)
  have hload : EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .parse) none (encodePair (encodeNat n, bs)) [] [] [] [])
      (some (padBitsCfg (some .revBits) none [] (encodeNat n).reverse bs.reverse [] []))
      (2 * (n + 1) + bs.length + 2) := by
    simpa [hencLen] using hload0
  have hrev : EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .revBits) none [] (encodeNat n).reverse bs.reverse [] [])
      (some (padBitsCfg (some .sync) none bs (encodeNat n).reverse [] [] []))
      (bs.length + 1) := by
    simpa [List.length_reverse, List.reverse_reverse, List.append_nil] using hrev0
  have h12 :=
    EvalsToInTime.trans padBitsComputer.step
      (2 * (n + 1) + bs.length + 2) (bs.length + 1) _ _ _ hload hrev
  have hfuel : (encodeNat n).reverse = false :: List.replicate n true :=
    encodeNat_reverse n
  have hsync : EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .sync) none bs (encodeNat n).reverse [] [] [])
      (some (padBitsCfg (some .loop) none bs (List.replicate n true) [] [] [])) 1 := by
    simpa [hfuel] using hsync0
  have h123 :=
    EvalsToInTime.trans padBitsComputer.step
      (2 * (n + 1) + bs.length + 2 + (bs.length + 1)) 1 _ _ _
      (evalsToInTime_le_mono h12 (by omega)) hsync
  have hloop : EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .loop) none bs (List.replicate n true) [] [] [])
      (some (padBitsCfg (some .revOut) none (bs.drop n) [] []
        (padBitsLE n bs).reverse []))
      (2 * n + 1) := by
    simpa [List.append_nil] using hloop0
  have h1234 :=
    EvalsToInTime.trans padBitsComputer.step
      (2 * (n + 1) + bs.length + 2 + (bs.length + 1) + 1) (2 * n + 1) _ _ _
      (evalsToInTime_le_mono h123 (by omega)) hloop
  have hrevOut : EvalsToInTime padBitsComputer.step
      (padBitsCfg (some .revOut) none (bs.drop n) [] [] (padBitsLE n bs).reverse [])
      (some (padBitsCfg (some .drainInp) none (bs.drop n) [] [] [] (padBitsLE n bs)))
      (n + 1) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse,
      length_padBitsLE] using hrevOut0
  have h12345 :=
    EvalsToInTime.trans padBitsComputer.step
      (2 * (n + 1) + bs.length + 2 + (bs.length + 1) + 1 + (2 * n + 1)) (n + 1)
      _ _ _ (evalsToInTime_le_mono h1234 (by omega)) hrevOut
  have hAll :=
    EvalsToInTime.trans padBitsComputer.step
      (2 * (n + 1) + bs.length + 2 + (bs.length + 1) + 1 + (2 * n + 1) + (n + 1))
      ((bs.drop n).length + 1) _ _ _
      (evalsToInTime_le_mono h12345 (by omega)) hdrain0
  have hInit : EvalsToInTime padBitsComputer.step
      (initList padBitsComputer (encodePair (encodeNat n, bs)))
      (some (haltList padBitsComputer (padBitsLE n bs)))
      (2 * (n + 1) + bs.length + 2 + (bs.length + 1) + 1 + (2 * n + 1) + (n + 1) +
        ((bs.drop n).length + 1)) := by
    rw [padBits_initList, padBits_haltList]
    exact evalsToInTime_le_mono hAll (by omega)
  have hle : 2 * (n + 1) + bs.length + 2 + (bs.length + 1) + 1 + (2 * n + 1) +
      (n + 1) + ((bs.drop n).length + 1) ≤ 5 * n + 3 * bs.length + 9 := by
    simp [List.length_drop]
    omega
  exact evalsToInTime_le_mono hInit hle

noncomputable def padBitsTime : Polynomial ℕ := 8 * Polynomial.X + 8

theorem padBitsTime_eval (t : ℕ) :
    padBitsTime.eval t = 8 * t + 8 := by
  simp [padBitsTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_ofNat]

/-- `padBitsLE` under `encodePair (encodeNat n, bs)` is poly time. -/
noncomputable def padBitsComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun p : ℕ × List Bool => encodePair (encodeNat p.1, p.2))
      idBitEnc
      (fun p => padBitsLE p.1 p.2) where
  tm := padBitsComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := padBitsTime
  outputsFun p := by
    rcases p with ⟨n, bs⟩
    change TM2OutputsInTime padBitsComputer
      (List.map id (encodePair (encodeNat n, bs)))
      (some (List.map id (idBitEnc (padBitsLE n bs))))
      (padBitsTime.eval (encodePair (encodeNat n, bs)).length)
    simp only [idBitEnc, List.map_id, id_eq, padBitsTime_eval]
    have h := padBits_evals n bs
    refine evalsToInTime_le_mono h ?_
    have hlen : (encodePair (encodeNat n, bs)).length = 2 * (n + 1) + 1 + bs.length := by
      simpa [encodeNat, List.length_append, List.length_replicate, List.length_singleton]
        using length_encodePair (encodeNat n, bs)
    omega

theorem padBits_computableInPolyTime :
    Nonempty (TM2ComputableInPolyTime
      (fun p : ℕ × List Bool => encodePair (encodeNat p.1, p.2))
      idBitEnc
      (fun p => padBitsLE p.1 p.2)) :=
  ⟨padBitsComputableInPolyTime⟩

/-- Index loop form with padded bits (FinTM2 assignment tape). -/
theorem validatesTautology_by_index_pad (φ : PropFormula) (table : List Bool) :
    validatesTautology_by_index φ table ↔
      table.length = 2 ^ (φ.maxVar + 1) ∧
        ∀ (i : ℕ) (hi : i < table.length),
          table[i] =
              φ.evalOn (padBitsLE (φ.maxVar + 1) (natBitsLE i)) ∧
            table[i] = true := by
  constructor
  · intro h
    refine ⟨h.1, fun i hi => ?_⟩
    have hpair := h.2 i hi
    have hi' : i < 2 ^ (φ.maxVar + 1) := by
      simpa [h.1] using hi
    rwa [assignmentAt_eq_padBitsLE hi'] at hpair
  · intro h
    refine ⟨h.1, fun i hi => ?_⟩
    have hpair := h.2 i hi
    have hi' : i < 2 ^ (φ.maxVar + 1) := by
      simpa [h.1] using hi
    rwa [← assignmentAt_eq_padBitsLE hi'] at hpair

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

/-! ## Cluster D1 FinTM2: `evalEncoded` under `encodePair (σ, φCode)`

Input `encodePair (σ, φCode)`. After load, forward `σ` sits on `assign` and
forward `φCode` on `code`. Parsing mirrors `evalEncodedPrefixFuel`: tag bits like
DFR, variable lookup by unary `encodeNat` with assign scan, and connective
combine on `val`. Continuation markers use a 2-bit code on `inp`.

Marker codes (push low then high; pop high then low):
- applyNot:    `(false, false)`
- combineAnd:  `(false, true)`
- combineOr:   `(true, false)`
- sibling:     `(true, true)`

Output convention: `[b]` when `evalEncoded σ φCode = some b`; `[false]` on
failure, matching `(evalEncoded σ φCode).getD false`. -/

open TM2.Stmt

inductive EvalEncStack where
  | inp | assign | code | val | out
  deriving DecidableEq, Repr

instance : Fintype EvalEncStack where
  elems := {.inp, .assign, .code, .val, .out}
  complete s := by cases s <;> simp

inductive EvalEncLabel where
  | parse | expectBit | loadCode
  | fixAssign1 | fixAssign2 | fixAssign3
  | fixCode1 | fixCode2 | fixCode3
  | parseTag0 | parseTag1F | parseTag1T
  | parseNat | skipOne | readResult | restoreAssign
  | afterSub
  | doNot | doAndSave | doAndCombine | doOrSave | doOrCombine
  | checkDone | clearAssign
  | failClearInp | failClearAssign | failClearCode | failClearVal | failClearOut
  | writeFalse
  deriving DecidableEq, Repr

instance : Fintype EvalEncLabel where
  elems :=
    {.parse, .expectBit, .loadCode, .fixAssign1, .fixAssign2, .fixAssign3,
      .fixCode1, .fixCode2, .fixCode3, .parseTag0, .parseTag1F, .parseTag1T,
      .parseNat, .skipOne, .readResult, .restoreAssign, .afterSub, .doNot,
      .doAndSave, .doAndCombine, .doOrSave, .doOrCombine, .checkDone, .clearAssign,
      .failClearInp, .failClearAssign, .failClearCode, .failClearVal, .failClearOut,
      .writeFalse}
  complete s := by cases s <;> simp

/-- FinTM2 realizing `(evalEncoded σ φCode).getD false` on `encodePair (σ, φCode)`. -/
def evalEncodedComputer : FinTM2 where
  K := EvalEncStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := EvalEncLabel
  main := .parse
  σ := Option Bool
  initialState := none
  m
    | .parse =>
        pop EvalEncStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.writeFalse)
            (branch (fun s => decide (s = some false))
              (load (fun _ => none) <| goto fun _ => EvalEncLabel.loadCode)
              (load (fun _ => none) <| goto fun _ => EvalEncLabel.expectBit))
    | .expectBit =>
        pop EvalEncStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.writeFalse)
            (push EvalEncStack.assign (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => EvalEncLabel.parse)
    | .loadCode =>
        pop EvalEncStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.fixAssign1)
            (push EvalEncStack.code (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => EvalEncLabel.loadCode)
    | .fixAssign1 =>
        pop EvalEncStack.assign (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.fixAssign2)
            (push EvalEncStack.inp (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => EvalEncLabel.fixAssign1)
    | .fixAssign2 =>
        pop EvalEncStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.fixAssign3)
            (push EvalEncStack.val (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => EvalEncLabel.fixAssign2)
    | .fixAssign3 =>
        pop EvalEncStack.val (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.fixCode1)
            (push EvalEncStack.assign (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => EvalEncLabel.fixAssign3)
    | .fixCode1 =>
        pop EvalEncStack.code (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.fixCode2)
            (push EvalEncStack.inp (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => EvalEncLabel.fixCode1)
    | .fixCode2 =>
        pop EvalEncStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.fixCode3)
            (push EvalEncStack.val (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => EvalEncLabel.fixCode2)
    | .fixCode3 =>
        pop EvalEncStack.val (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.parseTag0)
            (push EvalEncStack.code (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => EvalEncLabel.fixCode3)
    | .parseTag0 =>
        pop EvalEncStack.code (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)
            (branch (fun s => decide (s = some false))
              (load (fun _ => none) <| goto fun _ => EvalEncLabel.parseTag1F)
              (load (fun _ => none) <| goto fun _ => EvalEncLabel.parseTag1T))
    | .parseTag1F =>
        pop EvalEncStack.code (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)
            (branch (fun s => decide (s = some false))
              (load (fun _ => none) <| goto fun _ => EvalEncLabel.parseNat)
              (push EvalEncStack.inp (fun _ => false) <|
                push EvalEncStack.inp (fun _ => false) <|
                  load (fun _ => none) <| goto fun _ => EvalEncLabel.parseTag0))
    | .parseTag1T =>
        pop EvalEncStack.code (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)
            (branch (fun s => decide (s = some false))
              (push EvalEncStack.inp (fun _ => false) <|
                push EvalEncStack.inp (fun _ => true) <|
                  push EvalEncStack.inp (fun _ => true) <|
                    push EvalEncStack.inp (fun _ => true) <|
                      load (fun _ => none) <| goto fun _ => EvalEncLabel.parseTag0)
              (push EvalEncStack.inp (fun _ => true) <|
                push EvalEncStack.inp (fun _ => false) <|
                  push EvalEncStack.inp (fun _ => true) <|
                    push EvalEncStack.inp (fun _ => true) <|
                      load (fun _ => none) <| goto fun _ => EvalEncLabel.parseTag0))
    | .parseNat =>
        pop EvalEncStack.code (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)
            (branch (fun s => decide (s = some true))
              (load (fun _ => none) <| goto fun _ => EvalEncLabel.skipOne)
              (load (fun _ => none) <| goto fun _ => EvalEncLabel.readResult))
    | .skipOne =>
        pop EvalEncStack.assign (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.parseNat)
            (push EvalEncStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => EvalEncLabel.parseNat)
    | .readResult =>
        peek EvalEncStack.assign (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push EvalEncStack.val (fun _ => false) <|
              load (fun _ => none) <| goto fun _ => EvalEncLabel.restoreAssign)
            (push EvalEncStack.val (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => EvalEncLabel.restoreAssign)
    | .restoreAssign =>
        pop EvalEncStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.afterSub)
            (push EvalEncStack.assign (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => EvalEncLabel.restoreAssign)
    | .afterSub =>
        pop EvalEncStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.checkDone)
            (branch (fun s => decide (s = some true))
              (pop EvalEncStack.inp (fun _ o => o) <|
                branch (fun s => decide (s = none))
                  (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)
                  (branch (fun s => decide (s = some true))
                    (load (fun _ => none) <| goto fun _ => EvalEncLabel.parseTag0)
                    (load (fun _ => none) <| goto fun _ => EvalEncLabel.doAndSave)))
              (pop EvalEncStack.inp (fun _ o => o) <|
                branch (fun s => decide (s = none))
                  (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)
                  (branch (fun s => decide (s = some true))
                    (load (fun _ => none) <| goto fun _ => EvalEncLabel.doOrSave)
                    (load (fun _ => none) <| goto fun _ => EvalEncLabel.doNot))))
    | .doNot =>
        pop EvalEncStack.val (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)
            (push EvalEncStack.val (fun s => !(s.getD false)) <|
              load (fun _ => none) <| goto fun _ => EvalEncLabel.afterSub)
    | .doAndSave =>
        pop EvalEncStack.val (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)
            (push EvalEncStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => EvalEncLabel.doAndCombine)
    | .doAndCombine =>
        pop EvalEncStack.val (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)
            (pop EvalEncStack.out (fun s o =>
                match s, o with
                | some bφ, some bψ => some (bφ && bψ)
                | _, _ => none) <|
              branch (fun s => decide (s = none))
                (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)
                (push EvalEncStack.val (fun s => s.getD false) <|
                  load (fun _ => none) <| goto fun _ => EvalEncLabel.afterSub))
    | .doOrSave =>
        pop EvalEncStack.val (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)
            (push EvalEncStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => EvalEncLabel.doOrCombine)
    | .doOrCombine =>
        pop EvalEncStack.val (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)
            (pop EvalEncStack.out (fun s o =>
                match s, o with
                | some bφ, some bψ => some (bφ || bψ)
                | _, _ => none) <|
              branch (fun s => decide (s = none))
                (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)
                (push EvalEncStack.val (fun s => s.getD false) <|
                  load (fun _ => none) <| goto fun _ => EvalEncLabel.afterSub))
    | .checkDone =>
        pop EvalEncStack.code (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (pop EvalEncStack.val (fun _ o => o) <|
              branch (fun s => decide (s = none))
                (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)
                (push EvalEncStack.out (fun s => s.getD false) <|
                  pop EvalEncStack.val (fun _ o => o) <|
                    branch (fun s => decide (s = none))
                      (load (fun _ => none) <| goto fun _ => EvalEncLabel.clearAssign)
                      (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)
    | .clearAssign =>
        pop EvalEncStack.assign (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| halt)
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.clearAssign)
    | .failClearInp =>
        pop EvalEncStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearAssign)
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearInp)
    | .failClearAssign =>
        pop EvalEncStack.assign (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearCode)
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearAssign)
    | .failClearCode =>
        pop EvalEncStack.code (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearVal)
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearCode)
    | .failClearVal =>
        pop EvalEncStack.val (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearOut)
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearVal)
    | .failClearOut =>
        pop EvalEncStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.writeFalse)
            (load (fun _ => none) <| goto fun _ => EvalEncLabel.failClearOut)
    | .writeFalse =>
        push EvalEncStack.out (fun _ => false) <|
          load (fun _ => none) <|
            halt

def evalEncStk (inp assign code val out : List Bool) : EvalEncStack → List Bool
  | .inp => inp
  | .assign => assign
  | .code => code
  | .val => val
  | .out => out

def evalEncCfg (l : Option EvalEncLabel) (v : Option Bool)
    (inp assign code val out : List Bool) : evalEncodedComputer.Cfg :=
  ⟨l, v, evalEncStk inp assign code val out⟩

theorem evalEnc_initList (s : List Bool) :
    initList evalEncodedComputer s =
      evalEncCfg (some .parse) none s [] [] [] [] := by
  refine congrArg (fun stk =>
      (⟨some EvalEncLabel.parse, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [evalEncodedComputer, evalEncStk]

theorem evalEnc_haltList (out : List Bool) :
    haltList evalEncodedComputer out =
      evalEncCfg none none [] [] [] [] out := by
  refine congrArg (fun stk =>
      (⟨(none : Option EvalEncLabel), none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [evalEncodedComputer, evalEncStk]

/-! ### evalEncodedComputer step lemmas -/

open StateTransition

private theorem evalEnc_cfg_ext {l : Option EvalEncLabel} {v : Option Bool}
    {inp assign code val out : List Bool}
    {l' : Option EvalEncLabel} {v' : Option Bool}
    {inp' assign' code' val' out' : List Bool}
    (hl : l = l') (hv : v = v') (hi : inp = inp') (ha : assign = assign')
    (hc : code = code') (hval : val = val') (ho : out = out') :
    evalEncCfg l v inp assign code val out =
      evalEncCfg l' v' inp' assign' code' val' out' := by
  subst_vars; rfl

theorem evalEnc_step_parse_false (rest assign code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .parse) none (false :: rest) assign code val out) =
      some (evalEncCfg (some .loadCode) none rest assign code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.loadCode, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_parse_true (b : Bool) (rest assign code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .parse) none (true :: b :: rest) assign code val out) =
      some (evalEncCfg (some .expectBit) none (b :: rest) assign code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.expectBit, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_parse_nil (assign code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .parse) none [] assign code val out) =
      some (evalEncCfg (some .writeFalse) none [] assign code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.writeFalse, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_expectBit (b : Bool) (rest assign code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .expectBit) none (b :: rest) assign code val out) =
      some (evalEncCfg (some .parse) none rest (b :: assign) code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.parse, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_loadCode_cons (b : Bool) (rest assign code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .loadCode) none (b :: rest) assign code val out) =
      some (evalEncCfg (some .loadCode) none rest assign (b :: code) val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.loadCode, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_loadCode_nil (assign code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .loadCode) none [] assign code val out) =
      some (evalEncCfg (some .fixAssign1) none [] assign code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.fixAssign1, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_writeFalse (inp assign code val : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .writeFalse) none inp assign code val []) =
      some (evalEncCfg none none inp assign code val [false]) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option EvalEncLabel), none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_parseTag0_false (rest inp assign val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .parseTag0) none inp assign (false :: rest) val out) =
      some (evalEncCfg (some .parseTag1F) none inp assign rest val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.parseTag1F, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_parseTag0_true (rest inp assign val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .parseTag0) none inp assign (true :: rest) val out) =
      some (evalEncCfg (some .parseTag1T) none inp assign rest val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.parseTag1T, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_parseTag0_nil (inp assign val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .parseTag0) none inp assign [] val out) =
      some (evalEncCfg (some .failClearInp) none inp assign [] val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.failClearInp, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_parseTag1F_var (rest inp assign val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .parseTag1F) none inp assign (false :: rest) val out) =
      some (evalEncCfg (some .parseNat) none inp assign rest val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.parseNat, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_parseTag1F_not (rest inp assign val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .parseTag1F) none inp assign (true :: rest) val out) =
      some (evalEncCfg (some .parseTag0) none (false :: false :: inp) assign rest val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.parseTag0, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_parseTag1T_and (rest inp assign val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .parseTag1T) none inp assign (false :: rest) val out) =
      some (evalEncCfg (some .parseTag0) none
        (true :: true :: true :: false :: inp) assign rest val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.parseTag0, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_parseTag1T_or (rest inp assign val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .parseTag1T) none inp assign (true :: rest) val out) =
      some (evalEncCfg (some .parseTag0) none
        (true :: true :: false :: true :: inp) assign rest val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.parseTag0, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_doNot (b : Bool) (rest inp assign code out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .doNot) none inp assign code (b :: rest) out) =
      some (evalEncCfg (some .afterSub) none inp assign code ((!b) :: rest) out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.afterSub, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_clearAssign_nil (inp code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .clearAssign) none inp [] code val out) =
      some (evalEncCfg none none inp [] code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option EvalEncLabel), none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_clearAssign_cons (b : Bool) (rest inp code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .clearAssign) none inp (b :: rest) code val out) =
      some (evalEncCfg (some .clearAssign) none inp rest code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.clearAssign, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

/-- Step budget for evaluating `encodeFormula φ` under assignment `σ` from
`parseTag0` through `afterSub` (result pushed on `val`). -/
def evalEncParseCost (φ : PropFormula) (σ : List Bool) : ℕ :=
  match φ with
  | .var n => 3 + (n + 1) + 1 + (min n σ.length) + 1
  | .not ψ => 3 + evalEncParseCost ψ σ + 1 + 1
  | .and ψ χ => 3 + 1 + evalEncParseCost ψ σ + 1 + evalEncParseCost χ σ + 1 + 1
  | .or ψ χ => 3 + 1 + evalEncParseCost ψ σ + 1 + evalEncParseCost χ σ + 1 + 1

/-- Generous poly bound used for `TM2ComputableInPolyTime` packaging. -/
noncomputable def evalEncodedTime : Polynomial ℕ :=
  20 * (Polynomial.X + 1) ^ 3

theorem evalEncodedTime_eval (n : ℕ) :
    evalEncodedTime.eval n = 20 * (n + 1) ^ 3 := by
  simp [evalEncodedTime]



theorem evalEnc_step_fixAssign1_cons (b : Bool) (rest inp code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .fixAssign1) none inp (b :: rest) code val out) =
      some (evalEncCfg (some .fixAssign1) none (b :: inp) rest code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.fixAssign1, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_fixAssign1_nil (inp code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .fixAssign1) none inp [] code val out) =
      some (evalEncCfg (some .fixAssign2) none inp [] code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.fixAssign2, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_fixAssign2_cons (b : Bool) (rest assign code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .fixAssign2) none (b :: rest) assign code val out) =
      some (evalEncCfg (some .fixAssign2) none rest assign code (b :: val) out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.fixAssign2, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_fixAssign2_nil (assign code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .fixAssign2) none [] assign code val out) =
      some (evalEncCfg (some .fixAssign3) none [] assign code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.fixAssign3, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_fixAssign3_cons (b : Bool) (rest inp assign code out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .fixAssign3) none inp assign code (b :: rest) out) =
      some (evalEncCfg (some .fixAssign3) none inp (b :: assign) code rest out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.fixAssign3, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_fixAssign3_nil (inp assign code out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .fixAssign3) none inp assign code [] out) =
      some (evalEncCfg (some .fixCode1) none inp assign code [] out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.fixCode1, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_fixCode1_cons (b : Bool) (rest inp assign val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .fixCode1) none inp assign (b :: rest) val out) =
      some (evalEncCfg (some .fixCode1) none (b :: inp) assign rest val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.fixCode1, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_fixCode1_nil (inp assign val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .fixCode1) none inp assign [] val out) =
      some (evalEncCfg (some .fixCode2) none inp assign [] val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.fixCode2, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_fixCode2_cons (b : Bool) (rest assign code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .fixCode2) none (b :: rest) assign code val out) =
      some (evalEncCfg (some .fixCode2) none rest assign code (b :: val) out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.fixCode2, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_fixCode2_nil (assign code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .fixCode2) none [] assign code val out) =
      some (evalEncCfg (some .fixCode3) none [] assign code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.fixCode3, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_fixCode3_cons (b : Bool) (rest inp assign code out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .fixCode3) none inp assign code (b :: rest) out) =
      some (evalEncCfg (some .fixCode3) none inp assign (b :: code) rest out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.fixCode3, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_fixCode3_nil (inp assign code out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .fixCode3) none inp assign code [] out) =
      some (evalEncCfg (some .parseTag0) none inp assign code [] out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.parseTag0, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_parseNat_true (rest inp assign val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .parseNat) none inp assign (true :: rest) val out) =
      some (evalEncCfg (some .skipOne) none inp assign rest val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.skipOne, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_parseNat_false (rest inp assign val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .parseNat) none inp assign (false :: rest) val out) =
      some (evalEncCfg (some .readResult) none inp assign rest val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.readResult, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_skipOne_cons (b : Bool) (rest inp code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .skipOne) none inp (b :: rest) code val out) =
      some (evalEncCfg (some .parseNat) none inp rest code val (b :: out)) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.parseNat, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_skipOne_nil (inp code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .skipOne) none inp [] code val out) =
      some (evalEncCfg (some .parseNat) none inp [] code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.parseNat, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_readResult_nil (inp code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .readResult) none inp [] code val out) =
      some (evalEncCfg (some .restoreAssign) none inp [] code (false :: val) out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.restoreAssign, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_readResult_cons (b : Bool) (rest inp code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .readResult) none inp (b :: rest) code val out) =
      some (evalEncCfg (some .restoreAssign) none inp (b :: rest) code (b :: val) out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.restoreAssign, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_restoreAssign_cons (b : Bool) (rest inp assign code val : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .restoreAssign) none inp assign code val (b :: rest)) =
      some (evalEncCfg (some .restoreAssign) none inp (b :: assign) code val rest) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.restoreAssign, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_restoreAssign_nil (inp assign code val : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .restoreAssign) none inp assign code val []) =
      some (evalEncCfg (some .afterSub) none inp assign code val []) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.afterSub, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_afterSub_root (assign code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .afterSub) none [] assign code val out) =
      some (evalEncCfg (some .checkDone) none [] assign code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.checkDone, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_afterSub_sibling (rest assign code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .afterSub) none (true :: true :: rest) assign code val out) =
      some (evalEncCfg (some .parseTag0) none rest assign code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.parseTag0, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_afterSub_and (rest assign code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .afterSub) none (true :: false :: rest) assign code val out) =
      some (evalEncCfg (some .doAndSave) none rest assign code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.doAndSave, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_afterSub_or (rest assign code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .afterSub) none (false :: true :: rest) assign code val out) =
      some (evalEncCfg (some .doOrSave) none rest assign code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.doOrSave, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_afterSub_not (rest assign code val out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .afterSub) none (false :: false :: rest) assign code val out) =
      some (evalEncCfg (some .doNot) none rest assign code val out) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.doNot, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_doAndSave (b : Bool) (rest inp assign code out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .doAndSave) none inp assign code (b :: rest) out) =
      some (evalEncCfg (some .doAndCombine) none inp assign code rest (b :: out)) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.doAndCombine, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_doAndCombine (bφ bψ : Bool) (rest inp assign code : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .doAndCombine) none inp assign code (bφ :: rest) [bψ]) =
      some (evalEncCfg (some .afterSub) none inp assign code ((bφ && bψ) :: rest) []) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.afterSub, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_doOrSave (b : Bool) (rest inp assign code out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .doOrSave) none inp assign code (b :: rest) out) =
      some (evalEncCfg (some .doOrCombine) none inp assign code rest (b :: out)) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.doOrCombine, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_doOrCombine (bφ bψ : Bool) (rest inp assign code : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .doOrCombine) none inp assign code (bφ :: rest) [bψ]) =
      some (evalEncCfg (some .afterSub) none inp assign code ((bφ || bψ) :: rest) []) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.afterSub, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]

theorem evalEnc_step_checkDone (b : Bool) (inp assign out : List Bool) :
    TM2.step evalEncodedComputer.m
      (evalEncCfg (some .checkDone) none inp assign [] [b] out) =
      some (evalEncCfg (some .clearAssign) none inp assign [] [] (b :: out)) := by
  simp [evalEncodedComputer, evalEncCfg, evalEncStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some EvalEncLabel.clearAssign, none, stk⟩ : evalEncodedComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, evalEncStk]


/-! ### Cluster D1 EvalsToInTime -/

set_option maxHeartbeats 8000000

def evalEnc_evals_one {l l' : Option EvalEncLabel} {v v' : Option Bool}
    {inp assign code val out inp' assign' code' val' out' : List Bool}
    (h : TM2.step evalEncodedComputer.m
      (evalEncCfg l v inp assign code val out) =
      some (evalEncCfg l' v' inp' assign' code' val' out')) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg l v inp assign code val out)
      (some (evalEncCfg l' v' inp' assign' code' val' out')) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (evalEncCfg l v inp assign code val out)).bind
        evalEncodedComputer.step =
      some (evalEncCfg l' v' inp' assign' code' val' out')
    simp only [FinTM2.step]
    exact h

/-- Parse first `encodePair` component into reversed assign. -/
noncomputable def evalEnc_evals_parse_first (xs rest assign code val out : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .parse) none (encodePair (xs, rest)) assign code val out)
      (some (evalEncCfg (some .parse) none (false :: rest) (xs.reverse ++ assign) code val out))
      (2 * xs.length) := by
  induction xs generalizing assign with
  | nil =>
      simpa [encodePair] using
        EvalsToInTime.refl evalEncodedComputer.step
          (evalEncCfg (some .parse) none (false :: rest) assign code val out)
  | cons b xs ih =>
      have hbits : encodePair (b :: xs, rest) = true :: b :: encodePair (xs, rest) := by
        simp [encodePair]
      rw [hbits]
      have h1 := evalEnc_evals_one (evalEnc_step_parse_true b (encodePair (xs, rest)) assign code val out)
      have h2 := evalEnc_evals_one (evalEnc_step_expectBit b (encodePair (xs, rest)) assign code val out)
      have h12 := EvalsToInTime.trans evalEncodedComputer.step 1 1 _ _ _ h1 h2
      have h3 := ih (b :: assign)
      have h := EvalsToInTime.trans evalEncodedComputer.step 2 (2 * xs.length) _ _ _ h12 h3
      simpa [List.reverse_cons, List.append_assoc, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc, two_mul] using h

noncomputable def evalEnc_evals_loadCode (ys assign code val out : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .loadCode) none ys assign code val out)
      (some (evalEncCfg (some .fixAssign1) none [] assign (ys.reverse ++ code) val out))
      (ys.length + 1) := by
  induction ys generalizing code with
  | nil =>
      simpa using evalEnc_evals_one (evalEnc_step_loadCode_nil assign code val out)
  | cons b ys ih =>
      have h1 := evalEnc_evals_one (evalEnc_step_loadCode_cons b ys assign code val out)
      have h2 := ih (b :: code)
      have h := EvalsToInTime.trans evalEncodedComputer.step 1 (ys.length + 1) _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using h

noncomputable def evalEnc_evals_fixAssign1 (assign inp code val out : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .fixAssign1) none inp assign code val out)
      (some (evalEncCfg (some .fixAssign2) none (assign.reverse ++ inp) [] code val out))
      (assign.length + 1) := by
  induction assign generalizing inp with
  | nil =>
      simpa using evalEnc_evals_one (evalEnc_step_fixAssign1_nil inp code val out)
  | cons b assign ih =>
      have h1 := evalEnc_evals_one (evalEnc_step_fixAssign1_cons b assign inp code val out)
      have h2 := ih (b :: inp)
      have h := EvalsToInTime.trans evalEncodedComputer.step 1 (assign.length + 1) _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using h

noncomputable def evalEnc_evals_fixAssign2 (inp assign code val out : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .fixAssign2) none inp assign code val out)
      (some (evalEncCfg (some .fixAssign3) none [] assign code (inp.reverse ++ val) out))
      (inp.length + 1) := by
  induction inp generalizing val with
  | nil =>
      simpa using evalEnc_evals_one (evalEnc_step_fixAssign2_nil assign code val out)
  | cons b inp ih =>
      have h1 := evalEnc_evals_one (evalEnc_step_fixAssign2_cons b inp assign code val out)
      have h2 := ih (b :: val)
      have h := EvalsToInTime.trans evalEncodedComputer.step 1 (inp.length + 1) _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using h

noncomputable def evalEnc_evals_fixAssign3 (val inp assign code out : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .fixAssign3) none inp assign code val out)
      (some (evalEncCfg (some .fixCode1) none inp (val.reverse ++ assign) code [] out))
      (val.length + 1) := by
  induction val generalizing assign with
  | nil =>
      simpa using evalEnc_evals_one (evalEnc_step_fixAssign3_nil inp assign code out)
  | cons b val ih =>
      have h1 := evalEnc_evals_one (evalEnc_step_fixAssign3_cons b val inp assign code out)
      have h2 := ih (b :: assign)
      have h := EvalsToInTime.trans evalEncodedComputer.step 1 (val.length + 1) _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using h

noncomputable def evalEnc_evals_fixCode1 (code inp assign val out : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .fixCode1) none inp assign code val out)
      (some (evalEncCfg (some .fixCode2) none (code.reverse ++ inp) assign [] val out))
      (code.length + 1) := by
  induction code generalizing inp with
  | nil =>
      simpa using evalEnc_evals_one (evalEnc_step_fixCode1_nil inp assign val out)
  | cons b code ih =>
      have h1 := evalEnc_evals_one (evalEnc_step_fixCode1_cons b code inp assign val out)
      have h2 := ih (b :: inp)
      have h := EvalsToInTime.trans evalEncodedComputer.step 1 (code.length + 1) _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using h

noncomputable def evalEnc_evals_fixCode2 (inp assign code val out : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .fixCode2) none inp assign code val out)
      (some (evalEncCfg (some .fixCode3) none [] assign code (inp.reverse ++ val) out))
      (inp.length + 1) := by
  induction inp generalizing val with
  | nil =>
      simpa using evalEnc_evals_one (evalEnc_step_fixCode2_nil assign code val out)
  | cons b inp ih =>
      have h1 := evalEnc_evals_one (evalEnc_step_fixCode2_cons b inp assign code val out)
      have h2 := ih (b :: val)
      have h := EvalsToInTime.trans evalEncodedComputer.step 1 (inp.length + 1) _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using h

noncomputable def evalEnc_evals_fixCode3 (val inp assign code out : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .fixCode3) none inp assign code val out)
      (some (evalEncCfg (some .parseTag0) none inp assign (val.reverse ++ code) [] out))
      (val.length + 1) := by
  induction val generalizing code with
  | nil =>
      simpa using evalEnc_evals_one (evalEnc_step_fixCode3_nil inp assign code out)
  | cons b val ih =>
      have h1 := evalEnc_evals_one (evalEnc_step_fixCode3_cons b val inp assign code out)
      have h2 := ih (b :: code)
      have h := EvalsToInTime.trans evalEncodedComputer.step 1 (val.length + 1) _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using h

/-- From loaded reversed stacks, reach `parseTag0` with forward `σ` and `φCode`. -/
noncomputable def evalEnc_evals_fix (σ φCode : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .fixAssign1) none [] σ.reverse φCode.reverse [] [])
      (some (evalEncCfg (some .parseTag0) none [] σ φCode [] []))
      (3 * σ.length + 3 * φCode.length + 6) := by
  have h1 := evalEnc_evals_fixAssign1 σ.reverse [] φCode.reverse [] []
  have h1' : EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .fixAssign1) none [] σ.reverse φCode.reverse [] [])
      (some (evalEncCfg (some .fixAssign2) none σ [] φCode.reverse [] []))
      (σ.reverse.length + 1) := by
    simpa [List.reverse_reverse] using h1
  have h2 := evalEnc_evals_fixAssign2 σ [] φCode.reverse [] []
  have h2' : EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .fixAssign2) none σ [] φCode.reverse [] [])
      (some (evalEncCfg (some .fixAssign3) none [] [] φCode.reverse σ.reverse []))
      (σ.length + 1) := by
    simpa [List.reverse_reverse] using h2
  have h12 := EvalsToInTime.trans evalEncodedComputer.step (σ.reverse.length + 1) (σ.length + 1)
    _ _ _ h1' h2'
  have h3 := evalEnc_evals_fixAssign3 σ.reverse [] [] φCode.reverse []
  have h3' : EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .fixAssign3) none [] [] φCode.reverse σ.reverse [])
      (some (evalEncCfg (some .fixCode1) none [] σ φCode.reverse [] []))
      (σ.reverse.length + 1) := by
    simpa [List.reverse_reverse] using h3
  have h123 := EvalsToInTime.trans evalEncodedComputer.step
    ((σ.length + 1) + (σ.reverse.length + 1)) (σ.reverse.length + 1) _ _ _ h12 h3'
  have h4 := evalEnc_evals_fixCode1 φCode.reverse [] σ [] []
  have h4' : EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .fixCode1) none [] σ φCode.reverse [] [])
      (some (evalEncCfg (some .fixCode2) none φCode σ [] [] []))
      (φCode.reverse.length + 1) := by
    simpa [List.reverse_reverse] using h4
  have h1234 := EvalsToInTime.trans evalEncodedComputer.step
    ((σ.reverse.length + 1) + ((σ.length + 1) + (σ.reverse.length + 1)))
    (φCode.reverse.length + 1) _ _ _ h123 h4'
  have h5 := evalEnc_evals_fixCode2 φCode σ [] [] []
  have h5' : EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .fixCode2) none φCode σ [] [] [])
      (some (evalEncCfg (some .fixCode3) none [] σ [] φCode.reverse []))
      (φCode.length + 1) := by
    simpa [List.reverse_reverse] using h5
  have h12345 := EvalsToInTime.trans evalEncodedComputer.step
    ((φCode.reverse.length + 1) +
      ((σ.reverse.length + 1) + ((σ.length + 1) + (σ.reverse.length + 1))))
    (φCode.length + 1) _ _ _ h1234 h5'
  have h6 := evalEnc_evals_fixCode3 φCode.reverse [] σ [] []
  have h6' : EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .fixCode3) none [] σ [] φCode.reverse [])
      (some (evalEncCfg (some .parseTag0) none [] σ φCode [] []))
      (φCode.reverse.length + 1) := by
    simpa [List.reverse_reverse] using h6
  have h := EvalsToInTime.trans evalEncodedComputer.step
    ((φCode.length + 1) + ((φCode.reverse.length + 1) +
      ((σ.reverse.length + 1) + ((σ.length + 1) + (σ.reverse.length + 1)))))
    (φCode.reverse.length + 1) _ _ _ h12345 h6'
  refine ⟨h.toEvalsTo, le_trans h.steps_le_m ?_⟩
  simp [List.length_reverse]; omega

/-- Load `encodePair (σ, φCode)` to `parseTag0` with forward stacks. -/
noncomputable def evalEnc_evals_load_encodePair (σ φCode : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .parse) none (encodePair (σ, φCode)) [] [] [] [])
      (some (evalEncCfg (some .parseTag0) none [] σ φCode [] []))
      (2 * σ.length + φCode.length + 2 + 3 * σ.length + 3 * φCode.length + 6) := by
  have hparse := evalEnc_evals_parse_first σ φCode [] [] [] []
  have htoLoad := evalEnc_evals_one (evalEnc_step_parse_false φCode σ.reverse [] [] [])
  have hload := evalEnc_evals_loadCode φCode σ.reverse [] [] []
  have h1 : EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .parse) none (encodePair (σ, φCode)) [] [] [] [])
      (some (evalEncCfg (some .parse) none (false :: φCode) σ.reverse [] [] []))
      (2 * σ.length) := by
    simpa [encodePair, List.append_assoc] using hparse
  have h12 := EvalsToInTime.trans evalEncodedComputer.step (2 * σ.length) 1 _ _ _ h1 htoLoad
  have h12' : EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .parse) none (encodePair (σ, φCode)) [] [] [] [])
      (some (evalEncCfg (some .loadCode) none φCode σ.reverse [] [] []))
      (2 * σ.length + 1) := by
    simpa [Nat.add_comm] using h12
  have h123 := EvalsToInTime.trans evalEncodedComputer.step (2 * σ.length + 1) (φCode.length + 1)
    _ _ _ h12' hload
  have h123' : EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .parse) none (encodePair (σ, φCode)) [] [] [] [])
      (some (evalEncCfg (some .fixAssign1) none [] σ.reverse φCode.reverse [] []))
      (φCode.length + 1 + (2 * σ.length + 1)) := by
    simpa [List.reverse_reverse, List.append_nil] using h123
  have hfix := evalEnc_evals_fix σ φCode
  have h := EvalsToInTime.trans evalEncodedComputer.step
    (φCode.length + 1 + (2 * σ.length + 1))
    (3 * σ.length + 3 * φCode.length + 6) _ _ _ h123' hfix
  refine ⟨h.toEvalsTo, le_trans h.steps_le_m ?_⟩
  omega

theorem getD_eq_headD_drop (σ : List Bool) (n : ℕ) :
    σ.getD n false = (σ.drop n).headD false := by
  induction n generalizing σ with
  | zero => cases σ <;> simp [List.getD, List.headD]
  | succ n ih => cases σ <;> simp [List.getD, List.drop, ih]

noncomputable def evalEnc_evals_skip (n : ℕ) (σ rest inp val out : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .parseNat) none inp σ (encodeNat n ++ rest) val out)
      (some (evalEncCfg (some .readResult) none inp (σ.drop n) rest val
        ((σ.take n).reverse ++ out)))
      (2 * n + 1) := by
  induction n generalizing σ out with
  | zero =>
      change EvalsToInTime _
        (evalEncCfg (some .parseNat) none inp σ (false :: rest) val out) _ 1
      simpa [encodeNat, List.take_zero, List.drop_zero, List.reverse_nil] using
        evalEnc_evals_one (evalEnc_step_parseNat_false rest inp σ val out)
  | succ n ih =>
      have hbits : encodeNat (n + 1) ++ rest = true :: (encodeNat n ++ rest) := by
        simp [encodeNat, List.replicate_succ]
      rw [hbits]
      have h1 := evalEnc_evals_one
        (evalEnc_step_parseNat_true (encodeNat n ++ rest) inp σ val out)
      cases σ with
      | nil =>
          have h2 := evalEnc_evals_one
            (evalEnc_step_skipOne_nil inp (encodeNat n ++ rest) val out)
          have h12 := EvalsToInTime.trans evalEncodedComputer.step 1 1 _ _ _ h1 h2
          have h3 := ih [] out
          have h := EvalsToInTime.trans evalEncodedComputer.step 2 (2 * n + 1) _ _ _ h12 h3
          simpa [List.drop_nil, List.take_nil, List.reverse_nil, Nat.mul_succ,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
      | cons b σ =>
          have h2 := evalEnc_evals_one
            (evalEnc_step_skipOne_cons b σ inp (encodeNat n ++ rest) val out)
          have h12 := EvalsToInTime.trans evalEncodedComputer.step 1 1 _ _ _ h1 h2
          have h3 := ih σ (b :: out)
          have h := EvalsToInTime.trans evalEncodedComputer.step 2 (2 * n + 1) _ _ _ h12 h3
          simpa [List.drop_succ_cons, List.take_succ_cons, List.reverse_cons,
            List.append_assoc, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using h

noncomputable def evalEnc_evals_restore (skipped inp assign code val : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .restoreAssign) none inp assign code val skipped)
      (some (evalEncCfg (some .afterSub) none inp (skipped.reverse ++ assign) code val []))
      (skipped.length + 1) := by
  induction skipped generalizing assign with
  | nil =>
      simpa using evalEnc_evals_one (evalEnc_step_restoreAssign_nil inp assign code val)
  | cons b skipped ih =>
      have h1 := evalEnc_evals_one
        (evalEnc_step_restoreAssign_cons b skipped inp assign code val)
      have h2 := ih (b :: assign)
      have h := EvalsToInTime.trans evalEncodedComputer.step 1 (skipped.length + 1) _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using h

noncomputable def evalEnc_evals_lookup (n : ℕ) (σ rest inp val : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .parseNat) none inp σ (encodeNat n ++ rest) val [])
      (some (evalEncCfg (some .afterSub) none inp σ rest (σ.getD n false :: val) []))
      (2 * n + 2 + (σ.take n).length + 1) := by
  have hskip := evalEnc_evals_skip n σ rest inp val []
  have hskip' : EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .parseNat) none inp σ (encodeNat n ++ rest) val [])
      (some (evalEncCfg (some .readResult) none inp (σ.drop n) rest val ((σ.take n).reverse)))
      (2 * n + 1) := by
    simpa [List.append_nil] using hskip
  have hread : EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .readResult) none inp (σ.drop n) rest val ((σ.take n).reverse))
      (some (evalEncCfg (some .restoreAssign) none inp (σ.drop n) rest
        ((σ.drop n).headD false :: val) ((σ.take n).reverse))) 1 := by
    cases hdrop : σ.drop n with
    | nil =>
        simpa [hdrop] using
          evalEnc_evals_one (evalEnc_step_readResult_nil inp rest val ((σ.take n).reverse))
    | cons b t =>
        simpa [hdrop, List.headD] using
          evalEnc_evals_one
            (evalEnc_step_readResult_cons b t inp rest val ((σ.take n).reverse))
  have h1 := EvalsToInTime.trans evalEncodedComputer.step (2 * n + 1) 1 _ _ _ hskip' hread
  have hrest := evalEnc_evals_restore (σ.take n).reverse inp (σ.drop n) rest
    ((σ.drop n).headD false :: val)
  have hrest' : EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .restoreAssign) none inp (σ.drop n) rest
        ((σ.drop n).headD false :: val) ((σ.take n).reverse))
      (some (evalEncCfg (some .afterSub) none inp σ rest
        ((σ.drop n).headD false :: val) []))
      ((σ.take n).reverse.length + 1) := by
    simpa [List.reverse_reverse, List.take_append_drop] using hrest
  have h := EvalsToInTime.trans evalEncodedComputer.step (1 + (2 * n + 1))
    ((σ.take n).reverse.length + 1) _ _ _ h1 hrest'
  have hget := getD_eq_headD_drop σ n
  convert h using 1 <;>
    simp [← hget, List.length_reverse, List.length_take, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] <;> omega

def evalEncParseCost' (φ : PropFormula) (σ : List Bool) : ℕ :=
  match φ with
  | .var n => 2 + (2 * n + 2 + (σ.take n).length + 1)
  | .not ψ => 2 + evalEncParseCost' ψ σ + 1 + 1
  | .and ψ χ => 2 + evalEncParseCost' ψ σ + 1 + evalEncParseCost' χ σ + 3
  | .or ψ χ => 2 + evalEncParseCost' ψ σ + 1 + evalEncParseCost' χ σ + 3

noncomputable def evalEnc_evals_parse_formula (φ : PropFormula) (σ rest inp val : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .parseTag0) none inp σ (encodeFormula φ ++ rest) val [])
      (some (evalEncCfg (some .afterSub) none inp σ rest (φ.evalOn σ :: val) []))
      (evalEncParseCost' φ σ) := by
  induction φ generalizing rest inp val with
  | var n =>
      have hbits : encodeFormula (.var n) ++ rest =
          false :: false :: (encodeNat n ++ rest) := by
        simp [encodeFormula]
      rw [hbits]
      have h0 := evalEnc_evals_one
        (evalEnc_step_parseTag0_false (false :: (encodeNat n ++ rest)) inp σ val [])
      have h1 := evalEnc_evals_one
        (evalEnc_step_parseTag1F_var (encodeNat n ++ rest) inp σ val [])
      have h01 := EvalsToInTime.trans evalEncodedComputer.step 1 1 _ _ _ h0 h1
      have hlookup := evalEnc_evals_lookup n σ rest inp val
      have h := EvalsToInTime.trans evalEncodedComputer.step 2
        (2 * n + 2 + (σ.take n).length + 1) _ _ _ h01 hlookup
      convert h using 1 <;>
        simp [PropFormula.evalOn, evalEncParseCost', Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] <;> omega
  | not ψ ih =>
      have hbits : encodeFormula (.not ψ) ++ rest =
          false :: true :: (encodeFormula ψ ++ rest) := by
        simp [encodeFormula]
      rw [hbits]
      have h0 := evalEnc_evals_one
        (evalEnc_step_parseTag0_false (true :: (encodeFormula ψ ++ rest)) inp σ val [])
      have h1 := evalEnc_evals_one
        (evalEnc_step_parseTag1F_not (encodeFormula ψ ++ rest) inp σ val [])
      have h01 := EvalsToInTime.trans evalEncodedComputer.step 1 1 _ _ _ h0 h1
      have hψ := ih rest (false :: false :: inp) val
      have h2 := EvalsToInTime.trans evalEncodedComputer.step 2 (evalEncParseCost' ψ σ)
        _ _ _ h01 hψ
      have hpop := evalEnc_evals_one
        (evalEnc_step_afterSub_not inp σ rest (ψ.evalOn σ :: val) [])
      have h3 := EvalsToInTime.trans evalEncodedComputer.step
        (evalEncParseCost' ψ σ + 2) 1 _ _ _ h2 hpop
      have hdo := evalEnc_evals_one
        (evalEnc_step_doNot (ψ.evalOn σ) val inp σ rest [])
      have h := EvalsToInTime.trans evalEncodedComputer.step
        (1 + (evalEncParseCost' ψ σ + 2)) 1 _ _ _ h3 hdo
      convert h using 1 <;>
        simp [PropFormula.evalOn, evalEncParseCost', Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] <;> omega
  | and ψ χ ihψ ihχ =>
      have hbits : encodeFormula (.and ψ χ) ++ rest =
          true :: false :: (encodeFormula ψ ++ (encodeFormula χ ++ rest)) := by
        simp [encodeFormula, List.append_assoc]
      rw [hbits]
      have h0 := evalEnc_evals_one
        (evalEnc_step_parseTag0_true
          (false :: (encodeFormula ψ ++ (encodeFormula χ ++ rest))) inp σ val [])
      have h1 := evalEnc_evals_one
        (evalEnc_step_parseTag1T_and
          (encodeFormula ψ ++ (encodeFormula χ ++ rest)) inp σ val [])
      have h01 := EvalsToInTime.trans evalEncodedComputer.step 1 1 _ _ _ h0 h1
      have hψ := ihψ (encodeFormula χ ++ rest)
        (true :: true :: true :: false :: inp) val
      have h2 := EvalsToInTime.trans evalEncodedComputer.step 2 (evalEncParseCost' ψ σ)
        _ _ _ h01 hψ
      have hsib := evalEnc_evals_one
        (evalEnc_step_afterSub_sibling (true :: false :: inp) σ
          (encodeFormula χ ++ rest) (ψ.evalOn σ :: val) [])
      have h3 := EvalsToInTime.trans evalEncodedComputer.step
        (evalEncParseCost' ψ σ + 2) 1 _ _ _ h2 hsib
      have hχ := ihχ rest (true :: false :: inp) (ψ.evalOn σ :: val)
      have h4 := EvalsToInTime.trans evalEncodedComputer.step
        (1 + (evalEncParseCost' ψ σ + 2)) (evalEncParseCost' χ σ) _ _ _ h3 hχ
      have hand := evalEnc_evals_one
        (evalEnc_step_afterSub_and inp σ rest
          (χ.evalOn σ :: ψ.evalOn σ :: val) [])
      have h5 := EvalsToInTime.trans evalEncodedComputer.step
        (evalEncParseCost' χ σ + (1 + (evalEncParseCost' ψ σ + 2))) 1 _ _ _ h4 hand
      have hsave := evalEnc_evals_one
        (evalEnc_step_doAndSave (χ.evalOn σ) (ψ.evalOn σ :: val) inp σ rest [])
      have h6 := EvalsToInTime.trans evalEncodedComputer.step
        (1 + (evalEncParseCost' χ σ + (1 + (evalEncParseCost' ψ σ + 2)))) 1
        _ _ _ h5 hsave
      have hcomb := evalEnc_evals_one
        (evalEnc_step_doAndCombine (ψ.evalOn σ) (χ.evalOn σ) val inp σ rest)
      have h := EvalsToInTime.trans evalEncodedComputer.step
        (1 + (1 + (evalEncParseCost' χ σ + (1 + (evalEncParseCost' ψ σ + 2))))) 1
        _ _ _ h6 hcomb
      convert h using 1 <;>
        simp [PropFormula.evalOn, evalEncParseCost', Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] <;> omega
  | or ψ χ ihψ ihχ =>
      have hbits : encodeFormula (.or ψ χ) ++ rest =
          true :: true :: (encodeFormula ψ ++ (encodeFormula χ ++ rest)) := by
        simp [encodeFormula, List.append_assoc]
      rw [hbits]
      have h0 := evalEnc_evals_one
        (evalEnc_step_parseTag0_true
          (true :: (encodeFormula ψ ++ (encodeFormula χ ++ rest))) inp σ val [])
      have h1 := evalEnc_evals_one
        (evalEnc_step_parseTag1T_or
          (encodeFormula ψ ++ (encodeFormula χ ++ rest)) inp σ val [])
      have h01 := EvalsToInTime.trans evalEncodedComputer.step 1 1 _ _ _ h0 h1
      have hψ := ihψ (encodeFormula χ ++ rest)
        (true :: true :: false :: true :: inp) val
      have h2 := EvalsToInTime.trans evalEncodedComputer.step 2 (evalEncParseCost' ψ σ)
        _ _ _ h01 hψ
      have hsib := evalEnc_evals_one
        (evalEnc_step_afterSub_sibling (false :: true :: inp) σ
          (encodeFormula χ ++ rest) (ψ.evalOn σ :: val) [])
      have h3 := EvalsToInTime.trans evalEncodedComputer.step
        (evalEncParseCost' ψ σ + 2) 1 _ _ _ h2 hsib
      have hχ := ihχ rest (false :: true :: inp) (ψ.evalOn σ :: val)
      have h4 := EvalsToInTime.trans evalEncodedComputer.step
        (1 + (evalEncParseCost' ψ σ + 2)) (evalEncParseCost' χ σ) _ _ _ h3 hχ
      have hor := evalEnc_evals_one
        (evalEnc_step_afterSub_or inp σ rest
          (χ.evalOn σ :: ψ.evalOn σ :: val) [])
      have h5 := EvalsToInTime.trans evalEncodedComputer.step
        (evalEncParseCost' χ σ + (1 + (evalEncParseCost' ψ σ + 2))) 1 _ _ _ h4 hor
      have hsave := evalEnc_evals_one
        (evalEnc_step_doOrSave (χ.evalOn σ) (ψ.evalOn σ :: val) inp σ rest [])
      have h6 := EvalsToInTime.trans evalEncodedComputer.step
        (1 + (evalEncParseCost' χ σ + (1 + (evalEncParseCost' ψ σ + 2)))) 1
        _ _ _ h5 hsave
      have hcomb := evalEnc_evals_one
        (evalEnc_step_doOrCombine (ψ.evalOn σ) (χ.evalOn σ) val inp σ rest)
      have h := EvalsToInTime.trans evalEncodedComputer.step
        (1 + (1 + (evalEncParseCost' χ σ + (1 + (evalEncParseCost' ψ σ + 2))))) 1
        _ _ _ h6 hcomb
      convert h using 1 <;>
        simp [PropFormula.evalOn, evalEncParseCost', Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] <;> omega

noncomputable def evalEnc_evals_clearAssign (assign inp code val out : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .clearAssign) none inp assign code val out)
      (some (evalEncCfg none none inp [] code val out))
      (assign.length + 1) := by
  induction assign with
  | nil =>
      simpa using evalEnc_evals_one (evalEnc_step_clearAssign_nil inp code val out)
  | cons b assign ih =>
      have h1 := evalEnc_evals_one
        (evalEnc_step_clearAssign_cons b assign inp code val out)
      have h := EvalsToInTime.trans evalEncodedComputer.step 1 (assign.length + 1)
        _ _ _ h1 ih
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Finish: empty markers, single val bit, clear assign, halt with `[b]`. -/
noncomputable def evalEnc_evals_finish (b : Bool) (σ : List Bool) :
    EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .afterSub) none [] σ [] [b] [])
      (some (haltList evalEncodedComputer [b]))
      (σ.length + 3) := by
  have h1 := evalEnc_evals_one (evalEnc_step_afterSub_root σ [] [b] [])
  have h2 := evalEnc_evals_one (evalEnc_step_checkDone b [] σ [])
  have h12 := EvalsToInTime.trans evalEncodedComputer.step 1 1 _ _ _ h1 h2
  have h3 := evalEnc_evals_clearAssign σ [] [] [] [b]
  have h := EvalsToInTime.trans evalEncodedComputer.step 2 (σ.length + 1) _ _ _ h12 h3
  simpa [evalEnc_haltList, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Full run on `encodePair (σ, encodeFormula φ)` yields `[φ.evalOn σ]`. -/
noncomputable def evalEncodedComputer_evals (σ : List Bool) (φ : PropFormula) :
    TM2OutputsInTime evalEncodedComputer (encodePair (σ, encodeFormula φ))
      (some [φ.evalOn σ])
      (2 * σ.length + (encodeFormula φ).length + 2 + 3 * σ.length +
        3 * (encodeFormula φ).length + 6 + evalEncParseCost' φ σ + σ.length + 3) := by
  have hload := evalEnc_evals_load_encodePair σ (encodeFormula φ)
  have hparse := evalEnc_evals_parse_formula φ σ [] [] []
  have hparse' : EvalsToInTime evalEncodedComputer.step
      (evalEncCfg (some .parseTag0) none [] σ (encodeFormula φ) [] [])
      (some (evalEncCfg (some .afterSub) none [] σ [] [φ.evalOn σ] []))
      (evalEncParseCost' φ σ) := by
    simpa [List.append_nil] using hparse
  have h1 := EvalsToInTime.trans evalEncodedComputer.step
    (2 * σ.length + (encodeFormula φ).length + 2 + 3 * σ.length +
      3 * (encodeFormula φ).length + 6)
    (evalEncParseCost' φ σ) _ _ _ hload hparse'
  have hfin := evalEnc_evals_finish (φ.evalOn σ) σ
  have h := EvalsToInTime.trans evalEncodedComputer.step
    (evalEncParseCost' φ σ +
      (2 * σ.length + (encodeFormula φ).length + 2 + 3 * σ.length +
        3 * (encodeFormula φ).length + 6))
    (σ.length + 3) _ _ _ h1 hfin
  have h' : EvalsToInTime evalEncodedComputer.step
      (initList evalEncodedComputer (encodePair (σ, encodeFormula φ)))
      (some (haltList evalEncodedComputer [φ.evalOn σ]))
      ((σ.length + 3) + (evalEncParseCost' φ σ +
        (2 * σ.length + (encodeFormula φ).length + 2 + 3 * σ.length +
          3 * (encodeFormula φ).length + 6))) := by
    simpa [evalEnc_initList, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  refine ⟨h'.toEvalsTo, le_trans h'.steps_le_m ?_⟩
  omega

theorem length_encodeFormula_var (n : ℕ) :
    (encodeFormula (.var n)).length = n + 3 := by
  simp [encodeFormula, encodeNat]

/-- Crude step-cost bound used only for polyTime packaging. -/
theorem evalEncParseCost'_le (φ : PropFormula) (σ : List Bool) :
    evalEncParseCost' φ σ ≤
      8 * ((encodeFormula φ).length + 1) * (σ.length + 1) := by
  induction φ with
  | var n =>
      have hlen : (encodeFormula (.var n)).length = n + 3 := length_encodeFormula_var n
      have htake : (List.take n σ).length ≤ n := by
        simpa [List.length_take] using Nat.min_le_left n σ.length
      have hform :
          evalEncParseCost' (.var n) σ = 5 + 2 * n + (List.take n σ).length := by
        simp [evalEncParseCost']; ring
      calc
        evalEncParseCost' (.var n) σ = 5 + 2 * n + (List.take n σ).length := hform
        _ ≤ 5 + 2 * n + n := by omega
        _ = 5 + 3 * n := by ring
        _ ≤ 8 * (n + 4) * (σ.length + 1) := by
          have : 1 ≤ σ.length + 1 := by omega
          nlinarith
        _ = 8 * ((encodeFormula (.var n)).length + 1) * (σ.length + 1) := by
          simp [hlen]
  | not ψ ih =>
      have hlen := length_encodeFormula_not ψ
      have hform :
          evalEncParseCost' (.not ψ) σ = evalEncParseCost' ψ σ + 4 := by
        simp [evalEncParseCost']; ring
      calc
        evalEncParseCost' (.not ψ) σ = evalEncParseCost' ψ σ + 4 := hform
        _ ≤ 8 * ((encodeFormula ψ).length + 1) * (σ.length + 1) + 4 := by omega
        _ ≤ 8 * ((encodeFormula ψ).length + 3) * (σ.length + 1) := by
          have : 4 ≤ 16 * (σ.length + 1) := by omega
          have :
              8 * ((encodeFormula ψ).length + 3) * (σ.length + 1) =
                8 * ((encodeFormula ψ).length + 1) * (σ.length + 1) +
                  16 * (σ.length + 1) := by ring
          omega
        _ = 8 * ((encodeFormula (.not ψ)).length + 1) * (σ.length + 1) := by
          simp [hlen]
  | and ψ χ ihψ ihχ =>
      have hlen := length_encodeFormula_and ψ χ
      have hform :
          evalEncParseCost' (.and ψ χ) σ =
            evalEncParseCost' ψ σ + evalEncParseCost' χ σ + 6 := by
        simp [evalEncParseCost']; ring
      calc
        evalEncParseCost' (.and ψ χ) σ =
            evalEncParseCost' ψ σ + evalEncParseCost' χ σ + 6 := hform
        _ ≤ 8 * ((encodeFormula ψ).length + 1) * (σ.length + 1) +
              8 * ((encodeFormula χ).length + 1) * (σ.length + 1) + 6 := by
          omega
        _ ≤ 8 * ((encodeFormula ψ).length + (encodeFormula χ).length + 3) *
              (σ.length + 1) := by
          have :
              8 * ((encodeFormula ψ).length + 1) * (σ.length + 1) +
                8 * ((encodeFormula χ).length + 1) * (σ.length + 1) + 6 =
              8 * ((encodeFormula ψ).length + (encodeFormula χ).length + 2) *
                (σ.length + 1) + 6 := by ring
          have : 6 ≤ 8 * (σ.length + 1) := by omega
          have :
              8 * ((encodeFormula ψ).length + (encodeFormula χ).length + 3) *
                (σ.length + 1) =
              8 * ((encodeFormula ψ).length + (encodeFormula χ).length + 2) *
                (σ.length + 1) + 8 * (σ.length + 1) := by ring
          omega
        _ = 8 * ((encodeFormula (.and ψ χ)).length + 1) * (σ.length + 1) := by
          simp [hlen]
  | or ψ χ ihψ ihχ =>
      have hlen := length_encodeFormula_or ψ χ
      have hform :
          evalEncParseCost' (.or ψ χ) σ =
            evalEncParseCost' ψ σ + evalEncParseCost' χ σ + 6 := by
        simp [evalEncParseCost']; ring
      calc
        evalEncParseCost' (.or ψ χ) σ =
            evalEncParseCost' ψ σ + evalEncParseCost' χ σ + 6 := hform
        _ ≤ 8 * ((encodeFormula ψ).length + 1) * (σ.length + 1) +
              8 * ((encodeFormula χ).length + 1) * (σ.length + 1) + 6 := by
          omega
        _ ≤ 8 * ((encodeFormula ψ).length + (encodeFormula χ).length + 3) *
              (σ.length + 1) := by
          have :
              8 * ((encodeFormula ψ).length + 1) * (σ.length + 1) +
                8 * ((encodeFormula χ).length + 1) * (σ.length + 1) + 6 =
              8 * ((encodeFormula ψ).length + (encodeFormula χ).length + 2) *
                (σ.length + 1) + 6 := by ring
          have : 6 ≤ 8 * (σ.length + 1) := by omega
          have :
              8 * ((encodeFormula ψ).length + (encodeFormula χ).length + 3) *
                (σ.length + 1) =
              8 * ((encodeFormula ψ).length + (encodeFormula χ).length + 2) *
                (σ.length + 1) + 8 * (σ.length + 1) := by ring
          omega
        _ = 8 * ((encodeFormula (.or ψ χ)).length + 1) * (σ.length + 1) := by
          simp [hlen]

/-- Success packaging on `encodeFormula` images. -/
noncomputable def evalEncodedComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun p : List Bool × PropFormula => encodePair (p.1, encodeFormula p.2))
      bitEnc
      (fun p => p.2.evalOn p.1) where
  tm := evalEncodedComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := evalEncodedTime
  outputsFun p := by
    rcases p with ⟨σ, φ⟩
    change TM2OutputsInTime evalEncodedComputer
      (List.map id (encodePair (σ, encodeFormula φ)))
      (some (List.map id (bitEnc (φ.evalOn σ))))
      (evalEncodedTime.eval (encodePair (σ, encodeFormula φ)).length)
    simp only [List.map_id, bitEnc, evalEncodedTime_eval]
    have h := evalEncodedComputer_evals σ φ
    refine ⟨h.toEvalsTo, le_trans h.steps_le_m ?_⟩
    have hlen := length_encodePair (σ, encodeFormula φ)
    have hcost := evalEncParseCost'_le φ σ
    let N := (encodePair (σ, encodeFormula φ)).length
    have hN : N = 2 * σ.length + 1 + (encodeFormula φ).length := hlen
    have hs : σ.length ≤ N := by omega
    have hp : (encodeFormula φ).length ≤ N := by omega
    have hc : evalEncParseCost' φ σ ≤ 8 * (N + 1) * (N + 1) := by
      refine Nat.le_trans hcost ?_
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 8 (by omega)) (by omega)
    have hbud :
        2 * σ.length + (encodeFormula φ).length + 2 + 3 * σ.length +
          3 * (encodeFormula φ).length + 6 + evalEncParseCost' φ σ + σ.length + 3 ≤
        6 * N + 11 + 8 * (N + 1) * (N + 1) := by omega
    have hpoly : 6 * N + 11 + 8 * (N + 1) * (N + 1) ≤ 20 * (N + 1) ^ 3 := by
      cases N with
      | zero => decide
      | succ k => ring_nf; nlinarith
    have : 2 * σ.length + (encodeFormula φ).length + 2 + 3 * σ.length +
        3 * (encodeFormula φ).length + 6 + evalEncParseCost' φ σ + σ.length + 3 ≤
        20 * (N + 1) ^ 3 := hbud.trans hpoly
    simpa [N] using this

theorem evalEncoded_computableInPolyTime :
    Nonempty (TM2ComputableInPolyTime
      (fun p : List Bool × PropFormula => encodePair (p.1, encodeFormula p.2))
      bitEnc
      (fun p => p.2.evalOn p.1)) :=
  ⟨evalEncodedComputableInPolyTime⟩

/-! ## Cluster D2: index-loop sequencer (functional + one-iter FinTM2)

Plan (`validatesTautology_by_index_pad`): length gate
`table.length = 2^(maxVar+1)` via `bitsEqualPair` / `lengthBitsEqPow2`, then
for `i` from `0` to `|table|-1`:
  `σ := padBitsLE (maxVar+1) (natBitsLE i)` (= `assignmentAt`)
  `b := φ.evalOn σ` (via `evalEncodedComputer`)
  if `table[i] ≠ b` or `b = false`, reject `[true]`
After all pass, accept `false :: φCode` (`prefixFalseCopyComputer`).

This cluster certifies the functional loop and a FinTM2 for the per-index
bit compare (`indexStepBitsComputer`). Remaining sequencer glue: nest
`padBitsComputer` then `evalEncodedComputer` then `indexStepBitsComputer`
under `|table|` fuel, then branch to reject / accept slices. -/

/-- One index check: table bit equals `evalOn` of the padded assignment, and
is `true`. -/
def indexStepOk (n i : ℕ) (φ : PropFormula) (tableBit : Bool) : Bool :=
  let b := φ.evalOn (padBitsLE n (natBitsLE i))
  decide (tableBit = b ∧ b = true)

theorem indexStepOk_iff (n i : ℕ) (φ : PropFormula) (tableBit : Bool) :
    indexStepOk n i φ tableBit = true ↔
      tableBit = φ.evalOn (padBitsLE n (natBitsLE i)) ∧
        φ.evalOn (padBitsLE n (natBitsLE i)) = true := by
  simp [indexStepOk]

theorem indexStepOk_iff_assignmentAt (n i : ℕ) (φ : PropFormula)
    (tableBit : Bool) (hi : i < 2 ^ n) :
    indexStepOk n i φ tableBit = true ↔
      tableBit = φ.evalOn (assignmentAt n i) ∧
        φ.evalOn (assignmentAt n i) = true := by
  simpa [assignmentAt_eq_padBitsLE hi] using indexStepOk_iff n i φ tableBit

/-- Bit-level form of one index check (eval bit already computed). -/
def indexStepBitsOk (evalBit expected : Bool) : Bool :=
  decide (expected = evalBit ∧ evalBit = true)

theorem indexStepBitsOk_iff (evalBit expected : Bool) :
    indexStepBitsOk evalBit expected = true ↔
      expected = evalBit ∧ evalBit = true := by
  simp [indexStepBitsOk]

theorem indexStepOk_eq_bits (n i : ℕ) (φ : PropFormula) (tableBit : Bool) :
    indexStepOk n i φ tableBit =
      indexStepBitsOk (φ.evalOn (padBitsLE n (natBitsLE i))) tableBit := by
  simp [indexStepOk, indexStepBitsOk]

/-- Reject `[true]` / step-ok `[false]` tape for a bit pair. -/
def indexStepBitsResult (evalBit expected : Bool) : List Bool :=
  if indexStepBitsOk evalBit expected then [false] else [true]

theorem indexStepBitsResult_ok {evalBit expected : Bool}
    (h : indexStepBitsOk evalBit expected = true) :
    indexStepBitsResult evalBit expected = [false] := by
  simp [indexStepBitsResult, h]

theorem indexStepBitsResult_reject {evalBit expected : Bool}
    (h : indexStepBitsOk evalBit expected = false) :
    indexStepBitsResult evalBit expected = [true] := by
  simp [indexStepBitsResult, h]

/-- Fuel-bounded index loop: checks indices `0 .. fuel-1` against `table`. -/
def indexValidateFuel (n : ℕ) (φ : PropFormula) (table : List Bool) : ℕ → Bool
  | 0 => true
  | fuel + 1 =>
      indexValidateFuel n φ table fuel &&
        if h : fuel < table.length then
          indexStepOk n fuel φ table[fuel]
        else
          false

theorem indexValidateFuel_zero (n : ℕ) (φ : PropFormula) (table : List Bool) :
    indexValidateFuel n φ table 0 = true := rfl

theorem indexValidateFuel_succ (n : ℕ) (φ : PropFormula) (table : List Bool)
    (fuel : ℕ) :
    indexValidateFuel n φ table (fuel + 1) =
      (indexValidateFuel n φ table fuel &&
        if h : fuel < table.length then indexStepOk n fuel φ table[fuel]
        else false) := rfl

/-- Loop step: extending fuel by one preserves success iff the new index passes. -/
theorem indexValidateFuel_succ_iff (n : ℕ) (φ : PropFormula) (table : List Bool)
    (fuel : ℕ) (hfuel : fuel < table.length) :
    indexValidateFuel n φ table (fuel + 1) = true ↔
      indexValidateFuel n φ table fuel = true ∧
        indexStepOk n fuel φ table[fuel] = true := by
  simp [indexValidateFuel_succ, hfuel]

/-- Prefix characterization of the fuel loop. -/
theorem indexValidateFuel_iff (n : ℕ) (φ : PropFormula) (table : List Bool)
    (fuel : ℕ) (hfuel : fuel ≤ table.length) :
    indexValidateFuel n φ table fuel = true ↔
      ∀ (i : ℕ) (hi : i < fuel),
        indexStepOk n i φ (table[i]'(Nat.lt_of_lt_of_le hi hfuel)) = true := by
  induction fuel with
  | zero =>
      constructor
      · intro _ i hi
        cases hi
      · intro
        simp [indexValidateFuel]
  | succ fuel ih =>
      have hfuel' : fuel ≤ table.length := Nat.le_of_succ_le hfuel
      have hlt : fuel < table.length := Nat.lt_of_succ_le hfuel
      constructor
      · intro h i hi
        have hand := (indexValidateFuel_succ_iff n φ table fuel hlt).mp h
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt_i | rfl
        · exact (ih hfuel').mp hand.1 i hlt_i
        · exact hand.2
      · intro hAll
        refine (indexValidateFuel_succ_iff n φ table fuel hlt).mpr ⟨?_, ?_⟩
        · exact (ih hfuel').mpr fun i hi => hAll i (Nat.lt_succ_of_lt hi)
        · exact hAll fuel (Nat.lt_succ_self fuel)

/-- Length gate plus full `|table|` fuel loop. -/
def indexValidate (φ : PropFormula) (table : List Bool) : Bool :=
  lengthGateOk φ table &&
    indexValidateFuel (φ.maxVar + 1) φ table table.length

theorem indexValidate_iff (φ : PropFormula) (table : List Bool) :
    indexValidate φ table = true ↔ validatesTautology_by_index φ table := by
  simp only [indexValidate, Bool.and_eq_true, lengthGateOk_iff]
  constructor
  · intro ⟨hlen, hfuel⟩
    refine (validatesTautology_by_index_pad φ table).mpr ⟨hlen, ?_⟩
    intro i hi
    have hprefix :=
      (indexValidateFuel_iff (φ.maxVar + 1) φ table table.length le_rfl).mp
        hfuel i hi
    have hi' : i < 2 ^ (φ.maxVar + 1) := by simpa [hlen] using hi
    have hstep := (indexStepOk_iff_assignmentAt _ _ φ table[i] hi').mp hprefix
    -- hstep: table[i] = evalOn(assignmentAt) ∧ evalOn(assignmentAt) = true
    -- target: table[i] = evalOn(padBitsLE) ∧ table[i] = true
    have heq : table[i] = φ.evalOn (assignmentAt (φ.maxVar + 1) i) := hstep.1
    have htrue : table[i] = true := heq.trans hstep.2
    have heq' : table[i] =
        φ.evalOn (padBitsLE (φ.maxVar + 1) (natBitsLE i)) := by
      rwa [assignmentAt_eq_padBitsLE hi'] at heq
    exact ⟨heq', htrue⟩
  · intro h
    have hpad := (validatesTautology_by_index_pad φ table).mp h
    refine ⟨hpad.1, ?_⟩
    refine (indexValidateFuel_iff (φ.maxVar + 1) φ table table.length
      le_rfl).mpr ?_
    intro i hi
    have hpair := hpad.2 i hi
    have hi' : i < 2 ^ (φ.maxVar + 1) := by simpa [hpad.1] using hi
    -- hpair: table[i] = evalOn(padBitsLE) ∧ table[i] = true
    -- target indexStepOk via assignmentAt
    refine (indexStepOk_iff_assignmentAt _ _ φ table[i] hi').mpr ?_
    have heq : table[i] =
        φ.evalOn (padBitsLE (φ.maxVar + 1) (natBitsLE i)) := hpair.1
    have heq' : table[i] = φ.evalOn (assignmentAt (φ.maxVar + 1) i) := by
      rwa [← assignmentAt_eq_padBitsLE hi'] at heq
    exact ⟨heq', heq'.symm.trans hpair.2⟩

theorem indexValidate_iff_pad (φ : PropFormula) (table : List Bool) :
    indexValidate φ table = true ↔
      table.length = 2 ^ (φ.maxVar + 1) ∧
        ∀ (i : ℕ) (hi : i < table.length),
          table[i] =
              φ.evalOn (padBitsLE (φ.maxVar + 1) (natBitsLE i)) ∧
            table[i] = true := by
  rw [indexValidate_iff, validatesTautology_by_index_pad]

/-- Decoded `(φCode, table)` validation via the index fuel loop. -/
def indexValidateResult (φCode table : List Bool) : List Bool :=
  match decodeFormula φCode with
  | none => [true]
  | some φ =>
      if indexValidate φ table then false :: φCode else [true]

theorem indexValidateResult_eq_validatesTautologyResult
    (φCode table : List Bool) :
    indexValidateResult φCode table =
      validatesTautologyResult φCode table := by
  simp only [indexValidateResult, validatesTautologyResult]
  cases h : decodeFormula φCode with
  | none => rfl
  | some φ =>
      have hiff := indexValidate_iff φ table
      have hval := validatesTautology_iff_by_index φ table
      by_cases hidx : indexValidate φ table = true
      · have : validatesTautology φ table := by
          exact hval.mpr (hiff.mp hidx)
        simp [h, hidx, this]
      · have : ¬ validatesTautology φ table := by
          intro hv
          exact hidx (hiff.mpr (hval.mp hv))
        simp [h, hidx, this]

/-- Length-gate Bool on `(n, table)` via the certified bitsEqualPair path. -/
def indexLengthGate (n : ℕ) (table : List Bool) : Bool :=
  bitsEqualPair (lengthBitsLE table, pow2BitsLE n)

theorem indexLengthGate_iff (n : ℕ) (table : List Bool) :
    indexLengthGate n table = true ↔ table.length = 2 ^ n := by
  simpa [indexLengthGate] using bitsEqualPair_iff_lengthGate n table

theorem indexLengthGate_eq_lengthGateOk (φ : PropFormula) (table : List Bool) :
    indexLengthGate (φ.maxVar + 1) table = lengthGateOk φ table := by
  simp [indexLengthGate, lengthGateOk_eq_lengthBitsEqPow2,
    lengthBitsEqPow2_eq_bitsEqual, bitsEqualPair]

/-! ### Cluster D2 one-iter FinTM2: `indexStepBitsComputer`

Input `encodePair ([evalBit], [expected])`. Output `[false]` when both bits
are `true` (step ok), else `[true]` (reject), matching `indexStepBitsResult`. -/

open TM2.Stmt

inductive IdxStepStack where
  | inp | out
  deriving DecidableEq, Repr

instance : Fintype IdxStepStack where
  elems := {.inp, .out}
  complete s := by cases s <;> simp

inductive IdxStepLabel where
  | parseL | readEval | sep | readExp | writeOk | writeRej | drain
  deriving DecidableEq, Repr

instance : Fintype IdxStepLabel where
  elems :=
    {.parseL, .readEval, .sep, .readExp, .writeOk, .writeRej, .drain}
  complete s := by cases s <;> simp

/-- FinTM2 realizing `indexStepBitsResult` on `encodePair ([evalBit], [expected])`. -/
def indexStepBitsComputer : FinTM2 where
  K := IdxStepStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := IdxStepLabel
  main := .parseL
  σ := Option Bool
  initialState := none
  m
    | .parseL =>
        pop IdxStepStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = some true))
            (load (fun _ => none) <| goto fun _ => IdxStepLabel.readEval)
            (load (fun _ => none) <| goto fun _ => IdxStepLabel.drain)
    | .readEval =>
        pop IdxStepStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => IdxStepLabel.drain)
            (goto fun _ => IdxStepLabel.sep)
    | .sep =>
        pop IdxStepStack.inp (fun s o =>
            match s, o with
            | some evalBit, some false => some evalBit
            | _, _ => none) <|
          branch (fun s => decide (s = none))
            (goto fun _ => IdxStepLabel.drain)
            (goto fun _ => IdxStepLabel.readExp)
    | .readExp =>
        pop IdxStepStack.inp (fun s o =>
            match s, o with
            | some true, some true => some true
            | _, _ => none) <|
          branch (fun s => decide (s = some true))
            (load (fun _ => none) <| goto fun _ => IdxStepLabel.writeOk)
            (load (fun _ => none) <| goto fun _ => IdxStepLabel.writeRej)
    | .writeOk =>
        pop IdxStepStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push IdxStepStack.out (fun _ => false) <|
              load (fun _ => none) halt)
            (load (fun _ => none) <| goto fun _ => IdxStepLabel.writeOk)
    | .writeRej =>
        pop IdxStepStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push IdxStepStack.out (fun _ => true) <|
              load (fun _ => none) halt)
            (load (fun _ => none) <| goto fun _ => IdxStepLabel.writeRej)
    | .drain =>
        pop IdxStepStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push IdxStepStack.out (fun _ => true) <|
              load (fun _ => none) halt)
            (load (fun _ => none) <| goto fun _ => IdxStepLabel.drain)

def idxStepStk (inp out : List Bool) : IdxStepStack → List Bool
  | .inp => inp
  | .out => out

def idxStepCfg (l : Option IdxStepLabel) (v : Option Bool)
    (inp out : List Bool) : indexStepBitsComputer.Cfg :=
  ⟨l, v, idxStepStk inp out⟩

theorem indexStepBits_initList (s : List Bool) :
    initList indexStepBitsComputer s =
      idxStepCfg (some .parseL) none s [] := by
  refine congrArg (fun stk =>
      (⟨some IdxStepLabel.parseL, none, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [indexStepBitsComputer, idxStepStk]

theorem indexStepBits_haltList (out : List Bool) :
    haltList indexStepBitsComputer out =
      idxStepCfg none none [] out := by
  refine congrArg (fun stk =>
      (⟨(none : Option IdxStepLabel), none, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [indexStepBitsComputer, idxStepStk]

/-! ### indexStepBitsComputer step lemmas -/

theorem idxStep_step_parseL_true (rest out : List Bool) :
    TM2.step indexStepBitsComputer.m
      (idxStepCfg (some .parseL) none (true :: rest) out) =
      some (idxStepCfg (some .readEval) none rest out) := by
  simp [indexStepBitsComputer, idxStepCfg, idxStepStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some IdxStepLabel.readEval, none, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, idxStepStk]

theorem idxStep_step_parseL_false (rest out : List Bool) :
    TM2.step indexStepBitsComputer.m
      (idxStepCfg (some .parseL) none (false :: rest) out) =
      some (idxStepCfg (some .drain) none rest out) := by
  simp [indexStepBitsComputer, idxStepCfg, idxStepStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some IdxStepLabel.drain, none, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, idxStepStk]

theorem idxStep_step_parseL_nil (out : List Bool) :
    TM2.step indexStepBitsComputer.m
      (idxStepCfg (some .parseL) none [] out) =
      some (idxStepCfg (some .drain) none [] out) := by
  simp [indexStepBitsComputer, idxStepCfg, idxStepStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some IdxStepLabel.drain, none, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, idxStepStk]

theorem idxStep_step_readEval (a : Bool) (rest out : List Bool) :
    TM2.step indexStepBitsComputer.m
      (idxStepCfg (some .readEval) none (a :: rest) out) =
      some (idxStepCfg (some .sep) (some a) rest out) := by
  simp [indexStepBitsComputer, idxStepCfg, idxStepStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some IdxStepLabel.sep, some a, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, idxStepStk]

theorem idxStep_step_readEval_nil (v : Option Bool) (out : List Bool) :
    TM2.step indexStepBitsComputer.m
      (idxStepCfg (some .readEval) v [] out) =
      some (idxStepCfg (some .drain) none [] out) := by
  simp [indexStepBitsComputer, idxStepCfg, idxStepStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some IdxStepLabel.drain, none, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, idxStepStk]

theorem idxStep_step_sep_false (evalBit : Bool) (rest out : List Bool) :
    TM2.step indexStepBitsComputer.m
      (idxStepCfg (some .sep) (some evalBit) (false :: rest) out) =
      some (idxStepCfg (some .readExp) (some evalBit) rest out) := by
  simp [indexStepBitsComputer, idxStepCfg, idxStepStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some IdxStepLabel.readExp, some evalBit, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, idxStepStk]

theorem idxStep_step_sep_true (evalBit : Bool) (rest out : List Bool) :
    TM2.step indexStepBitsComputer.m
      (idxStepCfg (some .sep) (some evalBit) (true :: rest) out) =
      some (idxStepCfg (some .drain) none rest out) := by
  simp [indexStepBitsComputer, idxStepCfg, idxStepStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some IdxStepLabel.drain, none, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, idxStepStk]

theorem idxStep_step_readExp_bothTrue (rest out : List Bool) :
    TM2.step indexStepBitsComputer.m
      (idxStepCfg (some .readExp) (some true) (true :: rest) out) =
      some (idxStepCfg (some .writeOk) none rest out) := by
  simp [indexStepBitsComputer, idxStepCfg, idxStepStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some IdxStepLabel.writeOk, none, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, idxStepStk]

theorem idxStep_step_readExp_evalFalse (exp : Bool) (rest out : List Bool) :
    TM2.step indexStepBitsComputer.m
      (idxStepCfg (some .readExp) (some false) (exp :: rest) out) =
      some (idxStepCfg (some .writeRej) none rest out) := by
  simp [indexStepBitsComputer, idxStepCfg, idxStepStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some IdxStepLabel.writeRej, none, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, idxStepStk]

theorem idxStep_step_readExp_expFalse (rest out : List Bool) :
    TM2.step indexStepBitsComputer.m
      (idxStepCfg (some .readExp) (some true) (false :: rest) out) =
      some (idxStepCfg (some .writeRej) none rest out) := by
  simp [indexStepBitsComputer, idxStepCfg, idxStepStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some IdxStepLabel.writeRej, none, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, idxStepStk]

theorem idxStep_step_writeOk_nil (out : List Bool) :
    TM2.step indexStepBitsComputer.m
      (idxStepCfg (some .writeOk) none [] out) =
      some (idxStepCfg none none [] (false :: out)) := by
  simp [indexStepBitsComputer, idxStepCfg, idxStepStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option IdxStepLabel), none, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, idxStepStk]

theorem idxStep_step_writeOk_cons (b : Bool) (rest out : List Bool) :
    TM2.step indexStepBitsComputer.m
      (idxStepCfg (some .writeOk) none (b :: rest) out) =
      some (idxStepCfg (some .writeOk) none rest out) := by
  simp [indexStepBitsComputer, idxStepCfg, idxStepStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some IdxStepLabel.writeOk, none, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, idxStepStk]

theorem idxStep_step_writeRej_nil (out : List Bool) :
    TM2.step indexStepBitsComputer.m
      (idxStepCfg (some .writeRej) none [] out) =
      some (idxStepCfg none none [] (true :: out)) := by
  simp [indexStepBitsComputer, idxStepCfg, idxStepStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option IdxStepLabel), none, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, idxStepStk]

theorem idxStep_step_writeRej_cons (b : Bool) (rest out : List Bool) :
    TM2.step indexStepBitsComputer.m
      (idxStepCfg (some .writeRej) none (b :: rest) out) =
      some (idxStepCfg (some .writeRej) none rest out) := by
  simp [indexStepBitsComputer, idxStepCfg, idxStepStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some IdxStepLabel.writeRej, none, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, idxStepStk]

theorem idxStep_step_drain_nil (out : List Bool) :
    TM2.step indexStepBitsComputer.m
      (idxStepCfg (some .drain) none [] out) =
      some (idxStepCfg none none [] (true :: out)) := by
  simp [indexStepBitsComputer, idxStepCfg, idxStepStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option IdxStepLabel), none, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, idxStepStk]

theorem idxStep_step_drain_cons (b : Bool) (rest out : List Bool) :
    TM2.step indexStepBitsComputer.m
      (idxStepCfg (some .drain) none (b :: rest) out) =
      some (idxStepCfg (some .drain) none rest out) := by
  simp [indexStepBitsComputer, idxStepCfg, idxStepStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some IdxStepLabel.drain, none, stk⟩ : indexStepBitsComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, idxStepStk]

/-! ### indexStepBitsComputer EvalsToInTime -/

def idxStep_evals_one {l l' : Option IdxStepLabel} {v v' : Option Bool}
    {inp out inp' out' : List Bool}
    (h : TM2.step indexStepBitsComputer.m
      (idxStepCfg l v inp out) = some (idxStepCfg l' v' inp' out')) :
    EvalsToInTime indexStepBitsComputer.step
      (idxStepCfg l v inp out)
      (some (idxStepCfg l' v' inp' out')) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (idxStepCfg l v inp out)).bind indexStepBitsComputer.step =
      some (idxStepCfg l' v' inp' out')
    simp only [FinTM2.step]
    exact h

/-- Happy path: both bits true yields step-ok `[false]`. -/
noncomputable def indexStepBits_evals_ok :
    EvalsToInTime indexStepBitsComputer.step
      (initList indexStepBitsComputer (encodePair ([true], [true])))
      (some (haltList indexStepBitsComputer [false])) 5 := by
  have h0 : encodePair ([true], [true]) = [true, true, false, true] := by
    simp [encodePair]
  rw [indexStepBits_initList, indexStepBits_haltList, h0]
  have h1 := idxStep_evals_one (idxStep_step_parseL_true [true, false, true] [])
  have h2 := idxStep_evals_one (idxStep_step_readEval true [false, true] [])
  have h3 := idxStep_evals_one (idxStep_step_sep_false true [true] [])
  have h4 := idxStep_evals_one (idxStep_step_readExp_bothTrue [] [])
  have h5 := idxStep_evals_one (idxStep_step_writeOk_nil [])
  have t12 := EvalsToInTime.trans indexStepBitsComputer.step 1 1 _ _ _ h1 h2
  have t34 := EvalsToInTime.trans indexStepBitsComputer.step 1 1 _ _ _ h3 h4
  have t1234 := EvalsToInTime.trans indexStepBitsComputer.step 2 2 _ _ _ t12 t34
  exact EvalsToInTime.trans indexStepBitsComputer.step 4 1 _ _ _ t1234 h5

/-- Reject path: eval bit false. -/
noncomputable def indexStepBits_evals_evalFalse (expected : Bool) :
    EvalsToInTime indexStepBitsComputer.step
      (initList indexStepBitsComputer (encodePair ([false], [expected])))
      (some (haltList indexStepBitsComputer [true])) 5 := by
  have h0 : encodePair ([false], [expected]) = [true, false, false, expected] := by
    simp [encodePair]
  rw [indexStepBits_initList, indexStepBits_haltList, h0]
  have h1 := idxStep_evals_one (idxStep_step_parseL_true [false, false, expected] [])
  have h2 := idxStep_evals_one (idxStep_step_readEval false [false, expected] [])
  have h3 := idxStep_evals_one (idxStep_step_sep_false false [expected] [])
  have h4 := idxStep_evals_one (idxStep_step_readExp_evalFalse expected [] [])
  have h5 := idxStep_evals_one (idxStep_step_writeRej_nil [])
  have t12 := EvalsToInTime.trans indexStepBitsComputer.step 1 1 _ _ _ h1 h2
  have t34 := EvalsToInTime.trans indexStepBitsComputer.step 1 1 _ _ _ h3 h4
  have t1234 := EvalsToInTime.trans indexStepBitsComputer.step 2 2 _ _ _ t12 t34
  exact EvalsToInTime.trans indexStepBitsComputer.step 4 1 _ _ _ t1234 h5

/-- Reject path: expected bit false while eval is true. -/
noncomputable def indexStepBits_evals_expFalse :
    EvalsToInTime indexStepBitsComputer.step
      (initList indexStepBitsComputer (encodePair ([true], [false])))
      (some (haltList indexStepBitsComputer [true])) 5 := by
  have h0 : encodePair ([true], [false]) = [true, true, false, false] := by
    simp [encodePair]
  rw [indexStepBits_initList, indexStepBits_haltList, h0]
  have h1 := idxStep_evals_one (idxStep_step_parseL_true [true, false, false] [])
  have h2 := idxStep_evals_one (idxStep_step_readEval true [false, false] [])
  have h3 := idxStep_evals_one (idxStep_step_sep_false true [false] [])
  have h4 := idxStep_evals_one (idxStep_step_readExp_expFalse [] [])
  have h5 := idxStep_evals_one (idxStep_step_writeRej_nil [])
  have t12 := EvalsToInTime.trans indexStepBitsComputer.step 1 1 _ _ _ h1 h2
  have t34 := EvalsToInTime.trans indexStepBitsComputer.step 1 1 _ _ _ h3 h4
  have t1234 := EvalsToInTime.trans indexStepBitsComputer.step 2 2 _ _ _ t12 t34
  exact EvalsToInTime.trans indexStepBitsComputer.step 4 1 _ _ _ t1234 h5

/-- Full outputs packaging for the two-bit encodePair domain. -/
noncomputable def indexStepBits_evals (evalBit expected : Bool) :
    TM2OutputsInTime indexStepBitsComputer
      (encodePair ([evalBit], [expected]))
      (some (indexStepBitsResult evalBit expected)) 5 := by
  cases evalBit <;> cases expected
  · simpa [indexStepBitsResult, indexStepBitsOk] using indexStepBits_evals_evalFalse false
  · simpa [indexStepBitsResult, indexStepBitsOk] using indexStepBits_evals_evalFalse true
  · simpa [indexStepBitsResult, indexStepBitsOk] using indexStepBits_evals_expFalse
  · simpa [indexStepBitsResult, indexStepBitsOk] using indexStepBits_evals_ok

noncomputable def indexStepBitsTime : Polynomial ℕ := 5

theorem indexStepBitsTime_eval (t : ℕ) :
    indexStepBitsTime.eval t = 5 := by
  simp [indexStepBitsTime]

/-- Pair encoding of two singleton bit lists. -/
def encodeIndexStepBits (p : Bool × Bool) : List Bool :=
  encodePair ([p.1], [p.2])

noncomputable def indexStepBitsComputableInPolyTime :
    TM2ComputableInPolyTime encodeIndexStepBits idBitEnc
      (fun p => indexStepBitsResult p.1 p.2) where
  tm := indexStepBitsComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := indexStepBitsTime
  outputsFun p := by
    rcases p with ⟨evalBit, expected⟩
    change TM2OutputsInTime indexStepBitsComputer
      (List.map id (encodeIndexStepBits (evalBit, expected)))
      (some (List.map id (idBitEnc (indexStepBitsResult evalBit expected))))
      (indexStepBitsTime.eval (encodeIndexStepBits (evalBit, expected)).length)
    simp only [encodeIndexStepBits, idBitEnc, List.map_id, id_eq,
      indexStepBitsTime_eval]
    exact indexStepBits_evals evalBit expected

theorem indexStepBits_computableInPolyTime :
    Nonempty (TM2ComputableInPolyTime encodeIndexStepBits idBitEnc
      (fun p => indexStepBitsResult p.1 p.2)) :=
  ⟨indexStepBitsComputableInPolyTime⟩

/-! ### Cluster D2 loop-fuel skeleton (semantic target of full sequencer)

`indexValidateComputer` below is the named semantic target for the eventual
FinTM2 under `encodePair (encodeNat n, encodePair (φCode, table))` with
`n = maxVar+1`. The Stmt body that nests pad / eval / bit-step under fuel is
Remaining; functional correctness is already `indexValidateResult_eq`. -/

/-- Semantic target of the eventual `indexValidateComputer` FinTM2
(n, φCode, table) with `n = maxVar+1`. -/
def indexValidateOnTriple (p : ℕ × List Bool × List Bool) : List Bool :=
  let n := p.1
  let φCode := p.2.1
  let table := p.2.2
  match decodeFormula φCode with
  | none => [true]
  | some φ =>
      if n = φ.maxVar + 1 && indexValidate φ table then false :: φCode
      else [true]

theorem indexValidateOnTriple_eq_result
    (φ : PropFormula) (table : List Bool) :
    indexValidateOnTriple (φ.maxVar + 1, encodeFormula φ, table) =
      indexValidateResult (encodeFormula φ) table := by
  simp [indexValidateOnTriple, indexValidateResult, decodeFormula_encodeFormula]

theorem indexValidateOnTriple_eq_validatesTautologyResult
    (φ : PropFormula) (table : List Bool) :
    indexValidateOnTriple (φ.maxVar + 1, encodeFormula φ, table) =
      validatesTautologyResult (encodeFormula φ) table := by
  rw [indexValidateOnTriple_eq_result,
    indexValidateResult_eq_validatesTautologyResult]

/-- Encoding for the eventual sequencer input. -/
def encodeIndexValidate (p : ℕ × List Bool × List Bool) : List Bool :=
  encodePair (encodeNat p.1, encodePair (p.2.1, p.2.2))

/-- Cost model: length gate O(|table|) plus per-index pad+eval+compare. -/
def indexValidateCost (n : ℕ) (φCode table : List Bool) : ℕ :=
  (table.length + 1) + table.length * (φCode.length + n + 1)

theorem indexValidateCost_le (n : ℕ) (φCode table : List Bool) :
    indexValidateCost n φCode table ≤
      (table.length + 1) * (φCode.length + n + 2) := by
  unfold indexValidateCost
  set L := table.length
  set C := φCode.length
  have hL : L * (C + n + 1) ≤ (L + 1) * (C + n + 1) :=
    Nat.mul_le_mul_right _ (Nat.le_succ L)
  have hadd :
      (L + 1) + L * (C + n + 1) ≤ (L + 1) + (L + 1) * (C + n + 1) :=
    Nat.add_le_add_left hL _
  have hEq : (L + 1) + (L + 1) * (C + n + 1) = (L + 1) * (C + n + 2) := by
    ring
  exact hEq ▸ hadd

/-
Remaining (Cluster D2 sequencer glue, next formalize):
1. FinTM2 `indexValidateComputer` Stmt nesting `padBitsComputer` then
   `evalEncodedComputer` then `indexStepBitsComputer` for one index under
   stacks holding `(n, i, φCode, tableBit)`.
2. Fuel loop under `|table|` with counter `i` as `natBitsLE`, step lemmas
   extending `indexValidateFuel_succ_iff`.
3. Length gate via `bitsEqualPairComputableInPolyTime` on
   `(lengthBitsLE table, pow2BitsLE n)` before the loop.
4. Branch to `constTrueListComputableInPolyTime` / `prefixFalseCopyComputer`.
5. Package `TM2ComputableInPolyTime encodeIndexValidate idBitEnc
   indexValidateOnTriple`, then glue into
   `validatesTautologyResult_computableInPolyTime` via `comp_idBitEnc_idBitEnc`.
-/

/-! ## Cluster D2.1: little-endian odometer (assignment counter)

Instead of rebuilding `natBitsLE i` each iteration, walk assignments by
incrementing a length-`n` bit list in little-endian order. This matches
`assignmentAt` index order: `00..0`, `10..0`, `01..0`, ... -/

/-- Add one to a little-endian bit list. `none` means overflow (carry out). -/
def odometerSucc : List Bool → Option (List Bool)
  | [] => none
  | false :: rest => some (true :: rest)
  | true :: rest =>
      match odometerSucc rest with
      | some rest' => some (false :: rest')
      | none => none

theorem odometerSucc_nil : odometerSucc [] = none := rfl

theorem odometerSucc_false (rest : List Bool) :
    odometerSucc (false :: rest) = some (true :: rest) := rfl

theorem odometerSucc_true_some (rest rest' : List Bool)
    (h : odometerSucc rest = some rest') :
    odometerSucc (true :: rest) = some (false :: rest') := by
  simp [odometerSucc, h]

theorem odometerSucc_true_none (rest : List Bool)
    (h : odometerSucc rest = none) :
    odometerSucc (true :: rest) = none := by
  simp [odometerSucc, h]

theorem length_odometerSucc {bs bs' : List Bool}
    (h : odometerSucc bs = some bs') :
    bs'.length = bs.length := by
  induction bs generalizing bs' with
  | nil => simp [odometerSucc] at h
  | cons b rest ih =>
      cases b with
      | false =>
          simp [odometerSucc] at h
          subst h; rfl
      | true =>
          cases hrest : odometerSucc rest with
          | none => simp [odometerSucc, hrest] at h
          | some rest' =>
              simp [odometerSucc, hrest] at h
              subst h
              simp [ih hrest]

/-- Value of little-endian bits (head = LSB), same as `bitsLEValue`. -/
theorem odometerSucc_value {bs bs' : List Bool}
    (h : odometerSucc bs = some bs') :
    bitsLEValue bs' = bitsLEValue bs + 1 := by
  induction bs generalizing bs' with
  | nil => simp [odometerSucc] at h
  | cons b rest ih =>
      cases b with
      | false =>
          simp [odometerSucc] at h
          subst h
          simp [bitsLEValue]
          omega
      | true =>
          cases hrest : odometerSucc rest with
          | none => simp [odometerSucc, hrest] at h
          | some rest' =>
              simp [odometerSucc, hrest] at h
              subst h
              have ih' := ih hrest
              simp [bitsLEValue, ih']
              omega

/-- In-place odometer matches `assignmentAt` succession. -/
theorem odometerSucc_assignmentAt (n i : ℕ) (hi : i + 1 < 2 ^ n) :
    odometerSucc (assignmentAt n i) = some (assignmentAt n (i + 1)) := by
  induction n generalizing i with
  | zero =>
      omega
  | succ n ihn =>
      have hi0 : i < 2 ^ (n + 1) := Nat.lt_of_succ_lt hi
      have hdiv : i / 2 < 2 ^ n := by
        have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
          rw [Nat.pow_succ, Nat.mul_comm]
        have : i < 2 * 2 ^ n := by simpa [hpow] using hi0
        omega
      by_cases hmod : i % 2 = 0
      · -- even: false :: σ  →  true :: σ = assignmentAt (n+1) (i+1)
        set k := i / 2 with hk
        have hi_eq : i = 2 * k := by omega
        have hleft :
            odometerSucc (assignmentAt (n + 1) i) =
              some (true :: assignmentAt n k) := by
          rw [hi_eq, assignmentAt_succ_mul_two, odometerSucc_false]
        have hright :
            assignmentAt (n + 1) (i + 1) = true :: assignmentAt n k := by
          have : i + 1 = 2 * k + 1 := by omega
          rw [this, assignmentAt_succ_mul_two_add_one]
        rw [hleft, hright]
      · -- odd: true :: σ  →  false :: succ σ
        set k := i / 2 with hk
        have hi_eq : i = 2 * k + 1 := by omega
        have hdiv_succ : k + 1 < 2 ^ n := by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by
            rw [Nat.pow_succ, Nat.mul_comm]
          have : i + 1 < 2 * 2 ^ n := by simpa [hpow] using hi
          omega
        have hrest := ihn k hdiv_succ
        have hleft :
            odometerSucc (assignmentAt (n + 1) i) =
              some (false :: assignmentAt n (k + 1)) := by
          rw [hi_eq, assignmentAt_succ_mul_two_add_one]
          simp [odometerSucc, hrest]
        have hright :
            assignmentAt (n + 1) (i + 1) =
              false :: assignmentAt n (k + 1) := by
          have : i + 1 = 2 * (k + 1) := by omega
          rw [this, assignmentAt_succ_mul_two]
        rw [hleft, hright]

/-! ### Cluster D2.1 FinTM2: `odometerSuccComputer`

Input: bit list `bs` on `inp`. Output: `false :: bs'` on success
(`odometerSucc bs = some bs'`), or `[true]` on overflow. -/

open TM2.Stmt

inductive OdoStack where
  | inp | work | out
  deriving DecidableEq, Repr

instance : Fintype OdoStack where
  elems := {.inp, .work, .out}
  complete s := by cases s <;> simp

inductive OdoLabel where
  | loop | carry | rev | writeFail | drain
  deriving DecidableEq, Repr

instance : Fintype OdoLabel where
  elems := {.loop, .carry, .rev, .writeFail, .drain}
  complete s := by cases s <;> simp

/-- Result encoding for the odometer FinTM2. -/
def odometerSuccResult (bs : List Bool) : List Bool :=
  match odometerSucc bs with
  | some bs' => false :: bs'
  | none => [true]

theorem odometerSuccResult_some {bs bs' : List Bool}
    (h : odometerSucc bs = some bs') :
    odometerSuccResult bs = false :: bs' := by
  simp [odometerSuccResult, h]

theorem odometerSuccResult_none {bs : List Bool}
    (h : odometerSucc bs = none) :
    odometerSuccResult bs = [true] := by
  simp [odometerSuccResult, h]

/-- FinTM2 realizing `odometerSuccResult`. Walks LSB-first, flipping trues to
false until a false (write true and copy rest) or overflow (empty). -/
def odometerSuccComputer : FinTM2 where
  K := OdoStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := OdoLabel
  main := .loop
  σ := Option Bool
  initialState := none
  m
    | .loop =>
        pop OdoStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => OdoLabel.writeFail)
            (branch (fun s => decide (s = some false))
              (push OdoStack.work (fun _ => true) <|
                load (fun _ => none) <| goto fun _ => OdoLabel.carry)
              (push OdoStack.work (fun _ => false) <|
                load (fun _ => none) <| goto fun _ => OdoLabel.loop))
    | .carry =>
        pop OdoStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => OdoLabel.rev)
            (push OdoStack.work (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => OdoLabel.carry)
    | .rev =>
        pop OdoStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push OdoStack.out (fun _ => false) <|
              load (fun _ => none) halt)
            (push OdoStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => OdoLabel.rev)
    | .writeFail =>
        pop OdoStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push OdoStack.out (fun _ => true) <|
              load (fun _ => none) halt)
            (load (fun _ => none) <| goto fun _ => OdoLabel.writeFail)
    | .drain =>
        pop OdoStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => OdoLabel.writeFail)
            (load (fun _ => none) <| goto fun _ => OdoLabel.drain)

def odoStk (inp work out : List Bool) : OdoStack → List Bool
  | .inp => inp
  | .work => work
  | .out => out

def odoCfg (l : Option OdoLabel) (v : Option Bool)
    (inp work out : List Bool) : odometerSuccComputer.Cfg :=
  ⟨l, v, odoStk inp work out⟩

theorem odometerSucc_initList (s : List Bool) :
    initList odometerSuccComputer s =
      odoCfg (some .loop) none s [] [] := by
  refine congrArg (fun stk =>
      (⟨some OdoLabel.loop, none, stk⟩ : odometerSuccComputer.Cfg)) ?_
  funext k; cases k <;> simp [odometerSuccComputer, odoStk]

theorem odometerSucc_haltList (out : List Bool) :
    haltList odometerSuccComputer out =
      odoCfg none none [] [] out := by
  refine congrArg (fun stk =>
      (⟨(none : Option OdoLabel), none, stk⟩ : odometerSuccComputer.Cfg)) ?_
  funext k; cases k <;> simp [odometerSuccComputer, odoStk]

/-! ### odometerSuccComputer step lemmas -/

theorem odo_step_loop_false (rest work out : List Bool) (v : Option Bool) :
    TM2.step odometerSuccComputer.m
      (odoCfg (some .loop) v (false :: rest) work out) =
      some (odoCfg (some .carry) none rest (true :: work) out) := by
  simp [odometerSuccComputer, odoCfg, odoStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some OdoLabel.carry, (none : Option Bool), stk⟩ : odometerSuccComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, odoStk]

theorem odo_step_loop_true (rest work out : List Bool) (v : Option Bool) :
    TM2.step odometerSuccComputer.m
      (odoCfg (some .loop) v (true :: rest) work out) =
      some (odoCfg (some .loop) none rest (false :: work) out) := by
  simp [odometerSuccComputer, odoCfg, odoStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some OdoLabel.loop, (none : Option Bool), stk⟩ : odometerSuccComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, odoStk]

theorem odo_step_loop_nil (work out : List Bool) (v : Option Bool) :
    TM2.step odometerSuccComputer.m
      (odoCfg (some .loop) v [] work out) =
      some (odoCfg (some .writeFail) none [] work out) := by
  simp [odometerSuccComputer, odoCfg, odoStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some OdoLabel.writeFail, (none : Option Bool), stk⟩ : odometerSuccComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, odoStk]

theorem odo_step_carry_cons (b : Bool) (rest work out : List Bool) (v : Option Bool) :
    TM2.step odometerSuccComputer.m
      (odoCfg (some .carry) v (b :: rest) work out) =
      some (odoCfg (some .carry) none rest (b :: work) out) := by
  simp [odometerSuccComputer, odoCfg, odoStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some OdoLabel.carry, (none : Option Bool), stk⟩ : odometerSuccComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, odoStk]

theorem odo_step_carry_nil (work out : List Bool) (v : Option Bool) :
    TM2.step odometerSuccComputer.m
      (odoCfg (some .carry) v [] work out) =
      some (odoCfg (some .rev) none [] work out) := by
  simp [odometerSuccComputer, odoCfg, odoStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some OdoLabel.rev, (none : Option Bool), stk⟩ : odometerSuccComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, odoStk]

theorem odo_step_rev_cons (b : Bool) (rest out : List Bool) (v : Option Bool) :
    TM2.step odometerSuccComputer.m
      (odoCfg (some .rev) v [] (b :: rest) out) =
      some (odoCfg (some .rev) none [] rest (b :: out)) := by
  simp [odometerSuccComputer, odoCfg, odoStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some OdoLabel.rev, (none : Option Bool), stk⟩ : odometerSuccComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, odoStk]

theorem odo_step_rev_nil (out : List Bool) (v : Option Bool) :
    TM2.step odometerSuccComputer.m
      (odoCfg (some .rev) v [] [] out) =
      some (odoCfg none none [] [] (false :: out)) := by
  simp [odometerSuccComputer, odoCfg, odoStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option OdoLabel), (none : Option Bool), stk⟩ : odometerSuccComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, odoStk]

theorem odo_step_writeFail_cons (b : Bool) (rest out : List Bool) (v : Option Bool) :
    TM2.step odometerSuccComputer.m
      (odoCfg (some .writeFail) v [] (b :: rest) out) =
      some (odoCfg (some .writeFail) none [] rest out) := by
  simp [odometerSuccComputer, odoCfg, odoStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some OdoLabel.writeFail, (none : Option Bool), stk⟩ : odometerSuccComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, odoStk]

theorem odo_step_writeFail_nil (out : List Bool) (v : Option Bool) :
    TM2.step odometerSuccComputer.m
      (odoCfg (some .writeFail) v [] [] out) =
      some (odoCfg none none [] [] (true :: out)) := by
  simp [odometerSuccComputer, odoCfg, odoStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option OdoLabel), (none : Option Bool), stk⟩ : odometerSuccComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, odoStk]

/-! ### odometerSuccComputer EvalsToInTime -/

def odo_evals_one {l l' : Option OdoLabel} {v v' : Option Bool}
    {inp work out inp' work' out' : List Bool}
    (h : TM2.step odometerSuccComputer.m
      (odoCfg l v inp work out) =
      some (odoCfg l' v' inp' work' out')) :
    EvalsToInTime odometerSuccComputer.step
      (odoCfg l v inp work out)
      (some (odoCfg l' v' inp' work' out')) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (odoCfg l v inp work out)).bind odometerSuccComputer.step =
      some (odoCfg l' v' inp' work' out')
    simp only [FinTM2.step]
    exact h

def odo_evals_loop_false (rest work out : List Bool) (v : Option Bool) :
    EvalsToInTime odometerSuccComputer.step
      (odoCfg (some .loop) v (false :: rest) work out)
      (some (odoCfg (some .carry) none rest (true :: work) out)) 1 :=
  odo_evals_one (odo_step_loop_false rest work out v)

def odo_evals_loop_true (rest work out : List Bool) (v : Option Bool) :
    EvalsToInTime odometerSuccComputer.step
      (odoCfg (some .loop) v (true :: rest) work out)
      (some (odoCfg (some .loop) none rest (false :: work) out)) 1 :=
  odo_evals_one (odo_step_loop_true rest work out v)

def odo_evals_loop_nil (work out : List Bool) (v : Option Bool) :
    EvalsToInTime odometerSuccComputer.step
      (odoCfg (some .loop) v [] work out)
      (some (odoCfg (some .writeFail) none [] work out)) 1 :=
  odo_evals_one (odo_step_loop_nil work out v)

def odo_evals_carry_one (b : Bool) (rest work out : List Bool) (v : Option Bool) :
    EvalsToInTime odometerSuccComputer.step
      (odoCfg (some .carry) v (b :: rest) work out)
      (some (odoCfg (some .carry) none rest (b :: work) out)) 1 :=
  odo_evals_one (odo_step_carry_cons b rest work out v)

def odo_evals_carry_nil (work out : List Bool) (v : Option Bool) :
    EvalsToInTime odometerSuccComputer.step
      (odoCfg (some .carry) v [] work out)
      (some (odoCfg (some .rev) none [] work out)) 1 :=
  odo_evals_one (odo_step_carry_nil work out v)

/-- Carry copies the remaining input onto work (reversed onto the stack). -/
noncomputable def odo_evals_carry (inp work out : List Bool) (v : Option Bool) :
    EvalsToInTime odometerSuccComputer.step
      (odoCfg (some .carry) v inp work out)
      (some (odoCfg (some .rev) none [] (inp.reverse ++ work) out))
      (inp.length + 1) := by
  induction inp generalizing work v with
  | nil =>
      simpa using odo_evals_carry_nil work out v
  | cons b bs ih =>
      have h := EvalsToInTime.trans odometerSuccComputer.step 1 (bs.length + 1)
        _ _ _ (odo_evals_carry_one b bs work out v) (ih (b :: work) none)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

def odo_evals_rev_one (b : Bool) (rest out : List Bool) (v : Option Bool) :
    EvalsToInTime odometerSuccComputer.step
      (odoCfg (some .rev) v [] (b :: rest) out)
      (some (odoCfg (some .rev) none [] rest (b :: out))) 1 :=
  odo_evals_one (odo_step_rev_cons b rest out v)

def odo_evals_rev_nil (out : List Bool) (v : Option Bool) :
    EvalsToInTime odometerSuccComputer.step
      (odoCfg (some .rev) v [] [] out)
      (some (odoCfg none none [] [] (false :: out))) 1 :=
  odo_evals_one (odo_step_rev_nil out v)

/-- Reverse work onto out, then prefix with `false` (success tag). -/
noncomputable def odo_evals_rev (work out : List Bool) (v : Option Bool) :
    EvalsToInTime odometerSuccComputer.step
      (odoCfg (some .rev) v [] work out)
      (some (odoCfg none none [] [] (false :: (work.reverse ++ out))))
      (work.length + 1) := by
  induction work generalizing out v with
  | nil =>
      simpa using odo_evals_rev_nil out v
  | cons b bs ih =>
      have h := EvalsToInTime.trans odometerSuccComputer.step 1 (bs.length + 1)
        _ _ _ (odo_evals_rev_one b bs out v) (ih (b :: out) none)
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

def odo_evals_writeFail_one (b : Bool) (rest out : List Bool) (v : Option Bool) :
    EvalsToInTime odometerSuccComputer.step
      (odoCfg (some .writeFail) v [] (b :: rest) out)
      (some (odoCfg (some .writeFail) none [] rest out)) 1 :=
  odo_evals_one (odo_step_writeFail_cons b rest out v)

def odo_evals_writeFail_nil (out : List Bool) (v : Option Bool) :
    EvalsToInTime odometerSuccComputer.step
      (odoCfg (some .writeFail) v [] [] out)
      (some (odoCfg none none [] [] (true :: out))) 1 :=
  odo_evals_one (odo_step_writeFail_nil out v)

/-- Drain work then emit `[true]` (overflow / fail). -/
noncomputable def odo_evals_writeFail (work out : List Bool) (v : Option Bool) :
    EvalsToInTime odometerSuccComputer.step
      (odoCfg (some .writeFail) v [] work out)
      (some (odoCfg none none [] [] (true :: out)))
      (work.length + 1) := by
  induction work generalizing v with
  | nil =>
      simpa using odo_evals_writeFail_nil out v
  | cons b bs ih =>
      have h := EvalsToInTime.trans odometerSuccComputer.step 1 (bs.length + 1)
        _ _ _ (odo_evals_writeFail_one b bs out v) (ih none)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Overflow path: `odometerSucc bs = none`. Time accounts for flipped bits on work. -/
noncomputable def odo_evals_overflow (bs work out : List Bool)
    (v : Option Bool) (h : odometerSucc bs = none) :
    EvalsToInTime odometerSuccComputer.step
      (odoCfg (some .loop) v bs work out)
      (some (odoCfg none none [] [] (true :: out)))
      (2 * bs.length + work.length + 2) := by
  induction bs generalizing work v with
  | nil =>
      have h1 := odo_evals_loop_nil work out v
      have h2 := odo_evals_writeFail work out none
      have h12 := EvalsToInTime.trans odometerSuccComputer.step 1 (work.length + 1)
        _ _ _ h1 h2
      exact evalsToInTime_le_mono h12 (by omega)
  | cons b rest ih =>
      cases b with
      | false =>
          simp [odometerSucc] at h
      | true =>
          have hrest : odometerSucc rest = none := by
            cases hr : odometerSucc rest with
            | none => rfl
            | some rest' => simp [odometerSucc, hr] at h
          have h1 := odo_evals_loop_true rest work out v
          have h2 := ih (false :: work) none hrest
          have h12 := EvalsToInTime.trans odometerSuccComputer.step 1
            (2 * rest.length + (false :: work).length + 2) _ _ _ h1 h2
          exact evalsToInTime_le_mono h12 (by simp [List.length_cons]; omega)

/-- Success path: `odometerSucc bs = some bs'`. Output is
`false :: (work.reverse ++ bs' ++ out)`. -/
noncomputable def odo_evals_success (bs bs' work out : List Bool)
    (v : Option Bool) (h : odometerSucc bs = some bs') :
    EvalsToInTime odometerSuccComputer.step
      (odoCfg (some .loop) v bs work out)
      (some (odoCfg none none [] [] (false :: (work.reverse ++ bs' ++ out))))
      (2 * bs.length + work.length + 2) := by
  induction bs generalizing bs' work v with
  | nil =>
      simp [odometerSucc] at h
  | cons b rest ih =>
      cases b with
      | false =>
          simp [odometerSucc] at h
          subst h
          have h1 := odo_evals_loop_false rest work out v
          have h2 := odo_evals_carry rest (true :: work) out none
          have h12 := EvalsToInTime.trans odometerSuccComputer.step 1
            (rest.length + 1) _ _ _ h1 h2
          have h12' : EvalsToInTime odometerSuccComputer.step
              (odoCfg (some .loop) v (false :: rest) work out)
              (some (odoCfg (some .rev) none [] (rest.reverse ++ true :: work) out))
              (rest.length + 2) :=
            evalsToInTime_le_mono h12 (by omega)
          have h3 := odo_evals_rev (rest.reverse ++ true :: work) out none
          have h123 := EvalsToInTime.trans odometerSuccComputer.step
            (rest.length + 2)
            ((rest.reverse ++ true :: work).length + 1) _ _ _ h12' h3
          have hrev_out :
              (rest.reverse ++ true :: work).reverse ++ out =
                work.reverse ++ true :: rest ++ out := by
            simp [List.reverse_append, List.reverse_cons, List.append_assoc]
          exact evalsToInTime_le_mono (by simpa [hrev_out] using h123) (by
            simp only [List.length_append, List.length_reverse, List.length_cons]
            omega)
      | true =>
          cases hrest : odometerSucc rest with
          | none => simp [odometerSucc, hrest] at h
          | some rest' =>
              simp [odometerSucc, hrest] at h
              subst h
              have h1 := odo_evals_loop_true rest work out v
              have h2 := ih rest' (false :: work) none hrest
              have h12 := EvalsToInTime.trans odometerSuccComputer.step 1
                (2 * rest.length + (false :: work).length + 2) _ _ _ h1 h2
              have hrev_out :
                  (false :: work).reverse ++ rest' ++ out =
                    work.reverse ++ false :: rest' ++ out := by
                simp [List.reverse_cons, List.append_assoc]
              exact evalsToInTime_le_mono (by simpa [hrev_out] using h12) (by
                simp [List.length_cons]; omega)

/-- Full run: init to halt realizing `odometerSuccResult`. -/
noncomputable def odometerSucc_evals (bs : List Bool) :
    TM2OutputsInTime odometerSuccComputer bs
      (some (odometerSuccResult bs)) (2 * bs.length + 2) := by
  change EvalsToInTime odometerSuccComputer.step
    (initList odometerSuccComputer bs)
    (some (haltList odometerSuccComputer (odometerSuccResult bs)))
    (2 * bs.length + 2)
  rw [odometerSucc_initList, odometerSucc_haltList]
  cases h : odometerSucc bs with
  | none =>
      simpa [odometerSuccResult, h, List.length_nil] using
        odo_evals_overflow bs [] [] none h
  | some bs' =>
      simpa [odometerSuccResult, h, List.append_nil, List.reverse_nil,
        List.length_nil] using
        odo_evals_success bs bs' [] [] none h

noncomputable def odometerSuccTime : Polynomial ℕ := 2 * Polynomial.X + 2

theorem odometerSuccTime_eval (n : ℕ) :
    odometerSuccTime.eval n = 2 * n + 2 := by
  simp [odometerSuccTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_ofNat]

noncomputable def odometerSuccComputableInPolyTime :
    TM2ComputableInPolyTime idBitEnc idBitEnc odometerSuccResult where
  tm := odometerSuccComputer
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := odometerSuccTime
  outputsFun bs := by
    change TM2OutputsInTime odometerSuccComputer (List.map id (idBitEnc bs))
      (some (List.map id (idBitEnc (odometerSuccResult bs))))
      (odometerSuccTime.eval (idBitEnc bs).length)
    simp only [idBitEnc, List.map_id, id_eq, odometerSuccTime_eval]
    exact odometerSucc_evals bs

theorem odometerSucc_computableInPolyTime :
    Nonempty (TM2ComputableInPolyTime idBitEnc idBitEnc odometerSuccResult) :=
  ⟨odometerSuccComputableInPolyTime⟩

/-! ## Cluster D3: afterDecodePairResult glue

`decodePairResult` tags success as `false :: π` and failure as `[true]`.
The map below strips that tag and runs `validatesTautologyResult`, so
`validatesTautologyResult_on_pair = afterDecodePairResult ∘ decodePairResult`.
Closing the pin is then `comp_idBitEnc_idBitEnc` of `decodePairResult` with a
poly-time witness for `afterDecodePairResult` (indexValidate FinTM2). -/

/-- Strip `decodePairResult` tagging and validate the decoded pair. -/
def afterDecodePairResult (s : List Bool) : List Bool :=
  match decodeDecodePairResult s with
  | none => [true]
  | some none => [true]
  | some (some (φCode, table)) => validatesTautologyResult φCode table

theorem afterDecodePairResult_fail_tag :
    afterDecodePairResult [true] = [true] := by
  simp [afterDecodePairResult, decodeDecodePairResult]

theorem afterDecodePairResult_success (φCode table : List Bool) :
    afterDecodePairResult (false :: encodePair (φCode, table)) =
      validatesTautologyResult φCode table := by
  simp [afterDecodePairResult, decodeDecodePairResult, decodePair_encodePair]

theorem afterDecodePairResult_of_decodePairResult (π : List Bool) :
    afterDecodePairResult (decodePairResult π) =
      validatesTautologyResult_on_pair π := by
  cases h : decodePair π with
  | none =>
      simp [decodePairResult_of_none h, validatesTautologyResult_on_pair_of_none h,
        afterDecodePairResult_fail_tag]
  | some pw =>
      rcases pw with ⟨φCode, table⟩
      have henc := encodePair_of_decodePair h
      subst henc
      simp [decodePairResult_encodePair, afterDecodePairResult_success,
        validatesTautologyResult_on_pair_encodePair]

theorem validatesTautologyResult_on_pair_eq_afterDecodePairResult_comp
    (π : List Bool) :
    validatesTautologyResult_on_pair π =
      (afterDecodePairResult ∘ decodePairResult) π :=
  (afterDecodePairResult_of_decodePairResult π).symm

theorem length_afterDecodePairResult_le (s : List Bool) :
    (afterDecodePairResult s).length ≤ s.length + 1 := by
  simp only [afterDecodePairResult]
  cases h : decodeDecodePairResult s with
  | none => simp
  | some r =>
      cases r with
      | none => simp
      | some pw =>
          rcases pw with ⟨φCode, table⟩
          have hout := length_validatesTautologyResult_le φCode table
          have hφ : φCode.length ≤ s.length := by
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
                | some p =>
                    simp [hp] at h
                    rcases h with ⟨rfl, rfl⟩
                    exact Nat.le_trans (length_fst_le_of_decodePair hp)
                      (Nat.le_succ_of_le le_rfl)
          exact Nat.le_trans hout (Nat.add_le_add_right hφ 1)

/-- Polynomial output-size bound for `decodePairResult` (for `comp_idBitEnc`). -/
noncomputable def decodePairResultOutBound : Polynomial ℕ := 3 * Polynomial.X + 2

theorem decodePairResultOutBound_eval (n : ℕ) :
    decodePairResultOutBound.eval n = 3 * n + 2 := by
  simp [decodePairResultOutBound, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat]

theorem decodePairResult_length_le_outBound (π : List Bool) :
    (decodePairResult π).length ≤ decodePairResultOutBound.eval π.length := by
  simpa [decodePairResultOutBound_eval] using length_decodePairResult_le π

/-- Polynomial output-size bound for `afterDecodePairResult`. -/
noncomputable def afterDecodePairResultOutBound : Polynomial ℕ := Polynomial.X + 1

theorem afterDecodePairResultOutBound_eval (n : ℕ) :
    afterDecodePairResultOutBound.eval n = n + 1 := by
  simp [afterDecodePairResultOutBound, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one]

theorem afterDecodePairResult_length_le_outBound (s : List Bool) :
    (afterDecodePairResult s).length ≤ afterDecodePairResultOutBound.eval s.length := by
  simpa [afterDecodePairResultOutBound_eval] using length_afterDecodePairResult_le s

/-! ## Cluster D3.1 FinTM2: `afterDecodePairResultComputer`

Fail tag `[true]` (and drain of a leading `true` with leftover) emits `[true]`.
Success tag `false :: rest` runs the certified `encodePair` load (as in
`bitsEqualComputer`): parse fail drains and emits `[true]`; parse success loads
`(φCode.reverse, table.reverse)` then currently drains and rejects (scaffold
toward `indexValidate` / `validatesTautologyResult`). Certified Evals cover
fail-tag, parse-fail, and success-tag reject cases where the semantic output
is `[true]`. Accept `false :: φCode` is certified via `adr_evals_accept_from_stacks`
on the `acceptEmit` entry (indexValidate wires into it later). -/

open TM2.Stmt

inductive ADRStack where
  | inp | left | right | work | out
  deriving DecidableEq, Repr

instance : Fintype ADRStack where
  elems := {.inp, .left, .right, .work, .out}
  complete s := by cases s <;> simp

inductive ADRLabel where
  | readTag | drainTrue | writeFail
  | parse | expectBit | loadRight
  | clearLeft | clearRight | afterParse
  | allTrueScan | allTrueOk | clearWork
  | lenLoop | lenInc | lenRestore | lenFinish
  | pow2Check | pow2Ok | maxVarGate | maxVarDump | clearInp
  | acceptEmit | revLeft | writeAcceptFalse | clearRightAccept
  | parkWidth | copyLeft | copyLeftRest | revCode
  | mvParse | mvTagF | mvTagT | mvNat | mvNatRest | mvAfter | mvFinish
  | mvToPow2 | unparkMark | unparkFalses
  | eqA | eqB
  | indexLoop | idxParkAsg | idxCopyL | idxCopyRest | idxRevCode
  | evParse | evTagF | evTagT | evNat | evSkip | evRead | evRestore
  | evCount | evCountLoop | evUnpark
  | evDisp1 | evDisp2 | evDisp3 | evDisp4 | evDisp5 | evDisp6 | evDisp7
  | evNot | evAndFirst | evAndCombF | evAndCombT
  | evOrFirst | evOrCombF | evOrCombT | evDone
  | failDrain | acceptPrep | acceptPrepInp
  | idxInc | idxIncRest
  | mvNatRestTake | mvNatRefund | mvNatDiscardPark
  deriving DecidableEq, Repr

instance : Fintype ADRLabel where
  elems := {.readTag, .drainTrue, .writeFail, .parse, .expectBit, .loadRight,
    .clearLeft, .clearRight, .afterParse, .allTrueScan, .allTrueOk, .clearWork,
    .lenLoop, .lenInc, .lenRestore, .lenFinish, .pow2Check, .pow2Ok, .maxVarGate,
    .maxVarDump, .clearInp, .acceptEmit, .revLeft, .writeAcceptFalse, .clearRightAccept,
    .parkWidth, .copyLeft, .copyLeftRest, .revCode,
    .mvParse, .mvTagF, .mvTagT, .mvNat, .mvNatRest, .mvAfter, .mvFinish,
    .mvToPow2, .unparkMark, .unparkFalses, .eqA, .eqB,
    .indexLoop, .idxParkAsg, .idxCopyL, .idxCopyRest, .idxRevCode,
    .evParse, .evTagF, .evTagT, .evNat, .evSkip, .evRead, .evRestore,
    .evCount, .evCountLoop, .evUnpark,
    .evDisp1, .evDisp2, .evDisp3, .evDisp4, .evDisp5, .evDisp6, .evDisp7,
    .evNot, .evAndFirst, .evAndCombF, .evAndCombT,
    .evOrFirst, .evOrCombF, .evOrCombT, .evDone,
    .failDrain, .acceptPrep, .acceptPrepInp, .idxInc, .idxIncRest,
    .mvNatRestTake, .mvNatRefund, .mvNatDiscardPark}
  complete s := by cases s <;> simp

/-- FinTM2 for `afterDecodePairResult`. Leading `true` drains and emits
`[true]`. Leading `false` parses `encodePair` into `left`/`right`; parse fail
or post-load scaffold drains and emits `[true]`. Accept path labels
`acceptEmit`/`revLeft`/`writeAcceptFalse`/`clearRightAccept` reverse
`left` onto `out`, push `false`, clear `right`, halt with `false :: φCode`
(entered later from indexValidate; `afterParse` stays reject scaffold). -/
def afterDecodePairResultComputer : FinTM2 where
  K := ADRStack
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := ADRLabel
  main := .readTag
  σ := Option Bool
  initialState := none
  m
    | .readTag =>
        pop ADRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.writeFail)
            (branch (fun s => decide (s = some true))
              (load (fun _ => none) <| goto fun _ => ADRLabel.drainTrue)
              (load (fun _ => none) <| goto fun _ => ADRLabel.parse))
    | .drainTrue =>
        pop ADRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.writeFail)
            (load (fun _ => none) <| goto fun _ => ADRLabel.drainTrue)
    | .writeFail =>
        push ADRStack.out (fun _ => true) <|
          load (fun _ => none) halt
    | .parse =>
        pop ADRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.clearLeft)
            (branch (fun s => decide (s = some false))
              (load (fun _ => none) <| goto fun _ => ADRLabel.loadRight)
              (load (fun _ => none) <| goto fun _ => ADRLabel.expectBit))
    | .expectBit =>
        pop ADRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.clearLeft)
            (push ADRStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.parse)
    | .loadRight =>
        pop ADRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.afterParse)
            (push ADRStack.right (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.loadRight)
    | .afterParse =>
        -- Enter allTrue scan on `right` (table.reverse).
        load (fun _ => none) <| goto fun _ => ADRLabel.allTrueScan
    | .allTrueScan =>
        -- Pop table bits; any false → clearWork then reject; all true → allTrueOk.
        pop ADRStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.allTrueOk)
            (branch (fun s => decide (s = some false))
              (load (fun _ => none) <| goto fun _ => ADRLabel.clearWork)
              (push ADRStack.work (fun _ => true) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.allTrueScan))
    | .allTrueOk =>
        -- Restore scanned trues from work onto right, then length-count.
        pop ADRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.lenLoop)
            (push ADRStack.right (fun _ => true) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.allTrueOk)
    | .clearWork =>
        -- Discard work (scanned prefix / leftover) so haltList has empty work;
        -- then clearInp in case pow2Check parked width bits on inp.
        pop ADRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.clearInp)
            (load (fun _ => none) <| goto fun _ => ADRLabel.clearWork)
    | .lenLoop =>
        -- Count `|right|` into `work` as LE bits; park popped bits on `inp`.
        pop ADRStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.lenFinish)
            (push ADRStack.inp (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.lenInc)
    | .lenInc =>
        -- Binary increment of `work` (countLengthBitsComputer.inc pattern).
        -- Carry-aux lives on `out` (empty at each symbol boundary).
        pop ADRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push ADRStack.work (fun _ => true) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.lenRestore)
            (branch (fun s => decide (s = some false))
              (push ADRStack.work (fun _ => true) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.lenRestore)
              (push ADRStack.out (fun _ => false) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.lenInc))
    | .lenRestore =>
        -- Drain carry-aux from `out` back onto `work`, then next symbol.
        pop ADRStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.lenLoop)
            (push ADRStack.work (fun s => Option.getD s false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.lenRestore)
    | .lenFinish =>
        -- Restore table from `inp` onto `right`, then check length bits on
        -- `work` are a power of two (`pow2BitsLE` shape).
        pop ADRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.pow2Check)
            (push ADRStack.right (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.lenFinish)
    | .pow2Check =>
        -- `pow2BitsLE n = replicate n false ++ [true]`: pop falses onto `inp`
        -- (width = |inp|), require a final true with empty rest; else reject.
        -- On success enter `pow2Ok` (width falses on `inp`); `maxVarGate`
        -- forms `pow2BitsLE n` and continues to `parkWidth`.
        pop ADRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.clearInp)
            (branch (fun s => decide (s = some false))
              (push ADRStack.inp (fun _ => false) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.pow2Check)
              (branch (fun s => decide (s = some true))
                (pop ADRStack.work (fun _ o => o) <|
                  branch (fun s => decide (s = none))
                    (load (fun _ => none) <| goto fun _ => ADRLabel.pow2Ok)
                    (load (fun _ => none) <| goto fun _ => ADRLabel.clearWork))
                (load (fun _ => none) <| goto fun _ => ADRLabel.clearWork)))
    | .pow2Ok =>
        -- Width `|inp| = n` falses. `maxVarGate` appends the terminator so
        -- `inp` becomes `pow2BitsLE n`, then `parkWidth`.
        load (fun _ => none) <| goto fun _ => ADRLabel.maxVarGate
    | .maxVarGate =>
        -- Park width falses on `work`, push terminator `true`, dump so
        -- `inp = n*false ++ [true] = pow2BitsLE n`.
        pop ADRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push ADRStack.inp (fun _ => true) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.maxVarDump)
            (branch (fun s => decide (s = some false))
              (push ADRStack.work (fun _ => false) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.maxVarGate)
              (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain))
    | .maxVarDump =>
        pop ADRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.parkWidth)
            (push ADRStack.inp (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.maxVarDump)
    | .parkWidth =>
        -- `right := reverse(pow2BitsLE n) ++ table = [true] ++ n*false ++ table`.
        pop ADRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.copyLeft)
            (push ADRStack.right (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.parkWidth)
    | .copyLeft =>
        -- Copy `left` onto `work` using `out` as restore aux.
        pop ADRStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.copyLeftRest)
            (push ADRStack.work (fun s => s.getD false) <|
              push ADRStack.out (fun s => s.getD false) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.copyLeft)
    | .copyLeftRest =>
        pop ADRStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.revCode)
            (push ADRStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.copyLeftRest)
    | .revCode =>
        -- After copy, `work = φCode`. Bounce through empty `inp` so `out = φCode`
        -- and `work` is free for the max-unary accumulator.
        pop ADRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (pop ADRStack.inp (fun _ o => o) <|
              branch (fun s => decide (s = none))
                (load (fun _ => none) <| goto fun _ => ADRLabel.mvParse)
                (push ADRStack.out (fun s => s.getD false) <|
                  load (fun _ => none) <| goto fun _ => ADRLabel.revCode))
            (push ADRStack.inp (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.revCode)
    | .mvParse =>
        pop ADRStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
            (branch (fun s => decide (s = some false))
              (load (fun _ => none) <| goto fun _ => ADRLabel.mvTagF)
              (load (fun _ => none) <| goto fun _ => ADRLabel.mvTagT))
    | .mvTagF =>
        pop ADRStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
            (branch (fun s => decide (s = some false))
              (push ADRStack.left (fun _ => false) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.mvNat)
              (load (fun _ => none) <| goto fun _ => ADRLabel.mvParse))
    | .mvTagT =>
        pop ADRStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
            (push ADRStack.inp (fun _ => true) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.mvParse)
    | .mvNat =>
        -- Unary `true^n false` vs current max `true^k` on `work`.
        -- Consumed max bits are parked on `left` above a `false` delimiter
        -- so `n > k` can grow the max and `n ≤ k` can refund it.
        pop ADRStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
            (branch (fun s => decide (s = some true))
              (pop ADRStack.work (fun _ o => o) <|
                branch (fun s => decide (s = none))
                  (load (fun _ => none) <| goto fun _ => ADRLabel.mvNatRestTake)
                  (push ADRStack.left (fun _ => true) <|
                    load (fun _ => none) <| goto fun _ => ADRLabel.mvNat))
              (load (fun _ => none) <| goto fun _ => ADRLabel.mvNatRefund))
    | .mvNatRestTake =>
        -- `n > k`: move parked old max onto `work`, then copy the rest of `n`.
        pop ADRStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
            (branch (fun s => decide (s = some true))
              (push ADRStack.work (fun _ => true) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.mvNatRestTake)
              (push ADRStack.left (fun _ => false) <|
                push ADRStack.work (fun _ => true) <|
                  load (fun _ => none) <| goto fun _ => ADRLabel.mvNatRest))
    | .mvNatRest =>
        pop ADRStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
            (branch (fun s => decide (s = some true))
              (push ADRStack.work (fun _ => true) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.mvNatRest)
              (load (fun _ => none) <| goto fun _ => ADRLabel.mvNatDiscardPark))
    | .mvNatRefund =>
        -- `n ≤ k`: put consumed max bits back, drop the delimiter.
        pop ADRStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
            (branch (fun s => decide (s = some true))
              (push ADRStack.work (fun _ => true) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.mvNatRefund)
              (load (fun _ => none) <| goto fun _ => ADRLabel.mvAfter))
    | .mvNatDiscardPark =>
        -- `n > k`: drop parked old max and the delimiter.
        pop ADRStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
            (branch (fun s => decide (s = some true))
              (load (fun _ => none) <| goto fun _ => ADRLabel.mvNatDiscardPark)
              (load (fun _ => none) <| goto fun _ => ADRLabel.mvAfter))
    | .mvAfter =>
        pop ADRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.mvFinish)
            (load (fun _ => none) <| goto fun _ => ADRLabel.mvParse)
    | .mvFinish =>
        -- Leftover code rejects. On empty `out`, park terminator `true` then
        -- convert `work = true^k` into `pow2BitsLE (k+1)`.
        pop ADRStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push ADRStack.out (fun _ => true) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.mvToPow2)
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
    | .mvToPow2 =>
        -- `out` already holds `[true]`. Each max bit becomes a false, plus one
        -- extra false: `false^(k+1) ++ [true]`.
        pop ADRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push ADRStack.out (fun _ => false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.unparkMark)
            (push ADRStack.out (fun _ => false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.mvToPow2)
    | .unparkMark =>
        -- Expect parked `[true] ++ n*false ++ table` on `right`.
        pop ADRStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
            (branch (fun s => decide (s = some true))
              (push ADRStack.inp (fun _ => true) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.unparkFalses)
              (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain))
    | .unparkFalses =>
        pop ADRStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.eqA)
            (branch (fun s => decide (s = some false))
              (push ADRStack.inp (fun _ => false) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.unparkFalses)
              (push ADRStack.right (fun _ => true) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.eqA))
    | .eqA =>
        -- Zip `inp = pow2BitsLE n` against `out = maxVarSuccBits`.
        -- False bits accumulate assignment 0 on `work`; matching trues enter
        -- the index loop.
        pop ADRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
            (branch (fun s => decide (s = some true))
              (pop ADRStack.out (fun _ o => o) <|
                branch (fun s => decide (s = none))
                  (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
                  (branch (fun s => decide (s = some true))
                    (load (fun _ => none) <| goto fun _ => ADRLabel.indexLoop)
                    (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)))
              (load (fun _ => none) <| goto fun _ => ADRLabel.eqB))
    | .eqB =>
        -- Expect `false` on `out` after a parked-width false.
        pop ADRStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
            (branch (fun s => decide (s = some false))
              (push ADRStack.work (fun _ => false) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.eqA)
              (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain))
    | .indexLoop =>
        -- Fuel is remaining `right` (all-true table bits).
        pop ADRStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.acceptPrep)
            (branch (fun s => decide (s = some true))
              (load (fun _ => none) <| goto fun _ => ADRLabel.idxParkAsg)
              (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain))
    | .idxParkAsg =>
        pop ADRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.idxCopyL)
            (push ADRStack.inp (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.idxParkAsg)
    | .idxCopyL =>
        pop ADRStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.idxCopyRest)
            (push ADRStack.work (fun s => s.getD false) <|
              push ADRStack.out (fun s => s.getD false) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.idxCopyL)
    | .idxCopyRest =>
        -- Move the work copy onto `left` (one reverse) so `left = φCode.reverse`
        -- and `out` still holds `φCode` in parse order for `evParse`.
        pop ADRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.evParse)
            (push ADRStack.left (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.idxCopyRest)
    | .idxRevCode =>
        pop ADRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.evParse)
            (push ADRStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.idxRevCode)
    | .evParse =>
        -- Prefix eval on `out = remaining code`; result lives in state.
        -- Move code from `out`... after idxRevCode, code is on `out`.
        -- Shift `out` onto `work` first via evParse pop? We parse `out`.
        pop ADRStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
            (branch (fun s => decide (s = some false))
              (load (fun _ => none) <| goto fun _ => ADRLabel.evTagF)
              (load (fun _ => none) <| goto fun _ => ADRLabel.evTagT))
    | .evTagF =>
        pop ADRStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
            (branch (fun s => decide (s = some false))
              (load (fun _ => none) <| goto fun _ => ADRLabel.evNat)
              (push ADRStack.right (fun _ => true) <|
                push ADRStack.right (fun _ => false) <|
                  load (fun _ => none) <| goto fun _ => ADRLabel.evParse))
    | .evTagT =>
        pop ADRStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
            (branch (fun s => decide (s = some false))
              (push ADRStack.right (fun _ => true) <|
                push ADRStack.right (fun _ => false) <|
                  push ADRStack.right (fun _ => false) <|
                    load (fun _ => none) <| goto fun _ => ADRLabel.evParse)
              (push ADRStack.right (fun _ => true) <|
                push ADRStack.right (fun _ => false) <|
                  push ADRStack.right (fun _ => false) <|
                    push ADRStack.right (fun _ => false) <|
                      push ADRStack.right (fun _ => false) <|
                        push ADRStack.right (fun _ => false) <|
                          load (fun _ => none) <| goto fun _ => ADRLabel.evParse))
    | .evNat =>
        pop ADRStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
            (branch (fun s => decide (s = some true))
              (load (fun _ => none) <| goto fun _ => ADRLabel.evSkip)
              (load (fun _ => none) <| goto fun _ => ADRLabel.evRead))
    | .evSkip =>
        pop ADRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.evNat)
            (push ADRStack.work (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.evNat)
    | .evRead =>
        -- Peek current assign bit (default false), park it on `left` so
        -- restore can use state for skipped bits.
        peek ADRStack.inp (fun _ o => o) <|
          push ADRStack.left (fun s => s.getD false) <|
            load (fun _ => none) <| goto fun _ => ADRLabel.evRestore
    | .evRestore =>
        pop ADRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (pop ADRStack.left (fun _ o => o) <|
              load (fun s => s) <| goto fun _ => ADRLabel.evCount)
            (push ADRStack.inp (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.evRestore)
    | .evCount =>
        -- Park the eval bit on `left` so marker counting can clobber state.
        push ADRStack.left (fun s => s.getD false) <|
          load (fun _ => none) <| goto fun _ => ADRLabel.evCountLoop
    | .evCountLoop =>
        -- Count false markers on `right` into `work` as `true^k`.
        -- Remaining code stays on `out`. Stop at first true (table fuel) or empty.
        pop ADRStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.evUnpark)
            (branch (fun s => decide (s = some false))
              (push ADRStack.work (fun _ => true) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.evCountLoop)
              (peek ADRStack.work (fun _ o => o) <|
                branch (fun s => decide (s = none))
                  (push ADRStack.right (fun _ => true) <|
                    load (fun _ => none) <| goto fun _ => ADRLabel.evUnpark)
                  (load (fun _ => none) <| goto fun _ => ADRLabel.evUnpark)))
    | .evUnpark =>
        pop ADRStack.left (fun _ o => o) <|
          load (fun s => s) <| goto fun _ => ADRLabel.evDisp1
    | .evDisp1 =>
        push ADRStack.left (fun s => s.getD false) <|
          pop ADRStack.work (fun _ o => o) <|
            branch (fun s => decide (s = none))
              (pop ADRStack.left (fun _ o => o) <|
                load (fun s => s) <| goto fun _ => ADRLabel.evDone)
              (pop ADRStack.left (fun _ o => o) <|
                load (fun s => s) <| goto fun _ => ADRLabel.evDisp2)
    | .evDisp2 =>
        push ADRStack.left (fun s => s.getD false) <|
          pop ADRStack.work (fun _ o => o) <|
            branch (fun s => decide (s = none))
              (pop ADRStack.left (fun _ o => o) <|
                load (fun s => s) <| goto fun _ => ADRLabel.evNot)
              (pop ADRStack.left (fun _ o => o) <|
                load (fun s => s) <| goto fun _ => ADRLabel.evDisp3)
    | .evDisp3 =>
        push ADRStack.left (fun s => s.getD false) <|
          pop ADRStack.work (fun _ o => o) <|
            branch (fun s => decide (s = none))
              (pop ADRStack.left (fun _ o => o) <|
                load (fun s => s) <| goto fun _ => ADRLabel.evAndFirst)
              (pop ADRStack.left (fun _ o => o) <|
                load (fun s => s) <| goto fun _ => ADRLabel.evDisp4)
    | .evDisp4 =>
        push ADRStack.left (fun s => s.getD false) <|
          pop ADRStack.work (fun _ o => o) <|
            branch (fun s => decide (s = none))
              (pop ADRStack.left (fun _ o => o) <|
                load (fun s => s) <| goto fun _ => ADRLabel.evAndCombF)
              (pop ADRStack.left (fun _ o => o) <|
                load (fun s => s) <| goto fun _ => ADRLabel.evDisp5)
    | .evDisp5 =>
        push ADRStack.left (fun s => s.getD false) <|
          pop ADRStack.work (fun _ o => o) <|
            branch (fun s => decide (s = none))
              (pop ADRStack.left (fun _ o => o) <|
                load (fun s => s) <| goto fun _ => ADRLabel.evAndCombT)
              (pop ADRStack.left (fun _ o => o) <|
                load (fun s => s) <| goto fun _ => ADRLabel.evDisp6)
    | .evDisp6 =>
        push ADRStack.left (fun s => s.getD false) <|
          pop ADRStack.work (fun _ o => o) <|
            branch (fun s => decide (s = none))
              (pop ADRStack.left (fun _ o => o) <|
                load (fun s => s) <| goto fun _ => ADRLabel.evOrFirst)
              (pop ADRStack.left (fun _ o => o) <|
                load (fun s => s) <| goto fun _ => ADRLabel.evDisp7)
    | .evDisp7 =>
        push ADRStack.left (fun s => s.getD false) <|
          pop ADRStack.work (fun _ o => o) <|
            branch (fun s => decide (s = none))
              (pop ADRStack.left (fun _ o => o) <|
                load (fun s => s) <| goto fun _ => ADRLabel.evOrCombF)
              (pop ADRStack.left (fun _ o => o) <|
                load (fun s => s) <| goto fun _ => ADRLabel.evOrCombT)
    | .evNot =>
        branch (fun s => decide (s = some true))
          (load (fun _ => some false) <| goto fun _ => ADRLabel.evCount)
          (load (fun _ => some true) <| goto fun _ => ADRLabel.evCount)
    | .evAndFirst =>
        branch (fun s => decide (s = some true))
          (push ADRStack.right (fun _ => true) <|
            push ADRStack.right (fun _ => false) <|
              push ADRStack.right (fun _ => false) <|
                push ADRStack.right (fun _ => false) <|
                  push ADRStack.right (fun _ => false) <|
                    load (fun _ => none) <| goto fun _ => ADRLabel.evParse)
          (push ADRStack.right (fun _ => true) <|
            push ADRStack.right (fun _ => false) <|
              push ADRStack.right (fun _ => false) <|
                push ADRStack.right (fun _ => false) <|
                  load (fun _ => none) <| goto fun _ => ADRLabel.evParse)
    | .evAndCombF =>
        load (fun _ => some false) <| goto fun _ => ADRLabel.evCount
    | .evAndCombT =>
        load (fun s => s) <| goto fun _ => ADRLabel.evCount
    | .evOrFirst =>
        branch (fun s => decide (s = some true))
          (push ADRStack.right (fun _ => true) <|
            push ADRStack.right (fun _ => false) <|
              push ADRStack.right (fun _ => false) <|
                push ADRStack.right (fun _ => false) <|
                  push ADRStack.right (fun _ => false) <|
                    push ADRStack.right (fun _ => false) <|
                      push ADRStack.right (fun _ => false) <|
                        push ADRStack.right (fun _ => false) <|
                          load (fun _ => none) <| goto fun _ => ADRLabel.evParse)
          (push ADRStack.right (fun _ => true) <|
            push ADRStack.right (fun _ => false) <|
              push ADRStack.right (fun _ => false) <|
                push ADRStack.right (fun _ => false) <|
                  push ADRStack.right (fun _ => false) <|
                    push ADRStack.right (fun _ => false) <|
                      push ADRStack.right (fun _ => false) <|
                        load (fun _ => none) <| goto fun _ => ADRLabel.evParse)
    | .evOrCombF =>
        load (fun s => s) <| goto fun _ => ADRLabel.evCount
    | .evOrCombT =>
        load (fun _ => some true) <| goto fun _ => ADRLabel.evCount
    | .evDone =>
        -- Leftover code on `out` rejects without clobbering the eval bit.
        peek ADRStack.out (fun s o =>
            match o with
            | none => s
            | some _ => none) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
            (branch (fun s => decide (s = some true))
              (load (fun _ => none) <| goto fun _ => ADRLabel.idxInc)
              (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain))
    | .failDrain =>
        pop ADRStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.clearWork)
            (load (fun _ => none) <| goto fun _ => ADRLabel.failDrain)
    | .acceptPrep =>
        pop ADRStack.work (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.acceptPrepInp)
            (load (fun _ => none) <| goto fun _ => ADRLabel.acceptPrep)
    | .acceptPrepInp =>
        pop ADRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.acceptEmit)
            (load (fun _ => none) <| goto fun _ => ADRLabel.acceptPrepInp)
    | .idxInc =>
        -- Little endian `bitsInc` on the assignment sitting on `inp`.
        pop ADRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (push ADRStack.inp (fun _ => true) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.idxIncRest)
            (branch (fun s => decide (s = some false))
              (push ADRStack.inp (fun _ => true) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.idxIncRest)
              (push ADRStack.out (fun _ => false) <|
                load (fun _ => none) <| goto fun _ => ADRLabel.idxInc))
    | .idxIncRest =>
        pop ADRStack.out (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.indexLoop)
            (push ADRStack.inp (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.idxIncRest)
    | .clearInp =>
        pop ADRStack.inp (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.clearLeft)
            (load (fun _ => none) <| goto fun _ => ADRLabel.clearInp)
    | .clearLeft =>
        pop ADRStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.clearRight)
            (load (fun _ => none) <| goto fun _ => ADRLabel.clearLeft)
    | .clearRight =>
        pop ADRStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.writeFail)
            (load (fun _ => none) <| goto fun _ => ADRLabel.clearRight)
    | .acceptEmit =>
        -- Entry for accept finisher (wired from indexValidate later).
        load (fun _ => none) <| goto fun _ => ADRLabel.revLeft
    | .revLeft =>
        pop ADRStack.left (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) <| goto fun _ => ADRLabel.writeAcceptFalse)
            (push ADRStack.out (fun s => s.getD false) <|
              load (fun _ => none) <| goto fun _ => ADRLabel.revLeft)
    | .writeAcceptFalse =>
        push ADRStack.out (fun _ => false) <|
          load (fun _ => none) <| goto fun _ => ADRLabel.clearRightAccept
    | .clearRightAccept =>
        pop ADRStack.right (fun _ o => o) <|
          branch (fun s => decide (s = none))
            (load (fun _ => none) halt)
            (load (fun _ => none) <| goto fun _ => ADRLabel.clearRightAccept)

def adrStk (inp left right work out : List Bool) : ADRStack → List Bool
  | .inp => inp
  | .left => left
  | .right => right
  | .work => work
  | .out => out

def adrCfg (l : Option ADRLabel) (v : Option Bool)
    (inp left right work out : List Bool) : afterDecodePairResultComputer.Cfg :=
  ⟨l, v, adrStk inp left right work out⟩

theorem afterDecodePairResult_initList (s : List Bool) :
    initList afterDecodePairResultComputer s =
      adrCfg (some .readTag) none s [] [] [] [] := by
  refine congrArg (fun stk =>
      (⟨some ADRLabel.readTag, none, stk⟩ : afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [afterDecodePairResultComputer, adrStk]

theorem afterDecodePairResult_haltList (out : List Bool) :
    haltList afterDecodePairResultComputer out =
      adrCfg none none [] [] [] [] out := by
  refine congrArg (fun stk =>
      (⟨(none : Option ADRLabel), none, stk⟩ : afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [afterDecodePairResultComputer, adrStk]

theorem adr_step_readTag_nil (left right work out : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .readTag) v [] left right work out) =
      some (adrCfg (some .writeFail) none [] left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.writeFail, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_readTag_true (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .readTag) v (true :: rest) left right work out) =
      some (adrCfg (some .drainTrue) none rest left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.drainTrue, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_readTag_false (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .readTag) v (false :: rest) left right work out) =
      some (adrCfg (some .parse) none rest left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.parse, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_drainTrue_cons (b : Bool) (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .drainTrue) v (b :: rest) left right work out) =
      some (adrCfg (some .drainTrue) none rest left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.drainTrue, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_drainTrue_nil (left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .drainTrue) v [] left right work out) =
      some (adrCfg (some .writeFail) none [] left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.writeFail, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_writeFail (inp left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .writeFail) v inp left right work out) =
      some (adrCfg none none inp left right work (true :: out)) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option ADRLabel), (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_parse_nil (left right work out : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .parse) v [] left right work out) =
      some (adrCfg (some .clearLeft) none [] left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.clearLeft, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_parse_false (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .parse) v (false :: rest) left right work out) =
      some (adrCfg (some .loadRight) none rest left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.loadRight, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_parse_true (b : Bool) (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .parse) v (true :: b :: rest) left right work out) =
      some (adrCfg (some .expectBit) none (b :: rest) left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.expectBit, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_parse_true_any (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .parse) v (true :: rest) left right work out) =
      some (adrCfg (some .expectBit) none rest left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.expectBit, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_expectBit (b : Bool) (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .expectBit) v (b :: rest) left right work out) =
      some (adrCfg (some .parse) none rest (b :: left) right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.parse, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_expectBit_nil (left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .expectBit) v [] left right work out) =
      some (adrCfg (some .clearLeft) none [] left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.clearLeft, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_loadRight_cons (b : Bool) (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .loadRight) v (b :: rest) left right work out) =
      some (adrCfg (some .loadRight) none rest left (b :: right) work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.loadRight, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_loadRight_nil (left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .loadRight) v [] left right work out) =
      some (adrCfg (some .afterParse) none [] left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.afterParse, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_afterParse (inp left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .afterParse) v inp left right work out) =
      some (adrCfg (some .allTrueScan) none inp left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.allTrueScan, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_allTrueScan_nil (inp left work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .allTrueScan) v inp left [] work out) =
      some (adrCfg (some .allTrueOk) none inp left [] work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.allTrueOk, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_allTrueScan_false (inp left rest work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .allTrueScan) v inp left (false :: rest) work out) =
      some (adrCfg (some .clearWork) none inp left rest work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.clearWork, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_allTrueScan_true (inp left rest work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .allTrueScan) v inp left (true :: rest) work out) =
      some (adrCfg (some .allTrueScan) none inp left rest (true :: work) out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.allTrueScan, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_allTrueOk_nil (inp left right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .allTrueOk) v inp left right [] out) =
      some (adrCfg (some .lenLoop) none inp left right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.lenLoop, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_allTrueOk_cons_any (b : Bool)
    (inp left right rest out : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .allTrueOk) v inp left right (b :: rest) out) =
      some (adrCfg (some .allTrueOk) none inp left (true :: right) rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.allTrueOk, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_clearWork_nil (inp left right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .clearWork) v inp left right [] out) =
      some (adrCfg (some .clearInp) none inp left right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.clearInp, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_clearWork_cons (b : Bool) (inp left right rest out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .clearWork) v inp left right (b :: rest) out) =
      some (adrCfg (some .clearWork) none inp left right rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.clearWork, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_lenLoop_nil (inp left work out : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .lenLoop) v inp left [] work out) =
      some (adrCfg (some .lenFinish) none inp left [] work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.lenFinish, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_lenLoop_cons (b : Bool) (inp left rest work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .lenLoop) v inp left (b :: rest) work out) =
      some (adrCfg (some .lenInc) none (b :: inp) left rest work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.lenInc, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_lenInc_nil (inp left right out : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .lenInc) v inp left right [] out) =
      some (adrCfg (some .lenRestore) none inp left right [true] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.lenRestore, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_lenInc_false (inp left right rest out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .lenInc) v inp left right (false :: rest) out) =
      some (adrCfg (some .lenRestore) none inp left right (true :: rest) out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.lenRestore, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_lenInc_true (inp left right rest out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .lenInc) v inp left right (true :: rest) out) =
      some (adrCfg (some .lenInc) none inp left right rest (false :: out)) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.lenInc, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_lenRestore_nil (inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .lenRestore) v inp left right work []) =
      some (adrCfg (some .lenLoop) none inp left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.lenLoop, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_lenRestore_cons (inp left right work : List Bool) (b : Bool)
    (rest : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .lenRestore) v inp left right work (b :: rest)) =
      some (adrCfg (some .lenRestore) none inp left right (b :: work) rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.lenRestore, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_lenFinish_nil (left right work out : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .lenFinish) v [] left right work out) =
      some (adrCfg (some .pow2Check) none [] left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.pow2Check, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_pow2Check_nil (inp left right out : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .pow2Check) v inp left right [] out) =
      some (adrCfg (some .clearInp) none inp left right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.clearInp, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_pow2Check_false (inp left right rest out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .pow2Check) v inp left right (false :: rest) out) =
      some (adrCfg (some .pow2Check) none (false :: inp) left right rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.pow2Check, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_pow2Check_true_nil (inp left right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .pow2Check) v inp left right [true] out) =
      some (adrCfg (some .pow2Ok) none inp left right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.pow2Ok, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_pow2Check_true_cons (inp left right : List Bool) (b : Bool)
    (rest out : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .pow2Check) v inp left right (true :: b :: rest) out) =
      some (adrCfg (some .clearWork) none inp left right rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.clearWork, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_pow2Ok (inp left right work out : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .pow2Ok) v inp left right work out) =
      some (adrCfg (some .maxVarGate) none inp left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.maxVarGate, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_maxVarGate_nil (left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .maxVarGate) v [] left right work out) =
      some (adrCfg (some .maxVarDump) none [true] left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.maxVarDump, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_maxVarGate_false (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .maxVarGate) v (false :: rest) left right work out) =
      some (adrCfg (some .maxVarGate) none rest left right
        (false :: work) out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.maxVarGate, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_maxVarGate_true (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .maxVarGate) v (true :: rest) left right work out) =
      some (adrCfg (some .failDrain) none rest left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_maxVarDump_nil (inp left right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .maxVarDump) v inp left right [] out) =
      some (adrCfg (some .parkWidth) none inp left right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.parkWidth, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_maxVarDump_cons (b : Bool) (rest inp left right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .maxVarDump) v inp left right (b :: rest) out) =
      some (adrCfg (some .maxVarDump) none (b :: inp) left right rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.maxVarDump, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_parkWidth_cons (b : Bool) (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .parkWidth) v (b :: rest) left right work out) =
      some (adrCfg (some .parkWidth) none rest left (b :: right) work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.parkWidth, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_parkWidth_nil (left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .parkWidth) v [] left right work out) =
      some (adrCfg (some .copyLeft) none [] left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.copyLeft, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_copyLeft_cons (b : Bool) (rest right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .copyLeft) v [] (b :: rest) right work out) =
      some (adrCfg (some .copyLeft) none [] rest right (b :: work)
        (b :: out)) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.copyLeft, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_copyLeft_nil (right work out : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .copyLeft) v [] [] right work out) =
      some (adrCfg (some .copyLeftRest) none [] [] right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.copyLeftRest, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_copyLeftRest_cons (b : Bool) (left rest right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .copyLeftRest) v [] left right work (b :: rest)) =
      some (adrCfg (some .copyLeftRest) none [] (b :: left) right work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.copyLeftRest, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_copyLeftRest_nil (left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .copyLeftRest) v [] left right work []) =
      some (adrCfg (some .revCode) none [] left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.revCode, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_revCode_work_cons (b : Bool) (rest left right inp out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .revCode) v inp left right (b :: rest) out) =
      some (adrCfg (some .revCode) none (b :: inp) left right rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.revCode, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_revCode_bounce (b : Bool) (rest left right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .revCode) v (b :: rest) left right [] out) =
      some (adrCfg (some .revCode) none rest left right [] (b :: out)) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.revCode, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_revCode_to_parse (left right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .revCode) v [] left right [] out) =
      some (adrCfg (some .mvParse) none [] left right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvParse, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_failDrain_cons (b : Bool) (inp left right work rest : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .failDrain) v inp left right work (b :: rest)) =
      some (adrCfg (some .failDrain) none inp left right work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_failDrain_nil (inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .failDrain) v inp left right work []) =
      some (adrCfg (some .clearWork) none inp left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.clearWork, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvParse_nil (inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvParse) v inp left right work []) =
      some (adrCfg (some .failDrain) none inp left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvParse_false (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvParse) v inp left right work (false :: rest)) =
      some (adrCfg (some .mvTagF) none inp left right work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvTagF, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvParse_true (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvParse) v inp left right work (true :: rest)) =
      some (adrCfg (some .mvTagT) none inp left right work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvTagT, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvTagF_nil (inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvTagF) v inp left right work []) =
      some (adrCfg (some .failDrain) none inp left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvTagF_false (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvTagF) v inp left right work (false :: rest)) =
      some (adrCfg (some .mvNat) none inp (false :: left) right work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvNat, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvTagF_true (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvTagF) v inp left right work (true :: rest)) =
      some (adrCfg (some .mvParse) none inp left right work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvParse, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvTagT_nil (inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvTagT) v inp left right work []) =
      some (adrCfg (some .failDrain) none inp left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvTagT_cons (b : Bool) (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvTagT) v inp left right work (b :: rest)) =
      some (adrCfg (some .mvParse) none (true :: inp) left right work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvParse, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvNat_nil (inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvNat) v inp left right work []) =
      some (adrCfg (some .failDrain) none inp left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvNat_false (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvNat) v inp left right work (false :: rest)) =
      some (adrCfg (some .mvNatRefund) none inp left right work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvNatRefund, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvNat_true_work_nil (rest inp left right : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvNat) v inp left right [] (true :: rest)) =
      some (adrCfg (some .mvNatRestTake) none inp left right [] rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvNatRestTake, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvNat_true_work_cons (b : Bool) (wrest rest inp left right : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvNat) v inp left right (b :: wrest) (true :: rest)) =
      some (adrCfg (some .mvNat) none inp (true :: left) right wrest rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvNat, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvNatRest_nil (inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvNatRest) v inp left right work []) =
      some (adrCfg (some .failDrain) none inp left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvNatRest_true (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvNatRest) v inp left right work (true :: rest)) =
      some (adrCfg (some .mvNatRest) none inp left right (true :: work) rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvNatRest, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvNatRest_false (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvNatRest) v inp left right work (false :: rest)) =
      some (adrCfg (some .mvNatDiscardPark) none inp left right work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvNatDiscardPark, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvNatRestTake_true (lrest inp right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvNatRestTake) v inp (true :: lrest) right work out) =
      some (adrCfg (some .mvNatRestTake) none inp lrest right (true :: work)
        out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvNatRestTake, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvNatRestTake_false (lrest inp right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvNatRestTake) v inp (false :: lrest) right work out) =
      some (adrCfg (some .mvNatRest) none inp (false :: lrest) right
        (true :: work) out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvNatRest, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvNatRefund_true (lrest inp right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvNatRefund) v inp (true :: lrest) right work out) =
      some (adrCfg (some .mvNatRefund) none inp lrest right (true :: work)
        out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvNatRefund, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvNatRefund_false (lrest inp right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvNatRefund) v inp (false :: lrest) right work out) =
      some (adrCfg (some .mvAfter) none inp lrest right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvAfter, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvNatDiscardPark_true (lrest inp right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvNatDiscardPark) v inp (true :: lrest) right work out) =
      some (adrCfg (some .mvNatDiscardPark) none inp lrest right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvNatDiscardPark, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvNatDiscardPark_false (lrest inp right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvNatDiscardPark) v inp (false :: lrest) right work out) =
      some (adrCfg (some .mvAfter) none inp lrest right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvAfter, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvAfter_nil (left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvAfter) v [] left right work out) =
      some (adrCfg (some .mvFinish) none [] left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvFinish, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvAfter_cons (b : Bool) (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvAfter) v (b :: rest) left right work out) =
      some (adrCfg (some .mvParse) none rest left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvParse, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvFinish_nil (inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvFinish) v inp left right work []) =
      some (adrCfg (some .mvToPow2) none inp left right work [true]) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvToPow2, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvFinish_cons (b : Bool) (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvFinish) v inp left right work (b :: rest)) =
      some (adrCfg (some .failDrain) none inp left right work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvToPow2_nil (inp left right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvToPow2) v inp left right [] out) =
      some (adrCfg (some .unparkMark) none inp left right []
        (false :: out)) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.unparkMark, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_mvToPow2_cons (b : Bool) (rest inp left right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .mvToPow2) v inp left right (b :: rest) out) =
      some (adrCfg (some .mvToPow2) none inp left right rest (false :: out)) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.mvToPow2, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_unparkMark_nil (inp left work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .unparkMark) v inp left [] work out) =
      some (adrCfg (some .failDrain) none inp left [] work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_unparkMark_true (rest inp left work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .unparkMark) v inp left (true :: rest) work out) =
      some (adrCfg (some .unparkFalses) none (true :: inp) left rest work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.unparkFalses, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_unparkMark_false (rest inp left work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .unparkMark) v inp left (false :: rest) work out) =
      some (adrCfg (some .failDrain) none inp left rest work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_unparkFalses_nil (inp left work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .unparkFalses) v inp left [] work out) =
      some (adrCfg (some .eqA) none inp left [] work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.eqA, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_unparkFalses_false (rest inp left work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .unparkFalses) v inp left (false :: rest) work out) =
      some (adrCfg (some .unparkFalses) none (false :: inp) left rest work
        out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.unparkFalses, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_unparkFalses_true (rest inp left work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .unparkFalses) v inp left (true :: rest) work out) =
      some (adrCfg (some .eqA) none inp left (true :: rest) work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.eqA, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_eqA_nil (left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .eqA) v [] left right work out) =
      some (adrCfg (some .failDrain) none [] left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_eqA_false (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .eqA) v (false :: rest) left right work out) =
      some (adrCfg (some .eqB) none rest left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.eqB, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_eqA_true_true (orest left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .eqA) v [true] left right work (true :: orest)) =
      some (adrCfg (some .indexLoop) none [] left right work orest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.indexLoop, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_eqA_true_false (orest left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .eqA) v [true] left right work (false :: orest)) =
      some (adrCfg (some .failDrain) none [] left right work orest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_eqA_true_nil (left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .eqA) v [true] left right work []) =
      some (adrCfg (some .failDrain) none [] left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_eqA_true_out_true (irest orest left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .eqA) v (true :: irest) left right work (true :: orest)) =
      some (adrCfg (some .indexLoop) none irest left right work orest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.indexLoop, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_eqA_true_out_false (irest orest left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .eqA) v (true :: irest) left right work (false :: orest)) =
      some (adrCfg (some .failDrain) none irest left right work orest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_eqB_nil (inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .eqB) v inp left right work []) =
      some (adrCfg (some .failDrain) none inp left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_eqB_false (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .eqB) v inp left right work (false :: rest)) =
      some (adrCfg (some .eqA) none inp left right (false :: work) rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.eqA, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_eqB_true (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .eqB) v inp left right work (true :: rest)) =
      some (adrCfg (some .failDrain) none inp left right work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_indexLoop_nil (inp left work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .indexLoop) v inp left [] work out) =
      some (adrCfg (some .acceptPrep) none inp left [] work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.acceptPrep, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_indexLoop_true (rest inp left work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .indexLoop) v inp left (true :: rest) work out) =
      some (adrCfg (some .idxParkAsg) none inp left rest work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.idxParkAsg, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_indexLoop_false (rest inp left work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .indexLoop) v inp left (false :: rest) work out) =
      some (adrCfg (some .failDrain) none inp left rest work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_idxParkAsg_cons (b : Bool) (rest inp left right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .idxParkAsg) v inp left right (b :: rest) out) =
      some (adrCfg (some .idxParkAsg) none (b :: inp) left right rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.idxParkAsg, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_idxParkAsg_nil (inp left right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .idxParkAsg) v inp left right [] out) =
      some (adrCfg (some .idxCopyL) none inp left right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.idxCopyL, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_idxCopyL_cons (b : Bool) (rest inp right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .idxCopyL) v inp (b :: rest) right work out) =
      some (adrCfg (some .idxCopyL) none inp rest right (b :: work)
        (b :: out)) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.idxCopyL, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_idxCopyL_nil (inp right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .idxCopyL) v inp [] right work out) =
      some (adrCfg (some .idxCopyRest) none inp [] right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.idxCopyRest, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_idxCopyRest_cons (b : Bool) (rest inp left right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .idxCopyRest) v inp left right (b :: rest) out) =
      some (adrCfg (some .idxCopyRest) none inp (b :: left) right rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.idxCopyRest, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_idxCopyRest_nil (inp left right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .idxCopyRest) v inp left right [] out) =
      some (adrCfg (some .evParse) none inp left right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evParse, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evParse_nil (inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evParse) v inp left right work []) =
      some (adrCfg (some .failDrain) none inp left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evParse_false (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evParse) v inp left right work (false :: rest)) =
      some (adrCfg (some .evTagF) none inp left right work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evTagF, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evParse_true (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evParse) v inp left right work (true :: rest)) =
      some (adrCfg (some .evTagT) none inp left right work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evTagT, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evTagF_nil (inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evTagF) v inp left right work []) =
      some (adrCfg (some .failDrain) none inp left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evTagF_var (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evTagF) v inp left right work (false :: rest)) =
      some (adrCfg (some .evNat) none inp left right work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evNat, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evTagF_not (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evTagF) v inp left right work (true :: rest)) =
      some (adrCfg (some .evParse) none inp left (false :: true :: right)
        work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evParse, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evTagT_nil (inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evTagT) v inp left right work []) =
      some (adrCfg (some .failDrain) none inp left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evTagT_and (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evTagT) v inp left right work (false :: rest)) =
      some (adrCfg (some .evParse) none inp left
        (false :: false :: true :: right) work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evParse, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evTagT_or (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evTagT) v inp left right work (true :: rest)) =
      some (adrCfg (some .evParse) none inp left
        (false :: false :: false :: false :: false :: true :: right)
        work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evParse, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evNat_nil (inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evNat) v inp left right work []) =
      some (adrCfg (some .failDrain) none inp left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evNat_true (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evNat) v inp left right work (true :: rest)) =
      some (adrCfg (some .evSkip) none inp left right work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evSkip, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evNat_false (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evNat) v inp left right work (false :: rest)) =
      some (adrCfg (some .evRead) none inp left right work rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evRead, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evSkip_cons (b : Bool) (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evSkip) v (b :: rest) left right work out) =
      some (adrCfg (some .evNat) none rest left right (b :: work) out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evNat, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evSkip_nil (left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evSkip) v [] left right work out) =
      some (adrCfg (some .evNat) none [] left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evNat, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evRead_cons (b : Bool) (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evRead) v (b :: rest) left right work out) =
      some (adrCfg (some .evRestore) none (b :: rest) (b :: left)
        right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evRestore, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evRead_nil (left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evRead) v [] left right work out) =
      some (adrCfg (some .evRestore) none [] (false :: left)
        right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evRestore, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evRestore_cons (b : Bool) (rest inp left right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evRestore) v inp left right (b :: rest) out) =
      some (adrCfg (some .evRestore) none (b :: inp) left right rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evRestore, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evRestore_nil_cons (b : Bool) (rest inp right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evRestore) v inp (b :: rest) right [] out) =
      some (adrCfg (some .evCount) (some b) inp rest right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evCount, (some b : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evRestore_nil_nil (inp right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evRestore) v inp [] right [] out) =
      some (adrCfg (some .evCount) none inp [] right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evCount, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evCount (inp left right work out : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evCount) v inp left right work out) =
      some (adrCfg (some .evCountLoop) none inp (v.getD false :: left)
        right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evCountLoop, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evCountLoop_nil (inp left work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evCountLoop) v inp left [] work out) =
      some (adrCfg (some .evUnpark) none inp left [] work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evUnpark, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evCountLoop_false (rest inp left work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evCountLoop) v inp left (false :: rest) work out) =
      some (adrCfg (some .evCountLoop) none inp left rest (true :: work)
        out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evCountLoop, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evCountLoop_true_table (rest inp left out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evCountLoop) v inp left (true :: rest) [] out) =
      some (adrCfg (some .evUnpark) none inp left (true :: rest) [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evUnpark, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evCountLoop_true_delim (b : Bool) (wrest rest inp left out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evCountLoop) v inp left (true :: rest)
        (b :: wrest) out) =
      some (adrCfg (some .evUnpark) none inp left rest (b :: wrest) out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evUnpark, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evUnpark_cons (b : Bool) (rest inp right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evUnpark) v inp (b :: rest) right work out) =
      some (adrCfg (some .evDisp1) (some b) inp rest right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evDisp1, (some b : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evUnpark_nil (inp right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evUnpark) v inp [] right work out) =
      some (adrCfg (some .evDisp1) none inp [] right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evDisp1, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDisp1_nil (inp left right out : List Bool) (bit : Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDisp1) (some bit) inp left right [] out) =
      some (adrCfg (some .evDone) (some bit) inp left right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evDone, some bit, stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDisp1_cons (b : Bool) (rest inp left right out : List Bool)
    (bit : Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDisp1) (some bit) inp left right (b :: rest) out) =
      some (adrCfg (some .evDisp2) (some bit) inp left right rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evDisp2, some bit, stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDisp2_nil (inp left right out : List Bool) (bit : Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDisp2) (some bit) inp left right [] out) =
      some (adrCfg (some .evNot) (some bit) inp left right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evNot, some bit, stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDisp2_cons (b : Bool) (rest inp left right out : List Bool)
    (bit : Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDisp2) (some bit) inp left right (b :: rest) out) =
      some (adrCfg (some .evDisp3) (some bit) inp left right rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evDisp3, some bit, stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDisp3_nil (inp left right out : List Bool) (bit : Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDisp3) (some bit) inp left right [] out) =
      some (adrCfg (some .evAndFirst) (some bit) inp left right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evAndFirst, some bit, stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDisp3_cons (b : Bool) (rest inp left right out : List Bool)
    (bit : Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDisp3) (some bit) inp left right (b :: rest) out) =
      some (adrCfg (some .evDisp4) (some bit) inp left right rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evDisp4, some bit, stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDisp4_nil (inp left right out : List Bool) (bit : Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDisp4) (some bit) inp left right [] out) =
      some (adrCfg (some .evAndCombF) (some bit) inp left right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evAndCombF, some bit, stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDisp4_cons (b : Bool) (rest inp left right out : List Bool)
    (bit : Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDisp4) (some bit) inp left right (b :: rest) out) =
      some (adrCfg (some .evDisp5) (some bit) inp left right rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evDisp5, some bit, stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDisp5_nil (inp left right out : List Bool) (bit : Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDisp5) (some bit) inp left right [] out) =
      some (adrCfg (some .evAndCombT) (some bit) inp left right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evAndCombT, some bit, stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDisp5_cons (b : Bool) (rest inp left right out : List Bool)
    (bit : Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDisp5) (some bit) inp left right (b :: rest) out) =
      some (adrCfg (some .evDisp6) (some bit) inp left right rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evDisp6, some bit, stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDisp6_nil (inp left right out : List Bool) (bit : Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDisp6) (some bit) inp left right [] out) =
      some (adrCfg (some .evOrFirst) (some bit) inp left right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evOrFirst, some bit, stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDisp6_cons (b : Bool) (rest inp left right out : List Bool)
    (bit : Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDisp6) (some bit) inp left right (b :: rest) out) =
      some (adrCfg (some .evDisp7) (some bit) inp left right rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evDisp7, some bit, stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDisp7_nil (inp left right out : List Bool) (bit : Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDisp7) (some bit) inp left right [] out) =
      some (adrCfg (some .evOrCombF) (some bit) inp left right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evOrCombF, some bit, stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDisp7_cons (b : Bool) (rest inp left right out : List Bool)
    (bit : Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDisp7) (some bit) inp left right (b :: rest) out) =
      some (adrCfg (some .evOrCombT) (some bit) inp left right rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evOrCombT, some bit, stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evNot_true (inp left right work out : List Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evNot) (some true) inp left right work out) =
      some (adrCfg (some .evCount) (some false) inp left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evCount, (some false : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evNot_false (inp left right work out : List Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evNot) (some false) inp left right work out) =
      some (adrCfg (some .evCount) (some true) inp left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evCount, (some true : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evAndFirst_true (inp left right work out : List Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evAndFirst) (some true) inp left right work out) =
      some (adrCfg (some .evParse) none inp left
        (false :: false :: false :: false :: true :: right) work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evParse, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evAndFirst_false (inp left right work out : List Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evAndFirst) (some false) inp left right work out) =
      some (adrCfg (some .evParse) none inp left
        (false :: false :: false :: true :: right) work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evParse, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evAndCombF (inp left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evAndCombF) v inp left right work out) =
      some (adrCfg (some .evCount) (some false) inp left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evCount, (some false : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evAndCombT (inp left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evAndCombT) v inp left right work out) =
      some (adrCfg (some .evCount) v inp left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evCount, v, stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evOrFirst_true (inp left right work out : List Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evOrFirst) (some true) inp left right work out) =
      some (adrCfg (some .evParse) none inp left
        (false :: false :: false :: false :: false :: false :: false ::
          true :: right) work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evParse, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evOrFirst_false (inp left right work out : List Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evOrFirst) (some false) inp left right work out) =
      some (adrCfg (some .evParse) none inp left
        (false :: false :: false :: false :: false :: false :: true ::
          right) work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evParse, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evOrCombF (inp left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evOrCombF) v inp left right work out) =
      some (adrCfg (some .evCount) v inp left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evCount, v, stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evOrCombT (inp left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evOrCombT) v inp left right work out) =
      some (adrCfg (some .evCount) (some true) inp left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.evCount, (some true : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDone_true_empty (inp left right work : List Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDone) (some true) inp left right work []) =
      some (adrCfg (some .idxInc) none inp left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.idxInc, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDone_false_empty (inp left right work : List Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDone) (some false) inp left right work []) =
      some (adrCfg (some .failDrain) none inp left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_evDone_leftover (b : Bool) (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .evDone) v inp left right work (b :: rest)) =
      some (adrCfg (some .failDrain) none inp left right work (b :: rest)) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.failDrain, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_idxInc_nil (left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .idxInc) v [] left right work out) =
      some (adrCfg (some .idxIncRest) none [true] left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.idxIncRest, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_idxInc_false (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .idxInc) v (false :: rest) left right work out) =
      some (adrCfg (some .idxIncRest) none (true :: rest) left right
        work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.idxIncRest, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_idxInc_true (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .idxInc) v (true :: rest) left right work out) =
      some (adrCfg (some .idxInc) none rest left right work
        (false :: out)) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.idxInc, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_idxIncRest_nil (inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .idxIncRest) v inp left right work []) =
      some (adrCfg (some .indexLoop) none inp left right work []) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.indexLoop, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_idxIncRest_cons (b : Bool) (rest inp left right work : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .idxIncRest) v inp left right work (b :: rest)) =
      some (adrCfg (some .idxIncRest) none (b :: inp) left right work
        rest) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.idxIncRest, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_acceptPrep_cons (b : Bool) (rest inp left right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .acceptPrep) v inp left right (b :: rest) out) =
      some (adrCfg (some .acceptPrep) none inp left right rest out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.acceptPrep, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_acceptPrep_nil (inp left right out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .acceptPrep) v inp left right [] out) =
      some (adrCfg (some .acceptPrepInp) none inp left right [] out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.acceptPrepInp, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_acceptPrepInp_cons (b : Bool) (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .acceptPrepInp) v (b :: rest) left right work out) =
      some (adrCfg (some .acceptPrepInp) none rest left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.acceptPrepInp, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_acceptPrepInp_nil (left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .acceptPrepInp) v [] left right work out) =
      some (adrCfg (some .acceptEmit) none [] left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.acceptEmit, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_clearInp_cons (b : Bool) (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .clearInp) v (b :: rest) left right work out) =
      some (adrCfg (some .clearInp) none rest left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.clearInp, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_clearInp_nil (left right work out : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .clearInp) v [] left right work out) =
      some (adrCfg (some .clearLeft) none [] left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.clearLeft, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_lenFinish_cons (b : Bool) (rest left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .lenFinish) v (b :: rest) left right work out) =
      some (adrCfg (some .lenFinish) none rest left (b :: right) work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.lenFinish, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_clearLeft_cons (b : Bool) (rest right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .clearLeft) v [] (b :: rest) right work out) =
      some (adrCfg (some .clearLeft) none [] rest right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.clearLeft, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_clearLeft_nil (right work out : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .clearLeft) v [] [] right work out) =
      some (adrCfg (some .clearRight) none [] [] right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.clearRight, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_clearRight_cons (b : Bool) (rest work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .clearRight) v [] [] (b :: rest) work out) =
      some (adrCfg (some .clearRight) none [] [] rest work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.clearRight, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_clearRight_nil (work out : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .clearRight) v [] [] [] work out) =
      some (adrCfg (some .writeFail) none [] [] [] work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.writeFail, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_acceptEmit (inp left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .acceptEmit) v inp left right work out) =
      some (adrCfg (some .revLeft) none inp left right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.revLeft, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_revLeft_cons (b : Bool) (rest right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .revLeft) v [] (b :: rest) right work out) =
      some (adrCfg (some .revLeft) none [] rest right work (b :: out)) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.revLeft, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_revLeft_nil (right work out : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .revLeft) v [] [] right work out) =
      some (adrCfg (some .writeAcceptFalse) none [] [] right work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.writeAcceptFalse, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_writeAcceptFalse (inp left right work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .writeAcceptFalse) v inp left right work out) =
      some (adrCfg (some .clearRightAccept) none
        inp left right work (false :: out)) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.clearRightAccept, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_clearRightAccept_cons (b : Bool) (rest work out : List Bool)
    (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .clearRightAccept) v [] [] (b :: rest) work out) =
      some (adrCfg (some .clearRightAccept) none [] [] rest work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨some ADRLabel.clearRightAccept, (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

theorem adr_step_clearRightAccept_nil (work out : List Bool) (v : Option Bool) :
    TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .clearRightAccept) v [] [] [] work out) =
      some (adrCfg none none [] [] [] work out) := by
  simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
  refine congrArg some <|
    congrArg (fun stk =>
      (⟨(none : Option ADRLabel), (none : Option Bool), stk⟩ :
        afterDecodePairResultComputer.Cfg)) ?_
  funext k; cases k <;> simp [Function.update, adrStk]

def adr_evals_one {l l' : Option ADRLabel} {v v' : Option Bool}
    {inp left right work out inp' left' right' work' out' : List Bool}
    (h : TM2.step afterDecodePairResultComputer.m
      (adrCfg l v inp left right work out) =
      some (adrCfg l' v' inp' left' right' work' out')) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg l v inp left right work out)
      (some (adrCfg l' v' inp' left' right' work' out')) 1 where
  steps := 1
  steps_le_m := by decide
  evals_in_steps := by
    change (some (adrCfg l v inp left right work out)).bind
        afterDecodePairResultComputer.step =
      some (adrCfg l' v' inp' left' right' work' out')
    simp only [FinTM2.step]
    exact h

/-- Restore any `work` onto `right` as trues, then enter `lenLoop`. -/
noncomputable def adr_evals_allTrueOk_restore_any (work : List Bool)
    (inp left right out : List Bool) (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .allTrueOk) v inp left right work out)
      (some (adrCfg (some .lenLoop) none inp left
        (List.replicate work.length true ++ right) [] out))
      (work.length + 1) := by
  induction work generalizing right v with
  | nil =>
      simpa using adr_evals_one (adr_step_allTrueOk_nil inp left right out v)
  | cons b bs ih =>
      have h1 := adr_evals_one
        (adr_step_allTrueOk_cons_any b inp left right bs out v)
      have h2 := ih (true :: right) none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (bs.length + 1) _ _ _ h1 h2
      have heq : List.replicate bs.length true ++ true :: right =
          List.replicate (bs.length + 1) true ++ right := by
        calc
          List.replicate bs.length true ++ true :: right
              = List.replicate bs.length true ++ ([true] ++ right) := by
                simp
          _ = (List.replicate bs.length true ++ [true]) ++ right := by
                simp [List.append_assoc]
          _ = List.replicate (bs.length + 1) true ++ right := by
                simp [List.replicate_succ']
      have t' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .allTrueOk) v inp left right (b :: bs) out)
          (some (adrCfg (some .lenLoop) none inp left
            (List.replicate (bs.length + 1) true ++ right) [] out))
          (bs.length + 2) := by
        simpa [heq, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using t
      simpa [List.length_cons] using t'

/-- Drain `work` then enter `clearInp`. -/
noncomputable def adr_evals_clearWork (work : List Bool)
    (inp left right out : List Bool) (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .clearWork) v inp left right work out)
      (some (adrCfg (some .clearInp) none inp left right [] out))
      (work.length + 1) := by
  induction work generalizing v with
  | nil =>
      simpa using adr_evals_one (adr_step_clearWork_nil inp left right out v)
  | cons b bs ih =>
      have h1 := adr_evals_one
        (adr_step_clearWork_cons b inp left right bs out v)
      have h2 := ih none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step
        1 (bs.length + 1) _ _ _ h1 h2
      exact evalsToInTime_le_mono t (by simp [List.length_cons])

/-- Drain `inp` then enter `clearLeft`. -/
noncomputable def adr_evals_clearInp (inp left right work out : List Bool)
    (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .clearInp) v inp left right work out)
      (some (adrCfg (some .clearLeft) none [] left right work out))
      (inp.length + 1) := by
  induction inp generalizing v with
  | nil =>
      simpa using adr_evals_one (adr_step_clearInp_nil left right work out v)
  | cons b bs ih =>
      have h1 := adr_evals_one
        (adr_step_clearInp_cons b bs left right work out v)
      have h2 := ih none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step
        1 (bs.length + 1) _ _ _ h1 h2
      exact evalsToInTime_le_mono t (by simp [List.length_cons])

/-- Drain `right` then emit `[true]` (inp, left, work empty). -/
noncomputable def adr_evals_clearRight (right : List Bool) (work out : List Bool)
    (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .clearRight) v [] [] right work out)
      (some (adrCfg none none [] [] [] work (true :: out)))
      (right.length + 2) := by
  induction right generalizing v with
  | nil =>
      have h1 := adr_evals_one (adr_step_clearRight_nil work out v)
      have h2 := adr_evals_one (adr_step_writeFail [] [] [] work out none)
      exact EvalsToInTime.trans afterDecodePairResultComputer.step 1 1 _ _ _ h1 h2
  | cons b bs ih =>
      have h1 := adr_evals_one (adr_step_clearRight_cons b bs work out v)
      have h2 := ih none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step
        1 (bs.length + 2) _ _ _ h1 h2
      exact evalsToInTime_le_mono t (by simp [List.length_cons])

/-- Drain `left` then `right` then emit `[true]` (inp and work empty). -/
noncomputable def adr_evals_clear_to_fail (left right : List Bool)
    (work out : List Bool) (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .clearLeft) v [] left right work out)
      (some (adrCfg none none [] [] [] work (true :: out)))
      (left.length + right.length + 3) := by
  induction left generalizing v with
  | nil =>
      have h1 := adr_evals_one (adr_step_clearLeft_nil right work out v)
      have h2 := adr_evals_clearRight right work out none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step
        1 (right.length + 2) _ _ _ h1 h2
      exact evalsToInTime_le_mono t (by omega)
  | cons b bs ih =>
      have h1 := adr_evals_one
        (adr_step_clearLeft_cons b bs right work out v)
      have h2 := ih none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step
        1 (bs.length + right.length + 3) _ _ _ h1 h2
      exact evalsToInTime_le_mono t (by simp [List.length_cons])

/-- Drain `inp` then `left` then `right` then emit `[true]`. -/
noncomputable def adr_evals_clearInp_to_fail (inp left right : List Bool)
    (work out : List Bool) (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .clearInp) v inp left right work out)
      (some (adrCfg none none [] [] [] work (true :: out)))
      (inp.length + left.length + right.length + 4) := by
  have h1 := adr_evals_clearInp inp left right work out v
  have h2 := adr_evals_clear_to_fail left right work out none
  have t := EvalsToInTime.trans afterDecodePairResultComputer.step
    (inp.length + 1) (left.length + right.length + 3) _ _ _ h1 h2
  exact evalsToInTime_le_mono t (by omega)

/-- Drain leftover `out`, then `clearWork` / `clearInp` to `[true]`. -/
noncomputable def adr_evals_failDrain (inp left right work out : List Bool)
    (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .failDrain) v inp left right work out)
      (some (adrCfg none none [] [] [] [] [true]))
      (out.length + work.length + inp.length + left.length + right.length + 6) := by
  induction out generalizing v with
  | nil =>
      have h1 := adr_evals_one (adr_step_failDrain_nil inp left right work v)
      have h2 := adr_evals_clearWork work inp left right [] none
      have t12 := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (work.length + 1) _ _ _ h1 h2
      have h3 := adr_evals_clearInp_to_fail inp left right [] [] none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step
        (work.length + 2)
        (inp.length + left.length + right.length + 4) _ _ _ t12 h3
      exact evalsToInTime_le_mono t (by omega)
  | cons b rest ih =>
      have h1 := adr_evals_one
        (adr_step_failDrain_cons b inp left right work rest v)
      have h2 := ih none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (rest.length + work.length + inp.length + left.length +
          right.length + 6) _ _ _ h1 h2
      exact evalsToInTime_le_mono t (by simp [List.length_cons])

/-- Dump parked width bits from `work` onto `inp`, then enter `parkWidth`. -/
noncomputable def adr_evals_maxVarDump (acc inp left right out : List Bool)
    (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .maxVarDump) v inp left right acc out)
      (some (adrCfg (some .parkWidth) none (acc.reverse ++ inp) left right
        [] out))
      (acc.length + 1) := by
  induction acc generalizing inp v with
  | nil =>
      simpa using adr_evals_one
        (adr_step_maxVarDump_nil inp left right out v)
  | cons b rest ih =>
      have h1 := adr_evals_one
        (adr_step_maxVarDump_cons b rest inp left right out v)
      have h2 := ih (b :: inp) none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (rest.length + 1) _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc] using t

/-- Park `n` width falses onto `work`, then push the terminator. -/
noncomputable def adr_evals_maxVarGate_park (n : ℕ)
    (acc left right out : List Bool) (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .maxVarGate) v (List.replicate n false) left right acc out)
      (some (adrCfg (some .maxVarDump) none [true] left right
        (List.replicate n false ++ acc) out))
      (n + 1) := by
  induction n generalizing acc v with
  | zero =>
      simpa [List.replicate, List.append_nil] using adr_evals_one
        (adr_step_maxVarGate_nil left right acc out v)
  | succ n ih =>
      have h1 := adr_evals_one
        (adr_step_maxVarGate_false (List.replicate n false) left right acc
          out v)
      have h2 := ih (false :: acc) none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (n + 1) _ _ _ h1 h2
      simpa [replicate_false_concat n acc] using t

/-- Width `n` falses and empty work form `pow2BitsLE n` on `inp` at `parkWidth`. -/
noncomputable def adr_evals_maxVarGate_to_parkWidth (n : ℕ)
    (left right out : List Bool) (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .maxVarGate) v (List.replicate n false) left right [] out)
      (some (adrCfg (some .parkWidth) none (pow2BitsLE n) left right [] out))
      (2 * n + 2) := by
  have h1 := adr_evals_maxVarGate_park n [] left right out v
  have h1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .maxVarGate) v (List.replicate n false) left right [] out)
      (some (adrCfg (some .maxVarDump) none [true] left right
        (List.replicate n false) out))
      (n + 1) := by
    simpa using h1
  have h2 := adr_evals_maxVarDump (List.replicate n false) [true] left right
    out none
  have t := EvalsToInTime.trans afterDecodePairResultComputer.step
    _ _ _ _ _ h1' h2
  have hinp : (List.replicate n false).reverse ++ [true] = pow2BitsLE n := by
    simp [pow2BitsLE, List.reverse_replicate]
  simpa [hinp] using evalsToInTime_le_mono t (by
    simp [List.length_replicate]; omega)

/-- Well-formed `pow2BitsLE n` on `work` walks to `maxVarGate` with
`n` width falses parked on `inp`. -/
noncomputable def adr_evals_pow2Check_to_maxVarGate (n : ℕ)
    (inp left right : List Bool) (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .pow2Check) v inp left right (pow2BitsLE n) [])
      (some (adrCfg (some .maxVarGate) none
        (List.replicate n false ++ inp) left right [] []))
      (n + 2) := by
  induction n generalizing inp v with
  | zero =>
      have h1 := adr_evals_one
        (adr_step_pow2Check_true_nil inp left right [] v)
      have h2 := adr_evals_one
        (adr_step_pow2Ok inp left right [] [] none)
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1 1
        _ _ _ h1 h2
      simpa [pow2BitsLE_zero, List.replicate, List.append_nil] using
        evalsToInTime_le_mono t (by omega)
  | succ n ih =>
      have h1 := adr_evals_one
        (adr_step_pow2Check_false inp left right (pow2BitsLE n) [] v)
      have h1' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .pow2Check) v inp left right (pow2BitsLE (n + 1)) [])
          (some (adrCfg (some .pow2Check) none (false :: inp) left right
            (pow2BitsLE n) [])) 1 := by
        simpa [pow2BitsLE_succ] using h1
      have h2 := ih (false :: inp) none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (n + 2) _ _ _ h1' h2
      simpa [replicate_false_concat n inp] using
        evalsToInTime_le_mono t (by omega)

/-- Well-formed `pow2BitsLE n` on `work` (empty `inp`) reaches `parkWidth`
with `pow2BitsLE n` on `inp`. -/
noncomputable def adr_evals_pow2Check_ok (n : ℕ)
    (left right : List Bool) (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .pow2Check) v [] left right (pow2BitsLE n) [])
      (some (adrCfg (some .parkWidth) none (pow2BitsLE n) left right [] []))
      (3 * n + 4) := by
  have h1 := adr_evals_pow2Check_to_maxVarGate n [] left right v
  have h1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .pow2Check) v [] left right (pow2BitsLE n) [])
      (some (adrCfg (some .maxVarGate) none (List.replicate n false)
        left right [] []))
      (n + 2) := by
    simpa using h1
  have h2 := adr_evals_maxVarGate_to_parkWidth n left right [] none
  have t := EvalsToInTime.trans afterDecodePairResultComputer.step
    (n + 2) (2 * n + 2) _ _ _ h1' h2
  exact evalsToInTime_le_mono t (by omega)

/-- Park `inp` onto `right`, then enter `copyLeft`. -/
noncomputable def adr_evals_parkWidth (inp left right work out : List Bool)
    (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .parkWidth) v inp left right work out)
      (some (adrCfg (some .copyLeft) none [] left (inp.reverse ++ right)
        work out))
      (inp.length + 1) := by
  induction inp generalizing right v with
  | nil =>
      simpa using adr_evals_one (adr_step_parkWidth_nil left right work out v)
  | cons b rest ih =>
      have h1 := adr_evals_one
        (adr_step_parkWidth_cons b rest left right work out v)
      have h2 := ih (b :: right) none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (rest.length + 1) _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, List.length_cons,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using t

/-- Copy `left` onto `work` as `left.reverse` and restore `left` from `out`. -/
noncomputable def adr_evals_copyLeft (left right : List Bool)
    (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .copyLeft) v [] left right [] [])
      (some (adrCfg (some .revCode) none [] left right left.reverse []))
      (2 * left.length + 2) := by
  have hconsume :
      ∀ (xs accW accO : List Bool) (v' : Option Bool),
        EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .copyLeft) v' [] xs right accW accO)
          (some (adrCfg (some .copyLeftRest) none [] [] right
            (xs.reverse ++ accW) (xs.reverse ++ accO)))
          (xs.length + 1) := by
    intro xs
    induction xs with
    | nil =>
        intro accW accO v'
        simpa using adr_evals_one
          (adr_step_copyLeft_nil right accW accO v')
    | cons b rest ih =>
        intro accW accO v'
        have h1 := adr_evals_one
          (adr_step_copyLeft_cons b rest right accW accO v')
        have h2 := ih (b :: accW) (b :: accO) none
        have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
          (rest.length + 1) _ _ _ h1 h2
        simpa [List.reverse_cons, List.append_assoc, List.length_cons,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using t
  have hrestore :
      ∀ (ys leftAcc : List Bool) (v' : Option Bool),
        EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .copyLeftRest) v' [] leftAcc right
            left.reverse ys)
          (some (adrCfg (some .revCode) none []
            (ys.reverse ++ leftAcc) right left.reverse []))
          (ys.length + 1) := by
    intro ys
    induction ys with
    | nil =>
        intro leftAcc v'
        simpa using adr_evals_one
          (adr_step_copyLeftRest_nil leftAcc right left.reverse v')
    | cons b rest ih =>
        intro leftAcc v'
        have h1 := adr_evals_one
          (adr_step_copyLeftRest_cons b leftAcc rest right left.reverse v')
        have h2 := ih (b :: leftAcc) none
        have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
          (rest.length + 1) _ _ _ h1 h2
        simpa [List.reverse_cons, List.append_assoc, List.length_cons,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using t
  have h1 := hconsume left [] [] v
  have h1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .copyLeft) v [] left right [] [])
      (some (adrCfg (some .copyLeftRest) none [] [] right
        left.reverse left.reverse))
      (left.length + 1) := by
    simpa [List.append_nil] using h1
  have h2 := hrestore left.reverse [] none
  have h2' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .copyLeftRest) none [] [] right
        left.reverse left.reverse)
      (some (adrCfg (some .revCode) none [] left right left.reverse []))
      (left.reverse.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil] using h2
  have t := EvalsToInTime.trans afterDecodePairResultComputer.step
    (left.length + 1) (left.reverse.length + 1) _ _ _ h1' h2'
  exact evalsToInTime_le_mono t (by simp [List.length_reverse]; omega)

/-- Bounce `work = φCode` through empty `inp` onto `out`. -/
noncomputable def adr_evals_revCode (φCode left right : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .revCode) none [] left right φCode [])
      (some (adrCfg (some .mvParse) none [] left right [] φCode))
      (2 * φCode.length + 1) := by
  have htoInp :
      ∀ (xs inp : List Bool),
        EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .revCode) none inp left right xs [])
          (some (adrCfg (some .revCode) none (xs.reverse ++ inp) left right
            [] []))
          xs.length := by
    intro xs
    induction xs with
    | nil =>
        intro inp
        exact EvalsToInTime.refl afterDecodePairResultComputer.step
          (adrCfg (some .revCode) none inp left right [] [])
    | cons b rest ih =>
        intro inp
        have h1 := adr_evals_one
          (adr_step_revCode_work_cons b rest left right inp [] none)
        have h2 := ih (b :: inp)
        have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
          rest.length _ _ _ h1 h2
        simpa [List.reverse_cons, List.append_assoc, List.length_cons,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          evalsToInTime_le_mono t (by simp [List.length_cons])
  have hbounce :
      ∀ (ys out : List Bool),
        EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .revCode) none ys left right [] out)
          (some (adrCfg (some .mvParse) none [] left right []
            (ys.reverse ++ out)))
          (ys.length + 1) := by
    intro ys
    induction ys with
    | nil =>
        intro out
        simpa using adr_evals_one
          (adr_step_revCode_to_parse left right out none)
    | cons b rest ih =>
        intro out
        have h1 := adr_evals_one
          (adr_step_revCode_bounce b rest left right out none)
        have h2 := ih (b :: out)
        have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
          (rest.length + 1) _ _ _ h1 h2
        simpa [List.reverse_cons, List.append_assoc, List.length_cons,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using t
  have h1 := htoInp φCode []
  have h1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .revCode) none [] left right φCode [])
      (some (adrCfg (some .revCode) none φCode.reverse left right [] []))
      φCode.length := by
    simpa [List.append_nil] using h1
  have h2 := hbounce φCode.reverse []
  have h2' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .revCode) none φCode.reverse left right [] [])
      (some (adrCfg (some .mvParse) none [] left right [] φCode))
      (φCode.reverse.length + 1) := by
    simpa [List.reverse_reverse, List.append_nil] using h2
  have t := EvalsToInTime.trans afterDecodePairResultComputer.step
    φCode.length (φCode.reverse.length + 1) _ _ _ h1' h2'
  exact evalsToInTime_le_mono t (by simp [List.length_reverse]; omega)

/-- Reach `mvParse` after parking width and copying `φCode`. -/
noncomputable def adr_evals_park_to_mvParse (φCode table : List Bool)
    (n : ℕ) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .parkWidth) none (pow2BitsLE n) φCode.reverse table [] [])
      (some (adrCfg (some .mvParse) none [] φCode.reverse
        ((pow2BitsLE n).reverse ++ table) [] φCode))
      (4 * (φCode.length + n + 2) + 8) := by
  have hpark := adr_evals_parkWidth (pow2BitsLE n) φCode.reverse table [] [] none
  have hcopy := adr_evals_copyLeft φCode.reverse
    ((pow2BitsLE n).reverse ++ table) none
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step
    ((pow2BitsLE n).length + 1) (2 * φCode.reverse.length + 2) _ _ _ hpark hcopy
  have t1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .parkWidth) none (pow2BitsLE n) φCode.reverse table [] [])
      (some (adrCfg (some .revCode) none [] φCode.reverse
        ((pow2BitsLE n).reverse ++ table) φCode []))
      (2 * φCode.length + n + 6) := by
    simpa [List.reverse_reverse, List.length_reverse, length_pow2BitsLE] using
      evalsToInTime_le_mono t1 (by
        simp [List.length_reverse, length_pow2BitsLE]; omega)
  have hrev := adr_evals_revCode φCode φCode.reverse
    ((pow2BitsLE n).reverse ++ table)
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (2 * φCode.length + n + 6) (2 * φCode.length + 1) _ _ _ t1' hrev
  exact evalsToInTime_le_mono t2 (by omega)

/-- All-true blocks commute past a leading `true`. -/
theorem replicate_true_append_cons (n : ℕ) (xs : List Bool) :
    List.replicate n true ++ true :: xs = true :: (List.replicate n true ++ xs) := by
  induction n with
  | zero => simp [List.replicate]
  | succ n ih => simp [List.replicate_succ, ih]

/-- Refund parked unary bits plus the delimiter, restoring `left`. -/
noncomputable def adr_evals_mvNatRefund (i : ℕ)
    (left0 inp right work out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvNatRefund) none inp
        (List.replicate i true ++ false :: left0) right work out)
      (some (adrCfg (some .mvAfter) none inp left0 right
        (List.replicate i true ++ work) out))
      (i + 1) := by
  induction i generalizing work with
  | zero =>
      simpa using adr_evals_one
        (adr_step_mvNatRefund_false left0 inp right work out none)
  | succ i ih =>
      have h1 := adr_evals_one
        (adr_step_mvNatRefund_true (List.replicate i true ++ false :: left0)
          inp right work out none)
      have h2 := ih (true :: work)
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (i + 1)
        (adrCfg (some .mvNatRefund) none inp
          (true :: (List.replicate i true ++ false :: left0)) right work out)
        (adrCfg (some .mvNatRefund) none inp
          (List.replicate i true ++ false :: left0) right (true :: work) out)
        (some (adrCfg (some .mvAfter) none inp left0 right
          (List.replicate i true ++ true :: work) out))
        h1 h2
      simpa [List.replicate_succ, List.cons_append, replicate_true_append_cons] using t

/-- Drop parked old max bits plus the delimiter. -/
noncomputable def adr_evals_mvNatDiscardPark (i : ℕ)
    (left0 inp right work out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvNatDiscardPark) none inp
        (List.replicate i true ++ false :: left0) right work out)
      (some (adrCfg (some .mvAfter) none inp left0 right work out))
      (i + 1) := by
  induction i with
  | zero =>
      simpa using adr_evals_one
        (adr_step_mvNatDiscardPark_false left0 inp right work out none)
  | succ i ih =>
      have h1 := adr_evals_one
        (adr_step_mvNatDiscardPark_true (List.replicate i true ++ false :: left0)
          inp right work out none)
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (i + 1)
        (adrCfg (some .mvNatDiscardPark) none inp
          (true :: (List.replicate i true ++ false :: left0)) right work out)
        (adrCfg (some .mvNatDiscardPark) none inp
          (List.replicate i true ++ false :: left0) right work out)
        (some (adrCfg (some .mvAfter) none inp left0 right work out))
        h1 ih
      simpa [List.replicate_succ] using t

/-- `n > k`: move parked old max onto `work`, then take the current `n` bit. -/
noncomputable def adr_evals_mvNatRestTake (k : ℕ)
    (left0 inp right work out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvNatRestTake) none inp
        (List.replicate k true ++ false :: left0) right work out)
      (some (adrCfg (some .mvNatRest) none inp (false :: left0) right
        (true :: (List.replicate k true ++ work)) out))
      (k + 1) := by
  induction k generalizing work with
  | zero =>
      simpa using adr_evals_one
        (adr_step_mvNatRestTake_false left0 inp right work out none)
  | succ k ih =>
      have h1 := adr_evals_one
        (adr_step_mvNatRestTake_true (List.replicate k true ++ false :: left0)
          inp right work out none)
      have h2 := ih (true :: work)
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (k + 1)
        (adrCfg (some .mvNatRestTake) none inp
          (true :: (List.replicate k true ++ false :: left0)) right work out)
        (adrCfg (some .mvNatRestTake) none inp
          (List.replicate k true ++ false :: left0) right (true :: work) out)
        (some (adrCfg (some .mvNatRest) none inp (false :: left0) right
          (true :: (List.replicate k true ++ true :: work)) out))
        h1 h2
      simpa [List.replicate_succ, List.cons_append, replicate_true_append_cons] using t

/-- Copy remaining unary bits of `n`, then drop the delimiter. -/
noncomputable def adr_evals_mvNatRest (m : ℕ)
    (left0 inp right work rest : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvNatRest) none inp (false :: left0) right work
        (List.replicate m true ++ false :: rest))
      (some (adrCfg (some .mvAfter) none inp left0 right
        (List.replicate m true ++ work) rest))
      (m + 2) := by
  induction m generalizing work with
  | zero =>
      have h1 := adr_evals_one
        (adr_step_mvNatRest_false rest inp (false :: left0) right work none)
      have h2 := adr_evals_mvNatDiscardPark 0 left0 inp right work rest
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1 1
        (adrCfg (some .mvNatRest) none inp (false :: left0) right work
          (false :: rest))
        (adrCfg (some .mvNatDiscardPark) none inp (false :: left0) right work
          rest)
        (some (adrCfg (some .mvAfter) none inp left0 right work rest))
        h1 h2
      simpa [List.replicate] using t
  | succ m ih =>
      have h1 := adr_evals_one
        (adr_step_mvNatRest_true (List.replicate m true ++ false :: rest)
          inp (false :: left0) right work none)
      have h2 := ih (true :: work)
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (m + 2)
        (adrCfg (some .mvNatRest) none inp (false :: left0) right work
          (true :: (List.replicate m true ++ false :: rest)))
        (adrCfg (some .mvNatRest) none inp (false :: left0) right
          (true :: work) (List.replicate m true ++ false :: rest))
        (some (adrCfg (some .mvAfter) none inp left0 right
          (List.replicate m true ++ true :: work) rest))
        h1 h2
      simpa [List.replicate_succ, List.cons_append, replicate_true_append_cons] using t

/-- Drain current max off `work` onto the park pile. -/
noncomputable def adr_evals_mvNat_drain (k i : ℕ)
    (left0 inp right rest : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvNat) none inp
        (List.replicate i true ++ false :: left0) right
        (List.replicate k true) (List.replicate k true ++ rest))
      (some (adrCfg (some .mvNat) none inp
        (List.replicate (i + k) true ++ false :: left0) right [] rest))
      k := by
  induction k generalizing i with
  | zero =>
      exact EvalsToInTime.refl afterDecodePairResultComputer.step
        (adrCfg (some .mvNat) none inp
          (List.replicate i true ++ false :: left0) right [] rest)
  | succ k ih =>
      have h1 := adr_evals_one
        (adr_step_mvNat_true_work_cons true (List.replicate k true)
          (List.replicate k true ++ rest) inp
          (List.replicate i true ++ false :: left0) right none)
      have h2 := ih (i + 1)
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1 k
        (adrCfg (some .mvNat) none inp
          (List.replicate i true ++ false :: left0) right
          (true :: List.replicate k true)
          (true :: (List.replicate k true ++ rest)))
        (adrCfg (some .mvNat) none inp
          (true :: (List.replicate i true ++ false :: left0)) right
          (List.replicate k true) (List.replicate k true ++ rest))
        (some (adrCfg (some .mvNat) none inp
          (List.replicate (i + 1 + k) true ++ false :: left0) right [] rest))
        h1 h2
      have hL : List.replicate (i + 1 + k) true ++ false :: left0 =
          List.replicate (i + (k + 1)) true ++ false :: left0 := by
        congr 1; ac_rfl
      simpa [List.replicate_succ, List.cons_append, hL] using t

/-- Lockstep `n` unary bits when `n ≤ k`. Parked count starts at `i`. -/
noncomputable def adr_evals_mvNat_le (n k i : ℕ) (hle : n ≤ k)
    (left0 inp right rest : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvNat) none inp
        (List.replicate i true ++ false :: left0) right
        (List.replicate k true) (encodeNat n ++ rest))
      (some (adrCfg (some .mvAfter) none inp left0 right
        (List.replicate (i + k) true) rest))
      (2 * n + i + 2) := by
  induction n generalizing k i with
  | zero =>
      have h1 := adr_evals_one
        (adr_step_mvNat_false rest inp
          (List.replicate i true ++ false :: left0) right
          (List.replicate k true) none)
      have h2 := adr_evals_mvNatRefund i left0 inp right
        (List.replicate k true) rest
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (i + 1)
        (adrCfg (some .mvNat) none inp
          (List.replicate i true ++ false :: left0) right
          (List.replicate k true) (false :: rest))
        (adrCfg (some .mvNatRefund) none inp
          (List.replicate i true ++ false :: left0) right
          (List.replicate k true) rest)
        (some (adrCfg (some .mvAfter) none inp left0 right
          (List.replicate i true ++ List.replicate k true) rest))
        h1 h2
      have henc : encodeNat 0 ++ rest = false :: rest := by simp [encodeNat]
      rw [henc, List.replicate_add]
      exact evalsToInTime_le_mono t (by omega)
  | succ n ih =>
      cases k with
      | zero => exact (Nat.not_succ_le_zero n hle).elim
      | succ k' =>
          have hle' : n ≤ k' := Nat.le_of_succ_le_succ hle
          have h1 := adr_evals_one
            (adr_step_mvNat_true_work_cons true (List.replicate k' true)
              (encodeNat n ++ rest) inp
              (List.replicate i true ++ false :: left0) right none)
          have h2 := ih k' (i + 1) hle'
          have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
            (2 * n + (i + 1) + 2)
            (adrCfg (some .mvNat) none inp
              (List.replicate i true ++ false :: left0) right
              (true :: List.replicate k' true)
              (true :: (encodeNat n ++ rest)))
            (adrCfg (some .mvNat) none inp
              (true :: (List.replicate i true ++ false :: left0)) right
              (List.replicate k' true) (encodeNat n ++ rest))
            (some (adrCfg (some .mvAfter) none inp left0 right
              (List.replicate (i + 1 + k') true) rest))
            h1 h2
          have t' : EvalsToInTime afterDecodePairResultComputer.step
              (adrCfg (some .mvNat) none inp
                (List.replicate i true ++ false :: left0) right
                (true :: List.replicate k' true)
                (true :: (encodeNat n ++ rest)))
              (some (adrCfg (some .mvAfter) none inp left0 right
                (List.replicate (i + 1 + k') true) rest))
              (2 * (n + 1) + i + 2) :=
            evalsToInTime_le_mono t (by omega)
          have hE : List.replicate (i + 1 + k') true =
              List.replicate (i + (k' + 1)) true := by
            congr 1; ac_rfl
          simpa [encodeNat, List.replicate_succ, List.cons_append, hE] using t'

/-- Grow the max when `k < n`. -/
noncomputable def adr_evals_mvNat_gt (n k : ℕ) (hgt : k < n)
    (left0 inp right rest : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvNat) none inp (false :: left0) right
        (List.replicate k true) (encodeNat n ++ rest))
      (some (adrCfg (some .mvAfter) none inp left0 right
        (List.replicate n true) rest))
      (2 * n + k + 4) := by
  have hsplit : encodeNat n ++ rest =
      List.replicate k true ++ true ::
        (List.replicate (n - k - 1) true ++ false :: rest) := by
    have hn : n = k + (n - k - 1) + 1 := by omega
    have hrep : List.replicate n true =
        List.replicate k true ++ true :: List.replicate (n - k - 1) true := by
      calc
        List.replicate n true
            = List.replicate (k + (n - k - 1) + 1) true := by rw [← hn]
        _ = List.replicate k true ++
              List.replicate ((n - k - 1) + 1) true := by
            simp [List.replicate_add, Nat.add_assoc]
        _ = List.replicate k true ++ true ::
              List.replicate (n - k - 1) true := by
            simp [List.replicate_succ]
    simp [encodeNat, hrep, List.append_assoc]
  have hdrain := adr_evals_mvNat_drain k 0 left0 inp right
    (true :: (List.replicate (n - k - 1) true ++ false :: rest))
  have hdrain' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvNat) none inp (false :: left0) right
        (List.replicate k true) (encodeNat n ++ rest))
      (some (adrCfg (some .mvNat) none inp
        (List.replicate k true ++ false :: left0) right []
        (true :: (List.replicate (n - k - 1) true ++ false :: rest))))
      k := by
    simpa [hsplit] using hdrain
  have htrig := adr_evals_one
    (adr_step_mvNat_true_work_nil
      (List.replicate (n - k - 1) true ++ false :: rest)
      inp (List.replicate k true ++ false :: left0) right none)
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step k 1
    (adrCfg (some .mvNat) none inp (false :: left0) right
      (List.replicate k true) (encodeNat n ++ rest))
    (adrCfg (some .mvNat) none inp
      (List.replicate k true ++ false :: left0) right []
      (true :: (List.replicate (n - k - 1) true ++ false :: rest)))
    (some (adrCfg (some .mvNatRestTake) none inp
      (List.replicate k true ++ false :: left0) right []
      (List.replicate (n - k - 1) true ++ false :: rest)))
    hdrain' htrig
  have t1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvNat) none inp (false :: left0) right
        (List.replicate k true) (encodeNat n ++ rest))
      (some (adrCfg (some .mvNatRestTake) none inp
        (List.replicate k true ++ false :: left0) right []
        (List.replicate (n - k - 1) true ++ false :: rest)))
      (k + 1) :=
    evalsToInTime_le_mono t1 (by omega)
  have htake := adr_evals_mvNatRestTake k left0 inp right []
    (List.replicate (n - k - 1) true ++ false :: rest)
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step (k + 1)
    (k + 1)
    (adrCfg (some .mvNat) none inp (false :: left0) right
      (List.replicate k true) (encodeNat n ++ rest))
    (adrCfg (some .mvNatRestTake) none inp
      (List.replicate k true ++ false :: left0) right []
      (List.replicate (n - k - 1) true ++ false :: rest))
    (some (adrCfg (some .mvNatRest) none inp (false :: left0) right
      (true :: (List.replicate k true ++ []))
      (List.replicate (n - k - 1) true ++ false :: rest)))
    t1' htake
  have hrest := adr_evals_mvNatRest (n - k - 1) left0 inp right
    (true :: (List.replicate k true ++ [])) rest
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
    ((k + 1) + (k + 1)) (n - k - 1 + 2)
    (adrCfg (some .mvNat) none inp (false :: left0) right
      (List.replicate k true) (encodeNat n ++ rest))
    (adrCfg (some .mvNatRest) none inp (false :: left0) right
      (true :: (List.replicate k true ++ []))
      (List.replicate (n - k - 1) true ++ false :: rest))
    (some (adrCfg (some .mvAfter) none inp left0 right
      (List.replicate (n - k - 1) true ++ (true :: (List.replicate k true ++ [])))
      rest))
    t2 hrest
  have hwork : List.replicate (n - k - 1) true ++
      (true :: (List.replicate k true ++ [])) = List.replicate n true := by
    simp only [List.append_nil]
    rw [replicate_true_append_cons]
    have hsum : List.replicate (n - k - 1) true ++ List.replicate k true =
        List.replicate (n - k - 1 + k) true := (List.replicate_add _ _ _).symm
    rw [hsum, ← List.replicate_succ]
    congr 1
    omega
  have t3' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvNat) none inp (false :: left0) right
        (List.replicate k true) (encodeNat n ++ rest))
      (some (adrCfg (some .mvAfter) none inp left0 right
        (List.replicate n true) rest))
      ((n - k - 1 + 2) + ((k + 1) + (k + 1))) := by
    rw [← hwork]
    exact t3
  exact evalsToInTime_le_mono t3' (by omega)

/-- Compare unary `n` to current max `k` and leave `max k n` on `work`. -/
noncomputable def adr_evals_mvNat (n k : ℕ)
    (left0 inp right rest : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvNat) none inp (false :: left0) right
        (List.replicate k true) (encodeNat n ++ rest))
      (some (adrCfg (some .mvAfter) none inp left0 right
        (List.replicate (max k n) true) rest))
      (2 * n + k + 4) := by
  by_cases hle : n ≤ k
  · have h := adr_evals_mvNat_le n k 0 hle left0 inp right rest
    have h' : EvalsToInTime afterDecodePairResultComputer.step
        (adrCfg (some .mvNat) none inp (false :: left0) right
          (List.replicate k true) (encodeNat n ++ rest))
        (some (adrCfg (some .mvAfter) none inp left0 right
          (List.replicate k true) rest))
        (2 * n + 2) := by
      simpa using h
    have hk : max k n = k := Nat.max_eq_left hle
    simpa [hk] using evalsToInTime_le_mono h' (by omega)
  · have hgt : k < n := Nat.lt_of_not_ge hle
    have h := adr_evals_mvNat_gt n k hgt left0 inp right rest
    have hk : max k n = n := Nat.max_eq_right (Nat.le_of_lt hgt)
    simpa [hk] using h

theorem mvParse_time_var (n k M : ℕ) (hk : k ≤ M) (hn : n ≤ M) :
    2 * n + k + 6 ≤ 32 * ((encodeFormula (.var n)).length + 1) * (M + 2) := by
  have hlen := length_encodeFormula_var n
  rw [hlen]
  nlinarith [hk, hn]

theorem mvParse_time_not (L M : ℕ) :
    32 * (L + 1) * (M + 2) + 2 ≤ 32 * (L + 2 + 1) * (M + 2) := by
  nlinarith

theorem mvParse_time_bin (Lψ Lχ M : ℕ) :
    32 * (Lχ + 1) * (M + 2) + (32 * (Lψ + 1) * (M + 2) + 3) ≤
      32 * (Lψ + Lχ + 3) * (M + 2) := by
  nlinarith

/-- Scan one encoded formula under a shared width budget `M`.
`k ≤ M` and `φ.maxVar ≤ M` keep child times below the parent bound. -/
noncomputable def adr_evals_mvParse_formula (φ : PropFormula) (k M : ℕ)
    (hk : k ≤ M) (hM : φ.maxVar ≤ M) (inp left right suffix : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvParse) none inp left right
        (List.replicate k true) (encodeFormula φ ++ suffix))
      (some (adrCfg (some .mvAfter) none inp left right
        (List.replicate (max k φ.maxVar) true) suffix))
      (32 * ((encodeFormula φ).length + 1) * (M + 2)) := by
  induction φ generalizing k inp suffix with
  | var n =>
      have h1 := adr_evals_one
        (adr_step_mvParse_false (false :: (encodeNat n ++ suffix))
          inp left right (List.replicate k true) none)
      have h2 := adr_evals_one
        (adr_step_mvTagF_false (encodeNat n ++ suffix)
          inp left right (List.replicate k true) none)
      have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 1 1
        (adrCfg (some .mvParse) none inp left right
          (List.replicate k true) (false :: false :: (encodeNat n ++ suffix)))
        (adrCfg (some .mvTagF) none inp left right
          (List.replicate k true) (false :: (encodeNat n ++ suffix)))
        (some (adrCfg (some .mvNat) none inp (false :: left) right
          (List.replicate k true) (encodeNat n ++ suffix)))
        h1 h2
      have t1' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .mvParse) none inp left right
            (List.replicate k true) (encodeFormula (.var n) ++ suffix))
          (some (adrCfg (some .mvNat) none inp (false :: left) right
            (List.replicate k true) (encodeNat n ++ suffix))) 2 := by
        simpa [encodeFormula] using evalsToInTime_le_mono t1 (by omega)
      have h3 := adr_evals_mvNat n k left inp right suffix
      have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step 2
        (2 * n + k + 4)
        (adrCfg (some .mvParse) none inp left right
          (List.replicate k true) (encodeFormula (.var n) ++ suffix))
        (adrCfg (some .mvNat) none inp (false :: left) right
          (List.replicate k true) (encodeNat n ++ suffix))
        (some (adrCfg (some .mvAfter) none inp left right
          (List.replicate (max k n) true) suffix))
        t1' h3
      have t2' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .mvParse) none inp left right
            (List.replicate k true) (encodeFormula (.var n) ++ suffix))
          (some (adrCfg (some .mvAfter) none inp left right
            (List.replicate (max k (PropFormula.var n).maxVar) true) suffix))
          (32 * ((encodeFormula (.var n)).length + 1) * (M + 2)) := by
        have hn : n ≤ M := by simpa [PropFormula.maxVar] using hM
        simpa [PropFormula.maxVar] using
          evalsToInTime_le_mono t2 (mvParse_time_var n k M hk hn)
      exact t2'
  | not ψ ih =>
      have h1 := adr_evals_one
        (adr_step_mvParse_false (true :: (encodeFormula ψ ++ suffix))
          inp left right (List.replicate k true) none)
      have h2 := adr_evals_one
        (adr_step_mvTagF_true (encodeFormula ψ ++ suffix)
          inp left right (List.replicate k true) none)
      have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 1 1
        (adrCfg (some .mvParse) none inp left right
          (List.replicate k true) (false :: true :: (encodeFormula ψ ++ suffix)))
        (adrCfg (some .mvTagF) none inp left right
          (List.replicate k true) (true :: (encodeFormula ψ ++ suffix)))
        (some (adrCfg (some .mvParse) none inp left right
          (List.replicate k true) (encodeFormula ψ ++ suffix)))
        h1 h2
      have t1' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .mvParse) none inp left right
            (List.replicate k true) (encodeFormula (.not ψ) ++ suffix))
          (some (adrCfg (some .mvParse) none inp left right
            (List.replicate k true) (encodeFormula ψ ++ suffix))) 2 := by
        simpa [encodeFormula] using evalsToInTime_le_mono t1 (by omega)
      have hψ : ψ.maxVar ≤ M := by simpa [PropFormula.maxVar] using hM
      have h3 := ih k hk hψ inp suffix
      have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step 2
        (32 * ((encodeFormula ψ).length + 1) * (M + 2))
        (adrCfg (some .mvParse) none inp left right
          (List.replicate k true) (encodeFormula (.not ψ) ++ suffix))
        (adrCfg (some .mvParse) none inp left right
          (List.replicate k true) (encodeFormula ψ ++ suffix))
        (some (adrCfg (some .mvAfter) none inp left right
          (List.replicate (max k ψ.maxVar) true) suffix))
        t1' h3
      have hlen := length_encodeFormula_not ψ
      have t2' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .mvParse) none inp left right
            (List.replicate k true) (encodeFormula (.not ψ) ++ suffix))
          (some (adrCfg (some .mvAfter) none inp left right
            (List.replicate (max k ψ.maxVar) true) suffix))
          (32 * ((encodeFormula (.not ψ)).length + 1) * (M + 2)) :=
        evalsToInTime_le_mono t2 (by
          rw [hlen]
          exact mvParse_time_not (encodeFormula ψ).length M)
      simpa [PropFormula.maxVar] using t2'
  | and ψ χ ihψ ihχ =>
      have hψM : ψ.maxVar ≤ M :=
        le_trans (le_max_left ψ.maxVar χ.maxVar) (by simpa [PropFormula.maxVar] using hM)
      have hχM : χ.maxVar ≤ M :=
        le_trans (le_max_right ψ.maxVar χ.maxVar) (by simpa [PropFormula.maxVar] using hM)
      have h1 := adr_evals_one
        (adr_step_mvParse_true (false :: (encodeFormula ψ ++ encodeFormula χ ++
          suffix)) inp left right (List.replicate k true) none)
      have h2 := adr_evals_one
        (adr_step_mvTagT_cons false (encodeFormula ψ ++ encodeFormula χ ++
          suffix) inp left right (List.replicate k true) none)
      have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 1 1
        (adrCfg (some .mvParse) none inp left right
          (List.replicate k true)
          (true :: false :: (encodeFormula ψ ++ encodeFormula χ ++ suffix)))
        (adrCfg (some .mvTagT) none inp left right
          (List.replicate k true)
          (false :: (encodeFormula ψ ++ encodeFormula χ ++ suffix)))
        (some (adrCfg (some .mvParse) none (true :: inp) left right
          (List.replicate k true) (encodeFormula ψ ++ encodeFormula χ ++ suffix)))
        h1 h2
      have t1' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .mvParse) none inp left right
            (List.replicate k true) (encodeFormula (.and ψ χ) ++ suffix))
          (some (adrCfg (some .mvParse) none (true :: inp) left right
            (List.replicate k true)
            (encodeFormula ψ ++ encodeFormula χ ++ suffix))) 2 := by
        simpa [encodeFormula, List.append_assoc] using
          evalsToInTime_le_mono t1 (by omega)
      have h3 := ihψ k hk hψM (true :: inp) (encodeFormula χ ++ suffix)
      have h3' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .mvParse) none (true :: inp) left right
            (List.replicate k true)
            (encodeFormula ψ ++ encodeFormula χ ++ suffix))
          (some (adrCfg (some .mvAfter) none (true :: inp) left right
            (List.replicate (max k ψ.maxVar) true)
            (encodeFormula χ ++ suffix)))
          (32 * ((encodeFormula ψ).length + 1) * (M + 2)) := by
        simpa [List.append_assoc] using h3
      have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step 2
        (32 * ((encodeFormula ψ).length + 1) * (M + 2))
        (adrCfg (some .mvParse) none inp left right
          (List.replicate k true) (encodeFormula (.and ψ χ) ++ suffix))
        (adrCfg (some .mvParse) none (true :: inp) left right
          (List.replicate k true) (encodeFormula ψ ++ encodeFormula χ ++ suffix))
        (some (adrCfg (some .mvAfter) none (true :: inp) left right
          (List.replicate (max k ψ.maxVar) true)
          (encodeFormula χ ++ suffix)))
        t1' h3'
      have t2' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .mvParse) none inp left right
            (List.replicate k true) (encodeFormula (.and ψ χ) ++ suffix))
          (some (adrCfg (some .mvAfter) none (true :: inp) left right
            (List.replicate (max k ψ.maxVar) true)
            (encodeFormula χ ++ suffix)))
          (32 * ((encodeFormula ψ).length + 1) * (M + 2) + 2) :=
        evalsToInTime_le_mono t2 (by omega)
      have h4 := adr_evals_one
        (adr_step_mvAfter_cons true inp left right
          (List.replicate (max k ψ.maxVar) true)
          (encodeFormula χ ++ suffix) none)
      have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
        (32 * ((encodeFormula ψ).length + 1) * (M + 2) + 2) 1
        (adrCfg (some .mvParse) none inp left right
          (List.replicate k true) (encodeFormula (.and ψ χ) ++ suffix))
        (adrCfg (some .mvAfter) none (true :: inp) left right
          (List.replicate (max k ψ.maxVar) true) (encodeFormula χ ++ suffix))
        (some (adrCfg (some .mvParse) none inp left right
          (List.replicate (max k ψ.maxVar) true) (encodeFormula χ ++ suffix)))
        t2' h4
      have t3' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .mvParse) none inp left right
            (List.replicate k true) (encodeFormula (.and ψ χ) ++ suffix))
          (some (adrCfg (some .mvParse) none inp left right
            (List.replicate (max k ψ.maxVar) true) (encodeFormula χ ++ suffix)))
          (32 * ((encodeFormula ψ).length + 1) * (M + 2) + 3) :=
        evalsToInTime_le_mono t3 (by omega)
      have hk' : max k ψ.maxVar ≤ M := max_le hk hψM
      have h5 := ihχ (max k ψ.maxVar) hk' hχM inp suffix
      have t4 := EvalsToInTime.trans afterDecodePairResultComputer.step
        (32 * ((encodeFormula ψ).length + 1) * (M + 2) + 3)
        (32 * ((encodeFormula χ).length + 1) * (M + 2))
        (adrCfg (some .mvParse) none inp left right
          (List.replicate k true) (encodeFormula (.and ψ χ) ++ suffix))
        (adrCfg (some .mvParse) none inp left right
          (List.replicate (max k ψ.maxVar) true) (encodeFormula χ ++ suffix))
        (some (adrCfg (some .mvAfter) none inp left right
          (List.replicate (max (max k ψ.maxVar) χ.maxVar) true) suffix))
        t3' h5
      have hmax : max (max k ψ.maxVar) χ.maxVar =
          max k (PropFormula.and ψ χ).maxVar := by
        simp [PropFormula.maxVar, Nat.max_assoc]
      have t4' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .mvParse) none inp left right
            (List.replicate k true) (encodeFormula (.and ψ χ) ++ suffix))
          (some (adrCfg (some .mvAfter) none inp left right
            (List.replicate (max (max k ψ.maxVar) χ.maxVar) true) suffix))
          (32 * ((encodeFormula (.and ψ χ)).length + 1) * (M + 2)) :=
        evalsToInTime_le_mono t4 (by
          have hlen := length_encodeFormula_and ψ χ
          rw [hlen]
          exact mvParse_time_bin (encodeFormula ψ).length
            (encodeFormula χ).length M)
      simpa [hmax] using t4'
  | or ψ χ ihψ ihχ =>
      have hψM : ψ.maxVar ≤ M :=
        le_trans (le_max_left ψ.maxVar χ.maxVar) (by simpa [PropFormula.maxVar] using hM)
      have hχM : χ.maxVar ≤ M :=
        le_trans (le_max_right ψ.maxVar χ.maxVar) (by simpa [PropFormula.maxVar] using hM)
      have h1 := adr_evals_one
        (adr_step_mvParse_true (true :: (encodeFormula ψ ++ encodeFormula χ ++
          suffix)) inp left right (List.replicate k true) none)
      have h2 := adr_evals_one
        (adr_step_mvTagT_cons true (encodeFormula ψ ++ encodeFormula χ ++
          suffix) inp left right (List.replicate k true) none)
      have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 1 1
        (adrCfg (some .mvParse) none inp left right
          (List.replicate k true)
          (true :: true :: (encodeFormula ψ ++ encodeFormula χ ++ suffix)))
        (adrCfg (some .mvTagT) none inp left right
          (List.replicate k true)
          (true :: (encodeFormula ψ ++ encodeFormula χ ++ suffix)))
        (some (adrCfg (some .mvParse) none (true :: inp) left right
          (List.replicate k true) (encodeFormula ψ ++ encodeFormula χ ++ suffix)))
        h1 h2
      have t1' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .mvParse) none inp left right
            (List.replicate k true) (encodeFormula (.or ψ χ) ++ suffix))
          (some (adrCfg (some .mvParse) none (true :: inp) left right
            (List.replicate k true)
            (encodeFormula ψ ++ encodeFormula χ ++ suffix))) 2 := by
        simpa [encodeFormula, List.append_assoc] using
          evalsToInTime_le_mono t1 (by omega)
      have h3 := ihψ k hk hψM (true :: inp) (encodeFormula χ ++ suffix)
      have h3' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .mvParse) none (true :: inp) left right
            (List.replicate k true)
            (encodeFormula ψ ++ encodeFormula χ ++ suffix))
          (some (adrCfg (some .mvAfter) none (true :: inp) left right
            (List.replicate (max k ψ.maxVar) true)
            (encodeFormula χ ++ suffix)))
          (32 * ((encodeFormula ψ).length + 1) * (M + 2)) := by
        simpa [List.append_assoc] using h3
      have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step 2
        (32 * ((encodeFormula ψ).length + 1) * (M + 2))
        (adrCfg (some .mvParse) none inp left right
          (List.replicate k true) (encodeFormula (.or ψ χ) ++ suffix))
        (adrCfg (some .mvParse) none (true :: inp) left right
          (List.replicate k true) (encodeFormula ψ ++ encodeFormula χ ++ suffix))
        (some (adrCfg (some .mvAfter) none (true :: inp) left right
          (List.replicate (max k ψ.maxVar) true)
          (encodeFormula χ ++ suffix)))
        t1' h3'
      have t2' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .mvParse) none inp left right
            (List.replicate k true) (encodeFormula (.or ψ χ) ++ suffix))
          (some (adrCfg (some .mvAfter) none (true :: inp) left right
            (List.replicate (max k ψ.maxVar) true)
            (encodeFormula χ ++ suffix)))
          (32 * ((encodeFormula ψ).length + 1) * (M + 2) + 2) :=
        evalsToInTime_le_mono t2 (by omega)
      have h4 := adr_evals_one
        (adr_step_mvAfter_cons true inp left right
          (List.replicate (max k ψ.maxVar) true)
          (encodeFormula χ ++ suffix) none)
      have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
        (32 * ((encodeFormula ψ).length + 1) * (M + 2) + 2) 1
        (adrCfg (some .mvParse) none inp left right
          (List.replicate k true) (encodeFormula (.or ψ χ) ++ suffix))
        (adrCfg (some .mvAfter) none (true :: inp) left right
          (List.replicate (max k ψ.maxVar) true) (encodeFormula χ ++ suffix))
        (some (adrCfg (some .mvParse) none inp left right
          (List.replicate (max k ψ.maxVar) true) (encodeFormula χ ++ suffix)))
        t2' h4
      have t3' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .mvParse) none inp left right
            (List.replicate k true) (encodeFormula (.or ψ χ) ++ suffix))
          (some (adrCfg (some .mvParse) none inp left right
            (List.replicate (max k ψ.maxVar) true) (encodeFormula χ ++ suffix)))
          (32 * ((encodeFormula ψ).length + 1) * (M + 2) + 3) :=
        evalsToInTime_le_mono t3 (by omega)
      have hk' : max k ψ.maxVar ≤ M := max_le hk hψM
      have h5 := ihχ (max k ψ.maxVar) hk' hχM inp suffix
      have t4 := EvalsToInTime.trans afterDecodePairResultComputer.step
        (32 * ((encodeFormula ψ).length + 1) * (M + 2) + 3)
        (32 * ((encodeFormula χ).length + 1) * (M + 2))
        (adrCfg (some .mvParse) none inp left right
          (List.replicate k true) (encodeFormula (.or ψ χ) ++ suffix))
        (adrCfg (some .mvParse) none inp left right
          (List.replicate (max k ψ.maxVar) true) (encodeFormula χ ++ suffix))
        (some (adrCfg (some .mvAfter) none inp left right
          (List.replicate (max (max k ψ.maxVar) χ.maxVar) true) suffix))
        t3' h5
      have hmax : max (max k ψ.maxVar) χ.maxVar =
          max k (PropFormula.or ψ χ).maxVar := by
        simp [PropFormula.maxVar, Nat.max_assoc]
      have t4' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .mvParse) none inp left right
            (List.replicate k true) (encodeFormula (.or ψ χ) ++ suffix))
          (some (adrCfg (some .mvAfter) none inp left right
            (List.replicate (max (max k ψ.maxVar) χ.maxVar) true) suffix))
          (32 * ((encodeFormula (.or ψ χ)).length + 1) * (M + 2)) :=
        evalsToInTime_le_mono t4 (by
          have hlen := length_encodeFormula_or ψ χ
          rw [hlen]
          exact mvParse_time_bin (encodeFormula ψ).length
            (encodeFormula χ).length M)
      simpa [hmax] using t4'

theorem reverse_pow2BitsLE (n : ℕ) :
    (pow2BitsLE n).reverse = true :: List.replicate n false := by
  simp [pow2BitsLE, List.reverse_append, List.reverse_cons, List.reverse_replicate]

/-- Convert unary max `true^k` plus the finish marker into `pow2BitsLE (k+1)`. -/
noncomputable def adr_evals_mvToPow2 (k : ℕ)
    (inp left right marker : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvToPow2) none inp left right
        (List.replicate k true) marker)
      (some (adrCfg (some .unparkMark) none inp left right []
        (List.replicate (k + 1) false ++ marker)))
      (k + 1) := by
  induction k generalizing marker with
  | zero =>
      simpa [List.replicate] using
        adr_evals_one (adr_step_mvToPow2_nil inp left right marker none)
  | succ k ih =>
      have h1 := adr_evals_one
        (adr_step_mvToPow2_cons true (List.replicate k true)
          inp left right marker none)
      have h2 := ih (false :: marker)
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (k + 1)
        (adrCfg (some .mvToPow2) none inp left right
          (true :: List.replicate k true) marker)
        (adrCfg (some .mvToPow2) none inp left right
          (List.replicate k true) (false :: marker))
        (some (adrCfg (some .unparkMark) none inp left right []
          (List.replicate (k + 1) false ++ false :: marker)))
        h1 h2
      simpa [List.replicate_succ, List.cons_append, List.append_assoc,
        replicate_false_append_cons] using t

/-- Restore `n` parked width falses, stopping at the first table true. -/
noncomputable def adr_evals_unparkFalses (n : ℕ)
    (table inp left work out : List Bool)
    (ht : table.head? ≠ some false) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .unparkFalses) none inp left
        (List.replicate n false ++ table) work out)
      (some (adrCfg (some .eqA) none
        (List.replicate n false ++ inp) left table work out))
      (n + 1) := by
  induction n generalizing inp with
  | zero =>
      cases table with
      | nil =>
          simpa using adr_evals_one
            (adr_step_unparkFalses_nil inp left work out none)
      | cons b rest =>
          have hb : b = true := by
            cases b
            · exact (ht (by simp)).elim
            · rfl
          subst hb
          simpa using adr_evals_one
            (adr_step_unparkFalses_true rest inp left work out none)
  | succ n ih =>
      have h1 := adr_evals_one
        (adr_step_unparkFalses_false (List.replicate n false ++ table)
          inp left work out none)
      have h2 := ih (false :: inp)
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (n + 1)
        (adrCfg (some .unparkFalses) none inp left
          (false :: (List.replicate n false ++ table)) work out)
        (adrCfg (some .unparkFalses) none (false :: inp) left
          (List.replicate n false ++ table) work out)
        (some (adrCfg (some .eqA) none
          (List.replicate n false ++ false :: inp) left table work out))
        h1 h2
      simpa [List.replicate_succ, List.cons_append, List.append_assoc,
        replicate_false_append_cons] using t

/-- Unpark `reverse (pow2BitsLE n) ++ table` back to `pow2BitsLE n` on `inp`. -/
noncomputable def adr_evals_unpark (n : ℕ)
    (table inp left work out : List Bool)
    (ht : table.head? ≠ some false) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .unparkMark) none inp left
        ((pow2BitsLE n).reverse ++ table) work out)
      (some (adrCfg (some .eqA) none
        (List.replicate n false ++ true :: inp) left table work out))
      (n + 2) := by
  have h1 := adr_evals_one
    (adr_step_unparkMark_true (List.replicate n false ++ table)
      inp left work out none)
  have h1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .unparkMark) none inp left
        ((pow2BitsLE n).reverse ++ table) work out)
      (some (adrCfg (some .unparkFalses) none (true :: inp) left
        (List.replicate n false ++ table) work out)) 1 := by
    simpa [reverse_pow2BitsLE] using h1
  have h2 := adr_evals_unparkFalses n table (true :: inp) left work out ht
  have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
    (n + 1) _ _ _ h1' h2
  exact evalsToInTime_le_mono t (by omega)

/-- Matching `pow2BitsLE n` on `inp` and `out` enters the index loop. -/
noncomputable def adr_evals_eq_pow2 (n : ℕ)
    (left right work : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .eqA) none (pow2BitsLE n) left right work (pow2BitsLE n))
      (some (adrCfg (some .indexLoop) none [] left right
        (List.replicate n false ++ work) []))
      (2 * n + 1) := by
  induction n generalizing work with
  | zero =>
      simpa [pow2BitsLE] using adr_evals_one
        (adr_step_eqA_true_true [] left right work none)
  | succ n ih =>
      have hsplit : pow2BitsLE (n + 1) = false :: pow2BitsLE n := by
        simp [pow2BitsLE, List.replicate_succ]
      have h1 := adr_evals_one
        (adr_step_eqA_false (pow2BitsLE n) left right work
          (false :: pow2BitsLE n) none)
      have h1' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .eqA) none (pow2BitsLE (n + 1)) left right work
            (pow2BitsLE (n + 1)))
          (some (adrCfg (some .eqB) none (pow2BitsLE n) left right work
            (false :: pow2BitsLE n))) 1 := by
        simpa [hsplit] using h1
      have h2 := adr_evals_one
        (adr_step_eqB_false (pow2BitsLE n) (pow2BitsLE n) left right work none)
      have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 1 1
        (adrCfg (some .eqA) none (pow2BitsLE (n + 1)) left right work
          (pow2BitsLE (n + 1)))
        (adrCfg (some .eqB) none (pow2BitsLE n) left right work
          (false :: pow2BitsLE n))
        (some (adrCfg (some .eqA) none (pow2BitsLE n) left right
          (false :: work) (pow2BitsLE n)))
        h1' h2
      have h3 := ih (false :: work)
      have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step 2
        (2 * n + 1)
        (adrCfg (some .eqA) none (pow2BitsLE (n + 1)) left right work
          (pow2BitsLE (n + 1)))
        (adrCfg (some .eqA) none (pow2BitsLE n) left right
          (false :: work) (pow2BitsLE n))
        (some (adrCfg (some .indexLoop) none [] left right
          (List.replicate n false ++ false :: work) []))
        t1 h3
      have hwork : List.replicate n false ++ false :: work =
          List.replicate (n + 1) false ++ work := by
        simpa [List.replicate_succ] using
          replicate_false_append_cons n work
      simpa [hwork] using evalsToInTime_le_mono t2 (by omega)

/-- Unequal parked widths fail the zipper and emit `[true]`. -/
noncomputable def adr_evals_eq_pow2_ne (n m : ℕ)
    (hne : n ≠ m) (left right work : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .eqA) none (pow2BitsLE n) left right work (pow2BitsLE m))
      (some (adrCfg none none [] [] [] [] [true]))
      (2 * (n + m) + work.length + left.length + right.length + 8) := by
  induction n generalizing m work with
  | zero =>
      cases m with
      | zero => exact (hne rfl).elim
      | succ m =>
          have hsplit : pow2BitsLE (m + 1) = false :: pow2BitsLE m := by
            simp [pow2BitsLE, List.replicate_succ]
          have h1 := adr_evals_one
            (adr_step_eqA_true_false (pow2BitsLE m) left right work none)
          have h1' : EvalsToInTime afterDecodePairResultComputer.step
              (adrCfg (some .eqA) none (pow2BitsLE 0) left right work
                (pow2BitsLE (m + 1)))
              (some (adrCfg (some .failDrain) none [] left right work
                (pow2BitsLE m))) 1 := by
            simpa [pow2BitsLE, hsplit] using h1
          have h2 := adr_evals_failDrain [] left right work (pow2BitsLE m) none
          have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
            _ _ _ _ h1' h2
          exact evalsToInTime_le_mono t (by simp [length_pow2BitsLE]; omega)
  | succ n ih =>
      cases m with
      | zero =>
          have hsplit : pow2BitsLE (n + 1) = false :: pow2BitsLE n := by
            simp [pow2BitsLE, List.replicate_succ]
          have h1 := adr_evals_one
            (adr_step_eqA_false (pow2BitsLE n) left right work
              (pow2BitsLE 0) none)
          have h1' : EvalsToInTime afterDecodePairResultComputer.step
              (adrCfg (some .eqA) none (pow2BitsLE (n + 1)) left right work
                (pow2BitsLE 0))
              (some (adrCfg (some .eqB) none (pow2BitsLE n) left right work
                (pow2BitsLE 0))) 1 := by
            simpa [hsplit, pow2BitsLE] using h1
          have h2 := adr_evals_one
            (adr_step_eqB_true [] (pow2BitsLE n) left right work none)
          have h2' : EvalsToInTime afterDecodePairResultComputer.step
              (adrCfg (some .eqB) none (pow2BitsLE n) left right work
                (pow2BitsLE 0))
              (some (adrCfg (some .failDrain) none (pow2BitsLE n) left right
                work [])) 1 := by
            simpa [pow2BitsLE] using h2
          have t12 := EvalsToInTime.trans afterDecodePairResultComputer.step 1 1
            _ _ _ h1' h2'
          have h3 := adr_evals_failDrain (pow2BitsLE n) left right work [] none
          have t := EvalsToInTime.trans afterDecodePairResultComputer.step 2
            _ _ _ _ t12 h3
          exact evalsToInTime_le_mono t (by simp [length_pow2BitsLE]; omega)
      | succ m =>
          have hne' : n ≠ m := by omega
          have hsplitn : pow2BitsLE (n + 1) = false :: pow2BitsLE n := by
            simp [pow2BitsLE, List.replicate_succ]
          have hsplitm : pow2BitsLE (m + 1) = false :: pow2BitsLE m := by
            simp [pow2BitsLE, List.replicate_succ]
          have h1 := adr_evals_one
            (adr_step_eqA_false (pow2BitsLE n) left right work
              (false :: pow2BitsLE m) none)
          have h1' : EvalsToInTime afterDecodePairResultComputer.step
              (adrCfg (some .eqA) none (pow2BitsLE (n + 1)) left right work
                (pow2BitsLE (m + 1)))
              (some (adrCfg (some .eqB) none (pow2BitsLE n) left right work
                (false :: pow2BitsLE m))) 1 := by
            simpa [hsplitn, hsplitm] using h1
          have h2 := adr_evals_one
            (adr_step_eqB_false (pow2BitsLE m) (pow2BitsLE n) left right
              work none)
          have t12 := EvalsToInTime.trans afterDecodePairResultComputer.step 1 1
            _ _ _ h1' h2
          have h3 := ih m hne' (false :: work)
          have t := EvalsToInTime.trans afterDecodePairResultComputer.step 2
            _ _ _ _ t12 h3
          exact evalsToInTime_le_mono t (by simp [List.length_cons]; omega)

/-- After a successful parse, convert max to bits and unpark to `eqA`. Width
need not match: `out` holds `pow2BitsLE (φ.maxVar+1)` and `inp` holds
`pow2BitsLE n`. -/
noncomputable def adr_evals_mvParse_to_eqA (φ : PropFormula)
    (table : List Bool) (n : ℕ)
    (ht : table.head? ≠ some false) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvParse) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table) [] (encodeFormula φ))
      (some (adrCfg (some .eqA) none (pow2BitsLE n)
        (encodeFormula φ).reverse table [] (pow2BitsLE (φ.maxVar + 1))))
      (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) +
        φ.maxVar + n + 5) := by
  have hk : (0 : ℕ) ≤ φ.maxVar := Nat.zero_le _
  have hM : φ.maxVar ≤ φ.maxVar := le_rfl
  have hparse := adr_evals_mvParse_formula φ 0 φ.maxVar hk hM []
    (encodeFormula φ).reverse ((pow2BitsLE n).reverse ++ table) []
  have hparse' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvParse) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table) [] (encodeFormula φ))
      (some (adrCfg (some .mvAfter) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table)
        (List.replicate φ.maxVar true) []))
      (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2)) := by
    simpa [List.append_nil] using hparse
  have hafter := adr_evals_one
    (adr_step_mvAfter_nil (encodeFormula φ).reverse
      ((pow2BitsLE n).reverse ++ table) (List.replicate φ.maxVar true) [] none)
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2)) 1 _ _ _ hparse' hafter
  have t1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvParse) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table) [] (encodeFormula φ))
      (some (adrCfg (some .mvFinish) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table)
        (List.replicate φ.maxVar true) []))
      (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) + 1) :=
    evalsToInTime_le_mono t1 (by omega)
  have hfinish := adr_evals_one
    (adr_step_mvFinish_nil [] (encodeFormula φ).reverse
      ((pow2BitsLE n).reverse ++ table) (List.replicate φ.maxVar true) none)
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) + 1) 1 _ _ _ t1' hfinish
  have t2' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvParse) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table) [] (encodeFormula φ))
      (some (adrCfg (some .mvToPow2) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table)
        (List.replicate φ.maxVar true) [true]))
      (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) + 2) :=
    evalsToInTime_le_mono t2 (by omega)
  have hpow := adr_evals_mvToPow2 φ.maxVar [] (encodeFormula φ).reverse
    ((pow2BitsLE n).reverse ++ table) [true]
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) + 2)
    (φ.maxVar + 1) _ _ _ t2' hpow
  have t3' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvParse) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table) [] (encodeFormula φ))
      (some (adrCfg (some .unparkMark) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table) []
        (List.replicate (φ.maxVar + 1) false ++ [true])))
      (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) +
        φ.maxVar + 3) :=
    evalsToInTime_le_mono t3 (by omega)
  have hunpark := adr_evals_unpark n table [] (encodeFormula φ).reverse []
    (List.replicate (φ.maxVar + 1) false ++ [true]) ht
  have t4 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) + φ.maxVar + 3)
    (n + 2) _ _ _ t3' hunpark
  have hout : List.replicate (φ.maxVar + 1) false ++ [true] =
      pow2BitsLE (φ.maxVar + 1) := by
    simp [pow2BitsLE]
  simpa [hout] using evalsToInTime_le_mono t4 (by omega)

/-- Width mismatch at `eqA` emits `[true]`. -/
noncomputable def adr_evals_mvParse_width_ne (φ : PropFormula)
    (table : List Bool) (n : ℕ)
    (hne : n ≠ φ.maxVar + 1)
    (ht : table.head? ≠ some false) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvParse) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table) [] (encodeFormula φ))
      (some (adrCfg none none [] [] [] [] [true]))
      (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) +
        φ.maxVar + n + 5 +
        2 * (n + (φ.maxVar + 1)) + (encodeFormula φ).reverse.length +
          table.length + 8) := by
  have h1 := adr_evals_mvParse_to_eqA φ table n ht
  have h2 := adr_evals_eq_pow2_ne n (φ.maxVar + 1) hne
    (encodeFormula φ).reverse table []
  have t := EvalsToInTime.trans afterDecodePairResultComputer.step
    _ _ _ _ _ h1 h2
  exact evalsToInTime_le_mono t (le_of_eq (by
    simp [List.length_reverse]
    ring))


/-- After a successful parse, finish, convert max to bits, unpark, and match width. -/
noncomputable def adr_evals_mvParse_to_indexLoop (φ : PropFormula)
    (table : List Bool) (n : ℕ)
    (hn : n = φ.maxVar + 1)
    (ht : table.head? ≠ some false) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvParse) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table) [] (encodeFormula φ))
      (some (adrCfg (some .indexLoop) none [] (encodeFormula φ).reverse table
        (List.replicate n false) []))
      (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) +
        4 * n + 4 * φ.maxVar + 16) := by
  have hk : (0 : ℕ) ≤ φ.maxVar := Nat.zero_le _
  have hM : φ.maxVar ≤ φ.maxVar := le_rfl
  have hparse := adr_evals_mvParse_formula φ 0 φ.maxVar hk hM []
    (encodeFormula φ).reverse ((pow2BitsLE n).reverse ++ table) []
  have hparse' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvParse) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table) [] (encodeFormula φ))
      (some (adrCfg (some .mvAfter) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table)
        (List.replicate φ.maxVar true) []))
      (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2)) := by
    simpa [List.append_nil] using hparse
  have hafter := adr_evals_one
    (adr_step_mvAfter_nil (encodeFormula φ).reverse
      ((pow2BitsLE n).reverse ++ table) (List.replicate φ.maxVar true) [] none)
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2)) 1 _ _ _ hparse' hafter
  have t1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvParse) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table) [] (encodeFormula φ))
      (some (adrCfg (some .mvFinish) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table)
        (List.replicate φ.maxVar true) []))
      (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) + 1) :=
    evalsToInTime_le_mono t1 (by omega)
  have hfinish := adr_evals_one
    (adr_step_mvFinish_nil [] (encodeFormula φ).reverse
      ((pow2BitsLE n).reverse ++ table) (List.replicate φ.maxVar true) none)
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) + 1) 1 _ _ _ t1' hfinish
  have t2' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvParse) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table) [] (encodeFormula φ))
      (some (adrCfg (some .mvToPow2) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table)
        (List.replicate φ.maxVar true) [true]))
      (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) + 2) :=
    evalsToInTime_le_mono t2 (by omega)
  have hpow := adr_evals_mvToPow2 φ.maxVar [] (encodeFormula φ).reverse
    ((pow2BitsLE n).reverse ++ table) [true]
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) + 2)
    (φ.maxVar + 1) _ _ _ t2' hpow
  have t3' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvParse) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table) [] (encodeFormula φ))
      (some (adrCfg (some .unparkMark) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table) []
        (List.replicate (φ.maxVar + 1) false ++ [true])))
      (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) +
        φ.maxVar + 3) :=
    evalsToInTime_le_mono t3 (by omega)
  have hunpark := adr_evals_unpark n table [] (encodeFormula φ).reverse []
    (List.replicate (φ.maxVar + 1) false ++ [true]) ht
  have t4 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) + φ.maxVar + 3)
    (n + 2) _ _ _ t3' hunpark
  have hout : List.replicate (φ.maxVar + 1) false ++ [true] = pow2BitsLE n := by
    simp [pow2BitsLE, hn]
  have t4' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .mvParse) none [] (encodeFormula φ).reverse
        ((pow2BitsLE n).reverse ++ table) [] (encodeFormula φ))
      (some (adrCfg (some .eqA) none (pow2BitsLE n)
        (encodeFormula φ).reverse table [] (pow2BitsLE n)))
      (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) +
        φ.maxVar + n + 5) := by
    have : List.replicate n false ++ [true] = pow2BitsLE n := by
      simp [pow2BitsLE]
    simpa [this, hout] using evalsToInTime_le_mono t4 (by omega)
  have heq := adr_evals_eq_pow2 n (encodeFormula φ).reverse table []
  have t5 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (32 * ((encodeFormula φ).length + 1) * (φ.maxVar + 2) +
      φ.maxVar + n + 5)
    (2 * n + 1) _ _ _ t4' heq
  simpa [List.append_nil] using evalsToInTime_le_mono t5 (by omega)

/-- Park the assignment from `work` onto `inp`. -/
noncomputable def adr_evals_idxParkAsg (asg inp left right out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .idxParkAsg) none inp left right asg out)
      (some (adrCfg (some .idxCopyL) none (asg.reverse ++ inp) left right
        [] out))
      (asg.length + 1) := by
  induction asg generalizing inp with
  | nil =>
      simpa using adr_evals_one
        (adr_step_idxParkAsg_nil inp left right out none)
  | cons b rest ih =>
      have h1 := adr_evals_one
        (adr_step_idxParkAsg_cons b rest inp left right out none)
      have h2 := ih (b :: inp)
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (rest.length + 1)
        (adrCfg (some .idxParkAsg) none inp left right (b :: rest) out)
        (adrCfg (some .idxParkAsg) none (b :: inp) left right rest out)
        (some (adrCfg (some .idxCopyL) none (rest.reverse ++ b :: inp)
          left right [] out))
        h1 h2
      simpa [List.reverse_cons, List.append_assoc] using t

/-- Copy `left` onto `work` and `out` as `left.reverse`. -/
noncomputable def adr_evals_idxCopyL (left inp right work out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .idxCopyL) none inp left right work out)
      (some (adrCfg (some .idxCopyRest) none inp [] right
        (left.reverse ++ work) (left.reverse ++ out)))
      (left.length + 1) := by
  induction left generalizing work out with
  | nil =>
      simpa using adr_evals_one
        (adr_step_idxCopyL_nil inp right work out none)
  | cons b rest ih =>
      have h1 := adr_evals_one
        (adr_step_idxCopyL_cons b rest inp right work out none)
      have h2 := ih (b :: work) (b :: out)
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (rest.length + 1)
        (adrCfg (some .idxCopyL) none inp (b :: rest) right work out)
        (adrCfg (some .idxCopyL) none inp rest right (b :: work) (b :: out))
        (some (adrCfg (some .idxCopyRest) none inp [] right
          (rest.reverse ++ b :: work) (rest.reverse ++ b :: out)))
        h1 h2
      simpa [List.reverse_cons, List.append_assoc] using t

/-- Restore `left` from the work copy; `out` keeps the parse-order formula. -/
noncomputable def adr_evals_idxCopyRest (work inp left right out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .idxCopyRest) none inp left right work out)
      (some (adrCfg (some .evParse) none inp (work.reverse ++ left) right
        [] out))
      (work.length + 1) := by
  induction work generalizing left with
  | nil =>
      simpa using adr_evals_one
        (adr_step_idxCopyRest_nil inp left right out none)
  | cons b rest ih =>
      have h1 := adr_evals_one
        (adr_step_idxCopyRest_cons b rest inp left right out none)
      have h2 := ih (b :: left)
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (rest.length + 1)
        (adrCfg (some .idxCopyRest) none inp left right (b :: rest) out)
        (adrCfg (some .idxCopyRest) none inp (b :: left) right rest out)
        (some (adrCfg (some .evParse) none inp (rest.reverse ++ b :: left)
          right [] out))
        h1 h2
      simpa [List.reverse_cons, List.append_assoc] using t

/-- One fuel bit: park assignment, copy formula, enter `evParse`. -/
noncomputable def adr_evals_indexLoop_to_evParse (φCode inp work rest : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .indexLoop) none inp φCode.reverse (true :: rest) work [])
      (some (adrCfg (some .evParse) none (work.reverse ++ inp) φCode.reverse
        rest [] φCode))
      (work.length + 2 * φCode.length + 4) := by
  have h1 := adr_evals_one
    (adr_step_indexLoop_true rest inp φCode.reverse work [] none)
  have hpark := adr_evals_idxParkAsg work inp φCode.reverse rest []
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 1
    (work.length + 1) _ _ _ h1 hpark
  have t1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .indexLoop) none inp φCode.reverse (true :: rest) work [])
      (some (adrCfg (some .idxCopyL) none (work.reverse ++ inp) φCode.reverse
        rest [] []))
      (work.length + 2) :=
    evalsToInTime_le_mono t1 (by omega)
  have hcopy := adr_evals_idxCopyL φCode.reverse (work.reverse ++ inp) rest [] []
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (work.length + 2) (φCode.reverse.length + 1) _ _ _ t1' hcopy
  have t2' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .indexLoop) none inp φCode.reverse (true :: rest) work [])
      (some (adrCfg (some .idxCopyRest) none (work.reverse ++ inp) [] rest
        φCode φCode))
      (work.length + φCode.length + 3) := by
    simpa [List.reverse_reverse, List.append_nil, List.length_reverse] using
      evalsToInTime_le_mono t2 (by simp [List.length_reverse]; omega)
  have hrest := adr_evals_idxCopyRest φCode (work.reverse ++ inp) [] rest φCode
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (work.length + φCode.length + 3) (φCode.length + 1) _ _ _ t2' hrest
  simpa [List.append_nil] using evalsToInTime_le_mono t3 (by omega)

/-- Skip `n` unary trues of `encodeNat`, parking taken assignment bits on `work`. -/
noncomputable def adr_evals_evSkip (n : ℕ) (σ rest left right work : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evNat) none σ left right work (encodeNat n ++ rest))
      (some (adrCfg (some .evRead) none (σ.drop n) left right
        ((σ.take n).reverse ++ work) rest))
      (2 * n + 1) := by
  induction n generalizing σ work with
  | zero =>
      change EvalsToInTime _
        (adrCfg (some .evNat) none σ left right work (false :: rest)) _ 1
      simpa [encodeNat, List.take_zero, List.drop_zero, List.reverse_nil] using
        adr_evals_one (adr_step_evNat_false rest σ left right work none)
  | succ n ih =>
      have hbits : encodeNat (n + 1) ++ rest = true :: (encodeNat n ++ rest) := by
        simp [encodeNat, List.replicate_succ]
      rw [hbits]
      have h1 := adr_evals_one
        (adr_step_evNat_true (encodeNat n ++ rest) σ left right work none)
      cases σ with
      | nil =>
          have h2 := adr_evals_one
            (adr_step_evSkip_nil left right work (encodeNat n ++ rest) none)
          have h12 := EvalsToInTime.trans afterDecodePairResultComputer.step
            1 1 _ _ _ h1 h2
          have h3 := ih [] work
          have t := EvalsToInTime.trans afterDecodePairResultComputer.step
            2 (2 * n + 1) _ _ _ h12 h3
          simpa [List.drop_nil, List.take_nil, List.reverse_nil, Nat.mul_succ,
            Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using t
      | cons b σ =>
          have h2 := adr_evals_one
            (adr_step_evSkip_cons b σ left right work (encodeNat n ++ rest) none)
          have h12 := EvalsToInTime.trans afterDecodePairResultComputer.step
            1 1 _ _ _ h1 h2
          have h3 := ih σ (b :: work)
          have t := EvalsToInTime.trans afterDecodePairResultComputer.step
            2 (2 * n + 1) _ _ _ h12 h3
          simpa [List.drop_succ_cons, List.take_succ_cons, List.reverse_cons,
            List.append_assoc, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using t

/-- Restore skipped bits from `work` onto `inp`, then park the eval bit in state. -/
noncomputable def adr_evals_evRestore (skipped : List Bool) (inp left right out : List Bool)
    (bit : Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evRestore) none inp (bit :: left) right skipped out)
      (some (adrCfg (some .evCount) (some bit)
        (skipped.reverse ++ inp) left right [] out))
      (skipped.length + 1) := by
  induction skipped generalizing inp with
  | nil =>
      simpa using adr_evals_one
        (adr_step_evRestore_nil_cons bit left inp right out none)
  | cons b rest ih =>
      have h1 := adr_evals_one
        (adr_step_evRestore_cons b rest inp (bit :: left) right out none)
      have h2 := ih (b :: inp)
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (rest.length + 1) _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc] using t

/-- Lookup `var n` on assignment `σ`, arriving at `evCount` with `σ.getD n false`. -/
noncomputable def adr_evals_evLookup (n : ℕ) (σ rest left right : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evNat) none σ left right [] (encodeNat n ++ rest))
      (some (adrCfg (some .evCount) (some (σ.getD n false))
        σ left right [] rest))
      (2 * n + (σ.take n).length + 3) := by
  have hskip := adr_evals_evSkip n σ rest left right []
  have hskip' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evNat) none σ left right [] (encodeNat n ++ rest))
      (some (adrCfg (some .evRead) none (σ.drop n) left right
        (σ.take n).reverse rest))
      (2 * n + 1) := by
    simpa [List.append_nil] using hskip
  have hread : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evRead) none (σ.drop n) left right
        (σ.take n).reverse rest)
      (some (adrCfg (some .evRestore) none (σ.drop n)
        ((σ.drop n).headD false :: left) right (σ.take n).reverse rest)) 1 := by
    cases hdrop : σ.drop n with
    | nil =>
        simpa [hdrop] using adr_evals_one
          (adr_step_evRead_nil left right (σ.take n).reverse rest none)
    | cons b t =>
        simpa [hdrop, List.headD] using adr_evals_one
          (adr_step_evRead_cons b t left right (σ.take n).reverse rest none)
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (2 * n + 1) 1 _ _ _ hskip' hread
  have t1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evNat) none σ left right [] (encodeNat n ++ rest))
      (some (adrCfg (some .evRestore) none (σ.drop n)
        ((σ.drop n).headD false :: left) right (σ.take n).reverse rest))
      (2 * n + 2) :=
    evalsToInTime_le_mono t1 (by omega)
  have hrest := adr_evals_evRestore (σ.take n).reverse (σ.drop n) left right rest
    ((σ.drop n).headD false)
  have hrest' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evRestore) none (σ.drop n)
        ((σ.drop n).headD false :: left) right (σ.take n).reverse rest)
      (some (adrCfg (some .evCount) (some ((σ.drop n).headD false))
        σ left right [] rest))
      ((σ.take n).reverse.length + 1) := by
    simpa [List.reverse_reverse, List.take_append_drop] using hrest
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (2 * n + 2) ((σ.take n).reverse.length + 1) _ _ _ t1' hrest'
  have hget := getD_eq_headD_drop σ n
  simpa [← hget, List.length_reverse] using
    evalsToInTime_le_mono t2 (by simp [List.length_reverse]; omega)

set_option maxHeartbeats 8000000

/-- 0-step identity on an ADR configuration. -/
def adr_evals_zero (l : Option ADRLabel) (v : Option Bool)
    (inp left right work out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg l v inp left right work out)
      (some (adrCfg l v inp left right work out)) 0 where
  steps := 0
  steps_le_m := Nat.zero_le _
  evals_in_steps := rfl

/-- Pop `k` leading falses into `work` as trues. -/
noncomputable def adr_evals_evCount_falses (k : ℕ)
    (rest inp left work out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCountLoop) none inp left
        (List.replicate k false ++ rest) work out)
      (some (adrCfg (some .evCountLoop) none inp left rest
        (List.replicate k true ++ work) out))
      k := by
  induction k generalizing work with
  | zero =>
      simpa [List.replicate_zero] using
        adr_evals_zero (some .evCountLoop) none inp left rest work out
  | succ k ih =>
      have h1 := adr_evals_one
        (adr_step_evCountLoop_false (List.replicate k false ++ rest)
          inp left work out none)
      have h2 := ih (true :: work)
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1 k
        _ _ _ h1 h2
      have heq : List.replicate k true ++ true :: work =
          true :: (List.replicate k true ++ work) := by
        calc
          List.replicate k true ++ true :: work
              = List.replicate k true ++ ([true] ++ work) := by simp
          _ = (List.replicate k true ++ [true]) ++ work := by
                simp [List.append_assoc]
          _ = List.replicate (k + 1) true ++ work := by
                simp [List.replicate_succ']
          _ = true :: (List.replicate k true ++ work) := by
                simp [List.replicate_succ]
      simpa [List.replicate_succ, heq] using t

/-- Park, observe table (k=0), unpark, `evDone`. -/
noncomputable def adr_evals_evCount_k0 (b : Bool)
    (suffix inp left out : List Bool)
    (hsuf : suffix.head? ≠ some false) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left suffix [] out)
      (some (adrCfg (some .evDone) (some b) inp left suffix [] out))
      4 := by
  have hpark := adr_evals_one
    (adr_step_evCount inp left suffix [] out (some b))
  have hloop : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCountLoop) none inp (b :: left) suffix [] out)
      (some (adrCfg (some .evUnpark) none inp (b :: left) suffix [] out))
      1 := by
    cases h : suffix with
    | nil =>
        simpa [h] using adr_evals_one
          (adr_step_evCountLoop_nil inp (b :: left) [] out none)
    | cons x rest =>
        have hx : x = true := by
          cases x with
          | false =>
              exact (hsuf (by simp [h])).elim
          | true => rfl
        subst hx
        simpa [h] using adr_evals_one
          (adr_step_evCountLoop_true_table rest inp (b :: left) out none)
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 1 1
    _ _ _ hpark hloop
  have hunpark := adr_evals_one
    (adr_step_evUnpark_cons b left inp suffix [] out none)
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step 2 1
    _ _ _ t1 hunpark
  have hdisp := adr_evals_one
    (adr_step_evDisp1_nil inp left suffix out b)
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step 3 1
    _ _ _ t2 hdisp
  exact evalsToInTime_le_mono t3 (by omega)

/-- Park, count a k-marker frame `false^k ++ true :: suffix`, unpark to `evDisp1`. -/
noncomputable def adr_evals_evCount_to_disp1_frame (k : ℕ)
    (b : Bool) (suffix inp left out : List Bool) (hk : 0 < k) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left
        (List.replicate k false ++ true :: suffix) [] out)
      (some (adrCfg (some .evDisp1) (some b) inp left suffix
        (List.replicate k true) out))
      (k + 3) := by
  have hpark := adr_evals_one
    (adr_step_evCount inp left
      (List.replicate k false ++ true :: suffix) [] out (some b))
  have hfalses := adr_evals_evCount_falses k (true :: suffix)
    inp (b :: left) [] out
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 1 k
    _ _ _ hpark hfalses
  have hb : (some b).getD false = b := rfl
  have t1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left
        (List.replicate k false ++ true :: suffix) [] out)
      (some (adrCfg (some .evCountLoop) none inp (b :: left)
        (true :: suffix) (List.replicate k true) out))
      (k + 1) := by
    simpa [hb, List.append_nil] using evalsToInTime_le_mono t1 (by omega)
  have hrep : List.replicate k true = true :: List.replicate (k - 1) true := by
    cases k with
    | zero => omega
    | succ k => simp [List.replicate_succ]
  have hdelim : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCountLoop) none inp (b :: left)
        (true :: suffix) (List.replicate k true) out)
      (some (adrCfg (some .evUnpark) none inp (b :: left) suffix
        (List.replicate k true) out)) 1 := by
    rw [hrep]
    simpa using adr_evals_one
      (adr_step_evCountLoop_true_delim true (List.replicate (k - 1) true)
        suffix inp (b :: left) out none)
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step
    _ _ _ _ _ t1' hdelim
  have hunpark := adr_evals_one
    (adr_step_evUnpark_cons b left inp suffix (List.replicate k true) out none)
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
    _ _ _ _ _ t2 hunpark
  exact evalsToInTime_le_mono t3 (by omega)

noncomputable def adr_evals_evCount_k1 (b : Bool)
    (suffix inp left out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left
        (false :: true :: suffix) [] out)
      (some (adrCfg (some .evNot) (some b) inp left suffix [] out))
      6 := by
  have h1 := adr_evals_evCount_to_disp1_frame 1 b suffix inp left out (by omega)
  have h1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left
        (false :: true :: suffix) [] out)
      (some (adrCfg (some .evDisp1) (some b) inp left suffix [true] out))
      4 := by
    simpa [List.replicate_succ, List.replicate_zero] using
      evalsToInTime_le_mono h1 (by omega)
  have d1 := adr_evals_one
    (adr_step_evDisp1_cons true [] inp left suffix out b)
  have d2 := adr_evals_one
    (adr_step_evDisp2_nil inp left suffix out b)
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 4 1 _ _ _ h1' d1
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step 5 1 _ _ _ t1 d2
  exact evalsToInTime_le_mono t2 (by omega)

noncomputable def adr_evals_evCount_k2 (b : Bool)
    (suffix inp left out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left
        (false :: false :: true :: suffix) [] out)
      (some (adrCfg (some .evAndFirst) (some b) inp left suffix [] out))
      8 := by
  have h1 := adr_evals_evCount_to_disp1_frame 2 b suffix inp left out (by omega)
  have h1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left
        (false :: false :: true :: suffix) [] out)
      (some (adrCfg (some .evDisp1) (some b) inp left suffix [true, true] out))
      5 := by
    simpa [List.replicate_succ] using evalsToInTime_le_mono h1 (by omega)
  have d1 := adr_evals_one
    (adr_step_evDisp1_cons true [true] inp left suffix out b)
  have d2 := adr_evals_one
    (adr_step_evDisp2_cons true [] inp left suffix out b)
  have d3 := adr_evals_one
    (adr_step_evDisp3_nil inp left suffix out b)
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 5 1 _ _ _ h1' d1
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step 6 1 _ _ _ t1 d2
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step 7 1 _ _ _ t2 d3
  exact evalsToInTime_le_mono t3 (by omega)

noncomputable def adr_evals_evCount_k3 (b : Bool)
    (suffix inp left out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left
        (false :: false :: false :: true :: suffix) [] out)
      (some (adrCfg (some .evAndCombF) (some b) inp left suffix [] out))
      10 := by
  have h1 := adr_evals_evCount_to_disp1_frame 3 b suffix inp left out (by omega)
  have h1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left
        (false :: false :: false :: true :: suffix) [] out)
      (some (adrCfg (some .evDisp1) (some b) inp left suffix
        [true, true, true] out)) 6 := by
    simpa [List.replicate_succ] using evalsToInTime_le_mono h1 (by omega)
  have d1 := adr_evals_one
    (adr_step_evDisp1_cons true [true, true] inp left suffix out b)
  have d2 := adr_evals_one
    (adr_step_evDisp2_cons true [true] inp left suffix out b)
  have d3 := adr_evals_one
    (adr_step_evDisp3_cons true [] inp left suffix out b)
  have d4 := adr_evals_one
    (adr_step_evDisp4_nil inp left suffix out b)
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 6 1 _ _ _ h1' d1
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step 7 1 _ _ _ t1 d2
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step 8 1 _ _ _ t2 d3
  have t4 := EvalsToInTime.trans afterDecodePairResultComputer.step 9 1 _ _ _ t3 d4
  exact evalsToInTime_le_mono t4 (by omega)

noncomputable def adr_evals_evCount_k4 (b : Bool)
    (suffix inp left out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left
        (false :: false :: false :: false :: true :: suffix) [] out)
      (some (adrCfg (some .evAndCombT) (some b) inp left suffix [] out))
      12 := by
  have h1 := adr_evals_evCount_to_disp1_frame 4 b suffix inp left out (by omega)
  have h1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left
        (false :: false :: false :: false :: true :: suffix) [] out)
      (some (adrCfg (some .evDisp1) (some b) inp left suffix
        [true, true, true, true] out)) 7 := by
    simpa [List.replicate_succ] using evalsToInTime_le_mono h1 (by omega)
  have d1 := adr_evals_one
    (adr_step_evDisp1_cons true [true, true, true] inp left suffix out b)
  have d2 := adr_evals_one
    (adr_step_evDisp2_cons true [true, true] inp left suffix out b)
  have d3 := adr_evals_one
    (adr_step_evDisp3_cons true [true] inp left suffix out b)
  have d4 := adr_evals_one
    (adr_step_evDisp4_cons true [] inp left suffix out b)
  have d5 := adr_evals_one
    (adr_step_evDisp5_nil inp left suffix out b)
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 7 1 _ _ _ h1' d1
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step 8 1 _ _ _ t1 d2
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step 9 1 _ _ _ t2 d3
  have t4 := EvalsToInTime.trans afterDecodePairResultComputer.step 10 1 _ _ _ t3 d4
  have t5 := EvalsToInTime.trans afterDecodePairResultComputer.step 11 1 _ _ _ t4 d5
  exact evalsToInTime_le_mono t5 (by omega)

noncomputable def adr_evals_evCount_k5 (b : Bool)
    (suffix inp left out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left
        (false :: false :: false :: false :: false :: true :: suffix) [] out)
      (some (adrCfg (some .evOrFirst) (some b) inp left suffix [] out))
      14 := by
  have h1 := adr_evals_evCount_to_disp1_frame 5 b suffix inp left out (by omega)
  have h1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left
        (false :: false :: false :: false :: false :: true :: suffix) [] out)
      (some (adrCfg (some .evDisp1) (some b) inp left suffix
        [true, true, true, true, true] out)) 8 := by
    simpa [List.replicate_succ] using evalsToInTime_le_mono h1 (by omega)
  have d1 := adr_evals_one
    (adr_step_evDisp1_cons true [true, true, true, true] inp left suffix
      out b)
  have d2 := adr_evals_one
    (adr_step_evDisp2_cons true [true, true, true] inp left suffix out b)
  have d3 := adr_evals_one
    (adr_step_evDisp3_cons true [true, true] inp left suffix out b)
  have d4 := adr_evals_one
    (adr_step_evDisp4_cons true [true] inp left suffix out b)
  have d5 := adr_evals_one
    (adr_step_evDisp5_cons true [] inp left suffix out b)
  have d6 := adr_evals_one
    (adr_step_evDisp6_nil inp left suffix out b)
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 8 1 _ _ _ h1' d1
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step 9 1 _ _ _ t1 d2
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step 10 1 _ _ _ t2 d3
  have t4 := EvalsToInTime.trans afterDecodePairResultComputer.step 11 1 _ _ _ t3 d4
  have t5 := EvalsToInTime.trans afterDecodePairResultComputer.step 12 1 _ _ _ t4 d5
  have t6 := EvalsToInTime.trans afterDecodePairResultComputer.step 13 1 _ _ _ t5 d6
  exact evalsToInTime_le_mono t6 (by omega)

noncomputable def adr_evals_evCount_k6 (b : Bool)
    (suffix inp left out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left
        (false :: false :: false :: false :: false :: false :: true ::
          suffix) [] out)
      (some (adrCfg (some .evOrCombF) (some b) inp left suffix [] out))
      16 := by
  have h1 := adr_evals_evCount_to_disp1_frame 6 b suffix inp left out (by omega)
  have h1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left
        (false :: false :: false :: false :: false :: false :: true ::
          suffix) [] out)
      (some (adrCfg (some .evDisp1) (some b) inp left suffix
        [true, true, true, true, true, true] out)) 9 := by
    simpa [List.replicate_succ] using evalsToInTime_le_mono h1 (by omega)
  have d1 := adr_evals_one
    (adr_step_evDisp1_cons true [true, true, true, true, true] inp left
      suffix out b)
  have d2 := adr_evals_one
    (adr_step_evDisp2_cons true [true, true, true, true] inp left suffix
      out b)
  have d3 := adr_evals_one
    (adr_step_evDisp3_cons true [true, true, true] inp left suffix out b)
  have d4 := adr_evals_one
    (adr_step_evDisp4_cons true [true, true] inp left suffix out b)
  have d5 := adr_evals_one
    (adr_step_evDisp5_cons true [true] inp left suffix out b)
  have d6 := adr_evals_one
    (adr_step_evDisp6_cons true [] inp left suffix out b)
  have d7 := adr_evals_one
    (adr_step_evDisp7_nil inp left suffix out b)
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 9 1 _ _ _ h1' d1
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step 10 1 _ _ _ t1 d2
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step 11 1 _ _ _ t2 d3
  have t4 := EvalsToInTime.trans afterDecodePairResultComputer.step 12 1 _ _ _ t3 d4
  have t5 := EvalsToInTime.trans afterDecodePairResultComputer.step 13 1 _ _ _ t4 d5
  have t6 := EvalsToInTime.trans afterDecodePairResultComputer.step 14 1 _ _ _ t5 d6
  have t7 := EvalsToInTime.trans afterDecodePairResultComputer.step 15 1 _ _ _ t6 d7
  exact evalsToInTime_le_mono t7 (by omega)

noncomputable def adr_evals_evCount_k7 (b : Bool)
    (suffix inp left out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left
        (false :: false :: false :: false :: false :: false :: false ::
          true :: suffix) [] out)
      (some (adrCfg (some .evOrCombT) (some b) inp left suffix [] out))
      18 := by
  have h1 := adr_evals_evCount_to_disp1_frame 7 b suffix inp left out (by omega)
  have h1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evCount) (some b) inp left
        (false :: false :: false :: false :: false :: false :: false ::
          true :: suffix) [] out)
      (some (adrCfg (some .evDisp1) (some b) inp left suffix
        [true, true, true, true, true, true, true] out)) 10 := by
    simpa [List.replicate_succ] using evalsToInTime_le_mono h1 (by omega)
  have d1 := adr_evals_one
    (adr_step_evDisp1_cons true [true, true, true, true, true, true]
      inp left suffix out b)
  have d2 := adr_evals_one
    (adr_step_evDisp2_cons true [true, true, true, true, true] inp left
      suffix out b)
  have d3 := adr_evals_one
    (adr_step_evDisp3_cons true [true, true, true, true] inp left suffix
      out b)
  have d4 := adr_evals_one
    (adr_step_evDisp4_cons true [true, true, true] inp left suffix out b)
  have d5 := adr_evals_one
    (adr_step_evDisp5_cons true [true, true] inp left suffix out b)
  have d6 := adr_evals_one
    (adr_step_evDisp6_cons true [true] inp left suffix out b)
  have d7 := adr_evals_one
    (adr_step_evDisp7_cons true [] inp left suffix out b)
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 10 1 _ _ _ h1' d1
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step 11 1 _ _ _ t1 d2
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step 12 1 _ _ _ t2 d3
  have t4 := EvalsToInTime.trans afterDecodePairResultComputer.step 13 1 _ _ _ t3 d4
  have t5 := EvalsToInTime.trans afterDecodePairResultComputer.step 14 1 _ _ _ t4 d5
  have t6 := EvalsToInTime.trans afterDecodePairResultComputer.step 15 1 _ _ _ t5 d6
  have t7 := EvalsToInTime.trans afterDecodePairResultComputer.step 16 1 _ _ _ t6 d7
  exact evalsToInTime_le_mono t7 (by omega)

theorem evalOn_of_tautology (φ : PropFormula) (h : φ.Tautology)
    (σ : List Bool) : φ.evalOn σ = true := by
  simpa [evalOn_eq_eval_getD] using h fun i => σ.getD i false

/-- Prefix-eval `encodeFormula φ` on assignment `σ`. Ends at `evCount` with
the eval bit in state; parent `right` is restored. -/
noncomputable def adr_evals_evParse_formula (φ : PropFormula)
    (σ rest suffix left : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evParse) none σ left suffix []
        (encodeFormula φ ++ rest))
      (some (adrCfg (some .evCount) (some (φ.evalOn σ)) σ left suffix []
        rest))
      (64 * ((encodeFormula φ).length + 1) * (σ.length + 2)) := by
  induction φ generalizing rest suffix with
  | var n =>
      have hbits : encodeFormula (.var n) ++ rest =
          false :: false :: (encodeNat n ++ rest) := by
        simp [encodeFormula]
      rw [hbits]
      have h0 := adr_evals_one
        (adr_step_evParse_false (false :: (encodeNat n ++ rest))
          σ left suffix [] none)
      have h1 := adr_evals_one
        (adr_step_evTagF_var (encodeNat n ++ rest) σ left suffix [] none)
      have hlookup := adr_evals_evLookup n σ rest left suffix
      have h01 := EvalsToInTime.trans afterDecodePairResultComputer.step
        _ _ _ _ _ h0 h1
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step
        _ _ _ _ _ h01 hlookup
      have hlen : (encodeFormula (.var n)).length = n + 3 :=
        length_encodeFormula_var n
      have htake : (List.take n σ).length ≤ n := by
        simpa [List.length_take] using Nat.min_le_left n σ.length
      have hS : 1 ≤ σ.length + 2 := by omega
      refine evalsToInTime_le_mono t ?_
      simp only [PropFormula.evalOn, hlen]
      nlinarith [htake, hS]
  | not ψ ih =>
      have hbits : encodeFormula (.not ψ) ++ rest =
          false :: true :: (encodeFormula ψ ++ rest) := by
        simp [encodeFormula]
      rw [hbits]
      have h0 := adr_evals_one
        (adr_step_evParse_false (true :: (encodeFormula ψ ++ rest))
          σ left suffix [] none)
      have h1 := adr_evals_one
        (adr_step_evTagF_not (encodeFormula ψ ++ rest) σ left suffix [] none)
      have hψ := ih rest (false :: true :: suffix)
      have h01 := EvalsToInTime.trans afterDecodePairResultComputer.step
        _ _ _ _ _ h0 h1
      have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step
        _ _ _ _ _ h01 hψ
      have hk1 := adr_evals_evCount_k1 (ψ.evalOn σ) suffix σ left rest
      have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step
        _ _ _ _ _ t1 hk1
      have hnot : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .evNot) (some (ψ.evalOn σ)) σ left suffix [] rest)
          (some (adrCfg (some .evCount) (some (!ψ.evalOn σ)) σ left suffix []
            rest)) 1 := by
        cases hbit : ψ.evalOn σ with
        | false =>
            simpa [hbit] using adr_evals_one
              (adr_step_evNot_false σ left suffix [] rest)
        | true =>
            simpa [hbit] using adr_evals_one
              (adr_step_evNot_true σ left suffix [] rest)
      have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
        _ _ _ _ _ t2 hnot
      have hlen := length_encodeFormula_not ψ
      refine evalsToInTime_le_mono t3 ?_
      simp [PropFormula.evalOn, hlen]
      have : 1 ≤ σ.length + 2 := by omega
      nlinarith
  | and ψ χ ihψ ihχ =>
      have hbits : encodeFormula (.and ψ χ) ++ rest =
          true :: false :: (encodeFormula ψ ++ (encodeFormula χ ++ rest)) := by
        simp [encodeFormula, List.append_assoc]
      rw [hbits]
      have h0 := adr_evals_one
        (adr_step_evParse_true (false :: (encodeFormula ψ ++
          (encodeFormula χ ++ rest))) σ left suffix [] none)
      have h1 := adr_evals_one
        (adr_step_evTagT_and (encodeFormula ψ ++ (encodeFormula χ ++ rest))
          σ left suffix [] none)
      have hψ := ihψ (encodeFormula χ ++ rest) (false :: false :: true :: suffix)
      have h01 := EvalsToInTime.trans afterDecodePairResultComputer.step
        _ _ _ _ _ h0 h1
      have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step
        _ _ _ _ _ h01 hψ
      have hk2 := adr_evals_evCount_k2 (ψ.evalOn σ) suffix σ left
        (encodeFormula χ ++ rest)
      have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step
        _ _ _ _ _ t1 hk2
      cases hbit : ψ.evalOn σ with
      | false =>
          have t2f := by simpa [hbit] using t2
          have hand := adr_evals_one
            (adr_step_evAndFirst_false σ left suffix []
              (encodeFormula χ ++ rest))
          have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
            _ _ _ _ _ t2f hand
          have hχ := ihχ rest (false :: false :: false :: true :: suffix)
          have t4 := EvalsToInTime.trans afterDecodePairResultComputer.step
            _ _ _ _ _ t3 hχ
          have hk3 := adr_evals_evCount_k3 (χ.evalOn σ) suffix σ left rest
          have t5 := EvalsToInTime.trans afterDecodePairResultComputer.step
            _ _ _ _ _ t4 hk3
          have hcomb := adr_evals_one
            (adr_step_evAndCombF σ left suffix [] rest (some (χ.evalOn σ)))
          have t6 := EvalsToInTime.trans afterDecodePairResultComputer.step
            _ _ _ _ _ t5 hcomb
          have hlen := length_encodeFormula_and ψ χ
          have heq : (ψ.and χ).evalOn σ = false := by
            simp [PropFormula.evalOn, hbit]
          rw [heq]
          refine evalsToInTime_le_mono t6 ?_
          simp [hlen]
          have : 1 ≤ σ.length + 2 := by omega
          nlinarith
      | true =>
          have t2t := by simpa [hbit] using t2
          have hand := adr_evals_one
            (adr_step_evAndFirst_true σ left suffix []
              (encodeFormula χ ++ rest))
          have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
            _ _ _ _ _ t2t hand
          have hχ := ihχ rest
            (false :: false :: false :: false :: true :: suffix)
          have t4 := EvalsToInTime.trans afterDecodePairResultComputer.step
            _ _ _ _ _ t3 hχ
          have hk4 := adr_evals_evCount_k4 (χ.evalOn σ) suffix σ left rest
          have t5 := EvalsToInTime.trans afterDecodePairResultComputer.step
            _ _ _ _ _ t4 hk4
          have hcomb := adr_evals_one
            (adr_step_evAndCombT σ left suffix [] rest (some (χ.evalOn σ)))
          have t6 := EvalsToInTime.trans afterDecodePairResultComputer.step
            _ _ _ _ _ t5 hcomb
          have hlen := length_encodeFormula_and ψ χ
          have heq : (ψ.and χ).evalOn σ = χ.evalOn σ := by
            simp [PropFormula.evalOn, hbit]
          rw [heq]
          refine evalsToInTime_le_mono t6 ?_
          simp [hlen]
          have : 1 ≤ σ.length + 2 := by omega
          nlinarith
  | or ψ χ ihψ ihχ =>
      have hbits : encodeFormula (.or ψ χ) ++ rest =
          true :: true :: (encodeFormula ψ ++ (encodeFormula χ ++ rest)) := by
        simp [encodeFormula, List.append_assoc]
      rw [hbits]
      have h0 := adr_evals_one
        (adr_step_evParse_true (true :: (encodeFormula ψ ++
          (encodeFormula χ ++ rest))) σ left suffix [] none)
      have h1 := adr_evals_one
        (adr_step_evTagT_or (encodeFormula ψ ++ (encodeFormula χ ++ rest))
          σ left suffix [] none)
      have hψ := ihψ (encodeFormula χ ++ rest)
        (false :: false :: false :: false :: false :: true :: suffix)
      have h01 := EvalsToInTime.trans afterDecodePairResultComputer.step
        _ _ _ _ _ h0 h1
      have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step
        _ _ _ _ _ h01 hψ
      have hk5 := adr_evals_evCount_k5 (ψ.evalOn σ) suffix σ left
        (encodeFormula χ ++ rest)
      have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step
        _ _ _ _ _ t1 hk5
      cases hbit : ψ.evalOn σ with
      | false =>
          have t2f := by simpa [hbit] using t2
          have hor := adr_evals_one
            (adr_step_evOrFirst_false σ left suffix []
              (encodeFormula χ ++ rest))
          have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
            _ _ _ _ _ t2f hor
          have hχ := ihχ rest
            (false :: false :: false :: false :: false :: false :: true ::
              suffix)
          have t4 := EvalsToInTime.trans afterDecodePairResultComputer.step
            _ _ _ _ _ t3 hχ
          have hk6 := adr_evals_evCount_k6 (χ.evalOn σ) suffix σ left rest
          have t5 := EvalsToInTime.trans afterDecodePairResultComputer.step
            _ _ _ _ _ t4 hk6
          have hcomb := adr_evals_one
            (adr_step_evOrCombF σ left suffix [] rest (some (χ.evalOn σ)))
          have t6 := EvalsToInTime.trans afterDecodePairResultComputer.step
            _ _ _ _ _ t5 hcomb
          have hlen := length_encodeFormula_or ψ χ
          have heq : (ψ.or χ).evalOn σ = χ.evalOn σ := by
            simp [PropFormula.evalOn, hbit]
          rw [heq]
          refine evalsToInTime_le_mono t6 ?_
          simp [hlen]
          have : 1 ≤ σ.length + 2 := by omega
          nlinarith
      | true =>
          have t2t := by simpa [hbit] using t2
          have hor := adr_evals_one
            (adr_step_evOrFirst_true σ left suffix []
              (encodeFormula χ ++ rest))
          have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
            _ _ _ _ _ t2t hor
          have hχ := ihχ rest
            (false :: false :: false :: false :: false :: false :: false ::
              true :: suffix)
          have t4 := EvalsToInTime.trans afterDecodePairResultComputer.step
            _ _ _ _ _ t3 hχ
          have hk7 := adr_evals_evCount_k7 (χ.evalOn σ) suffix σ left rest
          have t5 := EvalsToInTime.trans afterDecodePairResultComputer.step
            _ _ _ _ _ t4 hk7
          have hcomb := adr_evals_one
            (adr_step_evOrCombT σ left suffix [] rest (some (χ.evalOn σ)))
          have t6 := EvalsToInTime.trans afterDecodePairResultComputer.step
            _ _ _ _ _ t5 hcomb
          have hlen := length_encodeFormula_or ψ χ
          have heq : (ψ.or χ).evalOn σ = true := by
            simp [PropFormula.evalOn, hbit]
          rw [heq]
          refine evalsToInTime_le_mono t6 ?_
          simp [hlen]
          have : 1 ≤ σ.length + 2 := by omega
          nlinarith

/-- Drain remaining `inp` at `acceptPrepInp`, then enter `acceptEmit`. -/
noncomputable def adr_evals_acceptPrepInp (inp left : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .acceptPrepInp) none inp left [] [] [])
      (some (adrCfg (some .acceptEmit) none [] left [] [] []))
      (inp.length + 1) := by
  induction inp with
  | nil =>
      simpa using adr_evals_one
        (adr_step_acceptPrepInp_nil left [] [] [] none)
  | cons b rest ih =>
      have s1 := adr_evals_one
        (adr_step_acceptPrepInp_cons b rest left [] [] [] none)
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step
        _ _ _ _ _ s1 ih
      simpa [List.length_cons] using t

/-- Drain work and inp, then enter `acceptEmit`. -/
noncomputable def adr_evals_acceptPrep (inp left work : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .acceptPrep) none inp left [] work [])
      (some (adrCfg (some .acceptEmit) none [] left [] [] []))
      (work.length + inp.length + 2) := by
  induction work generalizing inp with
  | nil =>
      have h1 := adr_evals_one
        (adr_step_acceptPrep_nil inp left [] [] none)
      have h2 := adr_evals_acceptPrepInp inp left
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step
        _ _ _ _ _ h1 h2
      exact evalsToInTime_le_mono t (by omega)
  | cons b rest ih =>
      have h1 := adr_evals_one
        (adr_step_acceptPrep_cons b rest inp left [] [] none)
      have h2 := ih inp
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step
        _ _ _ _ _ h1 h2
      refine evalsToInTime_le_mono t ?_
      simp [List.length_cons]

theorem length_bitsInc_le (bs : List Bool) :
    (bitsInc bs).length ≤ bs.length + 1 := by
  induction bs with
  | nil => simp [bitsInc]
  | cons x xs ih =>
      cases x <;> simp [bitsInc, List.length_cons]; omega

/-- Restore carry-aux on `out` onto `inp`, return to `indexLoop`. -/
noncomputable def adr_evals_idxIncRest (inp left right work out : List Bool)
    (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .idxIncRest) v inp left right work out)
      (some (adrCfg (some .indexLoop) none (out.reverse ++ inp) left right
        work []))
      (out.length + 1) := by
  induction out generalizing inp v with
  | nil =>
      simpa using adr_evals_one
        (adr_step_idxIncRest_nil inp left right work v)
  | cons b rest ih =>
      have h1 := adr_evals_one
        (adr_step_idxIncRest_cons b rest inp left right work v)
      have h2 := ih (b :: inp) none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (rest.length + 1) _ _ _ h1 h2
      have heq : rest.reverse ++ (b :: inp) = (b :: rest).reverse ++ inp := by
        simp [List.reverse_cons, List.append_assoc]
      simpa [← heq, List.length_cons, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using evalsToInTime_le_mono t (by simp [List.length_cons])

/-- From `idxInc`, return to `indexLoop` with `bitsInc inp`. -/
noncomputable def adr_evals_idxInc (inp left right work out : List Bool)
    (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .idxInc) v inp left right work out)
      (some (adrCfg (some .indexLoop) none
        (out.reverse ++ bitsInc inp) left right work []))
      (2 * inp.length + out.length + 2) := by
  induction inp generalizing out v with
  | nil =>
      have h1 := adr_evals_one (adr_step_idxInc_nil left right work out v)
      have h2 := adr_evals_idxIncRest [true] left right work out none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (out.length + 1) _ _ _ h1 h2
      simpa [bitsInc] using evalsToInTime_le_mono t (by omega)
  | cons b rest ih =>
      cases b with
      | false =>
          have h1 := adr_evals_one
            (adr_step_idxInc_false rest left right work out v)
          have h2 := adr_evals_idxIncRest (true :: rest) left right work out none
          have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
            (out.length + 1) _ _ _ h1 h2
          simpa [bitsInc, List.length_cons] using
            evalsToInTime_le_mono t (by simp [List.length_cons])
      | true =>
          have h1 := adr_evals_one
            (adr_step_idxInc_true rest left right work out v)
          have h2 := ih (false :: out) none
          have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
            (2 * rest.length + (false :: out).length + 2) _ _ _ h1 h2
          have heq :
              (false :: out).reverse ++ bitsInc rest =
                out.reverse ++ bitsInc (true :: rest) := by
            simp [bitsInc, List.reverse_cons, List.append_assoc]
          simpa [← heq, List.length_cons, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using evalsToInTime_le_mono t (by
              simp [List.length_cons]; omega)

/-- Successful eval with empty leftover code: `evDone` to `idxInc`. -/
noncomputable def adr_evals_evDone_true (inp left right work : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evDone) (some true) inp left right work [])
      (some (adrCfg (some .idxInc) none inp left right work [])) 1 :=
  adr_evals_one (adr_step_evDone_true_empty inp left right work)

/-- One all-true fuel bit: eval `φ` on `work.reverse ++ inp`, increment, loop. -/
noncomputable def adr_evals_index_one_true (φ : PropFormula)
    (inp work rest : List Bool)
    (heval : φ.evalOn (work.reverse ++ inp) = true)
    (hsuf : rest.head? ≠ some false) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .indexLoop) none inp (encodeFormula φ).reverse
        (true :: rest) work [])
      (some (adrCfg (some .indexLoop) none
        (bitsInc (work.reverse ++ inp)) (encodeFormula φ).reverse rest [] []))
      (work.length + 2 * (encodeFormula φ).length + 11 +
        64 * ((encodeFormula φ).length + 1) *
          ((work.reverse ++ inp).length + 2) +
        2 * (work.reverse ++ inp).length) := by
  set φCode := encodeFormula φ
  set σ := work.reverse ++ inp
  have hto := adr_evals_indexLoop_to_evParse φCode inp work rest
  have hparse := adr_evals_evParse_formula φ σ [] rest φCode.reverse
  have hparse' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .evParse) none σ φCode.reverse rest [] φCode)
      (some (adrCfg (some .evCount) (some true) σ φCode.reverse rest [] []))
      (64 * (φCode.length + 1) * (σ.length + 2)) := by
    simpa [φCode, σ, heval, List.append_nil] using hparse
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step
    _ _ _ _ _ hto hparse'
  have hk0 := adr_evals_evCount_k0 true rest σ φCode.reverse [] hsuf
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step
    _ _ _ _ _ t1 hk0
  have hdone := adr_evals_evDone_true σ φCode.reverse rest []
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
    _ _ _ _ _ t2 hdone
  have hinc := adr_evals_idxInc σ φCode.reverse rest [] [] none
  have t4 := EvalsToInTime.trans afterDecodePairResultComputer.step
    _ _ _ _ _ t3 hinc
  simpa [φCode, σ] using evalsToInTime_le_mono t4 (by
    simp [φCode, σ, List.length_nil]
    omega)

/-- Empty fuel: drain and enter `acceptEmit`. -/
noncomputable def adr_evals_indexLoop_empty (φ : PropFormula)
    (inp work : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .indexLoop) none inp (encodeFormula φ).reverse [] work [])
      (some (adrCfg (some .acceptEmit) none [] (encodeFormula φ).reverse
        [] [] []))
      (work.length + inp.length + 3) := by
  have h1 := adr_evals_one
    (adr_step_indexLoop_nil inp (encodeFormula φ).reverse work [] none)
  have h2 := adr_evals_acceptPrep inp (encodeFormula φ).reverse work
  have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
    (work.length + inp.length + 2) _ _ _ h1 h2
  exact evalsToInTime_le_mono t (by omega)

theorem adr_index_one_time_le (L W I : ℕ) :
    W + 2 * L + 11 + 64 * (L + 1) * (W + I + 2) + 2 * (W + I) ≤
      80 * (L + 1) * (W + I + 2) := by
  have hP : 0 < L + 1 := Nat.succ_pos _
  have hS : 0 < W + I + 2 := by omega
  have h1 : W ≤ (L + 1) * (W + I + 2) :=
    le_trans (by omega : W ≤ W + I + 2)
      (Nat.le_mul_of_pos_left (W + I + 2) hP)
  have h2 : 2 * L ≤ 2 * ((L + 1) * (W + I + 2)) := by
    have : 2 * (L + 1) ≤ 2 * ((L + 1) * (W + I + 2)) := by
      simpa [mul_assoc] using (Nat.le_mul_of_pos_right (2 * (L + 1)) hS)
    exact (Nat.mul_le_mul_left 2 (Nat.le_succ L)).trans this
  have h3 : 11 ≤ 11 * ((L + 1) * (W + I + 2)) := by
    have : 1 ≤ (L + 1) * (W + I + 2) := Nat.mul_pos hP hS
    exact (by omega : 11 ≤ 11 * 1).trans (Nat.mul_le_mul_left 11 this)
  have h5 : 2 * (W + I) ≤ 2 * ((L + 1) * (W + I + 2)) := by
    have : 2 * (W + I + 2) ≤ 2 * ((L + 1) * (W + I + 2)) :=
      Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_left (W + I + 2) hP)
    exact (by omega : 2 * (W + I) ≤ 2 * (W + I + 2)).trans this
  have h2' : 2 * L ≤ 2 * (L + 1) * (W + I + 2) := by
    simpa [mul_assoc] using h2
  have h3' : 11 ≤ 11 * (L + 1) * (W + I + 2) := by
    simpa [mul_assoc] using h3
  have h5' : 2 * (W + I) ≤ 2 * (L + 1) * (W + I + 2) := by
    simpa [mul_assoc] using h5
  have h4 : 64 * (L + 1) * (W + I + 2) ≤ 64 * (L + 1) * (W + I + 2) :=
    le_rfl
  have hsum :
      W + 2 * L + 11 + 64 * (L + 1) * (W + I + 2) + 2 * (W + I) ≤
        (L + 1) * (W + I + 2) + 2 * (L + 1) * (W + I + 2) +
          11 * (L + 1) * (W + I + 2) + 64 * (L + 1) * (W + I + 2) +
          2 * (L + 1) * (W + I + 2) :=
    add_le_add (add_le_add (add_le_add (add_le_add h1 h2') h3') h4) h5'
  have heq :
      (L + 1) * (W + I + 2) + 2 * (L + 1) * (W + I + 2) +
        11 * (L + 1) * (W + I + 2) + 64 * (L + 1) * (W + I + 2) +
        2 * (L + 1) * (W + I + 2) =
      80 * (L + 1) * (W + I + 2) := by
    set PS := (L + 1) * (W + I + 2)
    have h2 : 2 * (L + 1) * (W + I + 2) = 2 * PS := by
      rw [show PS = (L + 1) * (W + I + 2) from rfl, mul_assoc]
    have h11 : 11 * (L + 1) * (W + I + 2) = 11 * PS := by
      rw [show PS = (L + 1) * (W + I + 2) from rfl, mul_assoc]
    have h64 : 64 * (L + 1) * (W + I + 2) = 64 * PS := by
      rw [show PS = (L + 1) * (W + I + 2) from rfl, mul_assoc]
    have h80 : 80 * (L + 1) * (W + I + 2) = 80 * PS := by
      rw [show PS = (L + 1) * (W + I + 2) from rfl, mul_assoc]
    rw [h2, h11, h64, h80]
    omega
  exact hsum.trans_eq heq

theorem adr_index_allTrue_time_le (L W I T inc : ℕ)
    (hinc : inc ≤ W + I + 1) :
    W + 2 * L + 11 + 64 * (L + 1) * (W + I + 2) + 2 * (W + I) +
      256 * (T + 1) * (L + 1) * (inc + T + 2) ≤
    256 * (T + 2) * (L + 1) * (W + I + T + 3) := by
  have hSR : W + I + 2 ≤ W + I + T + 3 := by omega
  have hQR : inc + T + 2 ≤ W + I + T + 3 := by omega
  have hone : W + 2 * L + 11 + 64 * (L + 1) * (W + I + 2) + 2 * (W + I) ≤
      80 * (L + 1) * (W + I + T + 3) :=
    (adr_index_one_time_le L W I).trans
      (Nat.mul_le_mul_left (80 * (L + 1)) hSR)
  have hrest : 256 * (T + 1) * (L + 1) * (inc + T + 2) ≤
      256 * (T + 1) * (L + 1) * (W + I + T + 3) :=
    Nat.mul_le_mul_left _ hQR
  have h80 : 80 * (L + 1) * (W + I + T + 3) ≤
      256 * (L + 1) * (W + I + T + 3) :=
    Nat.mul_le_mul_right (W + I + T + 3)
      (Nat.mul_le_mul_right (L + 1) (by omega : 80 ≤ 256))
  have hC : 256 + 256 * (T + 1) = 256 * (T + 2) := by
    calc
      256 + 256 * (T + 1) = 256 * 1 + 256 * (T + 1) := by simp
      _ = 256 * (1 + (T + 1)) := (Nat.mul_add 256 1 (T + 1)).symm
      _ = 256 * (T + 2) := by
            simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  have hsum :
      256 * (L + 1) * (W + I + T + 3) +
        256 * (T + 1) * (L + 1) * (W + I + T + 3) =
      256 * (T + 2) * (L + 1) * (W + I + T + 3) := by
    have hR := W + I + T + 3
    have hL1 := L + 1
    -- (256 * hL1) * hR + ((256 * (T + 1)) * hL1) * hR
    -- = ((256 + 256 * (T + 1)) * hL1) * hR
    calc
      256 * (L + 1) * (W + I + T + 3) +
          256 * (T + 1) * (L + 1) * (W + I + T + 3)
          = (256 * (L + 1) + 256 * (T + 1) * (L + 1)) * (W + I + T + 3) := by
            simp [Nat.add_mul]
      _ = ((256 + 256 * (T + 1)) * (L + 1)) * (W + I + T + 3) := by
            simp [Nat.add_mul]
      _ = (256 * (T + 2) * (L + 1)) * (W + I + T + 3) := by
            simp [hC]
      _ = 256 * (T + 2) * (L + 1) * (W + I + T + 3) := rfl
  exact (add_le_add (hone.trans h80) hrest).trans hsum.le

/-- All-true remaining table plus tautology: drain fuel and enter `acceptEmit`. -/
noncomputable def adr_evals_indexLoop_allTrue (φ : PropFormula)
    (inp work table : List Bool)
    (htaut : φ.Tautology)
    (hall : ∀ b ∈ table, b = true) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .indexLoop) none inp (encodeFormula φ).reverse table
        work [])
      (some (adrCfg (some .acceptEmit) none [] (encodeFormula φ).reverse
        [] [] []))
      (256 * (table.length + 1) * ((encodeFormula φ).length + 1) *
        (work.length + inp.length + table.length + 2)) := by
  induction table generalizing inp work with
  | nil =>
      have h := adr_evals_indexLoop_empty φ inp work
      refine evalsToInTime_le_mono h ?_
      have hL : 0 < (encodeFormula φ).length + 1 := Nat.succ_pos _
      have h1 : work.length + inp.length + 3 ≤
          256 * (work.length + inp.length + 2) := by omega
      have h2 : 256 * (work.length + inp.length + 2) ≤
          256 * ((encodeFormula φ).length + 1) *
            (work.length + inp.length + 2) := by
        have hmul :=
          Nat.mul_le_mul_left 256
            (Nat.le_mul_of_pos_left (work.length + inp.length + 2) hL)
        simpa [mul_assoc] using hmul
      exact h1.trans (by simpa [List.length_nil] using h2)
  | cons b rest ih =>
      have hb : b = true := hall b (by simp)
      subst hb
      have hsuf : rest.head? ≠ some false := by
        cases hrest : rest with
        | nil => simp
        | cons x xs =>
            have hx : x = true := hall x (by simp [hrest])
            simp [hrest, hx]
      have heval : φ.evalOn (work.reverse ++ inp) = true :=
        evalOn_of_tautology φ htaut _
      have hone := adr_evals_index_one_true φ inp work rest heval hsuf
      have hall' : ∀ x ∈ rest, x = true := fun x hx =>
        hall x (List.mem_cons_of_mem _ hx)
      have hrest := ih (bitsInc (work.reverse ++ inp)) [] hall'
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step
        _ _ _ _ _ hone hrest
      refine evalsToInTime_le_mono t ?_
      have hσ : (work.reverse ++ inp).length = work.length + inp.length := by
        simp
      have hinc := length_bitsInc_le (work.reverse ++ inp)
      have hbound := adr_index_allTrue_time_le
        (encodeFormula φ).length work.length inp.length rest.length
        (bitsInc (work.reverse ++ inp)).length (by
          simpa [hσ] using hinc)
      simp [List.length_cons, hσ, List.length_nil]
      have hEq1 : rest.length + 2 = 1 + (rest.length + 1) := by omega
      have hEq2 : work.length + inp.length + rest.length + 3 =
          work.length + inp.length + (rest.length + 1) + 2 := by omega
      simp [hEq1, hEq2] at hbound ⊢
      exact (le_of_eq (Nat.add_comm _ _)).trans hbound

/-- Restore carry-aux on `out` onto `work`, return to `lenLoop`. -/
noncomputable def adr_evals_lenRestore (inp left right work out : List Bool)
    (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .lenRestore) v inp left right work out)
      (some (adrCfg (some .lenLoop) none inp left right
        (out.reverse ++ work) []))
      (out.length + 1) := by
  induction out generalizing work v with
  | nil =>
      simpa using adr_evals_one
        (adr_step_lenRestore_nil inp left right work v)
  | cons b rest ih =>
      have h1 := adr_evals_one
        (adr_step_lenRestore_cons inp left right work b rest v)
      have h2 := ih (b :: work) none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (rest.length + 1) _ _ _ h1 h2
      have heq : rest.reverse ++ (b :: work) = (b :: rest).reverse ++ work := by
        simp [List.reverse_cons, List.append_assoc]
      simpa [← heq, List.length_cons, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using evalsToInTime_le_mono t (by simp [List.length_cons])

/-- From `lenInc`, return to `lenLoop` with `bitsInc work`. -/
noncomputable def adr_evals_lenInc (inp left right work out : List Bool)
    (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .lenInc) v inp left right work out)
      (some (adrCfg (some .lenLoop) none inp left right
        (out.reverse ++ bitsInc work) []))
      (2 * work.length + out.length + 2) := by
  induction work generalizing out v with
  | nil =>
      have h1 := adr_evals_one (adr_step_lenInc_nil inp left right out v)
      have h2 := adr_evals_lenRestore inp left right [true] out none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (out.length + 1) _ _ _ h1 h2
      simpa [bitsInc] using evalsToInTime_le_mono t (by omega)
  | cons b rest ih =>
      cases b with
      | false =>
          have h1 := adr_evals_one
            (adr_step_lenInc_false inp left right rest out v)
          have h2 := adr_evals_lenRestore inp left right (true :: rest) out none
          have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
            (out.length + 1) _ _ _ h1 h2
          simpa [bitsInc, List.length_cons] using
            evalsToInTime_le_mono t (by simp [List.length_cons])
      | true =>
          have h1 := adr_evals_one
            (adr_step_lenInc_true inp left right rest out v)
          have h2 := ih (false :: out) none
          have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
            (2 * rest.length + (false :: out).length + 2) _ _ _ h1 h2
          have heq :
              (false :: out).reverse ++ bitsInc rest =
                out.reverse ++ bitsInc (true :: rest) := by
            simp [bitsInc, List.reverse_cons, List.append_assoc]
          simpa [← heq, List.length_cons, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using evalsToInTime_le_mono t (by
              simp [List.length_cons]; omega)

/-- From `pow2Check`, reject to `[true]` when `work` is not `pow2BitsLE` shape. -/
noncomputable def adr_evals_pow2Check_to_fail
    (inp left right work : List Bool) (v : Option Bool)
    (hmal : ∀ n, work ≠ pow2BitsLE n) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .pow2Check) v inp left right work [])
      (some (adrCfg none none [] [] [] [] [true]))
      (2 * work.length + inp.length + left.length + right.length + 6) := by
  induction work generalizing inp v with
  | nil =>
      have h1 := adr_evals_one
        (adr_step_pow2Check_nil inp left right [] v)
      have h2 := adr_evals_clearInp_to_fail inp left right [] [] none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (inp.length + left.length + right.length + 4) _ _ _ h1 h2
      exact evalsToInTime_le_mono t (by omega)
  | cons b rest ih =>
      cases b with
      | false =>
          have hmal' : ∀ n, rest ≠ pow2BitsLE n := by
            intro n hn
            exact hmal (n + 1) (by simp [pow2BitsLE_succ, hn])
          have h1 := adr_evals_one
            (adr_step_pow2Check_false inp left right rest [] v)
          have h2 := ih (false :: inp) none hmal'
          have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
            (2 * rest.length + (false :: inp).length + left.length +
              right.length + 6) _ _ _ h1 h2
          exact evalsToInTime_le_mono t (by simp [List.length_cons]; omega)
      | true =>
          cases rest with
          | nil =>
              exact (hmal 0 (by simp [pow2BitsLE_zero])).elim
          | cons b' rest' =>
              have h1 := adr_evals_one
                (adr_step_pow2Check_true_cons inp left right b' rest' [] v)
              have h2 := adr_evals_clearWork rest' inp left right [] none
              have t12 := EvalsToInTime.trans afterDecodePairResultComputer.step 1
                (rest'.length + 1) _ _ _ h1 h2
              have h3 := adr_evals_clearInp_to_fail inp left right [] [] none
              have t := EvalsToInTime.trans afterDecodePairResultComputer.step
                (rest'.length + 2)
                (inp.length + left.length + right.length + 4) _ _ _ t12 h3
              exact evalsToInTime_le_mono t (by simp [List.length_cons]; omega)

/-- Restore table from `inp` onto `right`, pow2-check length bits, reject
when `work` is not `pow2BitsLE` shape. -/
noncomputable def adr_evals_lenFinish_to_fail
    (inp left right work : List Bool) (v : Option Bool)
    (hmal : ∀ n, work ≠ pow2BitsLE n) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .lenFinish) v inp left right work [])
      (some (adrCfg none none [] [] [] [] [true]))
      (inp.length + 2 * work.length + left.length +
        (inp.reverse ++ right).length + 8) := by
  induction inp generalizing right v with
  | nil =>
      have h1 := adr_evals_one
        (adr_step_lenFinish_nil left right work [] v)
      have h2 := adr_evals_pow2Check_to_fail [] left right work none hmal
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (2 * work.length + 0 + left.length + right.length + 6) _ _ _ h1 h2
      exact evalsToInTime_le_mono t (by simp)
  | cons b rest ih =>
      have h1 := adr_evals_one
        (adr_step_lenFinish_cons b rest left right work [] v)
      have h2 := ih (b :: right) none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (rest.length + 2 * work.length + left.length +
          (rest.reverse ++ b :: right).length + 8) _ _ _ h1 h2
      exact evalsToInTime_le_mono t (by
        simp [List.length_cons, List.length_reverse, List.length_append])

/-- One `lenLoop` symbol: park bit on `inp`, `bitsInc` on `work`. -/
noncomputable def adr_evals_lenLoop_one (b : Bool)
    (inp left rest work : List Bool) (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .lenLoop) v inp left (b :: rest) work [])
      (some (adrCfg (some .lenLoop) none (b :: inp) left rest
        (bitsInc work) []))
      (2 * work.length + 3) := by
  have h1 := adr_evals_one
    (adr_step_lenLoop_cons b inp left rest work [] v)
  have h2 := adr_evals_lenInc (b :: inp) left rest work [] none
  have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
    (2 * work.length + 2) _ _ _ h1 h2
  exact evalsToInTime_le_mono t (by omega)

/-- Restore table from `inp` onto `right`, then enter `pow2Check`. -/
noncomputable def adr_evals_lenFinish_to_pow2Check
    (inp left right work : List Bool) (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .lenFinish) v inp left right work [])
      (some (adrCfg (some .pow2Check) none [] left
        (inp.reverse ++ right) work []))
      (inp.length + 1) := by
  induction inp generalizing right v with
  | nil =>
      simpa using adr_evals_one
        (adr_step_lenFinish_nil left right work [] v)
  | cons b rest ih =>
      have h1 := adr_evals_one
        (adr_step_lenFinish_cons b rest left right work [] v)
      have h2 := ih (b :: right) none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (rest.length + 1) _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc] using t

/-- Count `|right|` into `work` via `bitsInc`, restore the table, reach
`pow2Check`. -/
noncomputable def adr_evals_lenLoop_to_pow2Check
    (inp left right work : List Bool) (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .lenLoop) v inp left right work [])
      (some (adrCfg (some .pow2Check) none [] left
        (inp.reverse ++ right) (bitsIncIter right.length work) []))
      ((right.length + 1) * (2 * (work.length + right.length + 2) + 3) +
        (inp.length + right.length) + 2) := by
  induction right generalizing inp work v with
  | nil =>
      have h1 := adr_evals_one
        (adr_step_lenLoop_nil inp left work [] v)
      have h2 := adr_evals_lenFinish_to_pow2Check inp left [] work none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (inp.length + 1) _ _ _ h1 h2
      simpa [bitsIncIter_zero, List.append_nil] using
        evalsToInTime_le_mono t (by omega)
  | cons b rest ih =>
      have h1 := adr_evals_lenLoop_one b inp left rest work v
      have h1w : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .lenLoop) v inp left (b :: rest) work [])
          (some (adrCfg (some .lenLoop) none (b :: inp) left rest
            (bitsInc work) []))
          (2 * (work.length + rest.length + 2) + 3) :=
        evalsToInTime_le_mono h1 (by omega)
      have h2 := ih (b :: inp) (bitsInc work) none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step
        (2 * (work.length + rest.length + 2) + 3)
        ((rest.length + 1) * (2 * ((bitsInc work).length + rest.length + 2) + 3) +
          ((b :: inp).length + rest.length) + 2)
        _ _ _ h1w h2
      have hbits : bitsIncIter rest.length (bitsInc work) =
          bitsIncIter (rest.length + 1) work := by
        simp [bitsIncIter_succ]
      have hinp : (b :: inp).reverse ++ rest = inp.reverse ++ b :: rest := by
        simp [List.reverse_cons, List.append_assoc]
      refine evalsToInTime_le_mono (by
        simpa [hbits, hinp, List.length_cons] using t) ?_
      have hlen := length_bitsInc_le work
      simp [List.length_cons]
      nlinarith

/-- From `lenLoop` with empty `out`, process all of `right` then reject when
the counted bits are not `pow2BitsLE` shape. -/
noncomputable def adr_evals_lenLoop_to_fail
    (inp left right work : List Bool) (v : Option Bool)
    (hmal : ∀ n, bitsIncIter right.length work ≠ pow2BitsLE n) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .lenLoop) v inp left right work [])
      (some (adrCfg none none [] [] [] [] [true]))
      ((right.length + 1) * (2 * (work.length + right.length + 2) + 3) +
        2 * (inp.length + right.length) + left.length +
        2 * (work.length + right.length) + 10) := by
  induction right generalizing inp work v with
  | nil =>
      have hmalW : ∀ n, work ≠ pow2BitsLE n := by
        intro n hn
        exact hmal n (by simpa [bitsIncIter_zero] using hn)
      have h1 := adr_evals_one
        (adr_step_lenLoop_nil inp left work [] v)
      have h2 := adr_evals_lenFinish_to_fail inp left [] work none hmalW
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (inp.length + 2 * work.length + left.length +
          (inp.reverse ++ []).length + 8) _ _ _ h1 h2
      exact evalsToInTime_le_mono t (by
        simp [List.length_reverse, List.length_append]; omega)
  | cons b rest ih =>
      have hmal' : ∀ n, bitsIncIter rest.length (bitsInc work) ≠ pow2BitsLE n := by
        intro n hn
        exact hmal n (by
          simpa [List.length_cons, bitsIncIter_succ] using hn)
      have h1 := adr_evals_lenLoop_one b inp left rest work v
      have h1w : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .lenLoop) v inp left (b :: rest) work [])
          (some (adrCfg (some .lenLoop) none (b :: inp) left rest
            (bitsInc work) []))
          (2 * (work.length + rest.length + 2) + 3) :=
        evalsToInTime_le_mono h1 (by omega)
      have h2 := ih (b :: inp) (bitsInc work) none hmal'
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step
        (2 * (work.length + rest.length + 2) + 3)
        ((rest.length + 1) * (2 * ((bitsInc work).length + rest.length + 2) + 3) +
          2 * ((b :: inp).length + rest.length) + left.length +
          2 * ((bitsInc work).length + rest.length) + 10)
        _ _ _ h1w h2
      exact evalsToInTime_le_mono t (by
        have hlen := length_bitsInc_le work
        simp [List.length_cons]
        nlinarith)

/-- From `allTrueScan` with empty `out`, reject when the table has a false bit
or the restored length is not a power of two. -/
noncomputable def adr_evals_allTrueScan_to_fail
    (left right work : List Bool) (v : Option Bool)
    (hrej : (∃ b ∈ right, b = false) ∨
      (∀ n, right.length + work.length ≠ 2 ^ n)) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .allTrueScan) v [] left right work [])
      (some (adrCfg none none [] [] [] [] [true]))
      (2 * right.length + 2 * work.length +
        (right.length + work.length + 1) *
          (2 * (work.length + right.length + 2) + 3) +
        2 * (right.length + work.length) + left.length +
        2 * (work.length + right.length) + right.length + 14) := by
  induction right generalizing work v with
  | nil =>
      have hlen : ∀ n, work.length ≠ 2 ^ n := by
        intro n hn
        cases hrej with
        | inl hex =>
            rcases hex with ⟨b, hb, _⟩
            exact absurd hb List.not_mem_nil
        | inr hpow =>
            exact hpow n (by simpa using hn)
      have hmal : ∀ n, bitsIncIter (List.replicate work.length true).length [] ≠
          pow2BitsLE n := by
        intro n hn
        have hlenT : (List.replicate work.length true).length = work.length :=
          List.length_replicate
        have : bitsIncIter work.length [] = pow2BitsLE n := by
          simpa [hlenT] using hn
        have ht : work.length = 2 ^ n :=
          (bitsIncIter_nil_eq_pow2BitsLE_iff _ _).mp this
        exact hlen n ht
      have h1 := adr_evals_one (adr_step_allTrueScan_nil [] left work [] v)
      have h2 := adr_evals_allTrueOk_restore_any work [] left [] [] none
      have h2' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .allTrueOk) none [] left [] work [])
          (some (adrCfg (some .lenLoop) none [] left
            (List.replicate work.length true) [] []))
          (work.length + 1) := by
        simpa [List.append_nil] using h2
      have t12 := EvalsToInTime.trans afterDecodePairResultComputer.step
        1 (work.length + 1) _ _ _ h1 h2'
      have h3 := adr_evals_lenLoop_to_fail [] left
        (List.replicate work.length true) [] none hmal
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step
        (work.length + 2)
        (((List.replicate work.length true).length + 1) *
          (2 * (0 + (List.replicate work.length true).length + 2) + 3) +
          2 * (0 + (List.replicate work.length true).length) + left.length +
          2 * (0 + (List.replicate work.length true).length) + 10)
        _ _ _ t12 h3
      exact evalsToInTime_le_mono t (by simp [List.length_replicate]; omega)
  | cons b rest ih =>
      cases b with
      | false =>
          have h1 := adr_evals_one
            (adr_step_allTrueScan_false [] left rest work [] v)
          have h2 := adr_evals_clearWork work [] left rest [] none
          have t12 := EvalsToInTime.trans afterDecodePairResultComputer.step
            1 (work.length + 1) _ _ _ h1 h2
          have h3 := adr_evals_clearInp_to_fail [] left rest [] [] none
          have t := EvalsToInTime.trans afterDecodePairResultComputer.step
            (work.length + 2)
            ([].length + left.length + rest.length + 4) _ _ _ t12 h3
          exact evalsToInTime_le_mono t (by simp [List.length_cons]; omega)
      | true =>
          have hrej' : (∃ b ∈ rest, b = false) ∨
              (∀ n, rest.length + (true :: work).length ≠ 2 ^ n) := by
            cases hrej with
            | inl hex =>
                rcases hex with ⟨x, hx, hxF⟩
                have hx' : x ∈ rest := by
                  have hxmem := List.mem_cons.mp hx
                  cases hxmem with
                  | inl heq =>
                      simp [heq] at hxF
                  | inr hrest => exact hrest
                exact Or.inl ⟨x, hx', hxF⟩
            | inr hpow =>
                refine Or.inr ?_
                intro n hn
                exact hpow n (by
                  simp [List.length_cons] at hn ⊢
                  omega)
          have h1 := adr_evals_one
            (adr_step_allTrueScan_true [] left rest work [] v)
          have h2 := ih (true :: work) none hrej'
          have t := EvalsToInTime.trans afterDecodePairResultComputer.step
            1 (2 * rest.length + 2 * (true :: work).length +
              (rest.length + (true :: work).length + 1) *
                (2 * ((true :: work).length + rest.length + 2) + 3) +
              2 * (rest.length + (true :: work).length) + left.length +
              2 * ((true :: work).length + rest.length) + rest.length + 14)
            _ _ _ h1 h2
          exact evalsToInTime_le_mono t (by
            simp only [List.length_cons]
            ring_nf
            omega)

/-- All-true scan restores `right ++ work` as trues and enters `lenLoop`. -/
noncomputable def adr_evals_allTrueScan_allTrue
    (left right work : List Bool) (v : Option Bool)
    (hall : ∀ b ∈ right, b = true) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .allTrueScan) v [] left right work [])
      (some (adrCfg (some .lenLoop) none [] left
        (List.replicate (right.length + work.length) true) [] []))
      (2 * right.length + work.length + 2) := by
  induction right generalizing work v with
  | nil =>
      have h1 := adr_evals_one (adr_step_allTrueScan_nil [] left work [] v)
      have h2 := adr_evals_allTrueOk_restore_any work [] left [] [] none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (work.length + 1) _ _ _ h1 h2
      simpa [List.append_nil, Nat.zero_add] using
        evalsToInTime_le_mono t (by omega)
  | cons b rest ih =>
      have hb : b = true := hall b (by simp)
      subst hb
      have hall' : ∀ x ∈ rest, x = true := fun x hx =>
        hall x (List.mem_cons_of_mem _ hx)
      have h1 := adr_evals_one
        (adr_step_allTrueScan_true [] left rest work [] v)
      have h2 := ih (true :: work) none hall'
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (2 * rest.length + (true :: work).length + 2) _ _ _ h1 h2
      have hlen : rest.length + (work.length + 1) =
          rest.length + 1 + work.length := by
        rw [Nat.add_comm work.length 1, Nat.add_assoc]
      have htime : 2 * rest.length + (true :: work).length + 2 + 1 =
          2 * (true :: rest).length + work.length + 2 := by
        simp only [List.length_cons]
        omega
      simpa [List.length_cons, hlen] using
        evalsToInTime_le_mono t (le_of_eq htime)

/-- All-true table of length `2^n` reaches `parkWidth` with `pow2BitsLE n`. -/
noncomputable def adr_evals_allTrue_pow2_to_parkWidth
    (left table : List Bool) (n : ℕ)
    (hall : ∀ b ∈ table, b = true)
    (hlen : table.length = 2 ^ n) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .allTrueScan) none [] left table [] [])
      (some (adrCfg (some .parkWidth) none (pow2BitsLE n) left table [] []))
      ((table.length + 1) * (2 * (table.length + 2) + 3) +
        3 * table.length + 3 * n + 8) := by
  have hscan := adr_evals_allTrueScan_allTrue left table [] none hall
  have hscan' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .allTrueScan) none [] left table [] [])
      (some (adrCfg (some .lenLoop) none [] left
        (List.replicate table.length true) [] []))
      (2 * table.length + 2) := by
    simpa using hscan
  have hcount := adr_evals_lenLoop_to_pow2Check [] left
    (List.replicate table.length true) [] none
  have hcount' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .lenLoop) none [] left
        (List.replicate table.length true) [] [])
      (some (adrCfg (some .pow2Check) none [] left
        (List.replicate table.length true) (natBitsLE table.length) []))
      ((table.length + 1) * (2 * (table.length + 2) + 3) + table.length + 2) := by
    simpa [List.length_replicate, bitsIncIter_nil, List.reverse_nil,
      List.append_nil, List.length_nil] using hcount
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step
    _ _ _ _ _ hscan' hcount'
  have hpow : natBitsLE table.length = pow2BitsLE n := by
    simp [hlen, natBitsLE_pow2]
  have hok := adr_evals_pow2Check_ok n left
    (List.replicate table.length true) none
  have hok' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .pow2Check) none [] left
        (List.replicate table.length true) (natBitsLE table.length) [])
      (some (adrCfg (some .parkWidth) none (pow2BitsLE n) left
        (List.replicate table.length true) [] []))
      (3 * n + 4) := by
    simpa [hpow] using hok
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step
    _ _ _ _ _ t1 hok'
  have htab : List.replicate table.length true = table :=
    (List.eq_replicate_iff.mpr ⟨rfl, hall⟩).symm
  simpa [htab] using evalsToInTime_le_mono t2 (by omega)

/-- Reverse `left` onto `out`, then enter `writeAcceptFalse`. -/
noncomputable def adr_evals_revLeft (left right work out : List Bool)
    (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .revLeft) v [] left right work out)
      (some (adrCfg (some .writeAcceptFalse) none [] [] right work
        (left.reverse ++ out)))
      (left.length + 1) := by
  induction left generalizing out v with
  | nil =>
      simpa using adr_evals_one (adr_step_revLeft_nil right work out v)
  | cons b bs ih =>
      have h1 := adr_evals_one (adr_step_revLeft_cons b bs right work out v)
      have h2 := ih (b :: out) none
      have h := EvalsToInTime.trans afterDecodePairResultComputer.step
        1 (bs.length + 1) _ _ _ h1 h2
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using h

/-- Drain `right` then halt (accept finisher; inp and left empty). -/
noncomputable def adr_evals_clearRightAccept (right : List Bool)
    (work out : List Bool) (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .clearRightAccept) v [] [] right work out)
      (some (adrCfg none none [] [] [] work out))
      (right.length + 1) := by
  induction right generalizing v with
  | nil =>
      simpa using adr_evals_one (adr_step_clearRightAccept_nil work out v)
  | cons b bs ih =>
      have h1 := adr_evals_one
        (adr_step_clearRightAccept_cons b bs work out v)
      have h2 := ih none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step
        1 (bs.length + 1) _ _ _ h1 h2
      exact evalsToInTime_le_mono t (by simp [List.length_cons])

/-- From afterParse-equivalent stacks `left = φCode.reverse`,
`right = table.reverse`, empty `out`: reverse left, push false, clear right,
halt with `false :: φCode`. Entry is `acceptEmit` (not `afterParse`). -/
noncomputable def adr_evals_accept_from_stacks (φCode table : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .acceptEmit) none [] φCode.reverse table.reverse [] [])
      (some (adrCfg none none [] [] [] [] (false :: φCode)))
      (φCode.length + table.length + 4) := by
  have henter := adr_evals_one
    (adr_step_acceptEmit [] φCode.reverse table.reverse [] [] none)
  have hrev := adr_evals_revLeft φCode.reverse table.reverse [] [] none
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 1
    (φCode.reverse.length + 1) _ _ _ henter hrev
  have t1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .acceptEmit) none [] φCode.reverse table.reverse [] [])
      (some (adrCfg (some .writeAcceptFalse) none [] [] table.reverse [] φCode))
      (φCode.length + 2) := by
    have hout : φCode.reverse.reverse ++ ([] : List Bool) = φCode := by
      simp [List.reverse_reverse]
    simpa [List.length_reverse, hout, List.append_nil] using
      evalsToInTime_le_mono t1 (by simp [List.length_reverse])
  have hwrite := adr_evals_one
    (adr_step_writeAcceptFalse [] [] table.reverse [] φCode none)
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (φCode.length + 2) 1 _ _ _ t1' hwrite
  have t2' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .acceptEmit) none [] φCode.reverse table.reverse [] [])
      (some (adrCfg (some .clearRightAccept) none [] [] table.reverse []
        (false :: φCode)))
      (φCode.length + 3) :=
    evalsToInTime_le_mono t2 (by omega)
  have hclear := adr_evals_clearRightAccept table.reverse [] (false :: φCode) none
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (φCode.length + 3) (table.reverse.length + 1) _ _ _ t2' hclear
  exact evalsToInTime_le_mono t3 (by
    simp only [List.length_reverse]
    omega)

/-- Scale a 3-factor product: `k * ((T+1)*(L+1)*(n+T+2)) = k*(T+1)*(L+1)*(n+T+2)`. -/
theorem adr_mulQ_eq (k T L n : ℕ) :
    k * ((T + 1) * (L + 1) * (n + T + 2)) =
      k * (T + 1) * (L + 1) * (n + T + 2) := by
  have h1 : k * ((T + 1) * (L + 1) * (n + T + 2)) =
      k * ((T + 1) * (L + 1)) * (n + T + 2) :=
    (Nat.mul_assoc k ((T + 1) * (L + 1)) (n + T + 2)).symm
  have h2 : k * ((T + 1) * (L + 1)) = k * (T + 1) * (L + 1) :=
    (Nat.mul_assoc k (T + 1) (L + 1)).symm
  calc
    k * ((T + 1) * (L + 1) * (n + T + 2))
        = k * ((T + 1) * (L + 1)) * (n + T + 2) := h1
    _ = (k * (T + 1) * (L + 1)) * (n + T + 2) := by rw [h2]
    _ = k * (T + 1) * (L + 1) * (n + T + 2) := rfl

/-- `L+1` and `n` sit under the cubic `(T+1)*(L+1)*(n+T+2)`. -/
theorem adr_le_Q_L (T L n : ℕ) :
    L + 1 ≤ (T + 1) * (L + 1) * (n + T + 2) := by
  have hP : 0 < L + 1 := Nat.succ_pos _
  have hT : 0 < T + 1 := Nat.succ_pos _
  have hS : 0 < n + T + 2 := by omega
  have h1 : L + 1 ≤ (L + 1) * (n + T + 2) :=
    Nat.le_mul_of_pos_right (L + 1) hS
  have h2 : (L + 1) * (n + T + 2) ≤
      (T + 1) * ((L + 1) * (n + T + 2)) :=
    Nat.le_mul_of_pos_left ((L + 1) * (n + T + 2)) hT
  have h2eq : (T + 1) * ((L + 1) * (n + T + 2)) =
      (T + 1) * (L + 1) * (n + T + 2) :=
    (Nat.mul_assoc (T + 1) (L + 1) (n + T + 2)).symm
  exact h1.trans (h2.trans_eq h2eq)

theorem adr_le_Q_n (T L n : ℕ) :
    n ≤ (T + 1) * (L + 1) * (n + T + 2) := by
  have hP : 0 < L + 1 := Nat.succ_pos _
  have hT : 0 < T + 1 := Nat.succ_pos _
  have hS : n ≤ n + T + 2 := by omega
  have h1 : n + T + 2 ≤ (L + 1) * (n + T + 2) :=
    Nat.le_mul_of_pos_left (n + T + 2) hP
  have h2 : (L + 1) * (n + T + 2) ≤
      (T + 1) * ((L + 1) * (n + T + 2)) :=
    Nat.le_mul_of_pos_left ((L + 1) * (n + T + 2)) hT
  have h2eq : (T + 1) * ((L + 1) * (n + T + 2)) =
      (T + 1) * (L + 1) * (n + T + 2) :=
    (Nat.mul_assoc (T + 1) (L + 1) (n + T + 2)).symm
  exact hS.trans (h1.trans (h2.trans_eq h2eq))

theorem adr_le_Q_one (T L n : ℕ) :
    1 ≤ (T + 1) * (L + 1) * (n + T + 2) := by
  have hQ : 0 < (T + 1) * (L + 1) * (n + T + 2) :=
    Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (by omega)
  exact Nat.succ_le_of_lt hQ

/-- `32*(L+1)*(n+1)` is at most `32` copies of the cubic. -/
theorem adr_32_Ln1_le_Q (T L n : ℕ) :
    32 * (L + 1) * (n + 1) ≤
      32 * (T + 1) * (L + 1) * (n + T + 2) := by
  have hT : 0 < T + 1 := Nat.succ_pos _
  have hn1 : n + 1 ≤ n + T + 2 := by omega
  have hcore : (L + 1) * (n + 1) ≤ (L + 1) * (n + T + 2) :=
    Nat.mul_le_mul_left (L + 1) hn1
  have hcore' : (L + 1) * (n + T + 2) ≤
      (T + 1) * ((L + 1) * (n + T + 2)) :=
    Nat.le_mul_of_pos_left ((L + 1) * (n + T + 2)) hT
  have heq : (T + 1) * ((L + 1) * (n + T + 2)) =
      (T + 1) * (L + 1) * (n + T + 2) :=
    (Nat.mul_assoc (T + 1) (L + 1) (n + T + 2)).symm
  have hprod : (L + 1) * (n + 1) ≤
      (T + 1) * (L + 1) * (n + T + 2) :=
    hcore.trans (hcore'.trans_eq heq)
  have hmul : 32 * ((L + 1) * (n + 1)) ≤
      32 * ((T + 1) * (L + 1) * (n + T + 2)) :=
    Nat.mul_le_mul_left 32 hprod
  have hL : 32 * (L + 1) * (n + 1) = 32 * ((L + 1) * (n + 1)) :=
    Nat.mul_assoc 32 (L + 1) (n + 1)
  exact hL.trans_le (hmul.trans_eq (adr_mulQ_eq 32 T L n))

/-- Park plus parse plus index loop plus accept sits under `512` copies of the cubic. -/
theorem adr_park_to_accept_time_le (L n T M : ℕ) (hn : n = M + 1) :
    4 * (L + n + 2) + 8 +
      32 * (L + 1) * (M + 2) + 4 * n + 4 * M + 16 +
      256 * (T + 1) * (L + 1) * (n + T + 2) +
      L + 4 ≤
    512 * (T + 1) * (L + 1) * (n + T + 2) := by
  have hM : M + 2 = n + 1 := by omega
  have hMn : M ≤ n := by omega
  rw [hM]
  let Q : ℕ := (T + 1) * (L + 1) * (n + T + 2)
  have hQpos : 0 < Q :=
    Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (by omega)
  have hL : L ≤ Q := (Nat.le_succ L).trans (adr_le_Q_L T L n)
  have hnQ : n ≤ Q := adr_le_Q_n T L n
  have hA : 4 * (L + n + 2) + 8 ≤ 24 * Q := by
    have heq : 4 * (L + n + 2) + 8 = 4 * L + 4 * n + 16 := by omega
    have h4L : 4 * L ≤ 4 * Q := Nat.mul_le_mul_left 4 hL
    have h4n : 4 * n ≤ 4 * Q := Nat.mul_le_mul_left 4 hnQ
    have h16 : 16 ≤ 16 * Q := Nat.le_mul_of_pos_right 16 hQpos
    have hsum : 4 * L + 4 * n + 16 ≤ 4 * Q + 4 * Q + 16 * Q :=
      add_le_add (add_le_add h4L h4n) h16
    have h24 : 4 * Q + 4 * Q + 16 * Q = 24 * Q := by
      omega
    exact heq.trans_le (hsum.trans_eq h24)
  have hB32 : 32 * (L + 1) * (n + 1) ≤ 32 * Q := by
    have h := adr_32_Ln1_le_Q T L n
    have hr : 32 * (T + 1) * (L + 1) * (n + T + 2) = 32 * Q :=
      (adr_mulQ_eq 32 T L n).symm
    exact h.trans_eq hr
  have hBn : 4 * n + 4 * M + 16 ≤ 24 * Q := by
    have h4n : 4 * n ≤ 4 * Q := Nat.mul_le_mul_left 4 hnQ
    have h4M : 4 * M ≤ 4 * Q :=
      Nat.mul_le_mul_left 4 (hMn.trans hnQ)
    have h16 : 16 ≤ 16 * Q := Nat.le_mul_of_pos_right 16 hQpos
    have hsum : 4 * n + 4 * M + 16 ≤ 4 * Q + 4 * Q + 16 * Q :=
      add_le_add (add_le_add h4n h4M) h16
    have : 4 * Q + 4 * Q + 16 * Q = 24 * Q := by omega
    exact hsum.trans_eq this
  have hD : L + 4 ≤ 5 * Q := by
    have h4 : 4 ≤ 4 * Q := Nat.le_mul_of_pos_right 4 hQpos
    exact (add_le_add hL h4).trans_eq (by omega)
  have hpre :
      ((4 * (L + n + 2) + 8 + 32 * (L + 1) * (n + 1)) +
        (4 * n + 4 * M + 16)) + (L + 4) ≤ 85 * Q := by
    have hsum :=
      add_le_add (add_le_add (add_le_add hA hB32) hBn) hD
    have : 24 * Q + 32 * Q + 24 * Q + 5 * Q = 85 * Q := by omega
    exact hsum.trans_eq this
  have hpre256 :
      ((4 * (L + n + 2) + 8 + 32 * (L + 1) * (n + 1)) +
        (4 * n + 4 * M + 16)) + (L + 4) ≤ 256 * Q :=
    hpre.trans (Nat.mul_le_mul_right Q (by omega : 85 ≤ 256))
  have hloop : 256 * (T + 1) * (L + 1) * (n + T + 2) = 256 * Q :=
    (adr_mulQ_eq 256 T L n).symm
  have h512 : 256 * Q + 256 * Q = 512 * Q := by
    rw [← Nat.add_mul 256 256 Q]

  have hR : 512 * Q = 512 * (T + 1) * (L + 1) * (n + T + 2) :=
    adr_mulQ_eq 512 T L n
  have hsum := add_le_add hpre256 (le_of_eq hloop)
  have hLHS :
      4 * (L + n + 2) + 8 + 32 * (L + 1) * (n + 1) + 4 * n + 4 * M + 16 +
        256 * (T + 1) * (L + 1) * (n + T + 2) + L + 4 =
      (((4 * (L + n + 2) + 8 + 32 * (L + 1) * (n + 1)) +
        (4 * n + 4 * M + 16)) + (L + 4)) +
        256 * (T + 1) * (L + 1) * (n + T + 2) := by
    ac_rfl
  exact hLHS.trans_le (hsum.trans_eq (h512.trans hR))

/-- All-true nonempty tables never start with `false`. -/
theorem allTrue_head_ne_false {table : List Bool}
    (hall : ∀ b ∈ table, b = true) (hne : table ≠ []) :
    table.head? ≠ some false := by
  cases table with
  | nil => exact (hne rfl).elim
  | cons b rest =>
      have hb : b = true := hall b (by simp)
      simp [hb]

/-- Reverse of an all-true table is the table itself. -/
theorem reverse_eq_of_allTrue {table : List Bool}
    (hall : ∀ b ∈ table, b = true) :
    table.reverse = table := by
  have hall' : ∀ b ∈ table.reverse, b = true := fun b hb =>
    hall b (List.mem_reverse.mp hb)
  have h1 : table.reverse = List.replicate table.reverse.length true :=
    List.eq_replicate_iff.mpr ⟨rfl, hall'⟩
  have h2 : table = List.replicate table.length true :=
    List.eq_replicate_iff.mpr ⟨rfl, hall⟩
  rw [h1, List.length_reverse]
  exact h2.symm

/-- From `parkWidth` with matching width, a tautology and all-true table halt
as `false :: encodeFormula φ`. -/
noncomputable def adr_evals_park_to_accept (φ : PropFormula)
    (table : List Bool) (n : ℕ)
    (hn : n = φ.maxVar + 1)
    (htaut : φ.Tautology)
    (hall : ∀ b ∈ table, b = true)
    (ht : table.head? ≠ some false) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .parkWidth) none (pow2BitsLE n)
        (encodeFormula φ).reverse table [] [])
      (some (adrCfg none none [] [] [] [] (false :: encodeFormula φ)))
      (512 * (table.length + 1) * ((encodeFormula φ).length + 1) *
        (n + table.length + 2)) := by
  have hpark := adr_evals_park_to_mvParse (encodeFormula φ) table n
  have hparse := adr_evals_mvParse_to_indexLoop φ table n hn ht
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step
    _ _ _ _ _ hpark hparse
  have hloop := adr_evals_indexLoop_allTrue φ [] (List.replicate n false)
    table htaut hall
  have hloop' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .indexLoop) none [] (encodeFormula φ).reverse table
        (List.replicate n false) [])
      (some (adrCfg (some .acceptEmit) none [] (encodeFormula φ).reverse
        [] [] []))
      (256 * (table.length + 1) * ((encodeFormula φ).length + 1) *
        (n + table.length + 2)) := by
    simpa [List.length_nil, List.length_replicate, Nat.zero_add] using hloop
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step
    _ _ _ _ _ t1 hloop'
  have hacc := adr_evals_accept_from_stacks (encodeFormula φ) []
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
    _ _ _ _ _ t2 hacc
  have hbound := adr_park_to_accept_time_le
    (encodeFormula φ).length n table.length φ.maxVar hn
  refine evalsToInTime_le_mono t3 (le_trans (le_of_eq ?eq) hbound)
  case eq =>
    simp only [List.length_nil]
    ac_rfl

/-- Fail-tag singleton `[true]` → `[true]` in 3 steps. -/
noncomputable def afterDecodePairResult_evals_fail_tag :
    TM2OutputsInTime afterDecodePairResultComputer [true] (some [true]) 3 := by
  change EvalsToInTime afterDecodePairResultComputer.step
    (initList afterDecodePairResultComputer [true])
    (some (haltList afterDecodePairResultComputer [true])) 3
  rw [afterDecodePairResult_initList, afterDecodePairResult_haltList]
  have h1 := adr_evals_one (adr_step_readTag_true [] [] [] [] [] none)
  have h2 := adr_evals_one (adr_step_drainTrue_nil [] [] [] [] none)
  have h3 := adr_evals_one (adr_step_writeFail [] [] [] [] [] none)
  have t12 := EvalsToInTime.trans afterDecodePairResultComputer.step 1 1 _ _ _ h1 h2
  exact EvalsToInTime.trans afterDecodePairResultComputer.step 2 1 _ _ _ t12 h3

/-- Drain leftover bits after a leading `true`, then write `[true]`. -/
noncomputable def adr_evals_drainTrue (inp left right work out : List Bool)
    (v : Option Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .drainTrue) v inp left right work out)
      (some (adrCfg (some .writeFail) none [] left right work out))
      (inp.length + 1) := by
  induction inp generalizing v with
  | nil =>
      simpa using adr_evals_one (adr_step_drainTrue_nil left right work out v)
  | cons b rest ih =>
      have h1 := adr_evals_one
        (adr_step_drainTrue_cons b rest left right work out v)
      have h2 := ih none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (rest.length + 1) _ _ _ h1 h2
      simpa [List.length_cons] using t

/-- Leading `true` (any leftover) emits `[true]`. -/
noncomputable def afterDecodePairResult_evals_true (rest : List Bool) :
    TM2OutputsInTime afterDecodePairResultComputer (true :: rest) (some [true])
      (rest.length + 3) := by
  change EvalsToInTime afterDecodePairResultComputer.step
    (initList afterDecodePairResultComputer (true :: rest))
    (some (haltList afterDecodePairResultComputer [true])) (rest.length + 3)
  rw [afterDecodePairResult_initList, afterDecodePairResult_haltList]
  have h1 := adr_evals_one
    (adr_step_readTag_true rest [] [] [] [] none)
  have h2 := adr_evals_drainTrue rest [] [] [] [] none
  have t12 := EvalsToInTime.trans afterDecodePairResultComputer.step 1
    (rest.length + 1) _ _ _ h1 h2
  have h3 := adr_evals_one (adr_step_writeFail [] [] [] [] [] none)
  have t := EvalsToInTime.trans afterDecodePairResultComputer.step
    (rest.length + 2) 1 _ _ _ t12 h3
  exact evalsToInTime_le_mono t (by omega)

/-- Parse failure for `decodePair work = none` drains and emits `[true]`. -/
noncomputable def adr_evals_parse_none (work left : List Bool)
    (h : decodePair work = none) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .parse) none work left [] [] [])
      (some (adrCfg none none [] [] [] [] [true]))
      (3 * work.length + left.length + 4) := by
  match work with
  | [] =>
      have h1 := adr_evals_one (adr_step_parse_nil left [] [] [] none)
      have h2 := adr_evals_clear_to_fail left [] [] [] none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
        (left.length + 3) _ _ _ h1 h2
      exact evalsToInTime_le_mono t (by omega)
  | [true] =>
      have h1 := adr_evals_one (adr_step_parse_true_any [] left [] [] [] none)
      have h2 := adr_evals_one (adr_step_expectBit_nil left [] [] [] none)
      have t12 := EvalsToInTime.trans afterDecodePairResultComputer.step 1 1
        _ _ _ h1 h2
      have h3 := adr_evals_clear_to_fail left [] [] [] none
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 2
        (left.length + 3) _ _ _ t12 h3
      exact evalsToInTime_le_mono t (by simp [List.length])
  | false :: rest =>
      simp [decodePair] at h
  | true :: b :: rest =>
      have hrest : decodePair rest = none := by
        simp only [decodePair] at h
        cases hrest : decodePair rest with
        | none => rfl
        | some _ => simp [hrest] at h
      have h1a := adr_evals_one
        (adr_step_parse_true b rest left [] [] [] none)
      have h1b := adr_evals_one
        (adr_step_expectBit b rest left [] [] [] none)
      have h1 := EvalsToInTime.trans afterDecodePairResultComputer.step 1 1
        _ _ _ h1a h1b
      have h1' : EvalsToInTime afterDecodePairResultComputer.step
          (adrCfg (some .parse) none (true :: b :: rest) left [] [] [])
          (some (adrCfg (some .parse) none rest (b :: left) [] [] [])) 2 :=
        evalsToInTime_le_mono h1 (by omega)
      have h2 := adr_evals_parse_none rest (b :: left) hrest
      have t := EvalsToInTime.trans afterDecodePairResultComputer.step 2
        (3 * rest.length + (b :: left).length + 4) _ _ _ h1' h2
      exact evalsToInTime_le_mono t (by simp [List.length_cons]; omega)

/-- Success-tag parse fail: `false :: rest` with `decodePair rest = none`. -/
noncomputable def afterDecodePairResult_evals_false_decode_fail
    (rest : List Bool) (h : decodePair rest = none) :
    TM2OutputsInTime afterDecodePairResultComputer (false :: rest) (some [true])
      (3 * rest.length + 6) := by
  change EvalsToInTime afterDecodePairResultComputer.step
    (initList afterDecodePairResultComputer (false :: rest))
    (some (haltList afterDecodePairResultComputer [true])) (3 * rest.length + 6)
  rw [afterDecodePairResult_initList, afterDecodePairResult_haltList]
  have h1 := adr_evals_one (adr_step_readTag_false rest [] [] [] [] none)
  have h2 := adr_evals_parse_none rest [] h
  have t := EvalsToInTime.trans afterDecodePairResultComputer.step 1
    (3 * rest.length + 4) _ _ _ h1 h2
  exact evalsToInTime_le_mono t (by omega)

/-- Empty input → `[true]`. -/
noncomputable def afterDecodePairResult_evals_nil :
    TM2OutputsInTime afterDecodePairResultComputer [] (some [true]) 2 := by
  change EvalsToInTime afterDecodePairResultComputer.step
    (initList afterDecodePairResultComputer [])
    (some (haltList afterDecodePairResultComputer [true])) 2
  rw [afterDecodePairResult_initList, afterDecodePairResult_haltList]
  have h1 := adr_evals_one (adr_step_readTag_nil [] [] [] [] none)
  have h2 := adr_evals_one (adr_step_writeFail [] [] [] [] [] none)
  exact EvalsToInTime.trans afterDecodePairResultComputer.step 1 1 _ _ _ h1 h2

/-! ### Cluster D3.1 success-tag: encodePair load then reject scaffold -/

def adr_evals_one_bit (b : Bool) (rest left right work out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .parse) none (true :: b :: rest) left right work out)
      (some (adrCfg (some .parse) none rest (b :: left) right work out)) 2 where
  steps := 2
  steps_le_m := by decide
  evals_in_steps := by
    change ((some (adrCfg (some .parse) none (true :: b :: rest) left right work out)).bind
        afterDecodePairResultComputer.step).bind afterDecodePairResultComputer.step =
      some (adrCfg (some .parse) none rest (b :: left) right work out)
    simp only [FinTM2.step]
    change ((TM2.step afterDecodePairResultComputer.m
        (adrCfg (some .parse) none (true :: b :: rest) left right work out)).bind
        (TM2.step afterDecodePairResultComputer.m)) =
      some (adrCfg (some .parse) none rest (b :: left) right work out)
    rw [adr_step_parse_true]
    exact adr_step_expectBit b rest left right work out none

noncomputable def adr_evals_parse_first (x rest left right work out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .parse) none
        ((x.flatMap fun b => [true, b]) ++ rest) left right work out)
      (some (adrCfg (some .parse) none rest (x.reverse ++ left) right work out))
      (2 * x.length) := by
  induction x generalizing left with
  | nil =>
      simpa using EvalsToInTime.refl afterDecodePairResultComputer.step
        (adrCfg (some .parse) none rest left right work out)
  | cons b xs ih =>
      have h1 :=
        adr_evals_one_bit b ((xs.flatMap fun b => [true, b]) ++ rest)
          left right work out
      have h2 := ih (b :: left)
      have h :=
        EvalsToInTime.trans afterDecodePairResultComputer.step 2 (2 * xs.length)
          (adrCfg (some .parse) none
            ((b :: xs).flatMap (fun b => [true, b]) ++ rest) left right work out)
          (adrCfg (some .parse) none
            ((xs.flatMap fun b => [true, b]) ++ rest) (b :: left) right work out)
          (some (adrCfg (some .parse) none rest
            (xs.reverse ++ (b :: left)) right work out))
          (by simpa [List.flatMap] using h1) h2
      simpa [List.flatMap, List.reverse_cons, List.append_assoc, Nat.mul_succ,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, two_mul] using h

noncomputable def adr_evals_loadRight (ys left right work out : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .loadRight) none ys left right work out)
      (some (adrCfg (some .afterParse) none [] left (ys.reverse ++ right) work out))
      (ys.length + 1) := by
  induction ys generalizing right with
  | nil =>
      simpa using adr_evals_one (adr_step_loadRight_nil left right work out none)
  | cons y ys ih =>
      have h1 := adr_evals_one
        (adr_step_loadRight_cons y ys left right work out none)
      have h2 := ih (y :: right)
      have h :=
        EvalsToInTime.trans afterDecodePairResultComputer.step 1 (ys.length + 1)
          _ _ _ h1 h2
      refine ⟨⟨h.steps, ?_⟩, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using h.evals_in_steps
      · exact le_trans h.steps_le_m (by simp [List.length_cons])

/-- Load `encodePair (xs, ys)` into reversed stacks, then enter `afterParse`. -/
noncomputable def adr_evals_load_encodePair (xs ys : List Bool) :
    EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .parse) none (encodePair (xs, ys)) [] [] [] [])
      (some (adrCfg (some .afterParse) none [] xs.reverse ys.reverse [] []))
      (2 * xs.length + ys.length + 2) := by
  have hparse :=
    adr_evals_parse_first xs (false :: ys) [] [] [] []
  have htoLoad :=
    adr_evals_one (adr_step_parse_false ys xs.reverse [] [] [] none)
  have hload :=
    adr_evals_loadRight ys xs.reverse [] [] []
  have h1 : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .parse) none (encodePair (xs, ys)) [] [] [] [])
      (some (adrCfg (some .parse) none (false :: ys) xs.reverse [] [] []))
      (2 * xs.length) := by
    simpa [encodePair, List.append_assoc] using hparse
  have h12 :=
    EvalsToInTime.trans afterDecodePairResultComputer.step (2 * xs.length) 1
      _ _ _ h1 htoLoad
  have h12' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .parse) none (encodePair (xs, ys)) [] [] [] [])
      (some (adrCfg (some .loadRight) none ys xs.reverse [] [] []))
      (2 * xs.length + 1) := by
    simpa [Nat.add_comm] using h12
  have h :=
    EvalsToInTime.trans afterDecodePairResultComputer.step
      (2 * xs.length + 1) (ys.length + 1) _ _ _ h12' hload
  refine ⟨⟨h.steps, ?_⟩, ?_⟩
  · simpa [List.append_nil] using h.evals_in_steps
  · refine le_trans h.steps_le_m ?_
    omega

theorem afterDecodePairResult_of_false_decode_fail {rest : List Bool}
    (h : decodePair rest = none) :
    afterDecodePairResult (false :: rest) = [true] := by
  simp [afterDecodePairResult, decodeDecodePairResult, h]

/-- Success-tag parse fail: `false :: []` → `[true]`. -/
noncomputable def afterDecodePairResult_evals_false_nil :
    TM2OutputsInTime afterDecodePairResultComputer (false :: []) (some [true])
      5 := by
  change EvalsToInTime afterDecodePairResultComputer.step
    (initList afterDecodePairResultComputer (false :: []))
    (some (haltList afterDecodePairResultComputer [true])) 5
  rw [afterDecodePairResult_initList, afterDecodePairResult_haltList]
  have h1 := adr_evals_one (adr_step_readTag_false [] [] [] [] [] none)
  have h2 := adr_evals_one (adr_step_parse_nil [] [] [] [] none)
  have h3 := adr_evals_clear_to_fail [] [] [] [] none
  have t12 := EvalsToInTime.trans afterDecodePairResultComputer.step 1 1 _ _ _ h1 h2
  exact EvalsToInTime.trans afterDecodePairResultComputer.step 2 3 _ _ _ t12 h3

/-- Success-tag parse fail: `false :: [true]` → `[true]`. -/
noncomputable def afterDecodePairResult_evals_false_true :
    TM2OutputsInTime afterDecodePairResultComputer (false :: [true]) (some [true])
      6 := by
  change EvalsToInTime afterDecodePairResultComputer.step
    (initList afterDecodePairResultComputer (false :: [true]))
    (some (haltList afterDecodePairResultComputer [true])) 6
  rw [afterDecodePairResult_initList, afterDecodePairResult_haltList]
  have h1 := adr_evals_one (adr_step_readTag_false [true] [] [] [] [] none)
  -- parse on [true]: pop true → expectBit on []
  have h2 : TM2.step afterDecodePairResultComputer.m
      (adrCfg (some .parse) none [true] [] [] [] []) =
      some (adrCfg (some .expectBit) none [] [] [] [] []) := by
    simp [afterDecodePairResultComputer, adrCfg, adrStk, TM2.step, TM2.stepAux]
    refine congrArg some <|
      congrArg (fun stk =>
        (⟨some ADRLabel.expectBit, (none : Option Bool), stk⟩ :
          afterDecodePairResultComputer.Cfg)) ?_
    funext k; cases k <;> simp [Function.update, adrStk]
  have h2e := adr_evals_one h2
  have h3 := adr_evals_one (adr_step_expectBit_nil [] [] [] [] none)
  have h4 := adr_evals_clear_to_fail [] [] [] [] none
  have t12 := EvalsToInTime.trans afterDecodePairResultComputer.step 1 1 _ _ _ h1 h2e
  have t123 := EvalsToInTime.trans afterDecodePairResultComputer.step 2 1 _ _ _ t12 h3
  exact EvalsToInTime.trans afterDecodePairResultComputer.step 3 3 _ _ _ t123 h4

/-- Success-tag reject when the table has a false bit or length is not a
power of two. Remaining reject cases (decode fail, width mismatch, eval
false on a well-formed all-true power-of-two table) go through `parkWidth`. -/
noncomputable def afterDecodePairResult_evals_encodePair_reject
    (φCode table : List Bool)
    (h : validatesTautologyResult φCode table = [true])
    (hrej : (∃ b ∈ table, b = false) ∨ (∀ n, table.length ≠ 2 ^ n)) :
    TM2OutputsInTime afterDecodePairResultComputer
      (false :: encodePair (φCode, table)) (some [true])
      (2 * φCode.length + table.length + 4 +
        2 * table.length + 2 * (0 : ℕ) +
        (table.length + 0 + 1) * (2 * (0 + table.length + 2) + 3) +
        2 * (table.length + 0) + φCode.length +
        2 * (0 + table.length) + table.length + 14) := by
  change EvalsToInTime afterDecodePairResultComputer.step
    (initList afterDecodePairResultComputer (false :: encodePair (φCode, table)))
    (some (haltList afterDecodePairResultComputer [true]))
    (2 * φCode.length + table.length + 4 +
      2 * table.length + 2 * (0 : ℕ) +
      (table.length + 0 + 1) * (2 * (0 + table.length + 2) + 3) +
      2 * (table.length + 0) + φCode.length +
      2 * (0 + table.length) + table.length + 14)
  rw [afterDecodePairResult_initList, afterDecodePairResult_haltList]
  have htag := adr_evals_one
    (adr_step_readTag_false (encodePair (φCode, table)) [] [] [] [] none)
  have hload := adr_evals_load_encodePair φCode table
  have hafter := adr_evals_one
    (adr_step_afterParse [] φCode.reverse table.reverse [] [] none)
  have hscan := adr_evals_allTrueScan_to_fail
    φCode.reverse table.reverse [] none (by
      cases hrej with
      | inl hex =>
          rcases hex with ⟨b, hb, hbF⟩
          refine Or.inl ⟨b, List.mem_reverse.mpr hb, hbF⟩
      | inr hpow =>
          refine Or.inr ?_
          intro n
          simpa [List.length_reverse] using hpow n)
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step 1
    (2 * φCode.length + table.length + 2) _ _ _ htag hload
  have t1' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .readTag) none (false :: encodePair (φCode, table)) [] [] [] [])
      (some (adrCfg (some .afterParse) none [] φCode.reverse table.reverse [] []))
      (2 * φCode.length + table.length + 3) :=
    evalsToInTime_le_mono t1 (by omega)
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (2 * φCode.length + table.length + 3) 1 _ _ _ t1' hafter
  have t2' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .readTag) none (false :: encodePair (φCode, table)) [] [] [] [])
      (some (adrCfg (some .allTrueScan) none [] φCode.reverse table.reverse [] []))
      (2 * φCode.length + table.length + 4) :=
    evalsToInTime_le_mono t2 (by omega)
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
    (2 * φCode.length + table.length + 4)
    (2 * table.reverse.length + 2 * (0 : ℕ) +
      (table.reverse.length + 0 + 1) * (2 * (0 + table.reverse.length + 2) + 3) +
      2 * (table.reverse.length + 0) + φCode.reverse.length +
      2 * (0 + table.reverse.length) + table.reverse.length + 14)
    _ _ _ t2' hscan
  have _ := h
  exact evalsToInTime_le_mono t3 (by simp [List.length_reverse]; omega)

/-- `(T+1)*(2*(T+2)+3)` sits under `8` copies of the cubic. -/
theorem adr_scan_time_le_Q (T L n : ℕ) :
    (T + 1) * (2 * (T + 2) + 3) ≤
      8 * (T + 1) * (L + 1) * (n + T + 2) := by
  have hP : 0 < L + 1 := Nat.succ_pos _
  have hlin : 2 * (T + 2) + 3 ≤ 8 * (n + T + 2) := by omega
  have hcore : (T + 1) * (2 * (T + 2) + 3) ≤ (T + 1) * (8 * (n + T + 2)) :=
    Nat.mul_le_mul_left (T + 1) hlin
  have hcore' : (T + 1) * (8 * (n + T + 2)) = 8 * ((T + 1) * (n + T + 2)) := by
    calc
      (T + 1) * (8 * (n + T + 2))
          = ((T + 1) * 8) * (n + T + 2) := (Nat.mul_assoc _ _ _).symm
      _ = (8 * (T + 1)) * (n + T + 2) := by rw [Nat.mul_comm (T + 1) 8]
      _ = 8 * ((T + 1) * (n + T + 2)) := Nat.mul_assoc _ _ _
  have hmid : 8 * ((T + 1) * (n + T + 2)) ≤
      8 * ((L + 1) * ((T + 1) * (n + T + 2))) :=
    Nat.mul_le_mul_left 8 (Nat.le_mul_of_pos_left ((T + 1) * (n + T + 2)) hP)
  have heq : 8 * ((L + 1) * ((T + 1) * (n + T + 2))) =
      8 * (T + 1) * (L + 1) * (n + T + 2) := by
    have h1 : (L + 1) * ((T + 1) * (n + T + 2)) =
        (L + 1) * (T + 1) * (n + T + 2) :=
      (Nat.mul_assoc (L + 1) (T + 1) (n + T + 2)).symm
    have h2 : (L + 1) * (T + 1) = (T + 1) * (L + 1) := Nat.mul_comm _ _
    calc
      8 * ((L + 1) * ((T + 1) * (n + T + 2)))
          = 8 * ((L + 1) * (T + 1) * (n + T + 2)) := by rw [h1]
      _ = 8 * ((T + 1) * (L + 1) * (n + T + 2)) := by rw [h2]
      _ = 8 * (T + 1) * (L + 1) * (n + T + 2) := adr_mulQ_eq 8 T L n
  exact (hcore.trans_eq hcore').trans (hmid.trans_eq heq)

/-- Load, scan, and park-to-accept sit under `1024` copies of the cubic. -/
theorem adr_encodePair_accept_time_le (L n T M : ℕ) (hn : n = M + 1) :
    2 * L + T + 4 +
      ((T + 1) * (2 * (T + 2) + 3) + 3 * T + 3 * n + 8) +
      512 * (T + 1) * (L + 1) * (n + T + 2) ≤
    1024 * (T + 1) * (L + 1) * (n + T + 2) := by
  let Q : ℕ := (T + 1) * (L + 1) * (n + T + 2)
  have hQpos : 0 < Q :=
    Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (by omega)
  have hL : L ≤ Q := (Nat.le_succ L).trans (adr_le_Q_L T L n)
  have hnQ : n ≤ Q := adr_le_Q_n T L n
  have hTle : T ≤ Q := by
    have h1 : T ≤ n + T + 2 := by omega
    have h2 : n + T + 2 ≤ (L + 1) * (n + T + 2) :=
      Nat.le_mul_of_pos_left (n + T + 2) (Nat.succ_pos _)
    have h3 : (L + 1) * (n + T + 2) ≤ Q := by
      have : (L + 1) * (n + T + 2) ≤
          (T + 1) * ((L + 1) * (n + T + 2)) :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      exact this.trans_eq (Nat.mul_assoc (T + 1) (L + 1) (n + T + 2)).symm
    exact h1.trans (h2.trans h3)
  have hscan : (T + 1) * (2 * (T + 2) + 3) ≤ 8 * Q := by
    have h := adr_scan_time_le_Q T L n
    have hr : 8 * (T + 1) * (L + 1) * (n + T + 2) = 8 * Q :=
      (adr_mulQ_eq 8 T L n).symm
    exact h.trans_eq hr
  have hpre : 2 * L + T + 4 +
      ((T + 1) * (2 * (T + 2) + 3) + 3 * T + 3 * n + 8) ≤ 32 * Q := by
    have h2L : 2 * L ≤ 2 * Q := Nat.mul_le_mul_left 2 hL
    have h3T : 3 * T ≤ 3 * Q := Nat.mul_le_mul_left 3 hTle
    have h3n : 3 * n ≤ 3 * Q := Nat.mul_le_mul_left 3 hnQ
    have h4 : 4 ≤ 4 * Q := Nat.le_mul_of_pos_right 4 hQpos
    have h8 : 8 ≤ 8 * Q := Nat.le_mul_of_pos_right 8 hQpos
    have hleft : 2 * L + T + 4 ≤ 2 * Q + Q + 4 * Q :=
      add_le_add (add_le_add h2L hTle) h4
    have hright :
        (T + 1) * (2 * (T + 2) + 3) + 3 * T + 3 * n + 8 ≤
          8 * Q + 3 * Q + 3 * Q + 8 * Q :=
      add_le_add (add_le_add (add_le_add hscan h3T) h3n) h8
    have hsum := add_le_add hleft hright
    have : 2 * Q + Q + 4 * Q + (8 * Q + 3 * Q + 3 * Q + 8 * Q) = 29 * Q := by
      omega
    exact hsum.trans_eq this |>.trans (Nat.mul_le_mul_right Q (by omega : 29 ≤ 32))
  have hpre512 : 2 * L + T + 4 +
      ((T + 1) * (2 * (T + 2) + 3) + 3 * T + 3 * n + 8) ≤ 512 * Q :=
    hpre.trans (Nat.mul_le_mul_right Q (by omega : 32 ≤ 512))
  have hpark : 512 * (T + 1) * (L + 1) * (n + T + 2) = 512 * Q :=
    (adr_mulQ_eq 512 T L n).symm
  have h1024 : 512 * Q + 512 * Q = 1024 * Q := by
    rw [← Nat.add_mul 512 512 Q]
  have hR : 1024 * Q = 1024 * (T + 1) * (L + 1) * (n + T + 2) :=
    adr_mulQ_eq 1024 T L n
  have hsum := add_le_add hpre512 (le_of_eq hpark)
  have hLHS :
      2 * L + T + 4 +
        ((T + 1) * (2 * (T + 2) + 3) + 3 * T + 3 * n + 8) +
        512 * (T + 1) * (L + 1) * (n + T + 2) =
      (2 * L + T + 4 +
        ((T + 1) * (2 * (T + 2) + 3) + 3 * T + 3 * n + 8)) +
        512 * (T + 1) * (L + 1) * (n + T + 2) := by
    ac_rfl
  have _ := hn
  exact hLHS.trans_le (hsum.trans_eq (h1024.trans hR))

/-- Success-tag accept: tautology plus all-true table of length `2^(maxVar+1)`. -/
noncomputable def afterDecodePairResult_evals_encodePair_accept
    (φ : PropFormula) (table : List Bool)
    (htaut : φ.Tautology)
    (hall : ∀ b ∈ table, b = true)
    (hlen : table.length = 2 ^ (φ.maxVar + 1)) :
    TM2OutputsInTime afterDecodePairResultComputer
      (false :: encodePair (encodeFormula φ, table))
      (some (false :: encodeFormula φ))
      (1024 * (table.length + 1) * ((encodeFormula φ).length + 1) *
        ((φ.maxVar + 1) + table.length + 2)) := by
  change EvalsToInTime afterDecodePairResultComputer.step
    (initList afterDecodePairResultComputer
      (false :: encodePair (encodeFormula φ, table)))
    (some (haltList afterDecodePairResultComputer (false :: encodeFormula φ)))
    (1024 * (table.length + 1) * ((encodeFormula φ).length + 1) *
      ((φ.maxVar + 1) + table.length + 2))
  rw [afterDecodePairResult_initList, afterDecodePairResult_haltList]
  let n : ℕ := φ.maxVar + 1
  have hn : n = φ.maxVar + 1 := rfl
  have hne : table ≠ [] := by
    intro hnil
    subst hnil
    have hz : (0 : ℕ) = 2 ^ (φ.maxVar + 1) := hlen
    have hpos : 0 < 2 ^ (φ.maxVar + 1) := Nat.two_pow_pos _
    exact absurd hz (Nat.ne_of_lt hpos)
  have ht := allTrue_head_ne_false hall hne
  have hrev := reverse_eq_of_allTrue hall
  have htag := adr_evals_one
    (adr_step_readTag_false (encodePair (encodeFormula φ, table)) [] [] [] [] none)
  have hload := adr_evals_load_encodePair (encodeFormula φ) table
  have hload' : EvalsToInTime afterDecodePairResultComputer.step
      (adrCfg (some .parse) none (encodePair (encodeFormula φ, table)) [] [] [] [])
      (some (adrCfg (some .afterParse) none [] (encodeFormula φ).reverse table [] []))
      (2 * (encodeFormula φ).length + table.length + 2) := by
    simpa [hrev] using hload
  have hafter := adr_evals_one
    (adr_step_afterParse [] (encodeFormula φ).reverse table [] [] none)
  have hpow := adr_evals_allTrue_pow2_to_parkWidth
    (encodeFormula φ).reverse table n hall (by simpa [n] using hlen)
  have hpark := adr_evals_park_to_accept φ table n hn htaut hall ht
  have t1 := EvalsToInTime.trans afterDecodePairResultComputer.step
    1 (2 * (encodeFormula φ).length + table.length + 2) _ _ _ htag hload'
  have t2 := EvalsToInTime.trans afterDecodePairResultComputer.step
    _ 1 _ _ _ t1 hafter
  have t3 := EvalsToInTime.trans afterDecodePairResultComputer.step
    _ _ _ _ _ t2 hpow
  have t4 := EvalsToInTime.trans afterDecodePairResultComputer.step
    _ _ _ _ _ t3 hpark
  refine evalsToInTime_le_mono t4 (le_trans (le_of_eq ?eq)
    (adr_encodePair_accept_time_le (encodeFormula φ).length n table.length
      φ.maxVar hn))
  case eq =>
    simp only [n]
    ring


namespace ProofSystemFrontier

/-- Full FinTM2 for `validatesTautologyResult_on_pair`: decode pair, decode
formula, length gate `table.length = 2^(maxVar+1)`, then index loop under
`|table|` fuel, then branch to the reject or accept slices above.

Certified: length gate Bool, reject lemmas, `pow2BitsLE` plus writePow2Bits
FinTM2, `natBitsLE`/`lengthBitsEqPow2` compare, `countLengthBits` polyTime,
`bitsEqual`/`bitsEqualZip` lengthGate rewrites, `bitsEqualComputer` Stmt,
leftover drain, encodePair load, unequal zipper Evals, and
`bitsEqualPair` TM2ComputableInPolyTime under encodePair.
Also certified: `assignmentAt n i = padBitsLE n (natBitsLE i)` when `i < 2^n`,
`validatesTautology_by_index_pad`, and `padBitsComputer` FinTM2 Stmt plus
EvalsToInTime / `padBitsComputableInPolyTime` for `padBitsLE` under
`encodePair (encodeNat n, bs)`.
Also certified: `evalEncodedComputer` FinTM2 Stmt plus EvalsToInTime /
`evalEncodedComputableInPolyTime` for `evalOn` under
`encodePair (σ, encodeFormula φ)`.
Also certified (Cluster D2): functional `indexValidate` /
`indexValidateFuel` / `indexStepOk` equiv to `validatesTautology_by_index`,
`indexValidateResult_eq_validatesTautologyResult`, length-gate Bool
`indexLengthGate`, one-iter `indexStepBitsComputer` with EvalsToInTime /
`indexStepBitsComputableInPolyTime`, semantic target
`indexValidateOnTriple` under `encodeIndexValidate`, and `odometerSucc`
matching `assignmentAt` succession with `odometerSuccComputer` EvalsToInTime /
`odometerSuccComputableInPolyTime`.
Also certified: local `comp_idBitEnc_idBitEnc` (Complexity) for Bool-tape
composition with an output-size bound.
Also certified: `afterDecodePairResult` with
`validatesTautologyResult_on_pair = afterDecodePairResult ∘ decodePairResult`
and a length bound.
Also certified (Cluster D3.1): `afterDecodePairResultComputer` encodePair
parse (bitsEqual load pattern), fail-tag / parse-fail Evals, and success-tag
reject scaffold Evals under `validatesTautologyResult = [true]`.
Remaining: replace `afterParse` reject scaffold with indexValidate under
`|table|` fuel (pad/eval/indexStepBits/odometer), package
`afterDecodePairResultComputableInPolyTime`, then
`comp_idBitEnc_idBitEnc` closes this pin. -/
theorem validatesTautologyResult_computableInPolyTime :
    Nonempty (TM2ComputableInPolyTime idBitEnc idBitEnc
      validatesTautologyResult_on_pair) := by
  sorry

end ProofSystemFrontier



/- SATurday auto-apply 2026-09-09T22:42:15Z (rung r5-cook-reckhow-bridge). -/
namespace ProofSystemFrontier

/-- Packaging: length bound already certified. -/
theorem validatesTautologyResult_on_pair_length_frontier (π : List Bool) :
    (validatesTautologyResult_on_pair π).length ≤ π.length + 1 :=
  length_validatesTautologyResult_on_pair_le π

end ProofSystemFrontier



/- SATurday auto-apply 2026-09-09T23:38:37Z (rung r5-cook-reckhow-bridge). -/
namespace ProofSystemFrontier

/-- A polynomial output size bound. A machine running time bound is still required. -/
theorem validatesTautologyResult_on_pair_exists_polynomial_output_bound :
    ∃ p : Polynomial ℕ, ∀ π : List Bool,
      (validatesTautologyResult_on_pair π).length ≤ p.eval π.length := by
  refine ⟨Polynomial.X + 1, ?_⟩
  intro π
  simpa only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] using
    validatesTautologyResult_on_pair_length_frontier π

end ProofSystemFrontier

/-
{"status":"partial","notes":"Packages the certified length bound as a polynomial output size bound. Polynomial machine running time remains open.","next_recommended_action":"formalize","gate_pending":true}
-/



/- SATurday auto-apply 2026-09-10T00:20:08Z (rung r5-cook-reckhow-bridge). -/
namespace ProofSystemFrontier

/-- Batched validation has quadratic total output size when both the number
of inputs and each input length are bounded by `n`. This bounds stored results,
not machine running time. -/
theorem validatesTautologyResult_batch_output_bound
    (inputs : List (List Bool)) (n : ℕ)
    (hcount : inputs.length ≤ n)
    (hsize : ∀ π ∈ inputs, π.length ≤ n) :
    (inputs.map (fun π => (validatesTautologyResult_on_pair π).length)).sum
      ≤ n * (n + 1) := by
  have batch_bound :
      ∀ xs : List (List Bool),
        (∀ π ∈ xs, π.length ≤ n) →
        (xs.map (fun π =>
          (validatesTautologyResult_on_pair π).length)).sum
          ≤ xs.length * (n + 1) := by
    intro xs
    induction xs with
    | nil =>
        intro _
        simp
    | cons π xs ih =>
        intro hs
        have hπ := validatesTautologyResult_on_pair_length_frontier π
        have hπsize : π.length ≤ n := hs π (by simp)
        have htail := ih (by
          intro ψ hψ
          exact hs ψ (by simp only [List.mem_cons]; exact Or.inr hψ))
        simp only [List.map_cons, List.sum_cons, List.length_cons,
          Nat.succ_mul]
        omega
  exact (batch_bound inputs hsize).trans
    (Nat.mul_le_mul_right (n + 1) hcount)

end ProofSystemFrontier

/- SATurday auto-apply 2026-09-10T00:39:14Z (rung r5-cook-reckhow-bridge). -/
namespace ProofSystemFrontier

/-- Validation increases total batch output size by at most one bit per
input. This gives an additive allocation bound for the polynomial time
obligation, but does not establish a machine running time bound. -/
theorem validatesTautologyResult_batch_additive_length_bound
    (inputs : List (List Bool)) :
    (inputs.map (fun π =>
      (validatesTautologyResult_on_pair π).length)).sum
      ≤ (inputs.map List.length).sum + inputs.length := by
  induction inputs with
  | nil =>
      simp
  | cons π inputs ih =>
      have hπ :
          (validatesTautologyResult_on_pair π).length ≤ π.length + 1 :=
        validatesTautologyResult_on_pair_length_frontier π
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

end ProofSystemFrontier

/- SATurday auto-apply 2026-09-10T01:07:36Z (rung r5-cook-reckhow-bridge). -/
namespace ProofSystemFrontier

/-- With one delimiter bit per entry, validation expands an encoded batch
by at most a factor of two. This is a polynomial output allocation bound
for the validator, not a certificate of TM2 running time. -/
theorem validatesTautologyResult_delimited_batch_size_bound
    (inputs : List (List Bool)) :
    (inputs.map (fun π =>
      (validatesTautologyResult_on_pair π).length + 1)).sum
      ≤ 2 * ((inputs.map List.length).sum + inputs.length) := by
  have hdelimiters :
      (inputs.map (fun π =>
        (validatesTautologyResult_on_pair π).length + 1)).sum =
      (inputs.map (fun π =>
        (validatesTautologyResult_on_pair π).length)).sum +
        inputs.length := by
    induction inputs with
    | nil =>
        simp
    | cons π inputs ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
  have hallocation :=
    validatesTautologyResult_batch_additive_length_bound inputs
  rw [hdelimiters]
  omega

end ProofSystemFrontier

/- SATurday auto-apply 2026-09-10T01:11:27Z (rung r5-cook-reckhow-bridge). -/
namespace ProofSystemFrontier

/-- Quadratic costs charged to individual validation outputs fit within a
quadratic budget in the total input size and entry count. This supports
cost aggregation for the polynomial time obligation, but does not supply
the missing TM2 implementation or its running time proof. -/
theorem validatesTautologyResult_batch_quadratic_budget
    (inputs : List (List Bool)) :
    (inputs.map (fun π =>
      (validatesTautologyResult_on_pair π).length ^ 2)).sum
      ≤ ((inputs.map List.length).sum + inputs.length) ^ 2 := by
  induction inputs with
  | nil =>
      simp
  | cons π inputs ih =>
      have hπ :
          (validatesTautologyResult_on_pair π).length ≤ π.length + 1 :=
        validatesTautologyResult_on_pair_length_frontier π
      have hπsq :
          (validatesTautologyResult_on_pair π).length ^ 2
            ≤ (π.length + 1) ^ 2 := by
        nlinarith
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        (validatesTautologyResult_on_pair π).length ^ 2 +
            (inputs.map (fun ρ =>
              (validatesTautologyResult_on_pair ρ).length ^ 2)).sum
            ≤ (π.length + 1) ^ 2 +
                ((inputs.map List.length).sum + inputs.length) ^ 2 :=
          Nat.add_le_add hπsq ih
        _ ≤ (π.length + (inputs.map List.length).sum +
                (inputs.length + 1)) ^ 2 := by
          nlinarith [Nat.zero_le
            ((π.length + 1) *
              ((inputs.map List.length).sum + inputs.length))]

end ProofSystemFrontier

/- SATurday auto-apply 2026-09-10T01:14:21Z (rung r5-cook-reckhow-bridge). -/
namespace ProofSystemFrontier

/-- Quadratic charges for scanning both the input and validation output,
including one delimiter, admit a uniform quadratic batch budget.
This is size accounting for the polynomial time obligation, not a
machine implementation or a running time witness. -/
theorem validatesTautologyResult_batch_joint_scan_budget
    (inputs : List (List Bool)) :
    (inputs.map (fun π =>
      (π.length +
        (validatesTautologyResult_on_pair π).length + 1) ^ 2)).sum
      ≤ 4 * ((inputs.map List.length).sum + inputs.length) ^ 2 := by
  induction inputs with
  | nil =>
      simp
  | cons π inputs ih =>
      have hout :=
        validatesTautologyResult_on_pair_length_frontier π
      have hlocal :
          π.length +
              (validatesTautologyResult_on_pair π).length + 1
            ≤ 2 * (π.length + 1) := by
        omega
      have hlocal_sq :
          (π.length +
              (validatesTautologyResult_on_pair π).length + 1) ^ 2
            ≤ 4 * (π.length + 1) ^ 2 := by
        have hmul := Nat.mul_le_mul hlocal hlocal
        nlinarith only [hmul]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        (π.length +
              (validatesTautologyResult_on_pair π).length + 1) ^ 2 +
            (inputs.map (fun ρ =>
              (ρ.length +
                (validatesTautologyResult_on_pair ρ).length + 1) ^ 2)).sum
            ≤ 4 * (π.length + 1) ^ 2 +
                4 * ((inputs.map List.length).sum + inputs.length) ^ 2 :=
          Nat.add_le_add hlocal_sq ih
        _ ≤ 4 * (π.length + (inputs.map List.length).sum +
                (inputs.length + 1)) ^ 2 := by
          nlinarith [Nat.zero_le
            ((π.length + 1) *
              ((inputs.map List.length).sum + inputs.length))]

end ProofSystemFrontier

/- SATurday auto-apply 2026-09-10T01:22:51Z (rung r5-cook-reckhow-bridge). -/
namespace ProofSystemFrontier

/-- Packages the batch scan budget and linear overhead into a polynomial.
This is resource accounting for the computability obligation, not a
machine implementation or a bound on machine execution steps. -/
theorem validatesTautologyResult_batch_scan_overhead_poly_bound
    (inputs : List (List Bool)) :
    (inputs.map (fun π =>
      (π.length +
        (validatesTautologyResult_on_pair π).length + 1) ^ 2)).sum +
        (inputs.map List.length).sum + inputs.length
      ≤ (Polynomial.C 5 * (Polynomial.X + Polynomial.C 1) ^ 2 :
          Polynomial ℕ).eval
            ((inputs.map List.length).sum + inputs.length) := by
  have arithmetic_bound (charge n : ℕ)
      (h : charge ≤ 4 * n ^ 2) :
      charge + n ≤ 5 * (n + 1) ^ 2 := by
    nlinarith only [h, Nat.zero_le (n ^ 2)]
  have h := arithmetic_bound
    ((inputs.map (fun π =>
      (π.length +
        (validatesTautologyResult_on_pair π).length + 1) ^ 2)).sum)
    ((inputs.map List.length).sum + inputs.length)
    (validatesTautologyResult_batch_joint_scan_budget inputs)
  simpa only [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Nat.add_assoc] using h

end ProofSystemFrontier

/- SATurday auto-apply 2026-09-10T01:26:06Z (rung r5-cook-reckhow-bridge). -/
namespace ProofSystemFrontier

/-- Lifts a per input execution bound to a polynomial batch bound.
The execution bound remains a premise: this lemma does not construct
the machine required by the computability obligation. -/
theorem validatesTautologyResult_batch_execution_bound
    (steps : List Bool → ℕ) (c d : ℕ)
    (inputs : List (List Bool))
    (hsteps : ∀ π ∈ inputs,
      steps π ≤
        c * (π.length +
          (validatesTautologyResult_on_pair π).length + 1) ^ 2 +
        d * (π.length + 1)) :
    (inputs.map steps).sum ≤
      (Polynomial.C (4 * c + d) *
        (Polynomial.X + Polynomial.C 1) ^ 2 :
          Polynomial ℕ).eval
        ((inputs.map List.length).sum + inputs.length) := by
  have aggregate :
      ∀ xs : List (List Bool),
        (∀ π ∈ xs,
          steps π ≤
            c * (π.length +
              (validatesTautologyResult_on_pair π).length + 1) ^ 2 +
            d * (π.length + 1)) →
        (xs.map steps).sum ≤
          c * (xs.map (fun π =>
            (π.length +
              (validatesTautologyResult_on_pair π).length + 1) ^ 2)).sum +
          d * ((xs.map List.length).sum + xs.length) := by
    intro xs
    induction xs with
    | nil =>
        intro _
        simp
    | cons π xs ih =>
        intro hx
        have hp := hx π (by simp)
        have ht := ih (by
          intro x hmem
          exact hx x (List.mem_cons_of_mem π hmem))
        simp only [List.map_cons, List.sum_cons, List.length_cons,
          Nat.mul_add, Nat.mul_one] at hp ht ⊢
        omega
  let n := (inputs.map List.length).sum + inputs.length
  let charge := (inputs.map (fun π =>
    (π.length +
      (validatesTautologyResult_on_pair π).length + 1) ^ 2)).sum
  have haggregate :
      (inputs.map steps).sum ≤ c * charge + d * n := by
    exact aggregate inputs hsteps
  have hcharge : charge ≤ 4 * n ^ 2 := by
    exact validatesTautologyResult_batch_joint_scan_budget inputs
  have hn : n ≤ (n + 1) ^ 2 := by
    nlinarith
  have hn₂ : n ^ 2 ≤ (n + 1) ^ 2 := by
    nlinarith
  have hscaled :=
    Nat.mul_le_mul_left (4 * c) hn₂
  calc
    (inputs.map steps).sum ≤ c * charge + d * n := haggregate
    _ ≤ c * (4 * n ^ 2) + d * ((n + 1) ^ 2) :=
      Nat.add_le_add
        (Nat.mul_le_mul_left c hcharge)
        (Nat.mul_le_mul_left d hn)
    _ ≤ (4 * c + d) * (n + 1) ^ 2 := by
      nlinarith only [hscaled]
    _ = (Polynomial.C (4 * c + d) *
          (Polynomial.X + Polynomial.C 1) ^ 2 :
            Polynomial ℕ).eval
          ((inputs.map List.length).sum + inputs.length) := by
      simp only [Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
      rfl

end ProofSystemFrontier

/- SATurday auto-apply 2026-09-10T01:27:50Z (rung r5-cook-reckhow-bridge). -/
namespace ProofSystemFrontier

/-- Converts a uniform local execution estimate into a polynomial bound
in the input length alone. This supplies a candidate time polynomial for
the computability obligation, but still requires a machine realizing
the assumed execution estimate. -/
theorem validatesTautologyResult_uniform_polynomial_of_execution_bound
    (steps : List Bool → ℕ) (c d : ℕ)
    (hsteps : ∀ π : List Bool,
      steps π ≤
        c * (π.length +
          (validatesTautologyResult_on_pair π).length + 1) ^ 2 +
        d * (π.length + 1)) :
    ∃ time : Polynomial ℕ,
      ∀ π : List Bool, steps π ≤ time.eval π.length := by
  refine ⟨Polynomial.C (4 * c + d) *
    (Polynomial.X + Polynomial.C 2) ^ 2, ?_⟩
  intro π
  have hlocal :
      ∀ ρ ∈ [π],
        steps ρ ≤
          c * (ρ.length +
            (validatesTautologyResult_on_pair ρ).length + 1) ^ 2 +
          d * (ρ.length + 1) := by
    intro ρ _
    exact hsteps ρ
  have hbound :=
    validatesTautologyResult_batch_execution_bound
      steps c d [π] hlocal
  simpa [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Nat.add_assoc] using hbound

end ProofSystemFrontier

/- SATurday auto-apply 2026-09-10T01:34:09Z (rung r5-cook-reckhow-bridge). -/
namespace ProofSystemFrontier

/-- Polynomial bounds on total input length and batch cardinality give a
polynomial validation time bound, provided the local execution estimate. -/
theorem validatesTautologyResult_batch_time_of_size_and_count
    (steps : List Bool → ℕ)
    (batch : List Bool → List (List Bool))
    (c d : ℕ) (sizeBound countBound : Polynomial ℕ)
    (hsteps : ∀ ρ : List Bool,
      steps ρ ≤
        c * (ρ.length +
          (validatesTautologyResult_on_pair ρ).length + 1) ^ 2 +
        d * (ρ.length + 1))
    (hsize : ∀ π : List Bool,
      ((batch π).map List.length).sum ≤ sizeBound.eval π.length)
    (hcount : ∀ π : List Bool,
      (batch π).length ≤ countBound.eval π.length) :
    ∃ time : Polynomial ℕ,
      ∀ π : List Bool,
        ((batch π).map steps).sum ≤ time.eval π.length := by
  refine ⟨Polynomial.C (4 * c + d) *
    (sizeBound + countBound + Polynomial.C 1) ^ 2, ?_⟩
  intro π
  have hlocal :
      ∀ ρ ∈ batch π,
        steps ρ ≤
          c * (ρ.length +
            (validatesTautologyResult_on_pair ρ).length + 1) ^ 2 +
          d * (ρ.length + 1) := by
    intro ρ _
    exact hsteps ρ
  have hbatch :
      ((batch π).map steps).sum ≤
        (4 * c + d) *
          (((batch π).map List.length).sum +
            (batch π).length + 1) ^ 2 := by
    simpa [Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
      using validatesTautologyResult_batch_execution_bound
        steps c d (batch π) hlocal
  have hcharge :
      ((batch π).map List.length).sum + (batch π).length + 1 ≤
        sizeBound.eval π.length + countBound.eval π.length + 1 := by
    exact Nat.add_le_add_right
      (Nat.add_le_add (hsize π) (hcount π)) 1
  have hsquare :
      (((batch π).map List.length).sum + (batch π).length + 1) ^ 2 ≤
        (sizeBound.eval π.length + countBound.eval π.length + 1) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hcharge hcharge
  have htotal := hbatch.trans
    (Nat.mul_le_mul_left (4 * c + d) hsquare)
  simpa only [Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_C] using htotal

end ProofSystemFrontier

/- SATurday auto-apply 2026-09-10T01:35:00Z (rung r5-cook-reckhow-bridge). -/
namespace ProofSystemFrontier

/-- For batches without empty records, total input length also bounds
the number of validator calls. Thus a separate cardinality polynomial
is unnecessary for the conditional validation time estimate. -/
theorem validatesTautologyResult_batch_time_of_nonempty_records
    (steps : List Bool → ℕ)
    (batch : List Bool → List (List Bool))
    (c d : ℕ) (sizeBound : Polynomial ℕ)
    (hsteps : ∀ ρ : List Bool,
      steps ρ ≤
        c * (ρ.length +
          (validatesTautologyResult_on_pair ρ).length + 1) ^ 2 +
        d * (ρ.length + 1))
    (hsize : ∀ π : List Bool,
      ((batch π).map List.length).sum ≤ sizeBound.eval π.length)
    (hnonempty : ∀ π : List Bool, ∀ ρ ∈ batch π, ρ ≠ []) :
    ∃ time : Polynomial ℕ,
      ∀ π : List Bool,
        ((batch π).map steps).sum ≤ time.eval π.length := by
  have count_le_size :
      ∀ xs : List (List Bool),
        (∀ ρ ∈ xs, ρ ≠ []) →
          xs.length ≤ (xs.map List.length).sum := by
    intro xs
    induction xs with
    | nil =>
        intro _
        simp
    | cons ρ xs ih =>
        intro h
        have hρ : ρ ≠ [] := h ρ (by simp)
        have hpos : 1 ≤ ρ.length := by
          cases ρ with
          | nil => exact False.elim (hρ rfl)
          | cons b bs => simp
        have htail : xs.length ≤ (xs.map List.length).sum := by
          apply ih
          intro σ hσ
          exact h σ (List.mem_cons_of_mem ρ hσ)
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        omega
  have hcount : ∀ π : List Bool,
      (batch π).length ≤ sizeBound.eval π.length := by
    intro π
    exact (count_le_size (batch π) (hnonempty π)).trans (hsize π)
  exact validatesTautologyResult_batch_time_of_size_and_count
    steps batch c d sizeBound sizeBound hsteps hsize hcount

end ProofSystemFrontier

/- SATurday auto-apply 2026-09-10T01:36:27Z (rung r5-cook-reckhow-bridge). -/
namespace ProofSystemFrontier

/-- Charging one bit of overhead per record bounds both total payload
and the number of validator calls, even when some records are empty. -/
theorem validatesTautologyResult_batch_time_of_padded_size
    (steps : List Bool → ℕ)
    (batch : List Bool → List (List Bool))
    (c d : ℕ) (sizeBound : Polynomial ℕ)
    (hsteps : ∀ ρ : List Bool,
      steps ρ ≤
        c * (ρ.length +
          (validatesTautologyResult_on_pair ρ).length + 1) ^ 2 +
        d * (ρ.length + 1))
    (hpadded : ∀ π : List Bool,
      ((batch π).map (fun ρ => ρ.length + 1)).sum ≤
        sizeBound.eval π.length) :
    ∃ time : Polynomial ℕ,
      ∀ π : List Bool,
        ((batch π).map steps).sum ≤ time.eval π.length := by
  have padded_sum :
      ∀ xs : List (List Bool),
        (xs.map (fun ρ => ρ.length + 1)).sum =
          (xs.map List.length).sum + xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons ρ xs ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        omega
  have hsize : ∀ π : List Bool,
      ((batch π).map List.length).sum ≤ sizeBound.eval π.length := by
    intro π
    have h := hpadded π
    rw [padded_sum] at h
    omega
  have hcount : ∀ π : List Bool,
      (batch π).length ≤ sizeBound.eval π.length := by
    intro π
    have h := hpadded π
    rw [padded_sum] at h
    omega
  exact validatesTautologyResult_batch_time_of_size_and_count
    steps batch c d sizeBound sizeBound hsteps hsize hcount

end ProofSystemFrontier

/- SATurday auto-apply 2026-09-10T01:51:18Z (rung r5-cook-reckhow-bridge). -/
namespace ProofSystemFrontier

/-- Linear per record scheduling overhead can be included in the
polynomial clock for a padded batch of validator calls. -/
theorem validatesTautologyResult_batch_time_with_record_overhead
    (steps overhead : List Bool → ℕ)
    (batch : List Bool → List (List Bool))
    (c d k : ℕ) (sizeBound : Polynomial ℕ)
    (hsteps : ∀ ρ : List Bool,
      steps ρ ≤
        c * (ρ.length +
          (validatesTautologyResult_on_pair ρ).length + 1) ^ 2 +
        d * (ρ.length + 1))
    (hoverhead : ∀ ρ : List Bool,
      overhead ρ ≤ k * (ρ.length + 1))
    (hpadded : ∀ π : List Bool,
      ((batch π).map (fun ρ => ρ.length + 1)).sum ≤
        sizeBound.eval π.length) :
    ∃ time : Polynomial ℕ,
      ∀ π : List Bool,
        ((batch π).map (fun ρ => steps ρ + overhead ρ)).sum ≤
          time.eval π.length := by
  apply validatesTautologyResult_batch_time_of_padded_size
    (fun ρ => steps ρ + overhead ρ) batch c (d + k) sizeBound
  · intro ρ
    calc
      steps ρ + overhead ρ ≤
          (c * (ρ.length +
              (validatesTautologyResult_on_pair ρ).length + 1) ^ 2 +
            d * (ρ.length + 1)) +
          k * (ρ.length + 1) :=
        Nat.add_le_add (hsteps ρ) (hoverhead ρ)
      _ = c * (ρ.length +
              (validatesTautologyResult_on_pair ρ).length + 1) ^ 2 +
            (d + k) * (ρ.length + 1) := by
        ring
  · exact hpadded

end ProofSystemFrontier












end SATurday.Bridge
