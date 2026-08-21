import Theory.ProofComplexity.Bridge.FormulaEncoding
import Theory.ProofComplexity.Bridge.Complexity
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

/-- Cluster A complete: `decodePairResult` is poly time via the branching FinTM2. -/
theorem decodePairResult_computableInPolyTime :
    Nonempty (TM2ComputableInPolyTime idBitEnc idBitEnc decodePairResult) :=
  ⟨decodePairResultComputableInPolyTime⟩

end SATurday.Bridge
