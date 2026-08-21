import Theory.ProofComplexity.Bridge.Encoding
import Mathlib.Tactic

/-!
# Propositional formula encodings (Ladder Rung R5)

Inductive propositional formulas, bit string encode or decode, semantic
evaluation, and the language `TAUT` of encoded tautologies. First cluster
lands the datatype, a prefix encoding, evaluation, tautology of `p ∨ ¬p`,
concrete round trip for that seed, and non vacuity of `TAUT`.

General `decodeFormula_encodeFormula` for arbitrary formulas stays Frontier
(fuelled decoder correctness). Polynomial time machines stay for later.

LOG: R5 Bridge FormulaEncoding cluster 1 (formulas, TAUT nonvacuity)
-/

namespace SATurday.Bridge

/-! ## Formulas -/

/-- Propositional formulas over natural number variables. -/
inductive PropFormula : Type where
  | var : ℕ → PropFormula
  | not : PropFormula → PropFormula
  | and : PropFormula → PropFormula → PropFormula
  | or : PropFormula → PropFormula → PropFormula
deriving DecidableEq, Repr

/-- Semantic evaluation under a Boolean assignment to variables. -/
def PropFormula.eval (σ : ℕ → Bool) : PropFormula → Bool
  | var i => σ i
  | not φ => !(eval σ φ)
  | and φ ψ => eval σ φ && eval σ ψ
  | or φ ψ => eval σ φ || eval σ ψ

/-- A formula is a tautology when it evaluates to true under every assignment. -/
def PropFormula.Tautology (φ : PropFormula) : Prop :=
  ∀ σ : ℕ → Bool, φ.eval σ = true

/-- Classic non vacuity seed: `p ∨ ¬p` for variable `0`. -/
def tautSeed : PropFormula :=
  .or (.var 0) (.not (.var 0))

/-- `p ∨ ¬p` is a tautology. -/
theorem tautSeed_tautology : tautSeed.Tautology := by
  intro σ
  simp [tautSeed, PropFormula.eval, Bool.or_not_self]

/-! ## Prefix bit encoding

Tag bits:
- `false, false` then unary `true^n false` encodes `var n`
- `false, true` then payload encodes `not`
- `true, false` then left then right encodes `and`
- `true, true` then left then right encodes `or` -/

/-- Encode a natural as unary `true^n false`. -/
def encodeNat (n : ℕ) : List Bool :=
  List.replicate n true ++ [false]

/-- Decode unary `true^n false`, returning `(n, rest)`. -/
def decodeNat : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest =>
      match decodeNat rest with
      | some (n, rest') => some (n + 1, rest')
      | none => none

theorem decodeNat_encodeNat (n : ℕ) :
    decodeNat (encodeNat n) = some (n, []) := by
  induction n with
  | zero => simp [encodeNat, decodeNat]
  | succ n ih =>
      simp only [encodeNat, List.replicate_succ, List.cons_append]
      change decodeNat (true :: (List.replicate n true ++ [false])) =
        some (n + 1, [])
      have h : decodeNat (List.replicate n true ++ [false]) = some (n, []) := by
        simpa [encodeNat] using ih
      simp [decodeNat, h]

/-- Encode a formula as a bit string (prefix code). -/
def encodeFormula : PropFormula → List Bool
  | .var n => [false, false] ++ encodeNat n
  | .not φ => [false, true] ++ encodeFormula φ
  | .and φ ψ => [true, false] ++ encodeFormula φ ++ encodeFormula ψ
  | .or φ ψ => [true, true] ++ encodeFormula φ ++ encodeFormula ψ

/-- Fuel bounded prefix decode (well founded in the fuel argument). -/
def decodeFormulaPrefixFuel : ℕ → List Bool → Option (PropFormula × List Bool)
  | 0, _ => none
  | _fuel + 1, false :: false :: rest =>
      match decodeNat rest with
      | some (n, rest') => some (.var n, rest')
      | none => none
  | fuel + 1, false :: true :: rest =>
      match decodeFormulaPrefixFuel fuel rest with
      | some (φ, rest') => some (.not φ, rest')
      | none => none
  | fuel + 1, true :: false :: rest =>
      match decodeFormulaPrefixFuel fuel rest with
      | some (φ, rest₁) =>
          match decodeFormulaPrefixFuel fuel rest₁ with
          | some (ψ, rest₂) => some (.and φ ψ, rest₂)
          | none => none
      | none => none
  | fuel + 1, true :: true :: rest =>
      match decodeFormulaPrefixFuel fuel rest with
      | some (φ, rest₁) =>
          match decodeFormulaPrefixFuel fuel rest₁ with
          | some (ψ, rest₂) => some (.or φ ψ, rest₂)
          | none => none
      | none => none
  | _ + 1, _ => none

/-- Prefix decode with fuel `|bs| + 1`. -/
def decodeFormulaPrefix (bs : List Bool) : Option (PropFormula × List Bool) :=
  decodeFormulaPrefixFuel (bs.length + 1) bs

/-- Full decode: succeed only when the whole string is consumed. -/
def decodeFormula (bs : List Bool) : Option PropFormula :=
  match decodeFormulaPrefix bs with
  | some (φ, []) => some φ
  | _ => none

/-- Concrete encoding of the tautology seed (for decide friendly round trip). -/
theorem encodeFormula_tautSeed :
    encodeFormula tautSeed =
      [true, true, false, false, false, false, true, false, false, false] := by
  simp [tautSeed, encodeFormula, encodeNat]

/-- Concrete round trip for the tautology seed (kernel `decide`, not native). -/
theorem decodeFormula_encodeFormula_tautSeed :
    decodeFormula (encodeFormula tautSeed) = some tautSeed := by
  rw [encodeFormula_tautSeed]
  decide

/-! ## Language TAUT -/

/-- Encoded tautologies: bit strings that decode to a tautology. -/
def TAUT : Language := fun bs =>
  ∃ φ : PropFormula, decodeFormula bs = some φ ∧ φ.Tautology

/-- Non vacuity: the encoding of `p ∨ ¬p` is in `TAUT`. -/
theorem tautSeed_mem_TAUT : TAUT (encodeFormula tautSeed) := by
  refine ⟨tautSeed, decodeFormula_encodeFormula_tautSeed, tautSeed_tautology⟩

/-- `TAUT` is nonempty (statement hygiene for proof system pins). -/
theorem TAUT_nonempty : ∃ bs : List Bool, TAUT bs :=
  ⟨encodeFormula tautSeed, tautSeed_mem_TAUT⟩

namespace FormulaEncodingFrontier

/-- General round trip for arbitrary formulas (fuelled decoder correctness). -/
theorem decodeFormula_encodeFormula (φ : PropFormula) :
    decodeFormula (encodeFormula φ) = some φ := by
  sorry

/-- `encodeFormula` is injective once general round trip lands. -/
theorem encodeFormula_injective : Function.Injective encodeFormula := by
  sorry

end FormulaEncodingFrontier

end SATurday.Bridge
