import Theory.ProofComplexity.Bridge.Encoding
import Mathlib.Tactic

/-!
# Propositional formula encodings (Ladder Rung R5)

Inductive propositional formulas, bit string encode or decode, semantic
evaluation, and the language `TAUT` of encoded tautologies.

Cluster 1: datatype, seed tautology, `TAUT` nonvacuity.
Cluster 2 (2026-08-21): general fuelled decode round trip and injectivity.

Polynomial time encode or decode machines stay for later clusters.

LOG: R5 Bridge FormulaEncoding cluster 2 (general round trip)
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

/-! ## Prefix bit encoding -/

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

theorem decodeNat_encodeNat_append (n : ℕ) (suffix : List Bool) :
    decodeNat (encodeNat n ++ suffix) = some (n, suffix) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hform :
          encodeNat (n + 1) ++ suffix = true :: (encodeNat n ++ suffix) := by
        simp [encodeNat, List.replicate_succ]
      rw [hform, decodeNat, ih]

theorem decodeNat_encodeNat (n : ℕ) :
    decodeNat (encodeNat n) = some (n, []) := by
  simpa using decodeNat_encodeNat_append n []

/-- Encode a formula as a bit string (prefix code). -/
def encodeFormula : PropFormula → List Bool
  | .var n => [false, false] ++ encodeNat n
  | .not φ => [false, true] ++ encodeFormula φ
  | .and φ ψ => [true, false] ++ encodeFormula φ ++ encodeFormula ψ
  | .or φ ψ => [true, true] ++ encodeFormula φ ++ encodeFormula ψ

theorem length_encodeFormula_not (φ : PropFormula) :
    (encodeFormula (.not φ)).length = (encodeFormula φ).length + 2 := by
  simp [encodeFormula]

theorem length_encodeFormula_and (φ ψ : PropFormula) :
    (encodeFormula (.and φ ψ)).length =
      (encodeFormula φ).length + (encodeFormula ψ).length + 2 := by
  simp [encodeFormula]

theorem length_encodeFormula_or (φ ψ : PropFormula) :
    (encodeFormula (.or φ ψ)).length =
      (encodeFormula φ).length + (encodeFormula ψ).length + 2 := by
  simp [encodeFormula]

theorem encodeFormula_length_pos (φ : PropFormula) :
    0 < (encodeFormula φ).length := by
  induction φ with
  | var n => simp [encodeFormula, encodeNat]
  | not φ ih => rw [length_encodeFormula_not]; omega
  | and φ ψ ihφ ihψ => rw [length_encodeFormula_and]; omega
  | or φ ψ ihφ ihψ => rw [length_encodeFormula_or]; omega

/-- Fuel bounded prefix decode. -/
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

/-- Strong round trip: decode recovers `φ` and leaves the unread suffix. -/
theorem decodeFormulaPrefixFuel_encodeFormula_append (φ : PropFormula) :
    ∀ (fuel : ℕ) (suffix : List Bool),
      (encodeFormula φ).length ≤ fuel →
        decodeFormulaPrefixFuel (fuel + 1) (encodeFormula φ ++ suffix) =
          some (φ, suffix) := by
  induction φ with
  | var n =>
      intro fuel suffix hfuel
      cases fuel with
      | zero =>
          exact (Nat.not_lt_zero _ (lt_of_lt_of_le
            (encodeFormula_length_pos (.var n)) hfuel)).elim
      | succ f =>
          have hbits :
              encodeFormula (.var n) ++ suffix =
                false :: false :: (encodeNat n ++ suffix) := by
            simp [encodeFormula]
          rw [hbits, decodeFormulaPrefixFuel, decodeNat_encodeNat_append]
  | not φ ih =>
      intro fuel suffix hfuel
      cases fuel with
      | zero =>
          exact (Nat.not_lt_zero _ (lt_of_lt_of_le
            (encodeFormula_length_pos (.not φ)) hfuel)).elim
      | succ f =>
          have hlen : (encodeFormula φ).length ≤ f := by
            rw [length_encodeFormula_not] at hfuel
            omega
          have ih' := ih f suffix hlen
          have hbits :
              encodeFormula (.not φ) ++ suffix =
                false :: true :: (encodeFormula φ ++ suffix) := by
            simp [encodeFormula]
          rw [hbits, decodeFormulaPrefixFuel, ih']
  | and φ ψ ihφ ihψ =>
      intro fuel suffix hfuel
      cases fuel with
      | zero =>
          exact (Nat.not_lt_zero _ (lt_of_lt_of_le
            (encodeFormula_length_pos (.and φ ψ)) hfuel)).elim
      | succ f =>
          have hφ : (encodeFormula φ).length ≤ f := by
            rw [length_encodeFormula_and] at hfuel
            omega
          have hψ : (encodeFormula ψ).length ≤ f := by
            rw [length_encodeFormula_and] at hfuel
            omega
          have ihφ' := ihφ f (encodeFormula ψ ++ suffix) hφ
          have ihψ' := ihψ f suffix hψ
          have hbits :
              encodeFormula (.and φ ψ) ++ suffix =
                true :: false ::
                  (encodeFormula φ ++ (encodeFormula ψ ++ suffix)) := by
            simp [encodeFormula, List.append_assoc]
          rw [hbits, decodeFormulaPrefixFuel, ihφ']
          simp [ihψ']
  | or φ ψ ihφ ihψ =>
      intro fuel suffix hfuel
      cases fuel with
      | zero =>
          exact (Nat.not_lt_zero _ (lt_of_lt_of_le
            (encodeFormula_length_pos (.or φ ψ)) hfuel)).elim
      | succ f =>
          have hφ : (encodeFormula φ).length ≤ f := by
            rw [length_encodeFormula_or] at hfuel
            omega
          have hψ : (encodeFormula ψ).length ≤ f := by
            rw [length_encodeFormula_or] at hfuel
            omega
          have ihφ' := ihφ f (encodeFormula ψ ++ suffix) hφ
          have ihψ' := ihψ f suffix hψ
          have hbits :
              encodeFormula (.or φ ψ) ++ suffix =
                true :: true ::
                  (encodeFormula φ ++ (encodeFormula ψ ++ suffix)) := by
            simp [encodeFormula, List.append_assoc]
          rw [hbits, decodeFormulaPrefixFuel, ihφ']
          simp [ihψ']

/-- Prefix decode with fuel `|bs| + 1`. -/
def decodeFormulaPrefix (bs : List Bool) : Option (PropFormula × List Bool) :=
  decodeFormulaPrefixFuel (bs.length + 1) bs

/-- Full decode: succeed only when the whole string is consumed. -/
def decodeFormula (bs : List Bool) : Option PropFormula :=
  match decodeFormulaPrefix bs with
  | some (φ, []) => some φ
  | _ => none

/-- General round trip for `encodeFormula`. -/
theorem decodeFormula_encodeFormula (φ : PropFormula) :
    decodeFormula (encodeFormula φ) = some φ := by
  unfold decodeFormula decodeFormulaPrefix
  have h :=
    decodeFormulaPrefixFuel_encodeFormula_append φ (encodeFormula φ).length []
      (le_rfl)
  rw [List.append_nil] at h
  simp only [h]

/-- Concrete encoding of the tautology seed. -/
theorem encodeFormula_tautSeed :
    encodeFormula tautSeed =
      [true, true, false, false, false, false, true, false, false, false] := by
  simp [tautSeed, encodeFormula, encodeNat]

/-- Seed round trip (special case of the general theorem). -/
theorem decodeFormula_encodeFormula_tautSeed :
    decodeFormula (encodeFormula tautSeed) = some tautSeed :=
  decodeFormula_encodeFormula tautSeed

/-- `encodeFormula` is injective. -/
theorem encodeFormula_injective : Function.Injective encodeFormula := by
  intro φ ψ h
  have hφ := decodeFormula_encodeFormula φ
  have hψ := decodeFormula_encodeFormula ψ
  rw [h] at hφ
  exact Option.some_injective _ (hφ.symm.trans hψ)

/-! ## Language TAUT -/

/-- Encoded tautologies: bit strings that decode to a tautology. -/
def TAUT : Language := fun bs =>
  ∃ φ : PropFormula, decodeFormula bs = some φ ∧ φ.Tautology

/-- Non vacuity: the encoding of `p ∨ ¬p` is in `TAUT`. -/
theorem tautSeed_mem_TAUT : TAUT (encodeFormula tautSeed) := by
  refine ⟨tautSeed, decodeFormula_encodeFormula tautSeed, tautSeed_tautology⟩

/-- `TAUT` is nonempty (statement hygiene for proof system pins). -/
theorem TAUT_nonempty : ∃ bs : List Bool, TAUT bs :=
  ⟨encodeFormula tautSeed, tautSeed_mem_TAUT⟩

end SATurday.Bridge
