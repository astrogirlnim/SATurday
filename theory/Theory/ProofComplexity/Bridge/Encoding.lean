import Mathlib.Computability.Encoding
import Mathlib.Tactic

/-!
# Cook Reckhow bridge encodings (Ladder Rung R5)

Bit string alphabet and pairing used by `InP` / `InNP` over mathlib's
`Turing.TM2ComputableInPolyTime`. Languages are predicates on `List Bool`.

The pairing is self delimiting: each bit of the first component is packed as
`true :: b :: ...`, then a lone `false` separator, then the second component
verbatim. This keeps the alphabet as `Bool` (unlike mathlib's `finEncodingPair`,
which uses `Sum`).

LOG: R5 Bridge Encoding module (pairing and bit encodings)
-/

namespace SATurday.Bridge

/-- A language over bit strings. -/
abbrev Language := List Bool → Prop

/-- Identity encoding on bit strings (input side of `InP`). -/
abbrev idBitEnc : List Bool → List Bool := id

/-- Single bit encoding (output side of characteristic functions). Matches
`Computability.encodeBool`. -/
abbrev bitEnc : Bool → List Bool := fun b => [b]

/-- Mathlib's `encodeBool` agrees with `bitEnc`. -/
theorem bitEnc_eq_encodeBool : bitEnc = Computability.encodeBool := rfl

/-- Self delimiting pairing of two bit strings into one bit string.
Length identity: `|encodePair (x, w)| = 2 * |x| + 1 + |w|`. -/
def encodePair (p : List Bool × List Bool) : List Bool :=
  (p.1.flatMap fun b => [true, b]) ++ false :: p.2

/-- Inverse of `encodePair` (partial). -/
def decodePair : List Bool → Option (List Bool × List Bool)
  | [] => none
  | false :: rest => some ([], rest)
  | true :: b :: rest =>
      match decodePair rest with
      | some (x, w) => some (b :: x, w)
      | none => none
  | [true] => none

/-- Decoding recovers the paired inputs. -/
theorem decodePair_encodePair (p : List Bool × List Bool) :
    decodePair (encodePair p) = some p := by
  rcases p with ⟨x, w⟩
  induction x with
  | nil =>
      rfl
  | cons b x ih =>
      -- encodePair (b::x, w) = true :: b :: encodePair (x, w)
      change decodePair (true :: b :: encodePair (x, w)) = some (b :: x, w)
      simp only [decodePair, ih]

/-- `encodePair` is injective. -/
theorem encodePair_injective : Function.Injective encodePair := by
  intro p q h
  have hp := decodePair_encodePair p
  have hq := decodePair_encodePair q
  rw [h] at hp
  exact Option.some_injective _ (hp.symm.trans hq)

/-- Length of a paired encoding. -/
theorem length_encodePair (p : List Bool × List Bool) :
    (encodePair p).length = 2 * p.1.length + 1 + p.2.length := by
  rcases p with ⟨x, w⟩
  induction x with
  | nil =>
      simp [encodePair]; omega
  | cons b x ih =>
      -- |true :: b :: encodePair (x,w)| = 2 + |encodePair (x,w)|
      change (true :: b :: encodePair (x, w)).length =
        2 * (b :: x).length + 1 + w.length
      simp [ih]; omega

/-- Separator bit is always present, so the encoding is never empty. -/
theorem encodePair_ne_nil (p : List Bool × List Bool) : encodePair p ≠ [] := by
  intro h
  have := congrArg List.length h
  simp [length_encodePair] at this

/-- Length of `bitEnc`. -/
@[simp] theorem length_bitEnc (b : Bool) : (bitEnc b).length = 1 := rfl

/-- `bitEnc` is injective. -/
theorem bitEnc_injective : Function.Injective bitEnc := by
  intro a b h
  simpa [bitEnc] using congrArg List.head! h

end SATurday.Bridge
