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
      change (true :: b :: encodePair (x, w)).length =
        2 * (b :: x).length + 1 + w.length
      simp [ih]; omega

/-- Successful pair decode implies the second component fits in the string. -/
theorem length_ge_snd_of_decodePair {π x w : List Bool}
    (h : decodePair π = some (x, w)) : w.length ≤ π.length := by
  induction x generalizing π with
  | nil =>
      cases π with
      | nil => simp [decodePair] at h
      | cons a rest =>
          cases a
          · simp only [decodePair, Option.some.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            simp
          · cases rest with
            | nil => simp [decodePair] at h
            | cons b rest' =>
                simp only [decodePair] at h
                cases hrest : decodePair rest' with
                | none => simp [hrest] at h
                | some qw => simp [hrest] at h
  | cons b x ih =>
      cases π with
      | nil => simp [decodePair] at h
      | cons a rest =>
          cases a
          · simp only [decodePair, Option.some.injEq, Prod.mk.injEq] at h
            exact (List.cons_ne_nil _ _ h.1.symm).elim
          · cases rest with
            | nil => simp [decodePair] at h
            | cons c rest' =>
                simp only [decodePair] at h
                cases hrest : decodePair rest' with
                | none => simp [hrest] at h
                | some qw =>
                    simp only [hrest, Option.some.injEq, Prod.mk.injEq] at h
                    rcases qw with ⟨x', w'⟩
                    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
                    exact (ih hrest).trans (by simp; omega)

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

/-! ## DecodePair complexity certificate (TM2 cluster A) -/

/-- Bit examinations performed by `decodePair` (one per recursive call). -/
def decodePairCost : List Bool → ℕ
  | [] => 1
  | false :: _ => 1
  | true :: _ :: rest => decodePairCost rest + 1
  | [true] => 1

/-- Cost is linear in the input length. -/
theorem decodePairCost_le (π : List Bool) : decodePairCost π ≤ π.length + 1 := by
  match π with
  | [] => simp [decodePairCost]
  | false :: rest => simp [decodePairCost]
  | [true] => simp [decodePairCost]
  | true :: b :: rest =>
      have ih : decodePairCost rest ≤ rest.length + 1 := decodePairCost_le rest
      have hlen : (true :: b :: rest).length = rest.length + 2 := by simp
      -- cost = cost rest + 1 ≤ rest.length + 2 = |π|
      calc
        decodePairCost (true :: b :: rest) = decodePairCost rest + 1 := rfl
        _ ≤ (rest.length + 1) + 1 := by omega
        _ = rest.length + 2 := by ring
        _ = (true :: b :: rest).length := by simp
        _ ≤ (true :: b :: rest).length + 1 := by omega

/-- Tape encoding of an optional pair: `[true]` for none, else `false` then
`encodePair`. -/
def encodeDecodePairResult : Option (List Bool × List Bool) → List Bool
  | none => [true]
  | some p => false :: encodePair p

/-- Successful decode of the option encoding. -/
def decodeDecodePairResult : List Bool → Option (Option (List Bool × List Bool))
  | true :: [] => some none
  | false :: rest =>
      match decodePair rest with
      | some p => some (some p)
      | none => none
  | _ => none

theorem decodeDecodePairResult_encode (r : Option (List Bool × List Bool)) :
    decodeDecodePairResult (encodeDecodePairResult r) = some r := by
  cases r with
  | none => rfl
  | some p =>
      simp [encodeDecodePairResult, decodeDecodePairResult, decodePair_encodePair]

/-- Pure function the eventual FinTM2 must realize: decode then reencode. -/
def decodePairResult (π : List Bool) : List Bool :=
  encodeDecodePairResult (decodePair π)

/-- First component of a successful decode is no longer than the input. -/
theorem length_fst_le_of_decodePair {π x w : List Bool}
    (h : decodePair π = some (x, w)) : x.length ≤ π.length := by
  induction x generalizing π with
  | nil => simp
  | cons b x ih =>
      cases π with
      | nil => simp [decodePair] at h
      | cons a rest =>
          cases a
          · simp only [decodePair, Option.some.injEq, Prod.mk.injEq] at h
            exact (List.cons_ne_nil _ _ h.1.symm).elim
          · cases rest with
            | nil => simp [decodePair] at h
            | cons c rest' =>
                simp only [decodePair] at h
                cases hrest : decodePair rest' with
                | none => simp [hrest] at h
                | some qw =>
                    simp only [hrest, Option.some.injEq, Prod.mk.injEq] at h
                    rcases qw with ⟨x', w'⟩
                    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
                    have := ih hrest
                    simp at this ⊢
                    omega

/-- Successful decode recovers the canonical `encodePair` encoding. -/
theorem encodePair_of_decodePair {π : List Bool} {x w : List Bool}
    (h : decodePair π = some (x, w)) : encodePair (x, w) = π := by
  suffices ∀ n π x w, π.length = n → decodePair π = some (x, w) →
      encodePair (x, w) = π by
    exact this _ _ _ _ rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ihn =>
      intro π x w hlen hdec
      match π with
      | [] => simp [decodePair] at hdec
      | a :: rest =>
          cases a with
          | false =>
              simp only [decodePair, Option.some.injEq, Prod.mk.injEq] at hdec
              rcases hdec with ⟨rfl, rfl⟩
              rfl
          | true =>
              match rest with
              | [] => simp [decodePair] at hdec
              | b :: rest' =>
                  simp only [decodePair] at hdec
                  cases hrest : decodePair rest' with
                  | none => simp [hrest] at hdec
                  | some pw =>
                      rcases pw with ⟨x', w'⟩
                      simp only [hrest, Option.some.injEq, Prod.mk.injEq] at hdec
                      rcases hdec with ⟨rfl, rfl⟩
                      have hlt : rest'.length < n := by
                        have : n = (true :: b :: rest').length := hlen.symm
                        simp at this
                        omega
                      have hx' : encodePair (x', w') = rest' :=
                        ihn rest'.length hlt rest' x' w' rfl hrest
                      -- encodePair (b :: x', w') = true :: b :: encodePair (x', w')
                      change true :: b :: encodePair (x', w') = true :: b :: rest'
                      rw [hx']

/-- On successful decode, `decodePairResult` prefixes `false` to the input. -/
theorem decodePairResult_of_some {π x w : List Bool}
    (h : decodePair π = some (x, w)) :
    decodePairResult π = false :: π := by
  have henc := encodePair_of_decodePair h
  simp [decodePairResult, encodeDecodePairResult, h, henc]

/-- On failed decode, `decodePairResult` is the singleton `[true]`. -/
theorem decodePairResult_of_none {π : List Bool} (h : decodePair π = none) :
    decodePairResult π = [true] := by
  simp [decodePairResult, encodeDecodePairResult, h]

/-- Case split form used by the branching FinTM2: success copies with a leading
`false`, failure emits `[true]`. -/
theorem decodePairResult_eq (π : List Bool) :
    decodePairResult π =
      match decodePair π with
      | some _ => false :: π
      | none => [true] := by
  cases h : decodePair π with
  | none => simp [decodePairResult, encodeDecodePairResult, h]
  | some pw =>
      have henc := encodePair_of_decodePair h
      simp [decodePairResult, encodeDecodePairResult, h, henc]

/-- Successful decode iff the tape is exactly some `encodePair` image. -/
theorem decodePair_isSome_iff (π : List Bool) :
    (decodePair π).isSome ↔ ∃ p, encodePair p = π := by
  constructor
  · intro h
    cases hπ : decodePair π with
    | none => simp [hπ] at h
    | some p => exact ⟨p, encodePair_of_decodePair hπ⟩
  · intro ⟨p, hp⟩
    subst hp
    simp [decodePair_encodePair]

/-- On well formed pairs, `decodePairResult` is `false` then the encoding. -/
theorem decodePairResult_encodePair (p : List Bool × List Bool) :
    decodePairResult (encodePair p) = false :: encodePair p := by
  simp [decodePairResult, encodeDecodePairResult, decodePair_encodePair]

/-- Output length of `decodePairResult` is O(|π|). -/
theorem length_decodePairResult_le (π : List Bool) :
    (decodePairResult π).length ≤ 3 * π.length + 2 := by
  simp only [decodePairResult, encodeDecodePairResult]
  cases h : decodePair π with
  | none =>
      change ([true] : List Bool).length ≤ 3 * π.length + 2
      simp
  | some pw =>
      rcases pw with ⟨x, w⟩
      have hx := length_fst_le_of_decodePair h
      have hw := length_ge_snd_of_decodePair h
      simp only [length_encodePair, List.length_cons]
      omega

end SATurday.Bridge
