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

/-- `decodeNat` fails iff the tape is a (possibly empty) block of only `true`. -/
theorem decodeNat_eq_none_iff (bs : List Bool) :
    decodeNat bs = none ↔ ∀ b ∈ bs, b = true := by
  induction bs with
  | nil => simp [decodeNat]
  | cons b rest ih =>
      cases b with
      | false =>
          constructor
          · intro h; simp [decodeNat] at h
          · intro h
            have hf : false = true := h false (List.Mem.head (a := false) (as := rest))
            cases hf
      | true =>
          constructor
          · intro h b hb
            cases hb with
            | head => rfl
            | tail _ hmem =>
                cases hrest : decodeNat rest with
                | none => exact (ih.mp hrest) b hmem
                | some _ => simp [decodeNat, hrest] at h
          · intro h
            simp only [decodeNat]
            have hrest : decodeNat rest = none :=
              ih.mpr fun b hb => h b (List.Mem.tail (a := b) (b := true) hb)
            simp [hrest]

/-- Successful `decodeNat` recovers the unary encoding as a prefix. -/
theorem encodeNat_append_of_decodeNat {bs : List Bool} {n : ℕ} {rest : List Bool}
    (h : decodeNat bs = some (n, rest)) : bs = encodeNat n ++ rest := by
  induction bs generalizing n rest with
  | nil => simp [decodeNat] at h
  | cons b bs ih =>
      cases b with
      | false =>
          simp only [decodeNat, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | true =>
          simp only [decodeNat] at h
          cases hrest : decodeNat bs with
          | none => simp [hrest] at h
          | some nr =>
              rcases nr with ⟨n', rest'⟩
              simp only [hrest, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              have := ih hrest
              -- encodeNat (n' + 1) ++ rest' = true :: (encodeNat n' ++ rest')
              simp [encodeNat, List.replicate_succ, this]

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

/-- `decodeFormula` fails by prefix failure or by a nonempty unread suffix. -/
theorem decodeFormula_eq_none_iff {bs : List Bool} :
    decodeFormula bs = none ↔
      let pref := decodeFormulaPrefixFuel (bs.length + 1) bs
      pref = none ∨ ∃ φ rest, pref = some (φ, rest) ∧ rest ≠ [] := by
  constructor
  · intro h
    unfold decodeFormula decodeFormulaPrefix at h
    dsimp
    cases hpref : decodeFormulaPrefixFuel (bs.length + 1) bs with
    | none => exact Or.inl rfl
    | some pr =>
        rcases pr with ⟨φ, rest⟩
        simp only [hpref] at h
        -- After `cases hpref`, `pref` reduces to `some (φ, rest)`, so the equality is `rfl`.
        refine Or.inr ⟨φ, rest, And.intro rfl ?_⟩
        intro hnil
        subst hnil
        simp at h
  · intro h
    unfold decodeFormula decodeFormulaPrefix
    dsimp at h
    cases h with
    | inl hnone => simp [hnone]
    | inr hex =>
        rcases hex with ⟨φ, rest, hpref, hne⟩
        simp only [hpref]
        cases rest with
        | nil => exact (hne rfl).elim
        | cons _ _ => simp

/-- Successful fuelled prefix decode recovers `encodeFormula φ` as a prefix. -/
theorem encodeFormula_append_of_decodeFormulaPrefixFuel
    (fuel : ℕ) {bs : List Bool} {φ : PropFormula} {rest : List Bool}
    (h : decodeFormulaPrefixFuel fuel bs = some (φ, rest)) :
    bs = encodeFormula φ ++ rest := by
  induction fuel generalizing bs φ rest with
  | zero => simp [decodeFormulaPrefixFuel] at h
  | succ f ih =>
      cases bs with
      | nil => simp [decodeFormulaPrefixFuel] at h
      | cons b₁ bs₁ =>
          cases bs₁ with
          | nil => simp [decodeFormulaPrefixFuel] at h
          | cons b₂ rest0 =>
              cases b₁ with
              | false =>
                  cases b₂ with
                  | false =>
                      -- tag `false false`: variable
                      simp only [decodeFormulaPrefixFuel] at h
                      cases hn : decodeNat rest0 with
                      | none => simp [hn] at h
                      | some nr =>
                          rcases nr with ⟨n, rest'⟩
                          simp only [hn, Option.some.injEq, Prod.mk.injEq] at h
                          rcases h with ⟨rfl, rfl⟩
                          have hnat := encodeNat_append_of_decodeNat hn
                          simp [encodeFormula, hnat]
                  | true =>
                      -- tag `false true`: negation
                      simp only [decodeFormulaPrefixFuel] at h
                      cases hφ : decodeFormulaPrefixFuel f rest0 with
                      | none => simp [hφ] at h
                      | some pr =>
                          rcases pr with ⟨ψ, rest'⟩
                          simp only [hφ, Option.some.injEq, Prod.mk.injEq] at h
                          rcases h with ⟨rfl, rfl⟩
                          have := ih hφ
                          simp [encodeFormula, this]
              | true =>
                  cases b₂ with
                  | false =>
                      -- tag `true false`: conjunction
                      simp only [decodeFormulaPrefixFuel] at h
                      cases hφ : decodeFormulaPrefixFuel f rest0 with
                      | none => simp [hφ] at h
                      | some pr =>
                          rcases pr with ⟨ψ, rest₁⟩
                          simp only [hφ] at h
                          cases hψ : decodeFormulaPrefixFuel f rest₁ with
                          | none => simp [hψ] at h
                          | some qr =>
                              rcases qr with ⟨χ, rest₂⟩
                              simp only [hψ, Option.some.injEq, Prod.mk.injEq]
                                at h
                              rcases h with ⟨rfl, rfl⟩
                              have hψenc := ih hφ
                              have hχenc := ih hψ
                              simp [encodeFormula, List.append_assoc, hψenc,
                                hχenc]
                  | true =>
                      -- tag `true true`: disjunction
                      simp only [decodeFormulaPrefixFuel] at h
                      cases hφ : decodeFormulaPrefixFuel f rest0 with
                      | none => simp [hφ] at h
                      | some pr =>
                          rcases pr with ⟨ψ, rest₁⟩
                          simp only [hφ] at h
                          cases hψ : decodeFormulaPrefixFuel f rest₁ with
                          | none => simp [hψ] at h
                          | some qr =>
                              rcases qr with ⟨χ, rest₂⟩
                              simp only [hψ, Option.some.injEq, Prod.mk.injEq]
                                at h
                              rcases h with ⟨rfl, rfl⟩
                              have hψenc := ih hφ
                              have hχenc := ih hψ
                              simp [encodeFormula, List.append_assoc, hψenc,
                                hχenc]

/-- Successful full decode recovers the canonical `encodeFormula` encoding. -/
theorem encodeFormula_of_decodeFormula {bs : List Bool} {φ : PropFormula}
    (h : decodeFormula bs = some φ) : encodeFormula φ = bs := by
  unfold decodeFormula decodeFormulaPrefix at h
  cases hpref : decodeFormulaPrefixFuel (bs.length + 1) bs with
  | none => simp [hpref] at h
  | some pr =>
      rcases pr with ⟨ψ, rest⟩
      simp only [hpref] at h
      cases rest with
      | cons _ _ => simp at h
      | nil =>
          simp only [Option.some.injEq] at h
          subst h
          have henc :=
            encodeFormula_append_of_decodeFormulaPrefixFuel _ hpref
          simpa using henc.symm

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

/-! ## DecodeFormula complexity certificate (TM2 cluster B prep) -/

/-- Tape encoding of an optional formula: `[true]` for none, else `false` then
`encodeFormula`. -/
def encodeDecodeFormulaResult : Option PropFormula → List Bool
  | none => [true]
  | some φ => false :: encodeFormula φ

/-- Successful decode of the option encoding. -/
def decodeDecodeFormulaResult : List Bool → Option (Option PropFormula)
  | true :: [] => some none
  | false :: rest =>
      match decodeFormula rest with
      | some φ => some (some φ)
      | none => none
  | _ => none

theorem decodeDecodeFormulaResult_encode (r : Option PropFormula) :
    decodeDecodeFormulaResult (encodeDecodeFormulaResult r) = some r := by
  cases r with
  | none => rfl
  | some φ =>
      simp [encodeDecodeFormulaResult, decodeDecodeFormulaResult,
        decodeFormula_encodeFormula]

/-- Pure function the eventual FinTM2 must realize: decode then reencode. -/
def decodeFormulaResult (bs : List Bool) : List Bool :=
  encodeDecodeFormulaResult (decodeFormula bs)

/-- On well formed encodings, `decodeFormulaResult` is `false` then the encoding. -/
theorem decodeFormulaResult_encodeFormula (φ : PropFormula) :
    decodeFormulaResult (encodeFormula φ) = false :: encodeFormula φ := by
  simp [decodeFormulaResult, encodeDecodeFormulaResult, decodeFormula_encodeFormula]

/-- On successful decode, `decodeFormulaResult` prefixes `false` to the input. -/
theorem decodeFormulaResult_of_some {bs : List Bool} {φ : PropFormula}
    (h : decodeFormula bs = some φ) :
    decodeFormulaResult bs = false :: bs := by
  have henc := encodeFormula_of_decodeFormula h
  simp [decodeFormulaResult, encodeDecodeFormulaResult, h, henc]

/-- On failed decode, `decodeFormulaResult` is the singleton `[true]`. -/
theorem decodeFormulaResult_of_none {bs : List Bool} (h : decodeFormula bs = none) :
    decodeFormulaResult bs = [true] := by
  simp [decodeFormulaResult, encodeDecodeFormulaResult, h]

/-- Case split form used by the branching FinTM2: success copies with a leading
`false`, failure emits `[true]`. -/
theorem decodeFormulaResult_eq (bs : List Bool) :
    decodeFormulaResult bs =
      match decodeFormula bs with
      | some _ => false :: bs
      | none => [true] := by
  cases h : decodeFormula bs with
  | none => simp [decodeFormulaResult, encodeDecodeFormulaResult, h]
  | some φ =>
      have henc := encodeFormula_of_decodeFormula h
      simp [decodeFormulaResult, encodeDecodeFormulaResult, h, henc]

/-- Successful decode iff the tape is exactly some `encodeFormula` image. -/
theorem decodeFormula_isSome_iff (bs : List Bool) :
    (decodeFormula bs).isSome ↔ ∃ φ, encodeFormula φ = bs := by
  constructor
  · intro h
    cases hφ : decodeFormula bs with
    | none => simp [hφ] at h
    | some φ => exact ⟨φ, encodeFormula_of_decodeFormula hφ⟩
  · intro ⟨φ, hφ⟩
    subst hφ
    simp [decodeFormula_encodeFormula]

/-- Output length on the success slice is `|encodeFormula φ| + 1`. -/
theorem length_decodeFormulaResult_encodeFormula (φ : PropFormula) :
    (decodeFormulaResult (encodeFormula φ)).length =
      (encodeFormula φ).length + 1 := by
  simp [decodeFormulaResult_encodeFormula]

/-- Output length of `decodeFormulaResult` is O(|bs|). -/
theorem length_decodeFormulaResult_le (bs : List Bool) :
    (decodeFormulaResult bs).length ≤ bs.length + 1 := by
  simp only [decodeFormulaResult, encodeDecodeFormulaResult]
  cases h : decodeFormula bs with
  | none =>
      change ([true] : List Bool).length ≤ bs.length + 1
      simp
  | some φ =>
      have henc := encodeFormula_of_decodeFormula h
      simp [henc]

end SATurday.Bridge
