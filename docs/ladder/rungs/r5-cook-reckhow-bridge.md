# R5: Cook-Reckhow Bridge

Status: active
Lean home: theory/Theory/ProofComplexity/Bridge/ (Encoding.lean and Complexity.lean started)
Namespace plan: SATurday.Bridge (separate from SATurday.ProofComplexity)

## Statement (pinned 2026-08-04 prove)

Formalize in Lean, zero sorries, standard axioms only. Classification: adaptation
(Cook and Reckhow 1979; Arora and Barak textbook presentation).

Alphabet and encodings (pinned):
- Bit strings: `List Bool` with length `|x|`.
- Fixed encoding maps of type `α → List Bool` (mathlib style `ea`, `eb` as in
  `Turing.TM2ComputableInPolyTime`).
- Languages: predicates `L : List Bool → Prop` (or `Set (List Bool)`).

Machine model (pinned to mathlib, verified present):
- Import: `Mathlib.Computability.TuringMachine.Computable`.
- Polynomial time total functions: structure
  `Turing.TM2ComputableInPolyTime ea eb f` with fields `tm : FinTM2`,
  alphabet equivalences, `time : Polynomial ℕ`, and
  `outputsFun` bounding steps by `time.eval (ea a).length`.
- Related: `TM2Computable`, `TM2ComputableInTime`, `FinTM2`.
- Mathlib gap recorded: `proof_wanted TM2ComputableInPolyTime.comp` (composition
  of poly time maps is not yet a mathlib theorem). R5 must either prove
  composition locally or avoid relying on an unproved mathlib stub.

Complexity classes (pinned statements):
1. `InP L` means there exists a decidable characteristic function
   `χ : List Bool → Bool` with `∀ x, χ x = true ↔ L x`, and a witness
   `Turing.TM2ComputableInPolyTime (fun x => x) (fun b => [b]) χ`
   (identity encoding on inputs; single bit encoding on outputs).
2. `InNP L` means there exist a polynomial `p : Polynomial ℕ` and a
   polynomial time verifier
   `V : List Bool → List Bool → Bool` such that
   `Turing.TM2ComputableInPolyTime encodePair encodeBool V` holds for a fixed
   pairing `encodePair (x, w) = ⟨x, w⟩`, and
   `∀ x, L x ↔ ∃ w, |w| ≤ (p.eval |x|) ∧ V x w = true`.
3. `InCoNP L` means `InNP (complement L)`, where
   `complement L x ↔ ¬ L x`.
4. Class equalities: `ClassP = ClassNP` means `∀ L, InP L ↔ InNP L`;
   `ClassNP = ClassCoNP` means `∀ L, InNP L ↔ InCoNP L`.

Propositional proof systems (Cook and Reckhow, pinned):
5. Let `TAUT : List Bool → Prop` be the language of encodings of propositional
   tautologies under a fixed sound and complete encoding of formulas
   (encoding to be defined in Bridge/FormulaEncoding; must satisfy:
   every formula has a code, satisfiability of the decoded formula matches
   the semantic predicate, and decoding is polynomial time).
6. A propositional proof system is a triple `(f, hf_poly, hf_onto)` where
   `f : List Bool → List Bool`,
   `hf_poly : Turing.TM2ComputableInPolyTime idEnc idEnc f`,
   and `hf_onto : ∀ φ, TAUT φ → ∃ π, f π = φ`
   (equivalently: `f` maps onto `TAUT`). Soundness is the converse
   direction `f π = φ → TAUT φ`, required as part of the structure.
7. Equivalent UNSAT refutation system form (for CNF bridge to R0): a
   polynomial time function `r` onto encodings of unsatisfiable CNFs, with
   soundness `r π = ψ → Unsat ψ`. The two forms are interreducible by
   negation of the encoded formula; R5 may formalize either and derive the
   other.
8. Polynomially bounded: a proof system `f` is polynomially bounded if there
   exists `q : Polynomial ℕ` such that
   `∀ φ, TAUT φ → ∃ π, f π = φ ∧ |π| ≤ q.eval |φ|`.

Bridge theorems (pinned):
9. Bridge theorem 1 (Cook and Reckhow 1979):
   `(∃ f, IsPropProofSystem f ∧ PolynomiallyBounded f) ↔ ClassNP = ClassCoNP`.
10. Bridge theorem 2:
    `ClassP = ClassNP → ClassNP = ClassCoNP`.
11. Summit corollary (contrapositive packaging):
    `(∀ f, IsPropProofSystem f → ¬ PolynomiallyBounded f) → ClassP ≠ ClassNP`.
    Derived from (9) and (10); does not encode any lower bound as an axiom.

Non vacuity witnesses (statement hygiene):
- `InP` nonempty: the empty language and `List Bool → True` (all strings) are in P
  via constant output machines (build from `idComputableInPolyTime` style).
- `InNP` nonempty: SAT (under the same formula encoding) is the standard witness;
  even without SAT, every language in P is in NP via ignoring the witness.
- Proof systems nonempty: the truth table proof system (enumerate all
  assignments; accept if the formula is true on all) is a propositional proof
  system and is exponential size, hence not polynomially bounded; it witnesses
  that `IsPropProofSystem` is satisfiable so universal claims are nonvacuous.
- TAUT nonempty: encoding of `p ∨ ¬p` (or `True`) is a tautology.

## Why this rung

This replaces the vacuous opaque-constant PvsNPGoal module (archived) with a real
target statement. Until R5 is certified, the summit link is informal and cited, and
is never encoded as an axiom.

## Planned Lean module tree (Bridge/, separate from R2)

Do not place these under shared R2 width modules. Do not reopen R1. Create only at
formalize time; this prove cycle writes no Lean.

- `theory/Theory/ProofComplexity/Bridge/Encoding.lean`
  Pairing, length, bit encodings; `encodePair`, `encodeBool`.
- `theory/Theory/ProofComplexity/Bridge/Complexity.lean`
  `InP`, `InNP`, `InCoNP`, class equalities over `TM2ComputableInPolyTime`.
- `theory/Theory/ProofComplexity/Bridge/FormulaEncoding.lean`
  Propositional formulas as inductive type plus poly time encode or decode to
  `List Bool`; semantic `Tautology` and `TAUT`.
- `theory/Theory/ProofComplexity/Bridge/ProofSystem.lean`
  `IsPropProofSystem`, `PolynomiallyBounded`, truth table system witness.
- `theory/Theory/ProofComplexity/Bridge/CookReckhow.lean`
  Bridge theorems 1 and 2 and the summit corollary.
- Root import: add `Theory.ProofComplexity.Bridge.CookReckhow` to `Theory.lean`
  only when the first accepted Bridge declaration is ready for the axiom gate
  (not this cycle).

Independence: R5 does not import R2 width machinery
(`MonotoneWidth`, `MatchingRestriction`, `MonotoneCalculus`). Optional later
link from UNSAT encodings to `SATurday.ProofComplexity` CNF types is deferred
until Bridge theorem statements compile against `List Bool` alone.

## Falsification test

None (known mathematics). Risk is formalization cost: mathlib's complexity-theory
layer is thin, and encoding-invariance work is substantial. This is why R5 is
deferred until R1 proves the pipeline can certify hard content.

## Barrier notes

Not applicable (no lower-bound claim). Classical barriers (relativization,
natural proofs, algebraization) do not apply to this definitional bridge.
Formalization soundness risks (encoding games, poly time closure) are tracked
as gaps below, not as barrier walls. No barrier audit gate required before
formalize for R5 itself; audit would apply only if a future argument claimed a
lower bound via the bridge.

## Session log (append-only)

- 2026-08-03 reboot: rung proposed. Opens when R1 is certified.

- 2026-08-04 adopt: rung opened to active by R1 certification
  (path A honest-rate close). Next: prove cycle to pin the machine model and bridge theorem statements before Lean.

- 2026-08-04 prove (pin machine model and Cook Reckhow bridge): PARTIAL.

  Target this cycle: pin machine model, class definitions, proof system
  definition, bridge theorems 1 and 2, summit corollary, and Bridge module
  plan; develop one prose argument for the bridge; gap list; adversarial pass.
  No Lean written (prover contract).

  Existing names verified before pinning (no guessing):
  - mathlib: `Turing.TM2ComputableInPolyTime`, `TM2ComputableInTime`,
    `TM2Computable`, `FinTM2`, `idComputableInPolyTime`,
    `proof_wanted TM2ComputableInPolyTime.comp`
    in `Mathlib.Computability.TuringMachine.Computable`
  - repo: no `theory/Theory/ProofComplexity/Bridge/` files yet; R2 modules
    `Resolution`, `PHP`, `CriticalAssignments`, `ClauseComplexity`,
    `MonotoneWidth`, `MatchingRestriction`, `MonotoneCalculus` left untouched
  - docs: `docs/ladder/rungs/r5-cook-reckhow-bridge.md`,
    `docs/p-vs-np-main-attack.md`, `docs/p-vs-np-lemma-chain.md`

  Rejected alternate pins (sketches only):
  (A) Define P via arbitrary `ℕ → ℕ` time bounds without `Polynomial ℕ`.
      Rejected: weaker than mathlib's poly time structure and harder to compose
      with literature statements.
  (B) Start from opaque class constants again (archived PvsNPGoal). Rejected:
      fails proof standards (no opaque constants on the critical path).
  (C) Wait for R2. Rejected: R5 is independent after R1; DAG edge is R1 to R5.

  Developed argument (Cook and Reckhow 1979, adaptation; one argument):

  Definitions as pinned in Statement above. Work over bit strings.

  Lemma A (Psubseteq NP). For every language L, InP L implies InNP L.
  Proof sketch: if χ decides L in poly time, set V x w := χ x and ignore w,
  with witness length bound 0. Known; gap class routine once poly time
  machines can ignore an extra input tape or concatenate a dummy witness.

  Lemma B (Bridge theorem 2). ClassP = ClassNP implies ClassNP = ClassCoNP.
  Proof: assume ClassP = ClassNP. For any L in NP we have L in P, so
  complement L is in P (deterministic poly time closed under complement:
  flip the output bit of χ), hence complement L in NP, so L in coNP.
  Symmetrically every coNP language is in NP. Gap class: routine once
  complementation of P is formalized; hard if output flip needs a separate
  TM2 construction not yet in mathlib.

  Lemma C (Bridge theorem 1, => direction). If a polynomially bounded proof
  system f exists, then ClassNP = ClassCoNP.
  Proof sketch: TAUT is in coNP (a nontautology has a short falsifying
  assignment as an NP witness for the complement). If f is a polynomially
  bounded proof system, then TAUT is in NP: the short proof π is the witness
  and V(φ, π) checks f(π) = φ in poly time. So TAUT in NP ∩ coNP. The standard
  Cook Reckhow reduction shows every coNP language poly time many one reduces
  to TAUT (or dually every NP language reduces to SAT); with TAUT in NP one
  gets ClassCoNP ⊆ ClassNP, and the other inclusion is symmetric or via
  complements. Gap class: hard (needs poly time many one reductions and
  generalization from TAUT to all of coNP).

  Lemma D (Bridge theorem 1, <= direction). If ClassNP = ClassCoNP, then a
  polynomially bounded proof system exists.
  Proof sketch: TAUT is in coNP always, hence in NP by assumption. An NP
  machine for TAUT yields a verifier V(φ, π). Set f(π*) to decode a pair
  (φ, π) and output φ if V(φ, π) accepts, else output a trivial tautology.
  Then f is poly time, sound, onto TAUT, and proofs are poly length by the
  NP witness length bound. Gap class: hard (pairing/decoding machinery and
  careful onto proof).

  Lemma E (summit corollary). From Bridge theorems 1 and 2: if no proof system
  is polynomially bounded, then ClassNP ≠ ClassCoNP, hence ClassP ≠ ClassNP.
  Gap class: routine once 1 and 2 are theorems.

  Gap list:
  1. Poly time closure under complement for P (output bit flip on TM2).
     Class: routine.
  2. Poly time closure under pairing, projection, and composition. Mathlib
     leaves `TM2ComputableInPolyTime.comp` as `proof_wanted`. Class: hard.
  3. Formula encoding with poly time encode or decode and semantic agreement.
     Class: hard (bookkeeping, not new math).
  4. Poly time many one reduction from every coNP language to TAUT (or NP to
     SAT) sufficient for the generalization step in Lemma C. Class: hard.
  5. Truth table proof system as nonvacuity witness, including poly time proof
     checking of a truth table certificate. Class: routine to hard depending
     on formula encoding.
  6. Equivalence of TAUT proof systems and UNSAT refutation systems.
     Class: routine given encoding of negation.
  7. Encoding invariance: bridge theorems should not depend on bit level
     quirks of one fixed encoding. Class: unknown to hard; may be scoped by
     fixing one encoding for the whole ladder and proving invariance later.

  Self adversarial pass:
  - Quantifiers: class equalities are ∀ L; proof system existence is ∃ f;
    polynomially bounded is ∃ q ∀ φ ∃ π. Order matches Cook Reckhow; do not
    swap to ∀ φ ∃ q (that would be trivial per formula).
  - Hidden uniformity: NP witness length must be a single polynomial of |x|,
    not a per instance bound. Pinned via `Polynomial ℕ`.
  - Vacuity: truth table system prevents "all systems are unbounded" from
    quantifying over an empty set of systems; TAUT nonempty prevents empty
    language tricks on onto maps.
  - Does any step prove P ≠ NP? No. The corollary is an implication whose
    hypothesis is the open all systems program; R5 never assumes that
    hypothesis as an axiom.
  - Off by one: witness length `p.eval |x|` versus `|x| + 1` style bounds;
    pin `≤ p.eval |x|` and ensure pairing length accounts for separators.
  - Secret summit hardness: Lemma C's reduction step is the heaviest gap; if
    formalize stalls, keep Bridge theorem 1 as two lemmas with the reduction
    isolated so Complexity and ProofSystem can certify first.
  - R3+ barrier flag: no lower bound claimed; barrier audit not required for
    this definitional rung (see Barrier notes).

  Worst gap: item 2 (poly time composition and pairing on TM2) plus item 4
  (coNP to TAUT reduction). These dominate formalization cost.

  Result: PARTIAL. Statements and module plan pinned; prose argument complete
  with substantive formalization gaps remaining. Next: formalize starting at
  Encoding.lean and Complexity.lean (InP, InNP, InCoNP), not CookReckhow.lean
  first.

  Artifacts: docs/ladder/rungs/r5-cook-reckhow-bridge.md

- 2026-08-10 formalize (Encoding and Complexity cluster): PARTIAL.

  Target this cycle: start Bridge module tree with Encoding.lean and
  Complexity.lean; certify pairing encodings and InP InNP InCoNP statement
  shapes; wire into Theory.lean; axiom gate; merge certified cluster.

  Existing names verified before writing (no guessing):
  - mathlib: Turing.TM2ComputableInPolyTime, idComputableInPolyTime,
    Computability.encodeBool, FinTM2, TM2.Stmt
  - repo: no Bridge/ files existed; ProofComplexity has Resolution PHP Width
    SizeWidth FinGraph Tseitin CSExpansion and related R0 R1 R2 modules
    (CSExpansion left untouched; parallel R2 agent)
  - docs: docs/ladder/rungs/r5-cook-reckhow-bridge.md; docs/file_structure.md
    absent

  Variables and declarations used:
  - Language, idBitEnc, bitEnc, encodePair, decodePair
  - InP, InNP, InCoNP, complement
  - ClassP_eq_ClassNP, ClassNP_eq_ClassCoNP
  - emptyLanguage, fullLanguage, ignoreWitness, zeroWitnessBound
  - constBitComputer, constBitTime (defs; correctness Frontier)
  - BridgeFrontier: constBitComputableInPolyTime, emptyLanguage_in_P,
    fullLanguage_in_P, InP_implies_InNP, classP_eq_classNP_implies_NP_eq_coNP

  Accepted (axiom gate PASS, merge_certified auto applied):
  - SATurday.Bridge.bitEnc_eq_encodeBool
  - SATurday.Bridge.decodePair_encodePair
  - SATurday.Bridge.encodePair_injective
  - SATurday.Bridge.length_encodePair
  - SATurday.Bridge.encodePair_ne_nil
  - SATurday.Bridge.length_bitEnc
  - SATurday.Bridge.bitEnc_injective
  - SATurday.Bridge.InCoNP_iff
  - SATurday.Bridge.complement_complement
  - SATurday.Bridge.InNP_complement_complement
  - SATurday.Bridge.ClassNP_eq_ClassCoNP.complement_in_NP
  - SATurday.Bridge.constFalse_decides_empty
  - SATurday.Bridge.constTrue_decides_full
  - SATurday.Bridge.empty_witness_length_bound

  Frontier remaining: constant bit TM2 run lemmas and InP nonvacuity; Psubseteq
  NP via encodePair verifier; bridge theorem 2 (needs P closed under
  complement). FormulaEncoding ProofSystem CookReckhow not started.

  Result: PARTIAL. Smallest coherent certified cluster compiles and is gated.
  Next: formalize constBitComputableInPolyTime (close emptyLanguage_in_P) or
  start FormulaEncoding.

  Artifacts: theory/Theory/ProofComplexity/Bridge/Encoding.lean,
  theory/Theory/ProofComplexity/Bridge/Complexity.lean, theory/Theory.lean,
  scripts/accepted_declarations.txt

- 2026-08-10 formalize (constant bit InP nonvacuity): PARTIAL.

  Target this cycle: close `constBitComputableInPolyTime` and InP nonvacuity
  (`emptyLanguage_in_P`, `fullLanguage_in_P`); leave pairing and bridge theorem 2
  in Frontier if blocked.

  Existing names verified before editing (no guessing):
  - mathlib: Turing.TM2ComputableInPolyTime, FinTM2, TM2.step, TM2.stepAux,
    StateTransition.EvalsToInTime, initList, haltList, idComputableInPolyTime
  - repo: theory/Theory/ProofComplexity/Bridge/Encoding.lean,
    Complexity.lean (constBitComputer, constBitTime already present);
    CSExpansion.lean left untouched (parallel R2 agent)
  - docs: docs/ladder/rungs/r5-cook-reckhow-bridge.md

  Variables and declarations used:
  - constBitStk, constBitCfg, update_unit_stk, update_constBitStk
  - constBitComputer_step_cons, constBitComputer_step_nil,
    constBitComputer_step_write, constBitComputer_initList,
    constBitComputer_haltList
  - constBitComputer_evals_cons_step, constBitComputer_evals_nil,
    constBitComputer_evals, constBitTime_eval
  - constBitComputableInPolyTime (moved out of Frontier)
  - emptyLanguage_in_P, fullLanguage_in_P (moved out of Frontier)

  Accepted (axiom gate PASS, merge_certified auto applied):
  - SATurday.Bridge.update_unit_stk
  - SATurday.Bridge.update_constBitStk
  - SATurday.Bridge.constBitComputer_step_cons
  - SATurday.Bridge.constBitComputer_step_nil
  - SATurday.Bridge.constBitComputer_step_write
  - SATurday.Bridge.constBitComputer_initList
  - SATurday.Bridge.constBitComputer_haltList
  - SATurday.Bridge.constBitTime_eval
  - SATurday.Bridge.emptyLanguage_in_P
  - SATurday.Bridge.fullLanguage_in_P

  Frontier remaining: InP_implies_InNP (needs encodePair verifier TM);
  classP_eq_classNP_implies_NP_eq_coNP (needs P closed under complement).
  Learned: haltList zeros non output stacks, so constant output needs a clear
  loop on a shared input or output stack; step count is |x| + 2.

  Result: PARTIAL. InP nonvacuity certified. Next: formalize pairing verifier
  for InP_implies_InNP or start FormulaEncoding.

- 2026-08-10 formalize (encodePair projFirst toward InP_implies_InNP): PARTIAL.

  Target this cycle: close `InP_implies_InNP` (encodePair verifier for P ⊆ NP);
  leave `classP_eq_classNP_implies_NP_eq_coNP` Frontier unless it falls out cleanly.
  Do not edit CSExpansion.lean or R2 CS path.

  Existing names verified before editing (no guessing):
  - mathlib: Turing.TM2ComputableInPolyTime, TM2.step, TM2.stepAux, FinTM2,
    initList, haltList, EvalsToInTime, proof_wanted TM2ComputableInPolyTime.comp
  - repo: theory/Theory/ProofComplexity/Bridge/Encoding.lean (encodePair,
    decodePair, idBitEnc, bitEnc, length_encodePair),
    Complexity.lean (InP, InNP, ignoreWitness, zeroWitnessBound,
    constBitComputableInPolyTime); CSExpansion.lean left untouched
  - docs: docs/ladder/rungs/r5-cook-reckhow-bridge.md

  Variables and declarations used:
  - ProjStack (inp, work, out), ProjLabel (parse, expectBit, clear, rev)
  - projFirstComputer, projStk, projCfg
  - proj_step_parse_true, proj_step_parse_false, proj_step_expectBit,
    proj_step_clear_cons, proj_step_clear_nil, proj_step_rev_cons,
    proj_step_rev_nil, projFirst_initList, projFirst_haltList
  - proj_evals_one_bit, proj_evals_parse, proj_evals_to_clear,
    proj_evals_clear_one, proj_evals_clear_nil, proj_evals_clear,
    proj_evals_rev_one, proj_evals_rev_nil, proj_evals_rev
  - evalsToInTime_le_mono, projFirst_evals, projFirstTime, projFirstTime_bound
  - projFirstComputableInPolyTime
  - ignoreWitness_under_fst, ignoreWitness_zero_correct

  Accepted (axiom gate PASS, merge_certified auto applied):
  - SATurday.Bridge.proj_step_* and projFirst_initList / haltList
  - SATurday.Bridge.projFirstTime_bound
  - SATurday.Bridge.evalsToInTime_le_mono
  - SATurday.Bridge.projFirst_evals
  - SATurday.Bridge.projFirstComputableInPolyTime
  - SATurday.Bridge.ignoreWitness_under_fst
  - SATurday.Bridge.ignoreWitness_zero_correct

  Frontier remaining: InP_implies_InNP (needs local TM2ComputableInPolyTime.comp
  of projFirstComputableInPolyTime with the InP witness);
  classP_eq_classNP_implies_NP_eq_coNP (needs P closed under complement).
  Learned: Function.update equalities across FinTM2.kDecidableEq versus the
  ambient DecidableEq instance do not unify; prove stack residuals by funext
  and cases. Composition remains the hard gap (mathlib proof_wanted).

  Result: PARTIAL. encodePair first projection certified; full P ⊆ NP blocked
  on composition. Next: formalize local composition for Bool pair encodings,
  or prove P closed under complement for bridge theorem 2.

  Artifacts: theory/Theory/ProofComplexity/Bridge/Complexity.lean,
  scripts/accepted_declarations.txt

- 2026-08-10 formalize (local TM2 composition surgery toward InP_implies_InNP): PARTIAL.

  Target this cycle: close `InP_implies_InNP` via local TM2 polytime composition
  (mathlib `TM2ComputableInPolyTime.comp` is `proof_wanted`); maximize accepted
  progress if full close blocked. Do not edit CSExpansion.lean.

  Existing names verified before editing (no guessing):
  - mathlib: Turing.TM2ComputableInPolyTime, FinTM2, TM2.Stmt, TM2.step,
    TM2OutputsInTime, proof_wanted TM2ComputableInPolyTime.comp,
    idComputableInPolyTime
  - repo: Encoding.lean (encodePair, idBitEnc, bitEnc), Complexity.lean
    (InP, InNP, projFirstComputableInPolyTime, ignoreWitness_under_fst,
    constBitComputer, ignoreWitness_zero_correct); CSExpansion.lean untouched
  - docs: docs/ladder/rungs/r5-cook-reckhow-bridge.md

  Variables and declarations used or added:
  - stmtRemap, stmtRemapGoto, stmtLiftInl, stmtLiftInr, stmtLiftState₁,
    stmtLiftState₂
  - CompLabel, equivCompLabel, Compσ, compΓ
  - copyPopStmt, copyPushStmt, firstPhaseStmt, secondPhaseStmt, seqCompComputer
  - constBit_of_encoding, comp_const_right, constBit_encodePair,
    ignoreWitness_const_encodePair
  - emptyLanguage_in_NP, fullLanguage_in_NP
  - poly_add_eval, seqCompTime, seqCompTime_eval
  - Frontier: compose_projFirst_bitEnc, InP_implies_InNP,
    classP_eq_classNP_implies_NP_eq_coNP

  Accepted (axiom gate PASS, merge_certified auto applied):
  - SATurday.Bridge.stmtRemap and stmtRemapGoto
  - SATurday.Bridge.stmtLiftInl, stmtLiftInr, stmtLiftState₁, stmtLiftState₂
  - SATurday.Bridge.equivCompLabel, seqCompComputer
  - SATurday.Bridge.copyPopStmt, copyPushStmt, firstPhaseStmt, secondPhaseStmt
  - SATurday.Bridge.constBit_of_encoding, comp_const_right, constBit_encodePair
  - SATurday.Bridge.ignoreWitness_const_encodePair
  - SATurday.Bridge.emptyLanguage_in_NP, fullLanguage_in_NP
  - SATurday.Bridge.poly_add_eval, seqCompTime_eval

  Frontier remaining: compose_projFirst_bitEnc.outputsFun (sequential simulation
  of seqCompComputer after projFirst then InP witness); InP_implies_InNP;
  classP_eq_classNP_implies_NP_eq_coNP (P closed under complement).
  Learned: right-constant Bool composition needs no product machine
  (`(fun _ => b) ∘ f = fun _ => b`); general pair composition still needs
  phase simulation on seqCompComputer.

  Result: PARTIAL. Composition skeleton and NP nonvacuity certified; full
  P ⊆ NP blocked on seqComp outputsFun. Next: formalize sequential simulation
  for compose_projFirst_bitEnc.

  Artifacts: theory/Theory/ProofComplexity/Bridge/Complexity.lean,
  scripts/accepted_declarations.txt

- 2026-08-10 formalize (order preserving seqComp simulation toward InP_implies_InNP): PARTIAL.

  Target this cycle: close `compose_projFirst_bitEnc.outputsFun` via sequential
  simulation of `seqCompComputer`; maximize accepted progress if full close
  blocked. Do not edit CSExpansion.lean.

  Existing names verified before editing (no guessing):
  - mathlib: Turing.TM2ComputableInPolyTime, TM2.step, TM2.stepAux, FinTM2,
    initList, haltList, EvalsToInTime, Function.update
  - repo: Encoding.lean (encodePair, idBitEnc, bitEnc), Complexity.lean
    (seqCompComputer, firstPhaseStmt, copyPopStmt or copyPushStmt,
    projFirstComputableInPolyTime, compose_projFirst_bitEnc Frontier);
    CSExpansion.lean left untouched (parallel R2 agent; WIP restored after gate)
  - docs: docs/ladder/rungs/r5-cook-reckhow-bridge.md

  Variables and declarations used or added:
  - CompK, CompΓ, stmtLiftFirst, stmtLiftSecond, compAux
  - CompLabel.copyToAuxPop, copyToAuxPush, copyToInPop, copyToInPush
  - copyToAuxPopStmt, copyToAuxPushStmt, copyToInPopStmt, copyToInPushStmt
  - seqCompStk, seqCompCfg, emptyStk, instDecidableEqCompK
  - seqCompStk_update_first, seqCompStk_update_aux, seqCompStk_update_second
  - seqComp_copy_steps_bound, seqCompTime (now 4*(X+1) copy budget)
  - seqComp_step_copyToAuxPush, seqComp_step_copyToInPop_nil,
    seqComp_step_copyToInPop_cons (accepted)
  - Frontier: seqComp_step_copyToAuxPop_cons, seqComp_step_copyToAuxPop_nil,
    seqComp_step_copyToInPush, compose_projFirst_bitEnc, InP_implies_InNP,
    classP_eq_classNP_implies_NP_eq_coNP

  Accepted (axiom gate PASS with HEAD CSExpansion, merge_certified auto applied):
  - SATurday.Bridge.CompΓ, stmtLiftFirst, stmtLiftSecond, compAux
  - SATurday.Bridge.copyToAux*Stmt, copyToIn*Stmt
  - SATurday.Bridge.seqCompStk, seqCompCfg, emptyStk, instDecidableEqCompK
  - SATurday.Bridge.seqCompStk_update_*
  - SATurday.Bridge.seqComp_copy_steps_bound
  - SATurday.Bridge.seqComp_step_copyToAuxPush
  - SATurday.Bridge.seqComp_step_copyToInPop_nil
  - SATurday.Bridge.seqComp_step_copyToInPop_cons
  - rewritten seqCompComputer (out→aux→in; single out→in would reverse)

  Frontier remaining: first or second stack update steps under
  FinTM2.kDecidableEq versus ambient Function.update; first or second phase
  simulation; compose_projFirst_bitEnc.outputsFun; InP_implies_InNP;
  classP_eq_classNP_implies_NP_eq_coNP.
  Learned: a single stack transfer reverses list order, so composition needs an
  aux stack (two transfers). Aux only copy steps close with change or rfl;
  updates to first or second stacks still hit DecidableEq instance mismatch.

  Result: PARTIAL. Order preserving product machine and aux copy steps
  certified; full P ⊆ NP still blocked on remaining copy and phase simulation.
  Next: formalize seqComp_step_copyToAuxPop_cons and copyToInPush without
  ambient Function.update on the statement RHS, then lift projFirst_evals.

  Artifacts: theory/Theory/ProofComplexity/Bridge/Complexity.lean,
  scripts/accepted_declarations.txt

- 2026-08-11 formalize (remaining first or second stack copy steps): PARTIAL.

  Target this cycle: certify `seqComp_step_copyToAuxPop_nil`,
  `seqComp_step_copyToAuxPop_cons`, and `seqComp_step_copyToInPush` under the
  machine DecidableEq instance, then maximize toward
  `compose_projFirst_bitEnc.outputsFun`.

  Existing names verified before editing (no guessing):
  - mathlib: Function.update_self, Function.update_of_ne, FinTM2.kDecidableEq,
    TM2.step, TM2.stepAux, List.tail
  - repo: SATurday.Bridge.seqCompComputer, seqCompStk, seqCompCfg,
    seqCompStk_update_first, seqCompStk_update_second,
    seqComp_step_copyToAuxPush, seqComp_step_copyToInPop_nil,
    seqComp_step_copyToInPop_cons, BridgeFrontier.compose_projFirst_bitEnc
  - docs: docs/ladder/rungs/r5-cook-reckhow-bridge.md

  Variables and declarations used or added:
  - update_self_of_eq_nil
  - seqCompStk_update_first_nil_eq, seqCompStk_update_first_eq,
    seqCompStk_update_second_eq (pointwise; take ambient CompK DecidableEq)
  - seqComp_step_copyToAuxPop_nil, seqComp_step_copyToAuxPop_cons,
    seqComp_step_copyToInPush (accepted)
  - letI CompK DecidableEq := (seqCompComputer ...).kDecidableEq

  Accepted (axiom gate PASS, merge_certified auto applied):
  - SATurday.Bridge.update_self_of_eq_nil
  - SATurday.Bridge.seqCompStk_update_first_nil_eq
  - SATurday.Bridge.seqCompStk_update_first_eq
  - SATurday.Bridge.seqCompStk_update_second_eq
  - SATurday.Bridge.seqComp_step_copyToAuxPop_nil
  - SATurday.Bridge.seqComp_step_copyToAuxPop_cons
  - SATurday.Bridge.seqComp_step_copyToInPush

  Frontier remaining: compose_projFirst_bitEnc.outputsFun, InP_implies_InNP,
  classP_eq_classNP_implies_NP_eq_coNP (phase simulation still open).
  Learned: opaque FinTM2.kDecidableEq blocks simp reduction of Function.update
  at equal keys; Function.update_self with the machine instance closes the
  residual stack equality after List.tail simplification.

  Result: PARTIAL. All six order preserving copy steps are now accepted; full
  P ⊆ NP still blocked on sequential phase simulation for outputsFun.
  Next: formalize first then second phase simulation on seqCompComputer toward
  compose_projFirst_bitEnc.outputsFun.

  Artifacts: theory/Theory/ProofComplexity/Bridge/Complexity.lean,
  scripts/accepted_declarations.txt

- 2026-08-11 formalize (seqComp first or second phase simulation): PARTIAL.

  Target this cycle: prove first then copy then second phase evaluation for
  `seqCompComputer`, enough to discharge `compose_projFirst_bitEnc.outputsFun`,
  then finish `InP_implies_InNP`.

  Existing names verified before editing (no guessing):
  - mathlib: TM2.stepAux, FinTM2.step, EvalsToInTime, Function.update_self,
    Function.update_of_ne, flip bind iterate
  - repo: SATurday.Bridge.seqCompComputer, firstPhaseStmt, secondPhaseStmt,
    seqComp_step_copyToAux*, seqComp_step_copyToIn*, BridgeFrontier.compose_projFirst_bitEnc
  - docs: docs/ladder/rungs/r5-cook-reckhow-bridge.md

  Variables and declarations used or added:
  - liftFirstCfg, liftSecondCfg
  - seqCompStk_update_first_inline, seqCompStk_update_second_inline
  - firstPhase_stepAux, secondPhase_stepAux
  - seqComp_step_first, seqComp_step_second
  - liftFirstCfg_step, liftSecondCfg_step
  - option_bind_iterate_none, liftFirstCfg_iterate, liftSecondCfg_iterate
  - seqComp_evals_first, seqComp_evals_second
  - seqComp_evals_copyToAux_one, seqComp_evals_copyToAux_nil
  - seqComp_evals_copyToIn_one, seqComp_evals_copyToIn_nil
  - Frontier: seqComp_evals_copyToAux, seqComp_evals_copyToIn,
    compose_projFirst_bitEnc, InP_implies_InNP,
    classP_eq_classNP_implies_NP_eq_coNP

  Accepted (axiom gate PASS, merge_certified auto applied):
  - SATurday.Bridge.liftFirstCfg, liftSecondCfg
  - SATurday.Bridge.firstPhase_stepAux, secondPhase_stepAux
  - SATurday.Bridge.liftFirstCfg_iterate, liftSecondCfg_iterate
  - SATurday.Bridge.seqComp_evals_first, seqComp_evals_second
  - SATurday.Bridge.seqComp_evals_copyToAux_one or _nil
  - SATurday.Bridge.seqComp_evals_copyToIn_one or _nil

  Frontier remaining: full-list copy induction (EvalsToInTime time field Nat
  association blocked naive simpa), glue to outputsFun, InP_implies_InNP,
  classP_eq_classNP_implies_NP_eq_coNP.
  Learned: phase stepAux lifts need inline Function.update proofs under the
  machine FinTM2.kDecidableEq instance; multi-step lift stops at remapped halt
  (copyToAuxPop) without stepping the product past that config.

  Result: PARTIAL. Phase simulation certified; full P ⊆ NP still blocked on
  list copy induction then outputsFun glue.
  Next: formalize seqComp_evals_copyToAux or copyToIn via evalsToInTime_le_mono
  on the time field, then compose_projFirst_bitEnc.outputsFun.

  Artifacts: theory/Theory/ProofComplexity/Bridge/Complexity.lean,
  scripts/accepted_declarations.txt

- 2026-08-11 formalize (full-list seqComp copy transfer): PARTIAL.

  Target this cycle: close `seqComp_evals_copyToAux` and `seqComp_evals_copyToIn`,
  then glue `compose_projFirst_bitEnc.outputsFun` and `InP_implies_InNP`.

  Existing names verified before editing (no guessing):
  - SATurday.Bridge.seqComp_evals_copyToAux_one, _nil, copyToIn_one, _nil
  - seqComp_evals_first, seqComp_evals_second, liftFirstCfg, liftSecondCfg
  - evalsToInTime_le_mono, EvalsToInTime.trans

  Variables and declarations used or added:
  - evalsToInTime_congr_end
  - seqComp_evals_copyToAux, seqComp_evals_copyToIn (moved out of Frontier)
  - Frontier unchanged: compose_projFirst_bitEnc.outputsFun, InP_implies_InNP,
    classP_eq_classNP_implies_NP_eq_coNP

  Accepted (axiom gate PASS, merge_certified auto applied):
  - SATurday.Bridge.evalsToInTime_congr_end
  - SATurday.Bridge.seqComp_evals_copyToAux
  - SATurday.Bridge.seqComp_evals_copyToIn

  Frontier remaining: outputsFun glue needs initList or haltList equality for
  seqCompComputer versus liftFirstCfg or liftSecondCfg; FinTM2.initList dite
  casts on CompK do not unify with component dite by simple simp.
  Learned: rewrite ending Option cfg via evalsToInTime_congr_end, then
  evalsToInTime_le_mono for the Nat time association 2*n+1+2 versus 2*(n+1)+1.

  Result: PARTIAL. Full-list order preserving copy certified; P ⊆ NP still
  blocked on initList packaging for outputsFun.
  Next: formalize seqComp_initList and seqComp_haltList (dite cast hygiene),
  then chain first or copy or second into compose_projFirst_bitEnc.outputsFun.

  Artifacts: theory/Theory/ProofComplexity/Bridge/Complexity.lean,
  scripts/accepted_declarations.txt

- 2026-08-11 formalize (seqComp init halt and InP implies InNP): SUCCESS.

  Target this cycle: `seqComp_initList`, `seqComp_haltList`, full
  `seqComp_evals_compose`, `compose_projFirst_bitEnc.outputsFun`, and
  `InP_implies_InNP`.

  Existing names verified before editing (no guessing):
  - SATurday.Bridge.seqComp_evals_first, seqComp_evals_second
  - seqComp_evals_copyToAux, seqComp_evals_copyToIn
  - liftFirstCfg, liftSecondCfg, seqCompCfg, seqCompStk, emptyStk
  - projFirst_evals, projFirstTime_bound, ignoreWitness, zeroWitnessBound
  - mathlib: initList, haltList, TM2OutputsInTime, EvalsToInTime.trans
    (accumulates as m₂ + m₁)

  Variables and declarations used or added:
  - initList_stk_k₀, initList_stk_of_ne, haltList_stk_k₁, haltList_stk_of_ne
  - seqComp_initList, seqComp_haltList
  - haltList_stk_cleared, initList_stk_eq_update_empty
  - map_encode_decode_reverse_cancel, seqComp_evals_compose
  - poly_eval_mono, compose_projFirst_bitEnc, InP_implies_InNP
  - Frontier remaining: classP_eq_classNP_implies_NP_eq_coNP

  Accepted (axiom gate PASS, merge_certified auto applied):
  - SATurday.Bridge.seqComp_initList, seqComp_haltList
  - SATurday.Bridge.seqComp_evals_compose
  - SATurday.Bridge.compose_projFirst_bitEnc
  - SATurday.Bridge.InP_implies_InNP

  Learned: propositional rewrite on stk keys fails because Γ is key dependent;
  unfold seqCompComputer so product k₀ or k₁ is definitionally Sum.inl or
  Sum.inr. First halt remaps to copyToAuxPop via liftFirstCfg none branch.

  Result: SUCCESS for PsubseteqNP on the pinned TM2 classes. Bridge theorem 2
  remains Frontier.
  Next: formalize classP_eq_classNP_implies_NP_eq_coNP using InP_implies_InNP
  and complement closure, or audit the accepted PsubseteqNP certificate.

  Artifacts: theory/Theory/ProofComplexity/Bridge/Complexity.lean,
  scripts/accepted_declarations.txt

- 2026-08-11 formalize (P complement closure and bridge theorem 2): SUCCESS.

  Target this cycle: `InP_complement` via output bit flip, then
  `classP_eq_classNP_implies_NP_eq_coNP`.

  Existing names verified before editing (no guessing):
  - SATurday.Bridge.seqComp_evals_compose, seqCompTime, InP_implies_InNP
  - complement, complement_complement, ClassP_eq_ClassNP, ClassNP_eq_ClassCoNP
  - constBitComputer pattern for Unit stack TM2
  - mathlib: TM2.Stmt.pop, push, load, halt; TM2ComputableInPolyTime

  Variables and declarations used or added:
  - notBitComputer, notBitCfg, update_notBit_stk
  - notBit_step_read, notBit_step_write, notBit_initList, notBit_haltList
  - notBit_evals_one, notBitTime, notBitTime_eval, notBitComputableInPolyTime
  - compose_notAfter (seqCompTime slack +2 for length-1 mid at n=0)
  - not_chi_decides_complement, InP_complement
  - classP_eq_classNP_implies_NP_eq_coNP (moved out of Frontier)

  Accepted (axiom gate PASS, merge_certified auto applied):
  - SATurday.Bridge.notBitComputer, compose_notAfter, InP_complement
  - SATurday.Bridge.classP_eq_classNP_implies_NP_eq_coNP

  Learned: seqCompTime at input length 0 budgets only 6 copy steps while a
  length-1 mid needs 8; add a constant polynomial slack for bit flip compose.
  Complexity.lean BridgeFrontier is now empty of sorries.

  Result: SUCCESS for Cook Reckhow class equality bridge theorem 2 on pinned
  TM2 classes.
  Next: FormulaEncoding or proof system pin on R5, or audit the accepted
  bridge package; R2 CS track remains a parallel active rung.

  Artifacts: theory/Theory/ProofComplexity/Bridge/Complexity.lean,
  scripts/accepted_declarations.txt


- 2026-08-21 formalize (FormulaEncoding cluster 1): PARTIAL to SUCCESS on
  datatype and TAUT nonvacuity. Created planned
  `theory/Theory/ProofComplexity/Bridge/FormulaEncoding.lean`. Axiom gate PASS.
  General decode round trip remains Frontier sorry.

  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "formalize",
    "target": "FormulaEncoding cluster 1: PropFormula, encode or decode, TAUT nonvacuity",
    "rationale": "R5 is the lowest active rung; FormulaEncoding is the next pinned Block D module after Complexity bridge theorem 2."
  }
  ```

  ### Names verified before edit (no duplicates)

  New accepted: `PropFormula`, `PropFormula.eval`, `PropFormula.Tautology`,
  `tautSeed`, `tautSeed_tautology`, `encodeNat`, `decodeNat`,
  `decodeNat_encodeNat`, `encodeFormula`, `decodeFormulaPrefixFuel`,
  `decodeFormulaPrefix`, `decodeFormula`, `encodeFormula_tautSeed`,
  `decodeFormula_encodeFormula_tautSeed`, `TAUT`, `tautSeed_mem_TAUT`,
  `TAUT_nonempty`.
  Frontier: `decodeFormula_encodeFormula`, `encodeFormula_injective`.
  Reused: `Language` from Encoding.lean.

  ### What closed

  Formula inductive type, prefix encoding, fuelled decoder, seed tautology,
  concrete seed round trip via kernel `decide`, nonempty `TAUT`.

  ### What did not close

  General round trip, poly time encode or decode TM2 witnesses, ProofSystem.

  Most important thing learned: `native_decide` injects a nonstandard axiom and
  fails the gate; kernel `decide` is required for accepted certificates.
  gate_pending: none (merge_certified auto under loop policy after PASS).

- 2026-08-21 prove (FormulaEncoding general round trip plan): PARTIAL.
  Prose only; Lean attempt deferred after termination or simp friction on the
  fuelled append lemma. Loop switched to dynamic wake cadence.

  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "prove",
    "target": "pin decodeFormulaPrefixFuel_encodeFormula_append proof plan",
    "rationale": "Cluster 1 left general round trip Frontier; pin the inductive append lemma before the next formalize."
  }
  ```

  ### Argument

  Prove
  `decodeFormulaPrefixFuel (fuel+1) (encodeFormula φ ++ suffix) = some (φ, suffix)`
  whenever `|encodeFormula φ| ≤ fuel`, by induction on `φ`.

  Base `var n`: use `decodeNat_encodeNat_append`.
  Step `not` or `and` or `or`: match `fuel = f+1`, apply IH at fuel `f` on the
  strictly shorter payload strings (length drop by the two tag bits).

  Then `decodeFormula_encodeFormula` is the empty suffix case with
  `fuel = |encodeFormula φ|`, and injectivity follows.

  ### Gap list

  1. Carry the Lean induction without `simp` eating length hypotheses.
     Gap class: routine.
  2. Poly time TM2 encode or decode. Gap class: hard.
  3. ProofSystem module. Gap class: hard.

  Most important thing learned: keep the append form of the round trip as the
  induction invariant; empty suffix only at the end.
  gate_pending: none.

- 2026-08-21 formalize (FormulaEncoding cluster 2 general round trip): SUCCESS.
  `theory/Theory/ProofComplexity/Bridge/FormulaEncoding.lean`. Axiom gate PASS.
  `gate_auto: true` merge_certified justified by gate green and decls listed.

  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "formalize",
    "target": "decodeFormulaPrefixFuel_encodeFormula_append then decodeFormula_encodeFormula and injectivity",
    "rationale": "Pinned prose plan from prior cycle; close FormulaEncoding Frontier round trip."
  }
  ```

  Accepted: `decodeNat_encodeNat_append`, length lemmas, `encodeFormula_length_pos`,
  `decodeFormulaPrefixFuel_encodeFormula_append`, `decodeFormula_encodeFormula`,
  `encodeFormula_injective`. Frontier namespace removed (no remaining sorries in
  this module).

  Still open on R5: poly time TM2 encode or decode, `ProofSystem`, Lemmas C to E.

  Most important thing learned: after rewriting the first recursive match arm,
  finish the nested match with `simp [ihψ']` rather than a second `rw` that
  cannot see through the residual `match some (...)`.
  gate_pending: none (merge_certified auto under loop policy after PASS).

- 2026-08-21 formalize (ProofSystem cluster 1): PARTIAL to SUCCESS on defs.
  `theory/Theory/ProofComplexity/Bridge/ProofSystem.lean`. Axiom gate PASS.
  `gate_auto: true` merge_certified justified by gate green and decls listed.

  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "formalize",
    "target": "ProofSystem cluster 1: IsPropProofSystem, PolynomiallyBounded, TT semantic map",
    "rationale": "FormulaEncoding cluster 2 closed; next pinned Bridge module is ProofSystem."
  }
  ```

  Accepted: `IsPropProofSystem`, `PolynomiallyBounded`, `maxVar`, `evalOn`, agree or
  evalOn lemmas, `allBitstrings`, `truthTableOf`, `validatesTautology`,
  `truthTableProofSystem` with sound and complete theorems.

  Frontier: `truthTable_is_prop_proof_system` (TM2 poly witness),
  `truthTable_not_poly_bounded`.

  Still open on R5: TT TM2 poly time, Lemmas C to E, encode or decode TM2.

  Most important thing learned: `IsPropProofSystem` must be a Type structure
  (poly witness is data); a Prop structure cannot project a non Prop field.
  gate_pending: none (merge_certified auto under loop policy after PASS).

- 2026-08-21 formalize (ProofSystem cluster 2 TT length lower bound): PARTIAL.
  Edited `ProofSystem.lean` and `Encoding.lean`. Axiom gate PASS.
  `gate_auto: true` merge_certified for new length decls.

  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "formalize",
    "target": "truthTableProofSystem_length_ge via tautSeedAt family",
    "rationale": "Close the combinatorial half of not poly bounded without TM2."
  }
  ```

  Accepted: `length_ge_snd_of_decodePair`, `tautSeedAt` family, length identities,
  `truthTableProofSystem_length_ge` (`2^(k+1) ≤ |π|` for outputs of `tautSeedAt k`).

  Frontier unchanged: `truthTable_not_poly_bounded` (needs poly versus exp),
  `truthTable_is_prop_proof_system` (TM2).

  Most important thing learned: pair decode length lower bound by induction on
  the first component avoids fragile `encodePair` left inverse proofs.
  gate_pending: none.

- 2026-08-21 prove (pin poly versus exp for not_poly_bounded): PARTIAL.
  Prose only after a formalize attempt on Real asymptotics stalled (import and
  cast friction). Length lower bound already accepted.

  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "prove",
    "target": "pin exists_const_mul_pow_lt_two_pow then truthTable_not_poly_bounded",
    "rationale": "Cluster 2 left only poly versus exponential growth between length_ge and not_poly_bounded."
  }
  ```

  ### Argument

  Goal: `¬ PolynomiallyBounded truthTableProofSystem`.

  Assume `∃ q, ∀ φ ∈ TAUT, ∃ π, f(π)=φ ∧ |π| ≤ q.eval |φ|`.
  For `k ≥ 1` let `φ_k = encodeFormula (tautSeedAt k)`. Then `|φ_k| = 2k+10`
  and any proof satisfies `|π| ≥ 2^(k+1)` by
  `truthTableProofSystem_length_ge`.

  So it is enough to produce `k ≥ 1` with `q.eval (2k+10) < 2^(k+1)`.

  Lemma (Nat): for all `A d`, eventually `A * n^d < 2^n`.
  Proof plan: induct on `d`. Base `d = 0` uses `A < 2^n` for `n > A` via
  `Nat.lt_two_pow_self`. Succ step: reduce to the claim for degree `d` after
  the bound `2k+10 ≤ 3(k+1)` for `k ≥ 10`, so
  `C * (2k+10)^d ≤ (C * 3^d) * (k+1)^d`, then apply the lemma at `n = k+1`.

  Polynomial bound: `q.eval n ≤ C * n^deg` for `n ≥ 1` with
  `C = ∑ coeffs` (each `n^i ≤ n^deg`).

  Then `truthTable_not_poly_bounded` is immediate from length_ge plus the lemma.

  Prefer pure Nat induction (no Real `isLittleO`) on the next formalize.

  ### Gap list

  1. Complete Nat induction for `exists_const_mul_pow_lt_two_pow`. Gap class: routine.
  2. Wire `eval_le_sum_coeff_mul_pow`. Gap class: routine.
  3. TM2 poly witness for TT map. Gap class: hard.

  Most important thing learned: avoid Real asymptotics for this Nat growth fact;
  the cast path burned a cycle without landing the certificate.
  gate_pending: none (accept_prose auto under loop: plan matches critical path).

- 2026-08-21 formalize (truthTable_not_poly_bounded): DONE.
  Closed ProofSystem cluster 3 with pure Nat log growth (no Real isLittleO).
  Accepted: sq_lt_two_pow, exists_const_mul_lt_two_pow, exists_log_mul_lt,
  log_mul_le_add_one, log_pow_le_add, exists_const_mul_pow_lt_two_pow,
  Polynomial.eval_le_sum_coeff_mul_pow,
  Polynomial.exists_eval_two_k_ten_lt_two_pow, truthTable_not_poly_bounded.
  Axiom gate PASS. Remaining Frontier: truthTable_is_prop_proof_system (TM2).
  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "formalize",
    "target": "exists_const_mul_pow_lt_two_pow plus truthTable_not_poly_bounded",
    "rationale": "Prove pin accepted; close not poly bounded without TM2."
  }
  ```
  gate_pending: none.

- 2026-08-21 prove (pin TM2 poly time for truthTableProofSystem): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "prove",
    "target": "pin TM2 poly time witness plan for truthTable_is_prop_proof_system",
    "rationale": "Semantic map and not poly bounded are accepted; only FinTM2 poly time remains."
  }
  ```

  ### Argument

  Goal: `Nonempty (IsPropProofSystem truthTableProofSystem)`, which reduces to
  producing `TM2ComputableInPolyTime idBitEnc idBitEnc truthTableProofSystem`.
  Soundness and completeness are already accepted.

  Decompose the map on input π of length n:

  1. Run `decodePair π`. Pairing decode walks a length prefix then splits the
     tape. Existing Encoding lemmas (`decodePair_encodePair`,
     `length_ge_snd_of_decodePair`) pin the format. Implement as a FinTM2 that
     scans once and writes the two halves to stacks. Time O(n).

  2. On failure, output `encodeFormula tautSeed` (constant size). Constant
     output machines are already certified in Complexity
     (`constBitComputableInPolyTime` pattern). Time O(1) after decode fail.

  3. On success with (φCode, table), run `decodeFormula φCode`. Fuel bounded
     decode is a single left to right scan of φCode (length ≤ n). Accepted
     round trip lemmas already lock the datatype. Time O(|φCode|) ≤ O(n).

  4. On decode failure, again emit the seed encoding (constant machine).

  5. On success with φ, decide `validatesTautology φ table`:
     a. Recompute `truthTableOf φ` by enumerating `allBitstrings (maxVar φ + 1)`
        and evaluating `evalOn` on each. The table length is `2^(maxVar+1)`.
        Any accepting proof that reaches this branch with a matching table has
        `|table| = 2^(maxVar+1)` and `|π| ≥ |table|`, so the enumeration is
        linear in `|π|`, not exponential in an unbound parameter.
     b. Compare recomputed bits to `table` and check all bits are true.
     Time O(|π| · |φ|) which is polynomial in n.

  6. If validation succeeds, output φCode (a prefix of π, copyable in O(n));
     else emit the seed encoding.

  Glue: sequential composition of the FinTM2 stages. Mathlib still has
  `TM2ComputableInPolyTime.comp` as `proof_wanted`. Prefer the local
  Complexity pattern already used for `compose_projFirst_bitEnc` style
  sequencers (copy stacks, run second machine, bound time by sum of
  polynomial evals). Do not wait for upstream mathlib composition.

  Suggested formalize clusters (smallest first):
  A. FinTM2 for `decodePair` to an explicit option encoding on the tape.
  B. FinTM2 for `decodeFormula` under a length fuel.
  C. FinTM2 for `validatesTautology` given φ and table already decoded.
  D. Sequencer assembling A through C into `truthTableProofSystem`, then
     package as `IsPropProofSystem`.

  Non vacuity note: once D lands, `truthTable_not_poly_bounded` plus
  `IsPropProofSystem` give a concrete exponential system, so universal claims
  over all proof systems are nonvacuous.

  ### Gap list

  1. FinTM2 implementation of decodePair. Gap class: hard (engineering).
  2. FinTM2 decodeFormula. Gap class: hard (engineering).
  3. FinTM2 validatesTautology with poly bound via `|table| ≤ n`. Gap class: hard.
  4. Local TM2 sequencer avoiding mathlib `comp` proof_wanted. Gap class: hard
     but partially charted in Complexity.
  5. Bridge theorem 1 (poly bounded system iff NP equals coNP) still untouched.
     Gap class: hard; blocked on nonvacuity only for one direction.

  Self adversarial: the poly time claim fails if validation enumerates
  assignments from maxVar alone without tying runtime to `|table|`. The plan
  insists on iterating the provided table length (or aborting when
  `|table| ≠ 2^(maxVar+1)`), so time stays poly in n.

  Most important thing learned: treat TT poly time as four FinTM2 clusters plus
  a local sequencer, not one monolithic machine and not Real asymptotics style
  shortcuts.
  gate_pending: none (accept_prose auto under loop: plan is the only remaining
  ProofSystem Frontier path and matches Complexity composition patterns).

- 2026-08-21 formalize (decodePair cluster A prep): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "formalize",
    "target": "decodePairCost plus encodeDecodePairResult and decodePairResult",
    "rationale": "Cluster A FinTM2 needs a certified linear cost and tape format first."
  }
  ```
  Accepted: decodePairCost, decodePairCost_le, encodeDecodePairResult,
  decodeDecodePairResult, decodeDecodePairResult_encode, decodePairResult,
  length_fst_le_of_decodePair, length_decodePairResult_le.
  Frontier added: decodePairResult_computableInPolyTime (actual FinTM2).
  Axiom gate PASS. Next: FinTM2 realizing decodePairResult.
  Most important thing learned: separate the Nat cost and option tape encoding
  from the FinTM2 engineering so cluster A does not stall on Stmt plumbing.
  gate_pending: none.

- 2026-08-21 formalize (prefixFalseCopy FinTM2): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "formalize",
    "target": "prefixFalseCopyComputer realizing decodePairResult on encodePair",
    "rationale": "Well formed decodePairResult is false then copy; FinTM2 for that slice unblocks cluster A."
  }
  ```
  Accepted: decodePairResult_encodePair, prefixFalseCopyComputer family,
  prefixFalseCopyComputableInPolyTime,
  decodePairResult_on_encodePair_computableInPolyTime.
  Frontier unchanged: decodePairResult_computableInPolyTime on arbitrary
  idBitEnc inputs (malformed none branch still open).
  Most important thing learned: push false onto work before copy so reverse
  yields false :: s; out first gave s ++ [false].
  gate_pending: none.

- 2026-08-21 formalize (decodePair inverse plus constTrueList): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "formalize",
    "target": "encodePair_of_decodePair and constTrueListComputableInPolyTime",
    "rationale": "Both decodePairResult branches now have FinTM2 witnesses; glue remains."
  }
  ```
  Accepted: encodePair_of_decodePair, decodePairResult_of_some,
  decodePairResult_of_none, constTrueListComputer family,
  constTrueListComputableInPolyTime.
  Next: branch FinTM2 that runs prefixFalseCopy on success and constTrueList
  on failure (closes decodePairResult_computableInPolyTime).
  gate_pending: none.

- 2026-08-21 formalize (decodePairResult branching FinTM2): SUCCESS.
  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "formalize",
    "target": "commit constTrue then branch FinTM2 for decodePairResult",
    "rationale": "Both branches exist as separate machines; only the glue remains for cluster A."
  }
  ```
  Committed prior cycle: encodePair_of_decodePair, constTrueListComputableInPolyTime.
  Accepted this cycle: decodePairResultComputer (dup, validate, success prefix
  false copy, fail emit [true]), decodePairResultComputableInPolyTime,
  decodePairResult_computableInPolyTime (moved out of Frontier).
  Axiom gate PASS. Cluster A closed.
  Next: clusters B to D toward truthTable_is_prop_proof_system (TM2 for full
  TT map), then bridge theorem 1.
  gate_pending: merge_certified.

- 2026-08-21 formalize (decodeFormulaResult cluster B prep): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "formalize",
    "target": "decodeFormulaResult option tape format for cluster B",
    "rationale": "Mirror cluster A prep before FinTM2 for decodeFormula."
  }
  ```
  Accepted: encodeDecodeFormulaResult, decodeDecodeFormulaResult,
  decodeDecodeFormulaResult_encode, decodeFormulaResult,
  decodeFormulaResult_encodeFormula, decodeFormulaResult_of_none,
  length_decodeFormulaResult_encodeFormula.
  Frontier: decodeFormulaResult_computableInPolyTime; still need
  encodeFormula_of_decodeFormula inverse then FinTM2.
  Dynamic saturday loop armed (one shot wakes until stop).
  gate_pending: none.

- 2026-08-25 formalize (encodeFormula_of_decodeFormula inverse): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "formalize",
    "target": "encodeFormula_of_decodeFormula inverse for cluster B",
    "rationale": "Tape format from prior cycle; encode inverse unblocks FinTM2 success branch copy."
  }
  ```
  Accepted: encodeNat_append_of_decodeNat,
  encodeFormula_append_of_decodeFormulaPrefixFuel,
  encodeFormula_of_decodeFormula, decodeFormulaResult_of_some,
  decodeFormulaResult_eq, decodeFormula_isSome_iff,
  length_decodeFormulaResult_le (plus prior working tree cluster B prep
  decls retained).
  Frontier unchanged: decodeFormulaResult_computableInPolyTime (FinTM2).
  Most important thing learned: fuelled prefix inverse by tag cases mirrors
  encodePair_of_decodePair and gives the false :: bs success rewrite for free.
  gate_pending: merge_certified.

- 2026-08-25 human gate: merge_certified APPROVED for encodeFormula inverse
  cluster (axiom gate PASS; decls in accepted_declarations.txt).
  Next: formalize FinTM2 success slice for decodeFormulaResult.

- 2026-08-25 formalize (decodeFormulaResult success slice FinTM2): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "formalize",
    "target": "decodeFormulaResult_on_encodeFormula via prefixFalseCopyComputer",
    "rationale": "Mirror cluster A: on encodeFormula images, output is false :: encodeFormula."
  }
  ```
  Accepted: decodeFormulaResult_on_encodeFormula_computableInPolyTime,
  decodeFormulaResult_on_encodeFormula_eq (reuses prefixFalseCopyComputer).
  Frontier: decodeFormulaResult_computableInPolyTime (branching FinTM2;
  constTrueList already covers the none output shape).
  Most important thing learned: formula success slice needs no new TM; only
  validation differs from pairs, so glue is the remaining engineering.
  gate_pending: merge_certified.

- 2026-08-25 human gate: merge_certified APPROVED for decodeFormulaResult
  success slice (axiom gate PASS; decls listed).
  Next: branching FinTM2 for full decodeFormulaResult.

- 2026-08-25 formalize (decodeFormulaResultComputer def and steps): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "formalize",
    "target": "decodeFormulaResultComputer FinTM2 with formula prefix validator steps",
    "rationale": "Success and none output TMs exist; only validation glue remains for cluster B."
  }
  ```
  Accepted: DFRStack, DFRLabel, decodeFormulaResultComputer, dfrStk, dfrCfg,
  all dfr_step_* lemmas, decodeFormulaResult_initList,
  decodeFormulaResult_haltList.
  Frontier: multi step evals then decodeFormulaResult_computableInPolyTime.
  Most important thing learned: FinTM2 σ must stay finite, so formula descent
  uses an aux marker stack (sibling versus not) rather than a Nat fuel in σ.
  gate_pending: merge_certified.

- 2026-08-25 human gate: merge_certified APPROVED for DFR machine and steps
  (axiom gate PASS; decls listed).
  Next: multi step evals toward decodeFormulaResult_computableInPolyTime.

- 2026-08-25 formalize (DFR multi-step evals success path): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "formalize",
    "target": "dfr_evals scaffolding plus parse_formula and on_encodeFormula",
    "rationale": "Step lemmas exist; multi step evals unlock the polyTime witness."
  }
  ```
  Accepted: dfr_evals_dup through fail_from_clearInp, dfrParseCost,
  parseNat and tag helpers, dfr_evals_parse_formula (induction),
  dfr_evals_parse_encodeFormula, dfr_evals_on_encodeFormula,
  dfr_evals_on_nil.
  Frontier: dfr_evals_parse_none for arbitrary decodeFormula none, then
  decodeFormulaResult_computableInPolyTime.
  Most important thing learned: EvalsToInTime.trans returns m2 + m1, so cost
  casts need heq ▸ h rather than simpa on add_comm alone.
  gate_pending: merge_certified.

- 2026-08-25 human gate: merge_certified APPROVED for DFR success path evals
  (axiom gate PASS; decls listed).
  Next: dfr_evals_parse_none then decodeFormulaResult_computableInPolyTime.

- 2026-08-25 formalize (clearAuxFail plus junk suffix fail): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r5-cook-reckhow-bridge",
    "action_type": "formalize",
    "target": "clearAuxFail on fail path and dfr_evals_on_none_of_junk",
    "rationale": "Mid parse failure left markers on aux; junk suffix is the easy none half."
  }
  ```
  Accepted: clearAuxFail label and steps, clearAuxFail evals, generalized
  fail_from_clearInp (clears inp work aux), dfr_evals_checkWork_junk_one,
  dfr_evals_on_encodeFormula_junk, dfr_evals_on_none_of_junk; on_nil cost
  updated.
  Frontier: prefix none parse_fail, then decodeFormulaResult_computableInPolyTime.
  Most important thing learned: fail path must clear the marker stack or
  haltList lies about empty aux after nested and or not failures.
  gate_pending: merge_certified.
