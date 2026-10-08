# R4: The Open Frontier

Status: active
Lean home: theory/Theory/ProofComplexity/AC0pFrege.lean (Frontier: AC0pFregeFrontier)

## Statement

A super-polynomial lower bound for a propositional proof system with no known
super-polynomial lower bounds. Ordered subtargets:

1. AC0[p]-Frege: bounded-depth Frege with mod-p counting gates. Open since the late
   1980s although the circuit analogue (Razborov-Smolensky) is known. Candidate hard
   families: Count(q) principles against mod q' reasoning, Tseitin over expanders.
2. TC0-Frege.
3. Frege.
4. Extended Frege.

## Why this rung

This is the research frontier where new mathematics is required. Everything below
it is training and machinery; everything above it is the summit.

## Falsification tests

T4.1: for each candidate family and system, literature check plus bounded empirical
search for short proofs in simulable fragments; quasi-polynomial upper bounds kill
the family for that rung.
T4.2: every proposed argument names the proof-system property it exploits and
passes the barrier audit before formalization effort is spent.

## Barrier notes (the real walls)

- Interpolation unavailable (dies below this level).
- Krajicek generators and Razborov conjectures: strong-system lower bounds may
  require breaking cryptographic assumptions; every candidate argument must state
  why it does not implicitly construct a distinguisher for a standard pseudorandom
  object.
- Simulation order: an AC0[p]-Frege bound says nothing about TC0-Frege and above;
  each subtarget is its own wall.

## Session log (append-only)

- 2026-08-03 reboot: rung proposed. No active candidate argument. Prose search
  begins after R1 certification; empirical calibration may start earlier.
- 2026-10-08 adopt (operator "go"): first subtarget AC0[p] Frege. Lean surface certified
  in AC0pFrege.lean: formulas with MOD_p connectives (`Fm`), a dag like sequent calculus with
  MOD_p defining axioms (`FRefutes p d F L`), soundness (`frefutes_unsat`), and the non
  vacuity witness: every unsatisfiable CNF has a depth one refutation, by simulating
  resolution (`frefutes_of_unsat`). Locked target: `AC0pFregeFrontier.r4_target :
  ∀ p prime, AC0pFregeLB p` (some polynomial size unsatisfiable family needs super
  polynomial size refutations at every fixed depth). Primary candidate families: Tseitin
  mod q on expanders (q ≠ p), Count_q, onto PHP, random k CNF.
  Kill conditions: (T4.1) a quasi polynomial size AC0[p] Frege refutation of a candidate
  family kills that family; (T4.2) an argument that would also separate systems known
  to be equal, give a lower bound for a system with known short proofs of the family, or
  break a standard pseudorandom generator assumption fails the barrier audit. Three failed
  attempts on one method kill that method branch.
  Plan and checklist: docs/ladder/r4-research-plan.md, docs/ladder/r4-completion-checklist.md.
- 2026-10-08 formalize (Phase 1A): Smolensky's theorem certified, `smolensky_parity`: for an
  odd prime `p` and every depth `d`, AC0[p] circuits computing parity need super polynomial
  size. Pieces: OR approximation by random subset sums (`exists_good_choice`), circuit
  approximation (`circuit_approx`), `±1` Fourier expansion over F_p (`fourier`), the
  agreement set count (`agree_card_le`), central binomial bound. This is the circuit analogue
  of the R4 target; the proof analogue needs a different idea (the approximation does not
  transfer to proofs directly).
- 2026-10-08 formalize (Phase 1B.1-1B.2): Håstad's switching lemma certified,
  `switching_lemma` (Switching.lean): for a DNF of width `w` with consistent terms, the
  restrictions with `ℓ` stars whose canonical decision tree has depth `≥ s` number at most
  `|R^{ℓ-s}| (4w)^s`. Proof by Razborov's encoding: `encode` builds, for each bad
  restriction, an extension with `s` fewer stars and a code (blocks of positions inside
  terms plus answers) from which `dec` recovers it; `codes_card` bounds the codes by `(4w)^s`.
- 2026-10-08 formalize (Phase 1B.3): PHP switching lemma certified (Matching.lean,
  MatchingSwitch.lean). Canonical matching decision trees with block queries (`mdepth`,
  counting term edges); `cover_of_mdepth` (a depth `s` tree decides the DNF along a branch of at
  most `2 s` edges compatible with any free matching that leaves room); `mencode`/`mdec`
  encoding with partner codes relative to the image restriction; `mswitching_ratio`:
  `#bad · (m + 1 - |ρ0|)^s ≤ #R_m · ((|P| - m)(|H| - m) · 2 w C²)^s`.
- 2026-10-08 formalize (Phase 1B.4): k-evaluations certified (KEval.lean, PHPKEval.lean; uses the R1 `phpCNF`). Each
  sequent is read as its line formula `OR(¬Γ, Δ)`; an evaluation gives true/false branch sets
  (free partial matchings of size `≤ k`) with incompatibility, coverage (room `|π| + 3k ≤ ℓ`)
  and connective conditions. `keval_no_refutation`: with `5k ≤ ℓ` and all PHP clauses hit
  (`php_clauseHit`), no mod free proof contains the empty sequent.
- 2026-10-08 formalize (Phase 1B.5): bounded depth Frege PHP lower bound certified,
  `php_bdfrege_superpoly` (PHPFrege.lean): for every depth `d` and exponent `c`, for all large
  `n`, every mod free depth `d` refutation of `phpCNF n` in the R4 sequent calculus has size
  `> n^c`. Construction (KEvalBuild.lean): restriction of evaluations (`good_res`), depth zero
  base (`good_E0`), canonical step from shallow matching trees (`level_step`); union bound over
  random matching extensions (`exists_shallow_ext`) iterated over `d + 1` levels (`levels`)
  with free hole counts `M^{7^{T-t}}`, `s = 2·7^T·c + 2`, `k = 2s`. This is the mod free special
  case of the R4 target for PHP; the MOD_p axioms are exactly what the method cannot handle.
- 2026-10-08 formalize (Phase 1C.1-1C.2): polynomial calculus (PolyCalc.lean: `PCD`, `PCD₀`,
  soundness) and the Tseitin mod q degree lower bound in the binomial encoding
  (TseitinPC.lean): R-operator sending a monomial to its phase times the minimum degree
  monomial of its class modulo coboundaries; expansion gives unique small potentials, so the
  phase is additive on small vectors. Linear degree on the R2 cubic MGG expanders
  (`tseitin_pc_degree_cubic`). Open sub item 1C.2b: transfer to the Boolean one hot encoding
  over F_p.
- 2026-10-08 formalize (Phase 1C.2b): Boolean one hot Tseitin mod q over F_p certified
  (TseitinBool.lean, `tseitin_bool_degree_Fp`): linear PC degree on cubic expanders for every
  prime `p ∤ q`. Route: substitute Lagrange indicators over `CyclotomicField q F_p`, derive the
  clause images from `y_e^q - 1` and the vertex binomials by the Combinatorial
  Nullstellensatz, then apply the binomial bound.
- 2026-10-08 formalize (Phase 1C.3): size–degree tradeoff and exponential PC size for Tseitin
  mod q over F_p certified (PCSizeDegree.lean, TseitinSize.lean). Multilinear polynomials as
  `Finset ℕ →₀ F`; restrictions are combinatorial; `ips` restricts a variable occurring in many
  fat monomials, combining the two branches with `+2` degree on the killing branch.
  `tseitin_ml_size`: size `≥ 2^m`, `m = E / (2(|V|/E + 1))`, `E` a third of the linear degree
  bound. Phase 1C is complete: Tseitin mod q, a primary R4 candidate, is exponentially hard for
  polynomial calculus over F_p (the algebraic part of AC0[p] Frege lower bound attempts).
