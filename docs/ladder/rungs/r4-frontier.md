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

## Literature (1D.1, 2026-10-08)

Recorded from working knowledge; entries marked (verify) need a citation check against the
papers before they are used in a certified statement. Maciel–Pitassi–Woods, Garlík–Kołodziejczyk,
the Res(⊕) entries and Impagliazzo–Mouli–Pitassi were checked against abstracts and search
results on 2026-10-09 (see below); this is a citation check, not a read of the full papers.

Circuits.
- Razborov 1987 (AC0[⊕] majority); Smolensky 1987 (AC0[p] cannot compute MOD_q, q ≠ p^k).
  Certified analogue here: `smolensky_parity` (odd p).

Bounded depth Frege.
- Ajtai 1988 (PHP superpolynomial); Pitassi–Beame–Impagliazzo 1993 and Krajíček–Pudlák–Woods
  1995 (exponential, k-evaluations / matching switching). Certified here:
  `php_bdfrege_superpoly` (super polynomial, mod free).
- Ben-Sasson 2002, Pitassi–Rossman–Servedio–Tan 2016, Håstad 2017/2021 (Tseitin on grids and
  expanders for bounded depth Frege).

Algebraic systems.
- Beame–Impagliazzo–Krajíček–Pitassi–Pudlák 1994 (Nullstellensatz degree, designs).
- Buss–Impagliazzo–Krajíček–Pudlák–Razborov–Sgall 1996/97: Count_q needs exponential size in
  bounded depth Frege with Count_p axioms (q not a power of p), via Nullstellensatz degree.
  This is item 1D.2.
- Clegg–Edmonds–Impagliazzo 1996 (polynomial calculus); Razborov 1998 (PHP degree);
  Impagliazzo–Pudlák–Sgall 1999 (size–degree; certified: `MLPC.ips`);
  Buss–Grigoriev–Impagliazzo–Pitassi 2001 (Tseitin mod q linear degree over F_p; certified:
  `tseitin_bool_degree_Fp`, `tseitin_ml_size`); Alekhnovich–Razborov 2001/03 (expanding
  systems, non binomial case).

AC0[p] Frege and subsystems (the R4 frontier).
- Super polynomial AC0[p] Frege lower bounds: open (Razborov, Krajíček surveys; Buss list of
  open problems).
- Maciel–Pitassi–Woods, "A New Proof of the Weak Pigeonhole Principle" (STOC 2000; journal
  version 2002 not confirmed): quasi-polynomial size bounded depth proofs of weak PHP. Earlier
  entry said "AC0[p]-type proofs"; no AC0[p] content was found in the paper (checked 2026-10-09
  from search snippets only). Maciel–Pitassi separately give a quasi-polynomial simulation of
  AC0[p] proof systems by depth 3 threshold proofs (not re-checked).
- Garlík–Kołodziejczyk, "Some subsystems of constant-depth Frege with parity", ACM TOCL 19(4),
  29:1-29:34 (2018): confirmed. Tree-like PK(⊕) is quasi-polynomially equivalent to constant
  depth Frege with parity axioms; superpolynomial separation of dag-like PK(⊕) from AC0[2]-Frege;
  exponential lower bound for a system containing an extension of tree-like Res(lin).
- Res(⊕) (resolution over parities, the depth 1 case for p = 2), checked 2026-10-09:
  - Tree-like: Itsykson–Sokolov, "Resolution over linear equations modulo two", Ann. Pure Appl.
    Logic 171(1), 102722 (2020) (earlier MFCS 2014 version): exponential tree-like bounds
    (2-fold Tseitin, PHP encodings); Res and tree-like Res(⊕) are incomparable. Weak bit PHP
    tree-like 2^{Ω(n)}: Efremenko–Garlík–Itsykson.
  - Regular: Efremenko–Garlík–Itsykson, STOC 2024 (ECCC TR23-187; SIAM J. Comput. 54(4), 2025):
    regular Res(⊕) refutations of bit PHP with n+1 pigeons need size 2^{Ω(n^{1/3}/log n)}.
  - Regular vs general: Bhattacharya–Chattopadhyay–Dvořák, CCC 2024 (arXiv 2402.04364): formulas
    with polynomial size resolution proofs (depth O(√n)) that need regular Res(⊕) size
    2^{Ω(√n)}. This is a separation, not a bounded depth result (earlier entry corrected).
  - Lifting: Alekseev–Itsykson, "Lifting to Bounded-Depth and Regular Resolutions over Parities
    via Games", STOC 2025 (ECCC TR24-128): resolution width w lifted by a 1-stifling gadget
    (Maj3) gives Res(⊕) rank ≥ w; exponential regular bound with Maj5; exponential bound for
    depth ≤ c·N log log N.
  - Bounded depth, larger depth: Efremenko–Itsykson (depth O(N log N)); Bhattacharya–Chattopadhyay
    (arXiv 2507.23008): Tseitin on expanders with inner product gadget, size exp(Ω~(N^ε)) at
    depth O(N^{2-ε}); Byramji–Impagliazzo (arXiv 2511.20023): bit PHP and t-BPHP in bounded
    depth Res(⊕); Itsykson–Podolskii–Shekhovtsov, CCC 2026 (ECCC TR26-018): width lifts to
    quadratic size for unrestricted Res(⊕); Itsykson–Knop, ITCS 2026 (supercritical size/depth
    tradeoff).
  - Unrestricted dag-like Res(⊕): a claimed exponential lower bound for bit PHP, Braun,
    arXiv 2609.23015 (19 Sep 2026), size > exp(n/(32768 ℓ²)) for n = 2^ℓ holes, ℓ ≥ 32. Single
    author, AI-assisted, not peer reviewed, with a claimed Lean 4 formalization that this
    project has not yet built or independently checked. Treat as unconfirmed. Earlier text
    "open as far as recorded here" is superseded by this entry.
- Barriers: Impagliazzo–Mouli–Pitassi, "The Surprising Power of Constant Depth Algebraic
  Proofs", LICS 2020 (ECCC TR19-024), not CCC (AC0[p] Frege vs IPS fragments) and
  Grochow–Pitassi 2014 (IPS; not re-checked); Pich–Santhanam style natural-proof-like barriers
  for proof systems (not found / not checked, still (verify)). These feed the Phase 3.1 barrier
  audit.
- 2026-10-08 formalize (Phase 1A.7): `smolensky_mod3` certified (Smolensky2.lean): AC0[2]
  circuits computing MOD_3 need super polynomial size. Two inputs fixed to constants give the
  three residue circuits; over `F_4` with `y = ω^x`, `∏ y_i = ω^{|x|}` is a combination of the
  three residue approximations and `y⁻¹ = y²` is affine in `x`.
- 2026-10-08 formalize (Phase 1D.3): tree-like Res(⊕) lower bound certified (ResLin.lean):
  `treelike_reslin_php`: every tree-like Res(⊕) refutation of `PHP_n ∘ MAJ₃` has `≥ 2^n` axiom
  leaves. Route: refutation → parity decision tree (`tree_to_pdt`); stifling simulation keeps an
  affine parametrisation of solutions with stifled blocks fixed by a PHP matching adversary;
  every non constant query splits it, and a leaf needs `n` base queries. Dag-like (regular,
  bounded depth, general) Res(⊕) remain beyond this: general Res(⊕) is Phase 2.1.
- 2026-10-09 formalize (Phase 1D.2): Count_q lower bound for bounded depth Frege with Count_p
  axioms certified (`QP.countq_bdfrege_exp`, CountQ.lean): for a prime `p ∤ q`, `q ≥ 2`,
  every mod free depth `d` refutation of `countqCNF q N` in the sequent calculus plus all
  Count_p^M instances (`p ∤ M`, arbitrary formulas) has size `≥ 2^K / 8`, with
  `K = ⌊M^{1/(p+q+2)}⌋`, `M = ⌊N^{1/(q²+q+5)^{d+1}}⌋`. Route (modules QPart, Designs,
  CountMass, QSwitch, QTree, QKEval, QLevel, CountQ): tree valued k-evaluations over partial
  q-partition restrictions (q-analog of the PHP pipeline, with a Razborov encoding switching
  lemma using local point indices); Count_p instance lines are made sound by a design mass
  argument (`count_mass_false`): masses of the `1`-branches around each point sum to one, so
  `M = p Σ π_g = 0` in `ZMod p`; designs of degree `2^i - 1` exist on every universe of
  `≥ (p+q)^i q` points by the BIKPPRS Lemma 4.3 doubling (`stepD`, via a symmetry lemma over
  selections and an isolated-edge counting argument), padding and transport. Non vacuity:
  `countq_unsat`, `countSeq_valid`, `countq_refutable`.
- 2026-10-12 formalize (MAJ3 lifting warm-up, step 4; LiftDup.lean, LiftPHP.lean): a base
  Duplicator family `BaseDup F0 W G` on block sets lifts through MAJ3 to a Res(⊕) Duplicator
  (`hset_duplicator`; realizability by `solve_closure`, closure by `Closure.cl`, rank bound by the
  closure size), hence `maj3_lifting`/`maj3_lifting_rank`: no dag-like Res(⊕) refutation of
  `F0 ∘ MAJ3` has all lines of rank `≤ W`. Instance `php_maj3_rank`: every dag-like refutation of
  `PHP_n ∘ MAJ3` has a line of rank `≥ n - 1`. Caveat: the wide PHP axioms already have rank `2n`,
  so this instance is weak; the general theorem is meant for narrow encodings and size bounds
  need a further step (rank to size, Itsykson–Podolskii–Shekhovtsov or regular/depth variants).
- 2026-10-12 formalize (Phase 2.1, Braun port layer 0; BraunDag.lean): plan in
  `r4-braun-port-plan.md`. Ported K. Braun's finite affine clause DAG calculus (arXiv 2609.23015;
  credited in the docstring) as `Braun.PClause/PStep/PDag`, with the dictionary to our
  `LClause` (`toP`, `holds_toP`), `dag_to_pdag` (our `DagRefutes` with `s` lines gives a `PDag`
  with at most `s` nodes ending in the empty clause), `bphp_dag_to_pdag` (axioms of `bphpCNF` land
  in his `usualInitials`), and `BraunBitPHP` (his theorem as a Prop, not assumed) with
  `braun_implies_dag_lb`. The bound itself is not yet reproved (next: plan layers 1 and 2).
- 2026-10-13 docs status (Phase 2.1): Braun port layers 1 to 5 and 7 are merged, and layer 6
  part 1 (matching normal form, moment completeness, chains, cycles, relabeling, extension,
  filtration, cube residual dual separation) is merged, and the chessboard homology now proves
  `MatchingMomentFilling` (`matchingMomentFilling`); layer 8 remains, and `BraunBitPHP` is
  not yet proved. Details and line counts in `r4-braun-port-plan.md`. Phase 1 is complete; R4
  itself stays active and uncertified.
- 2026-10-13 formalize (Phase 2.2, Part-Tzameret tree-like Res(lin F_p) for Tseitin mod q; plan in
  `r4-phase22-plan.md`): layers 1, 2 and the width half of the assembly are in. ResLinF.lean:
  tree-like Res(lin F) derivations over a field with soundness (`rld_sound`). ResLinFPC.lean:
  Theorem 45, width `w` gives polynomial calculus degree `w + 1` (`rld_to_pcd₀`, `rld_cnf_pcd`).
  ResLinTseitin.lean: `reslin_tseitin_width`, every Res(lin F_p) tree-like refutation of the one
  hot Tseitin mod q CNF on the cubic expanders (p prime, p not dividing q) has width linear in
  the number of vertices. Not yet proved: the tree-like size-width relation (Theorem 44), so no
  size bound yet. Caveats: one hot formula, not the paper's Boolean edge variable formula; the
  combination rule carries a side condition (paper's Case 4 does not treat the resolvent already
  occurring in the side clauses). Rung stays active and uncertified.
