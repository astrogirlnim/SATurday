# R4 Phase 3.1: barrier audit, red team, and a scoped attempt on 2.4

Status: docs only. No Lean, no builds beyond the merge gate. Date 2026-10-27, branch r4/phase31-barrier-audit.
Reads: r4-frontier.md (T4.1, T4.2, barrier notes), r4-new-math-program.md, r4-phase23-{plan,analysis,program,c1,r3,killtest,overlap}.md,
statement-fidelity-dossier.md (sections 0, 6, 7, 10 to 17).

## 0. Plain statement of the situation

1. Super-polynomial lower bounds for AC0[p]-Frege, at any fixed depth including depth 2, are a long-standing open problem
   (open since the late 1980s; the circuit analogue is Razborov-Smolensky). This project has not proved one, has no candidate
   proof, and does not claim progress on it. Nothing below changes that.
2. Board card 3.1 says "Prose proof survives barrier audit and red team". There is no prose proof of the R4 target, so the card in
   its literal form cannot be completed. What can be done, and is done here, is an audit of every result that exists and of the
   best candidate routes, so that the next effort is not spent on a dead route. The card therefore stays in Todo with a note.
3. Labels: LEAN (machine checked in this repo, per the dossier), HAND (derived on paper in an earlier note, not machine checked),
   COMPUTED (a script in this repo), CITED-CHECKED (an earlier note or this session read an abstract), CITED-UNCHECKED
   (recalled, not verified), CONJECTURE (my judgment).

## 1. The audit questions (T4.2, made concrete)

For each argument I ask four things.

- Q0 What does it exploit? Name the property of the proof system or of the formula that the proof uses.
- Q1 Equal systems: would the argument separate two systems known to be polynomially equivalent? Test: does it survive the
  size-controlled embeddings of dossier section 16, and does it stay stated for the system, not for one presentation?
- Q2 Short-proof control: does the argument give a lower bound for a formula that has short proofs in the system? Controls used:
  Tseitin mod p over F_p (same modulus, constant PC degree, short Res(lin F_p) proofs); Count_p with Count_p axioms (the axiom
  itself); Tseitin of bounded cutwidth (ladders, polynomial size, COMPUTED by ub_probe.py: PC degree constant); weak PHP with
  at least 2n pigeons (quasi-polynomial bounded depth Frege proofs, Maciel-Pitassi-Woods, CITED-CHECKED to abstract level).
- Q3 Pseudorandomness: does the argument implicitly distinguish a pseudorandom object? Concrete form for AC0[p]: by
  Smolensky, MOD_q (q not a power of p) is average-case hard for AC0[p], and the Nisan-Wigderson construction then gives
  generators fooling AC0[p] circuits with quasi-polynomial seed (standard, CITED-UNCHECKED). So an argument that, run on a
  restricted proof system, yields an AC0[p] circuit distinguishing such a generator from random is impossible. This is a useful
  sharp test for any argument at depth d >= 2 that extracts a circuit from a proof. For depth 1 systems (Res(lin F_p)) feasible
  interpolation holds, so circuit-extraction arguments are not suspicious there; for bounded depth with MOD gates feasible
  interpolation fails under assumptions (Bonet-Pitassi-Raz and descendants, CITED-UNCHECKED), which is the closed door.

## 2. Audit of each proved result

None of these is a bound for AC0[p]-Frege. Each is a bound for a different, weaker or bespoke system. The audit says what each
one rests on and whether it can be reused for the target.

| Result (Lean) | System | Exploits (Q0) | Q1 equal systems | Q2 control | Q3 | Verdict for reuse at AC0[p] |
|---|---|---|---|---|---|---|
| smolensky_parity, smolensky_mod3 (LEAN) | AC0[p] circuits | low degree F_p approximation | not a proof system | n/a | consistent with the NW remark above | Circuit analogue only. The approximation does not transfer to proofs because error sets must be controlled on axiom-satisfying points only. DEAD as a direct route (HAND, program sec 1 item 1) |
| php_bdfrege_superpoly (LEAN) | bounded depth Frege, no MOD gates | switching lemma, k-evaluations | stated for the sequent calculus; standard | PHP has no short bounded depth proofs (this result); weak PHP with 2n pigeons is outside the statement (it is for n+1 pigeons) | AC0 side, no issue | DEAD for MOD gates: a MOD_p gate of m inputs stays a MOD_p gate after a restriction, so depth does not drop (HAND, program sec 1 item 2) |
| countq_bdfrege_exp (LEAN) | bounded depth Frege plus Count_p axioms, p not dividing q | k-evaluations, designs, mass argument | standard | Built in: the mass argument `count_mass_false` fails exactly when the axiom modulus equals the formula modulus, so Count_p with Count_p axioms is not covered | AC0-type | This is axioms as extra assumptions, not MOD_p connectives inside formulas. The gap between the two is the open problem. DEAD as a route, ALIVE as the nearest solved neighbor |
| tseitin_bool_degree_Fp, tseitin_ml_size (LEAN) | polynomial calculus over F_p | R-operator, expansion, Combinatorial Nullstellensatz over a cyclotomic field | PC over F_p; multilinear/one-hot conventions are stated | Passes: needs p not dividing q (a primitive q-th root of unity must not collapse); Tseitin mod p has constant degree | none | Degree-based, stays at depth 0 of the proof-system hierarchy. Feeds Pang, nothing else |
| treelike_reslin_php (LEAN) | tree-like Res(xor) on PHP composed with MAJ3 | stifling gadget, parity decision tree | tree-like only; tree-like and dag-like Res(xor) are incomparable (Itsykson-Sokolov, CITED-CHECKED), so no contradiction, but no transfer | formula is the composed PHP, not PHP | none | Tree-like is far from dag-like. DEAD as a route |
| reslin_tseitin_width, reslin_tseitin_size (LEAN) | tree-like Res(lin F_p) | PC degree vs width (Theorem 45), size-width (Theorem 44 route) | factor 2 embedding to RLDag and back (dossier 16) | Passes: p must not divide q | none | Tree-like again. Fine as a result, no route |
| lifting: maj3_lifting, php_maj3_rank (LEAN) | dag-like Res(xor), rank measure | Duplicator through a 1-stifling gadget | rank, not size | the PHP instance is weak (axioms already rank 2n, dossier) | none | Alive as a method for Res(xor) only; see route R6 below |
| Braun bit PHP, bphp_dag_exponential (LEAN, source unrefereed and AI-assisted) | dag-like Res(xor) | common-multiplier / chessboard homology | semantic weakening vs syntactic: factor 3 and 1 (dossier 16) | Not run: the statement is for N+1 pigeons; whether the argument degrades with more pigeons is unchecked and is the right Q2 control | none | Superseded by Pang for bit PHP. DEAD as a route to depth 2 (same rank-1 setting as Pang) |
| Pang tseitin_dag_exp, Khaniki dag bound, AR chain (LEAN; Pang and Khaniki shapes per dossier) | dag-like Res(lin F_p), depth 1 | PC degree D lower bound, rank shrinkage of approximants, common multiplier by a dimension count in V_K modulo C_D | RLDag and Pang.Refutation are equal up to factor 2 (dossier 16): Q1 passes | Passes: for q = p the PC degree is constant and the hypothesis D >= 8w fails; weak PHP not applicable (width) | Depth 1 has feasible interpolation, no barrier flag | The one real method. Its depth-2 extension is route R1 below |
| C1.c1_main (LEAN) | the bespoke semantic calculus R_rho^p with rho <= eps log n | Pang's method at rank eps log n | not a Cook-Reckhow system (dossier 7.1a); no embedding of Pang.Refutation or of AC0[p]-Frege into it exists | Not run: upper bounds (existence of refutations) in R_rho^p are not formalized, so the control that Tseitin mod p refutes cheaply in R_rho^p is unchecked | none | Red team: this result is evidence of nothing about AC0[p]-Frege. A semantic calculus with log rank is a defined restriction. FAILS the "bridge theorem" test: no translation from depth-d proofs with controlled rank exists |
| Embeddings, indexed families (LEAN) | bookkeeping | none | These are the Q1 evidence for the rows above | n/a | n/a | No barrier content |

Red-team notes on the numbers (from the dossier, restated so the audit is self-contained):

- Every Tseitin theorem has shape E (for all N there exists n at least N) unless the indexed version is used; padding to every n is
  not formalized. The R4 target has shape U.
- The Pang bound is non-vacuous only for n above about 2.3 times 10 to the 16 (dossier section 14). It is an asymptotic statement,
  not a statement about any feasible instance.
- Bit PHP bounds are exponential in the number of holes N, which is exp(L^(1/3 - o(1))) in the input length, not exp(Omega(L)).
- Three source papers (Braun, Pang, and the Krajicek preprints cited below) are unrefereed arXiv preprints, two of them with
  disclosed AI assistance. The Lean check removes the need to trust their proofs, not their statements.
- Existence of refutations (the upper bound side) is formalized only for bit PHP in dag-like Res(xor).

## 3. Candidate families for the target: alive or dead

| Family | Status as a hard family for constant depth AC0[p]-Frege | Why |
|---|---|---|
| Tseitin mod q on expanders, p not dividing q | ALIVE (no short proof known) | No quasi-polynomial AC0[p]-Frege refutation known; T4.1 not triggered. Evidence for hardness at depth 1 only |
| Tseitin mod p over F_p (same modulus) | DEAD | short Res(lin F_p) proofs (CITED-UNCHECKED, Pang 7.2, Part-Tzameret) |
| Tseitin of bounded cutwidth (ladders, grids of bounded width) | DEAD | polynomial size depth 1 algebraic proofs (COMPUTED, ub_probe.py: PC degree constant on ladders) |
| Count_q on mod p reasoning, p not dividing q | ALIVE, nothing known | short proofs not known, lower bound only with Count_p as axioms (LEAN) |
| PHP with n+1 pigeons / bit PHP | ALIVE for AC0[p]-Frege (unknown), DEAD for bounded depth Frege without MOD and for tree-like Res(xor) in the sense that bounds exist | AC0[p]-Frege proofs of PHP not known to be short or long |
| Weak PHP with 2n or more pigeons | DEAD for bounded depth Frege (quasi-polynomial upper bound, Maciel-Pitassi-Woods, abstract level); hence for AC0[p]-Frege | upper bound contains the system |
| Random k-CNF at linear density | ALIVE, no known short proofs, PC degree a small constant times n | the constant is far below the 0.467 needed by route R1 |
| Pseudorandom generator tautologies (Krajicek, Razborov style) | candidates only, hardness conditional | not an attack (program sec 1 item 7) |

## 4. Routes to constant-depth AC0[p]-Frege

Each route: what a proof would exploit, which of the T4.2 tests it passes, verdict.

R1. Extend Pang's approximation to depth 2 and then depth d (hypothesis H: a constant-width CNF with PC degree ratio D/n at
least about 0.467 over some F_p).
- Exploits: PC degree of the formula plus the shrinkage of approximants under a common multiplier (Razborov-Smolensky for proofs).
- Q1 passes (stated for dag-like systems up to factor 2). Q2 passes: the same-modulus control has constant PC degree so the
  hypothesis fails. Q3: not applicable to depth 1; at depth 2 the argument must not yield an AC0[p] circuit; no flag found.
- Why it stalls (HAND and COMPUTED, r4-phase23-*): (a) Tseitin mod 2 over odd p has PC degree at most n/4 + o(n), so H fails for
  the whole Tseitin family and for all XOR systems (sketch; rounding caveat in program sec 2.5). (b) No other family with ratio
  above 1/4 is known. (c) Even with H, the per-round loss is theta_1 ~ (K/n)^rho, which forces rank rho = O(log n) (killtest and
  overlap notes, COMPUTED at n at most 18).
- Verdict: DEAD for Tseitin. Alive only as a conditional shell on an unknown family. Rating from earlier notes: under 3 percent.

R2. Raise the rank barrier with a better measure (rank n^c instead of eps log n).
- Exploits: the exact structure of the line space instead of the Hilbert ratio of V_K.
- Q1, Q2 as R1. Same wall as Res(k) beyond log n (a known open direction without MOD gates).
- Sub-routes: block-aligned subspace W_K (tested: saturates to 88 to 95 percent of V_{K+t rho} for rho = 2, program sec 3):
  DEAD in the adversarial regime. Fourier/cohomological quotient for Tseitin (program D3): untested; the only sub-route that uses
  Tseitin structure.
- Verdict: ALIVE only as D3, odds about 3 percent (CONJECTURE).

R3. Switching lemma / k-evaluations for MOD_p gates.
- Verdict: DEAD. A MOD_p gate of fan-in m is not simplified by fixing a random subset; its decision tree depth is m. This is the same
  wall as for circuits, where restrictions are replaced by approximation (HAND, structural).

R4. Feasible interpolation, or any circuit-extraction argument.
- Verdict: DEAD at depth 2 and above with MOD gates (Bonet-Pitassi-Raz and descendants, CITED-UNCHECKED). It also fails Q3 in
  the following sense: if it worked it would turn proof lower bounds into circuit lower bounds only against classes where those are
  known; so it cannot give anything beyond what circuit bounds already give.

R5. Short proofs first (upper bound probe, program D1), then redirect.
- Exploits: nothing (it is a test for T4.1). A poly-size depth-2 proof family kills Tseitin as a candidate.
- Status: the depth-2 small-graph search was started and stopped by the owner on 2026-10-27 with no result. The depth 1 curve is
  COMPUTED (ladders constant degree, random cubic expanders degree about E/12.6).
- Verdict: ALIVE as a sanity check, not run. Odds that poly-size depth-2 proofs exist: about 5 percent (CONJECTURE).

R6. Lifting to formula depth (program D7; Alekseev-Itsykson STOC 2025 for Res(xor); LEAN has the MAJ3 warm-up).
- Exploits: a gadget that makes each line's relevant structure a single affine subspace, plus a Duplicator strategy.
- Q1: a bound for F composed with a gadget, not for Tseitin or PHP themselves, so equal-system and control tests apply to the
  composed family, which is not a family anyone has short-proof data for. Q3: unknown.
- Verdict: ALIVE, unexplored beyond depth 1, p = 2 only, about 4 percent.

R7. Krajicek's reduction (arXiv 1311.2501, search trees over low-degree polynomials) and pseudo-solutions (arXiv 2609.35927).
- Exploits: an equivalent search-tree formulation. No unconditional bound; the strong hypothesis would imply UENS does not
  simulate TC0-Frege, in tension with a cited remark that it simulates Extended Frege (CITED-CHECKED, abstract level).
- Verdict: a reformulation, not a method. DEAD as an attack, ALIVE as a target of study. The T4.2 reading is that any argument
  through constant-depth IPS also lands at the strength of the TC0-Frege simulations of Impagliazzo-Mouli-Pitassi (LICS 2020),
  so it must be checked against the barriers for strong systems, not just AC0[p].

R8. Hardness magnification / generator based families.
- Verdict: not routes. They give candidate families or locality warnings (program sec 1 items 7 and 8).

Summary of what is dead and what is alive.
- Dead: R1 for Tseitin, block-aligned W (R2), R3, R4, same-modulus and bounded-cutwidth families, weak PHP.
- Alive but unproved and unscored beyond a few percent: D3 (R2), R5, R6, and Tseitin mod q, Count_q, PHP and random CNF as families.
- Proved and valid for what they say, but not reusable: every row of section 2.

## 5. Scoped attempt on card 2.4 (constant-depth AC0[p]-Frege)

Rules for this attempt: at most three failed attempts per method, then the method is stopped (T4.2 session rule). Prior failures
count. Kill conditions: (K1) a quasi-polynomial AC0[p]-Frege refutation of the chosen family kills the family; (K2) a proof
that every constant-width CNF has PC degree at most (1/2 - c) n kills R1 for all families; (K3) the argument would separate equal
systems, bound a family with known short proofs, or distinguish an AC0[p]-fooling generator, and fails the audit; (K4) three
failed attempts on one method.

Method M1 (R1, Pang extension). Attempt 1 (earlier session, program sec 2): Tseitin mod 2 ratio capped at 1/4 + o(1). Failed.
Attempt 2 (this session, survey of families against the 0.467 threshold): PHP has PC degree about n/2 + 1 (Razborov, CITED-UNCHECKED
from the dossier chain) on n^2 variables, so ratio tends to 0, and clause width n violates D >= 8w; Tseitin is capped at 1/4;
random k-CNF has a small constant ratio. No family above 0.467. Failed, no new mathematics. M1 now has two recorded failures; the
owner has also closed 2.3 as a limit of this method, so a third attempt is not spent.

Method M2 (R5, upper bound first, paper side). Attempt 1 (this session, paper only): try to build a depth-2 proof of Tseitin mod q
over F_p by adding vertices one at a time and carrying the boundary residue. The line for the cut state must say "boundary sum
is c mod q"; that is a MOD_q gate over cut-size many inputs, which is exactly what Smolensky says AC0[p] cannot compute, but a
proof need not compute it, only relate consecutive states, and the number of states is q^cut for a vertex order. I did not find a
way to describe all states by few depth-2 lines. This is a failed construction, not evidence of hardness: it proves nothing about
lower bounds. M2 has one failed attempt; the exact small-graph search (the planned second attempt) was stopped by the owner.

Method M3 (R6, depth-2 lifting). Attempt 1 (this session, paper only): check whether the Duplicator invariant of the MAJ3 lifting
(a bound on the rank of the closure of the forms in one line) survives a depth-2 inference. A depth-2 line is an OR of s terms, each a
low-rank affine subspace. A single cut on such a line forces the Duplicator to commit to one disjunct, which in the base game costs
closure of size s times the rank of one term, unbounded in s although the line has size 1. So "rank at most W for every line" is
not the invariant; it would have to be a function of the number of terms, which is the Res(k) obstruction again (the same wall that
appears as (K/n)^rho for Pang). This is a heuristic failure analysis (CONJECTURE), not a theorem. Failed, one attempt.

Outcome of the 2.4 attempt: no progress on AC0[p]-Frege lower bounds. No new theorem, no new Lean, no candidate proof. Card 2.4
stays in Todo. What this session adds is a recorded list of dead routes (section 4), the control tests that every new argument must
pass (section 1), and the status of each method against the three-failures rule (M1: two, closed by the owner; M2: one; M3: one).

## 6. Literature check for 2026 (sparing; two web searches on 2026-10-27, plus the earlier recorded checks)

Question: does any 2026 result change the picture, that is, is there an unconditional super-polynomial lower bound for constant
depth AC0[p]-Frege, a new simulation that pushes it down to a known system, or a new barrier?

Findings (search tool is US-only and may not index everything; this is not a literature review).
- No 2026 result found claiming an AC0[p]-Frege lower bound at any depth.
- Impagliazzo-Mouli-Pitassi, "The Surprising Power of Constant Depth Algebraic Proofs" (LICS 2020, ECCC TR19-024,
  https://eccc.weizmann.ac.il/report/2019/024): constant-depth IPS over F_p quasi-polynomially simulates AC0[p]-Frege and also
  TC0-Frege, per the search snippet. The relevance to the audit is the T4.2 remark in R7. Read at snippet level only.
- Alekseev-Itsykson (ECCC TR24-128, https://eccc.weizmann.ac.il/report/2024/128/revision/1/download): states that lower bounds for
  AC0[p]-Frege are open for every p. Older than 2026, but it is the most recent explicit statement the search returned.
- CCC 2026 (LIPIcs vol 383, https://drops.dagstuhl.de/storage/00lipics/lipics-vol383-ccc2026/LIPIcs.CCC.2026.13/LIPIcs.CCC.2026.13.pdf,
  also ECCC TR26-018): quadratic size lower bound for unrestricted Res(xor), improving near-quadratic. This is depth 1 and size
  quadratic, not super-polynomial, and does not touch AC0[p]-Frege. Already recorded in r4-frontier.md.
- Efremenko-Itsykson (arXiv 2507.23008): bounds for Res(xor) of depth up to O(N log N), with the larger-depth statement of the
  follow-up; again a depth-of-DAG notion, not formula depth. Recorded earlier.
- Lu-Santhanam-Tzameret (arXiv 2509.16824; ITCS 2026): AC0[p]-Frege cannot efficiently prove constant-depth algebraic circuit lower
  bounds in DNF form. This is about a hard-or-false DNF family, not a bound for a known true family. In this session the search
  surfaced it only through a secondary summary page (lacker.io), which I did not rely on beyond what the earlier note already read
  from the abstract.
- Earlier recorded checks (r4-phase23-plan.md): Krajicek's preprints are conditional; Davis-Robere (ECCC TR26-055) is reflection
  type and does not involve parity or mod p.

Conclusion of the literature check: nothing found changes the picture. The most recent results are depth-1 (Res(xor), Res(lin F_p))
lower bounds or reformulations; AC0[p]-Frege remains open. Unconfirmed items stay unconfirmed: the Braun and Pang preprints are
unrefereed, and the claim that the search tool saw everything from 2026 is not made.

## 7. Decision for the board

- 3.1: audit and red team of the current state are done (this note). The card as written, a prose proof surviving the audit, remains
  Todo because there is no proof to audit.
- 2.4: remains Todo. Attempt outcome: three method attempts recorded, all failed, no progress claimed.
- If effort continues: the three useful, low-cost items are the Q2 control for Braun and Pang on weak PHP (does the bound degrade
  with more pigeons), an existence of refutations check for R_rho^p on Tseitin mod p (to make C1 a real statement), and the D3
  small-graph kernel fraction test. None of them is a route to the target.
- Nothing here has been pushed.
