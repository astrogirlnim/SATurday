# R4 Phase 2.2 scouting: Khaniki's dag-like size bound for Res(lin F_p), and overlap with Pang

Status: scouting note, docs only, no Lean code written. Date 2026-10-13. Branch r4/scout-khaniki.
Anything marked UNVERIFIED was not checked against the source text.

## 1. The paper (verified against the ECCC PDF, Revision 3, 26 Jan 2021)

E. Khaniki, "On Proof complexity of Resolution over Polynomial Calculus", ECCC TR20-034
(submitted 12 Mar 2020; revisions Apr 2020, Nov 2020 with detailed proofs, Jan 2021 adding PHP).
Single author, Charles University and Czech Academy of Sciences. The later published version
(ACM TOCL 2022, per a secondary source) was NOT checked; theorem numbers below are Revision 3's.

Systems: Res(PC_d/R) for a finite ring R: clauses of degree <= d polynomials in Boolean variables,
rules resolution (a f + b g), weakening, simplification (drop a nonzero constant), multiplication
(C v f to C v g f), axioms 0 and x v (x-1). Res(lin F) is d = 1 (there multiplication is only by
constants). Size = number of clauses in the derivation (dag-like), also a lower bound for bit size.

Main tool, Theorem 3.1 (size-width), R a finite ring, F an unsatisfiable CNF_t on n variables, d >= t:
1. tree-like: w_{R,d}(F)/|R| - 1 <= max{3, w(F)} + log(3 S*_{R,d}(F)).
2. dag-like, F a CNF: w_{R,d}(F)/|R| - 1 <= max{3, w(F)} + O(sqrt((2n + 3S) log(3S))).
   (Pang's intro quotes this as w = O(sqrt((n+S) ln S)), consistent.)

Dag-like application, Corollary 3.2(1): F a finite field, q a fixed prime with char(F) != q. There is
a constant d_q such that for every fixed d and c >= d_q, for every large n, every c-regular
Ramanujan graph G on n nodes (any orientation) and every sigma with T_q(G, sigma) unsatisfiable:
n^{2 - (log log n)^2 / log n} <= S_{F,d}(T_q(G, sigma)). Part (2): random k-CNFs, k >= 3, linear
clause density (c 2^-k >= 0.7), same bound w.h.p.

Formula: T_q(G, sigma) is the paper's Boolean-edge Tseitin mod q formula (one variable per directed
edge, equations sum out - sum in = sigma(v) mod q, encoded as clauses; O(2^c |V|) clauses of width
O(c)). Linear clause count is essential: S >= |F| is used only to say the clause count is Theta(n).

Hypothesis on PC: the proof needs only (i) a width-to-degree transfer (Lemma 5.2, Res(PC_d/F) of
width w gives PC/F of degree O(p w d)) and (ii) a linear PC degree lower bound (Theorem 5.3 =
Alekhnovich-Razborov, Omega(c n) for Tseitin mod q on Ramanujan graphs, any field of char != q).
So w_{F,d}(F) >= eps n, then Theorem 3.1(2) forces S = n^{2-o(1)}. It is a pure
"linear PC degree => almost quadratic dag size" argument, so it is NOT specific to the paper's
formula. Also proves tree-like bounds (Cor 3.3), exp(Omega(n/d)) for tree-like PHP, etc.

Proof of Theorem 3.1(2) (Section 4): replace each polynomial in a refutation pi by an atomic
extension variable q_f, giving a Resolution refutation of Ex(pi) v Q(F) of size <= 3|pi|
(Lemma 4.3(1)); apply Ben-Sasson-Wigderson to it; translate a width-w Resolution derivation
back to a Res(PC_d/R) derivation of width |R|(w+1) (Lemma 4.3(2), via Props 4.1-4.2).
Number of extension variables is <= number of distinct polynomials, so is O(n + S).

## 2. Dependency map onto the repo (state of main eabd0cd)

Existing and reusable:
- `SizeWidth.lean` (1355 lines) and `Width.lean`: Ben-Sasson-Wigderson for dag-like Resolution
  (`bsw_width_of_fatCount` core). UNVERIFIED: whether the final packaged theorem has the
  sqrt((n + S) log S) shape Khaniki quotes or only the core fat-count induction; check before use.
- `ResLinF.lean`, `ResLinFPC.lean` (Theorem 45, degree w+p), `ResLinFWidth/Size` (Theorem 44, tree-like
  only), `ResLinTseitin.lean` (`reslin_tseitin_width`, `reslin_tseitin_size`).
- `PolyCalc.lean` (PCD, cnfAx), `TseitinBool.lean` (`tseitin_bool_degree_Fp`, one-hot tcnf on cubic
  MGG expanders, degree ((n-2)/1312 - q(q+3))/(q-1) over ZMod p, p prime, p not dividing q).
- `ResLinDag.lean`: dag-like Res(xor) but F_2 only (`Der`, `DagRefutes`); not reusable for F_p except
  as a template for a dag derivation type.

Missing (new work):
- M1. Dag-like Res(lin F_p) derivation type (set of lines, as in `Der`, over `LEq F`), soundness,
  and the tree-like to dag-like comparison. Existing `RLD` is tree-like and indexed by leaves; the
  Theorem 45 transfer (`rld_to_pcd`) is an induction on the tree, so it must be redone as an induction
  over the dag's line sequence. Est. 300-450 lines (ResLinFPC is 389 lines; the PC-degree
  induction transfers nearly verbatim since each line's polynomial is closed under its own premises).
- M2. Khaniki's extension-variable translation (Lemma 4.3): map each distinct linear equation in a
  Res(lin F_p) line to an atom q_f, build Ex(pi) and the Resolution refutation of size <= 3|pi|,
  prove Res width w gives Res(lin) width |F|(w+1) (back-translation, the consequence clauses
  Q'(C): not q_f replaced by the OR over a != 0 of (f = a)). Needs a bridge between `Resolution.lean`
  Clause/CNF and the new line type. Est. 600-1000 lines. Risk: moderate, bookkeeping of the
  inductive width claim; Props 4.1, 4.2 (derive "OR over a of (f = a)" at width |F|+1) are small
  for d = 1.
- M3. Size-width bridge: apply BSW (in repo) to Ex(pi) v Q(F) with n' = n + #atoms variables.
  Est. 150-300 lines plus the asymptotics lemma (sqrt bound contradiction at S = n^{2-o(1)}),
  maybe 200 more lines of real analysis (the (log log n)^2 / log n exponent is fiddly; a cleaner
  honest statement S >= n^{2-eps} for each eps, or S >= c n^2 / polylog, is easier).
- M4. Linear PC degree lower bound for a linear-size CNF, then composition. Two options:
  (a) one-hot `tcnf` on cubic MGG expanders: ALREADY CERTIFIED, clause count and variable count
      are Theta(n) (cubic, bounded q), width <= max(q,3), so M1-M3 apply unchanged. No Alekhnovich-
      Razborov port needed. Result is for the one-hot variant, not the paper's literal formula.
  (b) paper's Boolean-edge formula: needs the AR port (4000-7000 lines, open risk = d >= d0(p)
      regular expander family), see r4-phase22-plan.md.
- M5. Final assembly in `ResLinTseitin`-style file. Est. 150-250 lines.

Totals for route (a): M1+M2+M3+M5 about 1300-2000 lines new Lean, no new expander or algebra
machinery. Route (b) adds the AR port and is dominated by it.

## 3. Layers, sizes, feasibility

| Layer | Content | Lines (est.) | Risk |
|---|---|---|---|
| K1 | dag-like Res(lin F_p) type, soundness | 150-250 | low |
| K2 | dag width-to-degree (Thm 45 on dags), CNF specialisation | 300-450 | low-moderate |
| K3 | atom translation Ex(pi), Res refutation of size <= 3|pi| | 400-600 | moderate |
| K4 | back-translation, width |F|(w+1) | 300-500 | moderate |
| K5 | BSW application, sqrt asymptotics, final bound | 300-500 | moderate |
| K6 | assembly with certified one-hot tseitin degree | 150-250 | low |

Feasibility: route (a) is feasible, roughly 1300-2000 lines over several sessions. The risky parts
are K3/K4 (translation back and forth with width tracking, only sketched in the paper) and K5
(whether our BSW packaging supports the n+S form; if it only gives the clean fat-count lemma, one
re-derives the sqrt form, which is a short calculation but needs care). Honest weakness: the
conclusion is only almost quadratic, n^{2-o(1)}, and (for route (a)) for the one-hot formula.
Weaker but cheaper statement available: S = Omega(n^{2-eps}).

## 4. Overlap with Pang (arXiv 2610.00837)

Pang, "A Degree-Size Relation for Resolution over Polynomials", Univ. of Bristol, v1 30 Sep 2026
(checked abstract, intro and Theorem 1.1 in the PDF; proofs not read here; owner reports an audit
clean). Theorem 1.1: p fixed prime, F a width-w CNF on n Boolean variables, Q(F) the PC encoding
(Boolean axioms plus clause falsity polynomials) over F_p. If Q(F) has no degree-D PC refutation,
D >= max{32 (p-1)^2 r, 8 w}, then every dag-like Res(PC_r/F_p) refutation of F has size S with
ln S >= (D / (32 p^2 r)) (D / 16n)^{(p-1) r}. For constant p, r, w, linear D gives exp(Omega(n)).
Includes r = 1 (Res(lin F_p), the same system as here) and the dag-like case; its proof avoids
extension variables (Razborov-Smolensky approximation with a common multiplier from Braun, plus
rank measure modulo bounded-degree PC). Intro explicitly says Khaniki gave only w = O(sqrt((n+S) ln S))
and almost quadratic bounds; Pang strictly improves it.

Comparison:
- Same hypothesis shape as Khaniki: a PC degree lower bound for the CNF over the same prime field.
  The existing certified `tseitin_bool_degree_Fp` (cubic one-hot tcnf, linear in n) feeds both.
  Pang's width condition is satisfied (width <= max(q,3)); D = Theta(n) is >= 16 n * const only up
  to constants, and the (D/16n)^{(p-1)r} factor is a constant when D = c n, so the bound is
  exp(Omega(n)) with a tiny constant.
- Shared layer: none of Khaniki's K3/K4/K5 is reused by Pang. The only shared piece is the PC
  degree input (K6-equivalent) and the Res(lin F_p) dag-like definition (K1), plus the Q(F)
  encoding versus `cnfAx`/`clausePoly` (check they agree: Pang's falsity polynomial is the product of
  literal falsity terms, which should match `clausePoly`; UNVERIFIED).
- Khaniki's dag-like route would be superseded by Pang's result: weaker bound (n^{2-o(1)} versus
  exp(Omega(n))), same hypothesis. It would not be a stepping stone: Pang's proof method is
  different (approximation, ranks, Braun's common multiplier), and Braun-side machinery is partly in
  the repo (Braun*.lean, F_2 Res(xor)), though whether it extends to F_p is UNVERIFIED.
- Caveat on Pang's cost: Theorem 1.1 is a new paper (one month old at this date) with an AI-assisted
  proof; owner reports the audit is clean. Its formalization cost is NOT scoped here (it needs
  low-rank/dimension arguments over F_p with PC consequence spaces, Lemma 4.2, in addition to a dag
  Res(lin F_p) type). A separate scouting pass on Pang's layers is advisable before committing.
  Khaniki is the lower-risk fallback with a known, elementary proof, giving a weaker result.

## 5. Recommendation

Khaniki can be skipped in favour of Pang if the goal is the strongest dag-like Res(lin F_p) bound
for Tseitin mod q: Pang implies Khaniki's Corollary 3.2(1) for any linear-degree PC input and needs
only K1 (dag type) and the existing certified degree bound. Khaniki is worth doing only as a
hedge if Pang's formalization looks too expensive (estimated here at 1300-2000 lines for route (a),
modest and elementary, versus an unscoped Pang port). If Pang is chosen, the dag type and the
degree input are shared work, so K1 should be built first either way.
Both results need an input for the linear PC degree; the cubic one-hot route avoids the
Alekhnovich-Razborov port that the paper-exact Boolean-edge formula requires.

## 6. Execution log (prover, branch r4/prover-khaniki; owner decision 2026-10-13 to do Khaniki now)

Checks against the repo and design changes (honest list of mismatches with section 2 above):

1. `SizeWidth.lean` is BSW for TREE-like resolution only: `Derivation.size` counts clause occurrences
   in a proof tree and `fatCount` counts tree nodes. The "dag" remark in section 2 was wrong. Its final form
   (`bsw_size_lower_bound`) is 2^((W-w0)^2/(24 n)) <= tree size, with n = number of variables.
   So a dag version had to be built (new file `ResDag.lean`, see below).
2. Design change (cheaper than K2/K3/K4 above): the translation goes Res(lin F_p) dag -> Resolution dag over
   atoms y_e (one atom per linear equation e = (f = a)) -> BSW -> width-w tree Resolution refutation ->
   directly to polynomial calculus, with clause polynomial prod of (1 - chi_e) / chi_e and
   chi_e = 1 - (f - a)^(p-1). The resolution step is an EXACT polynomial identity
   (P_U = P_{D'} P_{D''\D'} (1-chi) + ... ), so the back-translation to Res(lin) of width |F|(w+1) and a dag
   Theorem 45 are NOT needed; the PC degree obtained is (p-1)(w+1) up to additive constants.
   Atom clauses need only: Q = {not y_e1, not y_e2, y_(cmb e1 e2)} (degree 3(p-1), vanishes mod x^p - x),
   unit not y_(0,c) for c != 0, and the hypotheses of Phi and Boolean axioms. Weakening needs no axiom:
   each Res(lin) line is represented by a SUBSUMING atom line (invariant "empty clause derived or some
   atom line is a subset of A(L)"), so the atom dag has at most 3 lines per Res(lin) line.
3. Size measure: dag-like size = number of lines (as in the paper). In the BSW application the variable count
   n can be taken as the number of variables of the clauses actually used (<= max(w0,3) * 3S), so no
   separate "n + S" term and no bound on the number of distinct equations is needed (the paper's remark
   that the number of extension variables is O(n + S) is not needed, and as stated it is suspicious since a line
   may contain many equations). Expected final shape: S (log S + 1) >= c n^2 (an almost quadratic bound, same
   as Khaniki's n^{2 - o(1)}).

Progress:
- DONE `ResDag.lean`: `DDer` (dag-like resolution as a set of lines built by hypothesis and resolution
  steps), `DDer.to_tree`, `DDer.restrict` (restriction of a dag, subsuming lines), `bsw_dag_width_of_fatCount`
  (tree refutation of width <= w0 + t + fatSteps), and `bsw_dag_size_lower_bound`: if every tree refutation of F has width
  >= W then every dag refutation has >= 2^((W-w0)^2/(24 n)) lines.
