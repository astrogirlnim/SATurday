# R4 expander plan: large-degree expanders and the Alekhnovich-Razborov bound for the Boolean-edge Tseitin formula

Status: active, uncertified. Branch r4/prover-expander. Date 2026-10-13. Docs part written before any code.
Sources: Alekhnovich-Razborov (AR), "Lower bounds for polynomial calculus: non-binomial case"
(FOCS 2001 / Proc. Steklov 242, 2003), OCR copy used for Thm 3.8, Lemma 4.2, Def 4.3, Thm 4.4, Cor 4.5;
Part-Tzameret Cor 46; scope in r4-phase22-plan.md, r4-khaniki-plan.md. The OCR of the immunity formula in
Thm 4.4 is garbled; the constant below is UNVERIFIED and must be re-read from the PDF page images
(scratchpad copy p20.png area) before layer B.

## 1. What AR need from the graph (exactly)

Thm 3.8: A an (r,s,c)-expander 0-1 matrix (rows = vertices, columns = edge variables; row weight <= s;
for every row set I with |I| <= r the boundary, i.e. columns with exactly one 1 in I rows, has size
>= c|I|), f_i l-immune with Vars(f_i) in the row support, l > 4(s-c). Conclusion: every PC refutation
of {f_i = 0} has degree > r(l/4 - (s-c)).

For the Tseitin graph (rows = vertices, columns = edges, each column has exactly two ones) the boundary of
a vertex set I is the edge cut e(I, V-I) = d|I| - 2e(I). Row weight s = d. Vertex predicate: sum of
+-1 weighted Boolean variables = sigma mod q, d variables, immune to degree about d/(2q) (Thm 4.4, via
Green's weak degree theorem), so l = Theta(d/q).

Requirement l > 4(s-c) means c >= d(1 - 1/(8q)) roughly, i.e. every vertex set of size <= r spans fewer
than d|I|/(16q) edges per vertex on average ("induced average degree below d/(16q)"), with r = Theta(n/q).
Consequences:
- degree d >= d0(q) (d must beat both q and the sqrt/lambda slack; for the route below d0 = poly(q));
- NOT the cubic MGG: for d = 3 the vertex predicate has immunity <= 3, Thm 3.8 cannot apply;
- no full Ramanujan property is needed. Only (a) edge-density of small sets: the Bollobas-Chung-Sudakov /
  expander mixing bound e(S,T) <= d|S||T|/n + lambda sqrt(|S||T|) with lambda <= d/(32 q), and (b) d-regular.
  "Unique neighbour expansion" in AR is exactly this edge-boundary statement; no vertex expansion beyond it.
- Formula side: the paper's Boolean formula is on a finite ORIENTED graph with one Boolean variable per
  directed edge; vertex v: sum_{in} x - sum_{out} x = sigma(v) mod q. Unsatisfiable iff sum sigma != 0 mod q
  (each edge appears once with + and once with -). Parallel edges are harmless for the formula (distinct
  variables); Def 4.3 says "finite oriented graph". Whether the paper's Cor 46 tacitly means simple graphs is
  unverified; our family below is a bipartite MULTI-graph (see 4).

## 2. Routes to an existence statement

(a) Explicit LPS / Margulis Ramanujan graphs: needs Deligne/Weil or Kloosterman bounds, number theory far
    out of reach. Rejected.
(b) Random d-regular graphs (permutation or configuration model) with a union bound over small sets: needs
    probability/counting over permutation tuples, tail estimates for the number of edges inside a set,
    entropy-type calculus. Elementary but long and painful in Lean (est. 2000-4000 lines), and yields
    only an existence statement for each n via counting (fine) with large constants.
(c) Powers of the 8-regular factor-2 Gabber-Galil graph already in the repo. The repo has
    `MGGGabberGalil.gg_numerical_radius` (|<f,Af>| <= 5 sqrt2 ||f||^2 for mean-zero f; A = adjacency of the
    eight shears) and `mggF2MultiRayleigh_eq_ggAdj` identifying it with `mggF2MultiRayleigh`. Because 5 sqrt2
    < 8 the operator A restricted to mean-zero functions has norm <= 5 sqrt2 (symmetric operator: numerical
    radius = norm, short polarization argument). Then A^k has degree 8^k and norm <= (5 sqrt2)^k on
    mean-zero functions, relative eigenvalue (5 sqrt2/8)^k = 0.884^k -> 0. Choosing k = O(log q) gives
    lambda/d <= 1/(32 q) with d = 8^k = q^{O(1)} (the exponent is about 17; irrelevant for an existence
    statement d0(q)). Realize the graph as the bipartite double cover on the torus T = (Z/m)^2: left copy,
    right copy, one edge for every k-step walk (u, w in Fin 8^k) from u to its endpoint. It is exactly
    8^k-regular on both sides (steps are bijections), has no loops (bipartite), may have parallel edges.
    No randomness, no number theory, no new Fourier analysis. This is by far the cheapest route.
(d) Lifts / tensor products of cubic MGG: need a spectral bound for the cubic graph, which the repo
    explicitly does NOT have (MGG/SpectralFrontier.lean: unit-shear radius is false). Rejected.
(e) Weaker expansion: not possible, Thm 3.8 needs c close to s (edge density of small sets below
    d/(16q) per vertex). Girth-based sparsity gives only r = n^{o(1)}, hence a degree bound n^{o(1)}
    instead of Omega(dn); not enough for 2^{Omega(n)}.

Chosen: (c).

## 3. Layers and estimates

E1 `ExpanderMixing.lean` (~300 lines, generic, this session): step systems (V, D, steps with an involutive
   inverse labelling), adjacency operator, symmetry, operator norm bound on mean-zero from the Rayleigh
   hypothesis, iterate, expander mixing lemma for A^k: |#{k-walks from S ending in T} - D^k|S||T|/N|
   <= lambda^k sqrt(|S||T|); walk counting; regularity of both sides.
E2 `ExpanderMGG.lean` (~250 lines): instantiate with the factor-2 torus (needs m >= 3), the bipartite walk
   multigraph `GGW m k`, left/right degree 8^k, and the AR boundary statement: for every vertex set I with
   |I| <= r the edge cut >= |I|(8^k(1 - |I|/(2N)) - (5 sqrt2)^k) (an (r,s,c)-expander in AR's sense,
   rows = 2N vertices). Needs the edge-cut identity d|I| - 2e(I).
D1 `TseitinEdgeCNF.lean` (~300 lines): the oriented-graph Boolean Tseitin CNF `T_q(G,sigma)` (width-d clauses,
   one per bad local assignment), unsatisfiability iff sum sigma != 0 mod q, passage between the CNF axioms
   and the vertex polynomials f_v (f_v = sum of the clause polynomials of v is derived in degree d;
   each clause axiom equals clause*f_v mod Boolean axioms, degree 2d).
AR-A `ARReduction.lean` etc (~1500-2500 lines): Thm 3.8 and its tools: S_n(F) = functions on the cube,
   Razborov reduction operator R(t) = reduction mod Span(Sup(t)), Thm 3.1, Lemma 2.10, Lemmas 3.3-3.7, 3.11,
   3.12. The repo has one R-operator argument (TseitinPC.lean, binomial case) but not the general criterion.
AR-B `GreenImmunity.lean` (~800-1500 lines): Thm 4.4, the mod-q predicate on d Boolean variables is
   about d/(2q)-immune over char != q (Green 2000 weak-degree theorem via roots of unity, plus AR
   Lemma 2.5, 2.7, Cor 2.6). The proof of Green's theorem is cited, not reproduced, in AR; I do not have
   Green's paper in hand.
F  `ResLinTseitinEdge.lean` (~300 lines): assembly with `rld_cnf_size` (tree-like) and the Khaniki dag
   chain (`reslin_tseitin_dag_size`): lower bound 2^{Omega(d n)/|F|} resp. n^{2-o(1)} for T_q(GGW m k, sigma).
Total about 4000-6500 lines over several sessions. The graph part (E1, E2) is now about 550 lines instead of
the "unknown, large" of the earlier estimate.

## 4. How the final statement would read (and where it differs from the paper)

For every prime q (the modulus; the paper calls it p) there is k0(q) such that for every k >= k0, every m >= 3,
every sigma : V -> Z/q with sum sigma != 0 (mod q), and every finite field F of characteristic != q:
(i) every PC_F refutation of T_q(GGW m k, sigma) has degree >= c d n / q^2 with d = 8^k, n = 2m^2;
(ii) every tree-like Res(lin F) refutation has size 2^{Omega(d n / (|F| q^2))}.
Genuine match with the paper: the formula is Def 4.3 verbatim (Boolean variable per directed edge,
in-sum minus out-sum = sigma(v) mod q, encoded as the width-d CNF), degree theorem is AR Cor 4.5 shape.
Differences to state explicitly:
1. Graph hypothesis: the paper says "every d-regular Ramanujan graph with d >= d0". We prove it for an
   explicit infinite family of d-regular, bipartite, oriented MULTI-graphs with relative second singular
   value (5 sqrt2/8)^k, not for every Ramanujan graph and not for simple graphs. Not Ramanujan in the sense
   lambda <= 2 sqrt(d-1) (it is only d/poly(q)-small, which is all AR's argument uses).
2. The degrees d are only of the form 8^k with k >= k0(q) (d0(q) polynomial in q of large exponent).
3. Unsatisfiability: sum sigma != 0 mod q (both signs, every edge once in, once out).
4. The Res(lin) hypotheses of Part-Tzameret Thm 45 (our repaired version, degree w+p) are the repo's.

## 5. Feasibility call

The graph infrastructure is now cheap and low risk thanks to the existing Gabber-Galil numerical radius.
The whole chain is feasible but long (several sessions). SINGLE RISKIEST STEP: AR-B, Thm 4.4 / Green's weak
degree theorem for the mod-q predicate over arbitrary char != q fields (complex Fourier technique, cyclotomic
integrality, transfer between characteristic 0 and p). Second: AR-A (long but the paper proof is complete).

## Progress log (append-only)

- 2026-10-13 E1 and E2 DONE (ExpanderMixing.lean ~330 lines, ExpanderMGG.lean ~190 lines, no sorry):
  `StepSys` (bijective steps with involutive relabelling), `norm_adj_le` / `norm_pow_le` (operator norm
  on mean-zero functions from the Rayleigh hypothesis, by polarization), `mixing` (expander mixing lemma
  for A^k: (E - D^k|A||B|/N)^2 <= (lam^2)^k |A||B|), `pow_apply_eq_sum_walks`. Instance `ggSys m hm`
  (factor-2 Gabber-Galil on (Z/m)^2, m >= 3) with `ggSys_rayleigh` (lam = 5 sqrt 2, from
  `gg_numerical_radius`), `gg_mixing`, the bipartite walk multigraph edge boundary `ggwBoundary`,
  `ggw_boundary_card` (|boundary| = 8^k(|IL|+|IR|) - 2 cross) and `ggw_expansion`:
  for t = |IL|+|IR|, |boundary| >= t (8^k (1 - t/(2 m^2)) - (5 sqrt 2)^k). This is AR's (r, s, c)-expander
  property with s = 8^k, c = 8^k(1 - r/(2 m^2)) - (5 sqrt 2)^k for sets of size <= r. Right regularity:
  `ggw_right_count` with IR a singleton. Remaining of the graph part: pick k0(q) with
  (5 sqrt2/8)^k <= 1/(32 q) and r = m^2/(8q)-ish to get the explicit constants c, and package as an AR
  matrix once AR-A fixes its interface; D1, AR-A, AR-B, F not started.
