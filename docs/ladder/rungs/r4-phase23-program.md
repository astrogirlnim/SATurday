# R4 Phase 2.3 research program (round 1): depth-2 AC0[p]-Frege

Status: research notes, docs only. No Lean, no builds. Nothing here is a lower bound for depth-2
AC0[p]-Frege. Date 2026-10-14, branch r4/prover-p23b. Follows r4-phase23-plan.md and
r4-phase23-analysis.md (which found the Pang depth-2 sketch needs a CNF with PC degree
(1/2 - o(1)) n, "hypothesis H").

Labels: PROVED-BY-HAND (derived on paper this session, not machine checked), COMPUTED (a script in
r4-phase23-scripts/ produced it), CITED (from earlier docs or literature, not rechecked),
CONJECTURE. Conventions: PC = polynomial calculus over F_p with implicit Boolean (multilinear)
reduction, degree = degree of the reduced lines; n = number of Boolean variables; for Tseitin,
n = |E| (one 0/1 variable per edge).

## 0. Bottom line

1. The experiments overturn the analysis document's hope that Tseitin parity on high degree
   graphs could approach ratio 1/2. I found an exact combinatorial description of the PC degree of
   Tseitin mod 2 over odd characteristic (Section 2). Result: for d-regular graphs,
   ceil(b/2) <= PC degree <= about (cutwidth + d)/2, where b is a (1/3)-balanced min cut. The
   ratio D/n is therefore at most 1/4 + o(1), and at least (2/9)(1 - lambda/d) for spectral
   expanders. So H fails for the whole Tseitin-mod-2 family (PROVED-BY-HAND for the upper bound,
   lower bound proof given, 84/84 numerical checks). This is the K2 kill condition of the plan,
   for the main candidate family.
2. Quantitatively (Section 3), the Pang depth-2 argument at ratio c = K/n gives a size exponent
   a(c) = 1/(C_1 ln((1-c)/c)); a(1/4) = 0.017, and a(c) > 1 (non-vacuous, since a CNF already has
   size >= n/d) needs c >= 0.467. Nothing between 0.25 and 0.467 is known for any family.
3. Best concrete, checkable restricted statement (Section 4, candidate C1): depth-2 where the
   layer-1 terms are conjunctions of F_p-linear equations of total rank at most eps log n; this
   needs no H, because such a term is one exact degree-(p-1)rank equation.
4. Best new theorem candidate (C2): a two-sided PC degree theorem for Tseitin and for all
   unsatisfiable XOR systems (upper bound n/4 + o(n)). It is a negative result for this route but a
   clean positive mathematical statement.

## 1. Tools

Script pcdeg.py: exact PC degree over F_p. PC degree D is the least D such that 1 lies in the
smallest subspace S of V_D (multilinear polynomials of degree <= D) that contains the axioms and is
closed under g in S, deg(x_i g) <= D => x_i g in S. Computed as a fixpoint with dense linear
algebra mod p, for n up to about 12. Axioms are the clause polynomials (so width = degree d).
Script tmodel.py: the combinatorial model of Section 2 (any graph with E <= 64).
Both are cross-checked against each other below.

## 2. Task 1: data and the exact structure of Tseitin PC degree

### 2.1 Linear-algebra data (COMPUTED, pcdeg.py)

Tseitin mod 2, charge on one vertex, F_3 (also F_5 and other charge positions where marked):

| graph | n=E | d | PC degree | D/n |
|---|---|---|---|---|
| C3 | 3 | 2 | 2 | .67 |
| K4 | 6 | 3 | 3 | .50 |
| K3,3 | 9 | 3 | 3 | .33 |
| prism | 9 | 3 | 3 | .33 |
| K5 | 10 | 4 | 4 | .40 |
| cube Q3 | 12 | 3 | 3 | .25 |
| octahedron | 12 | 4 | 4 | .33 |
| K4 with doubled edges | 12 | 6 | 6 | .50 |

Tseitin mod 3 with Boolean oriented edges (sum of out minus in = charge mod 3), over F_2, F_3, F_5:
K4 3, K3,3 3, prism 3, K5 4, identical for all three p. The reduced-product Nullstellensatz degree
(x-monomial multiples, no closure) is larger: K4 5, C3 3 (so closure matters).
Random 3-CNF, n = 7..13, m = 4.5n, 6n, 10n over F_3: every unsatisfiable instance has PC degree
exactly 3 = width (D/n = .43 down to .25). Satisfiable ones return none.
Reading: at n <= 13 every family sits at D = width plus a little. Direct linear algebra cannot
show asymptotic ratios; it is useful only to validate structure (next section). Reason: D >= d
forces D/n >= 2/V trivially, so small V looks high.

### 2.2 The exact model (PROVED-BY-HAND sketch; COMPUTED agreement 23/23 on small graphs)

Work in y = 1 - 2x, y_e^2 = 1, F_p with p odd. The vertex axiom is y^{delta(v)} = s_v with
prod_v s_v = -1 (odd total charge). The clause form and this binomial form generate the same
degree-<=d span (each clause polynomial is a combination of y^S (y^delta - s) with S subset of
delta(v); pairs combine since 2 is invertible). Let U range over vertex sets, T = delta(U) in
F_2^E, sigma(U) = product of s_v over U.
Fact A (PROVED-BY-HAND). If y^A ~ y^{A xor T} holds in S with sign sigma(U) at one pair A with
|A|, |A xor T| <= D, it holds for every A' in F_T = {A : |A|, |A xor T| <= D}: F_T is connected under
single-variable flips (in coordinates a = |A cap T|, b = |A minus T| it is {a+b <= D, |T|-a+b <= D},
which contains the row b = 0), and multiplication by y_i transports the relation along a flip
(x_i g and y_i g have the same degree condition). Axioms give delta(v) valid when d <= D.
Fact B (composition, PROVED-BY-HAND). From U1, U2 derive U1 xor U2 iff the Hamming balls of radius
D around 0, T1, T2 have a common point S (S is the middle monomial). Contradiction iff some cut
vector is derived from both U and its complement.
This composition rule is why PC beats the naive "bottleneck path" (pair model, which needs
|delta(U)| <= D along a path and gives D = bisection width): the middle monomial lets
|delta(U)| reach 2D.
Soundness of the upper-bound direction is immediate from the derivation (every step is a PC rule
within degree D). The exactness (lower bound direction) is proved in 2.4.

### 2.3 Numerical agreement and law (COMPUTED)

tmodel.py equals pcdeg.py on 9 named graphs and 14 random small graphs (also F_5, other charge
positions). On 84 connected random regular graphs (V = 6..14, d = 3..13, E <= 63):
PC degree >= max(d, ceil(b13/2)) in 84/84, equality in 80/84, where b13 = min |delta(U)| over
V/3 <= |U| <= 2V/3. Selected exact values (V, d, E, PC, b13, max(d, ceil(b13/2))):
(14,4,28,4,8,4) (14,5,35,6,11,6) (14,6,42,7,14,7) (14,7,49,9,17,9) (14,8,56,11,22,11)
(14,9,63,13,25,13). Dense case: PC ratio 0.206 at E = 63, bisection ratio 0.40, PC is about
bisection/2.

### 2.4 Theorem LB (PROVED-BY-HAND; checked numerically as above)

If G is connected with odd charge, d <= D and 2D < b13(G), then 1 is not in C_D, i.e. PC degree
over any odd F_p exceeds D. Hence PC degree >= max(d, ceil(b13/2)).
Proof. Call U small if |U| < V/3. Let Gamma be the graph on monomials y^A, |A| <= D, with edges
A ~ A xor delta(U), U small, both ends of degree <= D. Along any path A_0, ..., A_k the partial
symmetric differences W_j = U_1 xor ... xor U_j satisfy |delta(W_j)| <= |A_j| + |A_0| <= 2D < b13,
so W_j is never of size in [V/3, 2V/3]. By induction W_j is small (W_j small, U small => |W_{j+1}| <
2V/3 => small). So a closed path has W = empty, never V, signs multiply to +1: there is a
potential w(A) = sigma(W) consistent on each component, with W the unique small representative.
Let B = {g in V_D : for every component C, sum_{A in C} w(A) g_A = 0}. Then B contains the axiom
binomials, 1 is not in B (w(emptyset) = 1), and B is closed under y_i whenever the product has
degree <= D: for A, A' in one component both valid after the shift, the transport U = W xor W' has
|delta(U)| <= 2D so it is small again, hence A xor i ~ A' xor i, with the same ratio of
potentials. Closure under x_i follows since x_i g = (g - y_i g)/2 has the same degree
condition. So the PC closure is inside B and 1 is not in it. QED.
Spectral consequence (PROVED-BY-HAND from the expander mixing lemma): for a d-regular graph with
second eigenvalue lambda, b13 >= (d - lambda)(V/3)(2V/3)/V, hence
PC degree >= (2/9)(1 - lambda/d) E. For Ramanujan-like graphs lambda <= 2 sqrt(d-1), so the ratio
is at least (2/9)(1 - 2/sqrt d) (CITED for the existence of such graphs, Friedman / LPS).

### 2.5 Upper bound: the 1/4 cap (PROVED-BY-HAND with a rounding caveat; COMPUTED)

Order the vertices; let c be the current prefix cut, a0 back edges and a2 forward edges of the next
vertex v (d = a0 + a2). Choose the middle monomial S inside T1 = delta(prefix) with half of T1
plus the right part of the shared edges. Then d(S,0), d(S,T1) <= ceil(c/2) and
d(S,T2) <= max(ceil(c/2) + a2 - a0, d). Since c_new = c + a2 - a0, every step costs at most
max(d, ceil((max(c, c_new) + d)/2)). Hence
 PC degree <= max(d, ceil((cutwidth(G) + d)/2))  (exact rounding not rechecked).
For a d-regular graph a uniformly random vertex order has every prefix cut at most
E/2 (1 + o(1)) (each edge is cut with probability <= 1/2 at its level; McDiarmid for permutations,
change per swap <= d), so PC degree <= (1/4 + o(1)) E + d. The chain bound computed on larger
random regular graphs (best of a few orders; COMPUTED, chain_ub.py):

| V | d | E | chain upper bound | ratio |
|---|---|---|---|---|
| 14 | 9 | 63 | 14 (exact 13) | .222 |
| 30 | 6 | 90 | 13 | .144 |
| 30 | 10 | 150 | 24 | .160 |
| 60 | 12 | 360 | 59 | .164 |
| 100 | 16 | 800 | 143 | .179 |
| 100 | 32 | 1600 | 333 | .208 |
| 200 | 40 | 4000 | 811 | .203 |
| 300 | 24 | 3600 | 670 | .186 |

Growing degree does push the ratio toward 1/4 from below, never beyond (as the proof says).
This strengthens the earlier cutwidth bound by a factor 2.

### 2.6 All XOR systems (PROVED-BY-HAND sketch for the upper bound; CONJECTURE for rounding)

The same derivation works for any unsatisfiable system of parity constraints (rows r_j in F_2^n, width
w): T = XOR of rows, same composition. Take a minimal contradictory subset of rows: every column has
even weight k >= 2 in it, so for a random row order the prefix XOR has expected weight
sum (1 - (1-2f)^k)/2 <= n/2 at every prefix fraction f. Concentration (change per swap <= w, core has
<= n+1 rows) gives PC degree <= n/4 + O(w sqrt(n) log n) over odd p, hence ratio <= 1/4 + o(1) as
long as w = o(sqrt n). Random sparse cores at n <= 11 are too small to test (PC = width, COMPUTED).
So every parity-type CNF is capped at 1/4: H cannot come from Tseitin, XOR-SAT or Count_2 style
families. Remaining untested: Tseitin mod q != 2 (data in 2.1 trivial), random k-CNF, PHP variants.
CONJECTURE: a similar halving holds for any CNF whose refutation is by linear elimination.

### 2.7 Trends summary

Sparse (d = 3,4): D = d for every instance with E <= 28, ratio decreasing as 1/V (cannot test
asymptotics). Dense and growing d: D ~ max(d, b13/2) and b13 <= E/2 + small, so D/E is
nondecreasing in d toward 1/4 and no further. Random 3-CNF: D = 3 for all feasible n. Dense
"slowly growing width" Tseitin is therefore not a route to 1/2; it is a route to 1/4.

## 3. Task 2: which hypotheses of Pang Theorem 4.3 / Section 6 are essential

Parameter chain (CITED from the analysis doc, redone): c = K/n, rho = c/(1-c),
eta_K(delta) ~ (1 - 1/p) rho^delta. First layer: Delta_1 = C_1 ln M, C_1 = (p-1)^2 r /((1-1/p) rho^{(p-1)r}).
Second layer: t_2 = ln(2M)/eta_K(Delta_1) ~ M^{C_1 ln(1/rho)} and Delta_2 ~ t_2. Need Delta_2 <= n,
so M <= n^{a}, a = 1/(C_1 ln(1/rho)). COMPUTED table (p = 3, r = 1):

| c | rho | C_1 | a |
|---|---|---|---|
| 0.10 | .111 | 486 | .001 |
| 0.222 | .285 | 73.7 | .011 |
| 0.25 | .333 | 54 | .017 |
| 0.30 | .429 | 32.7 | .036 |
| 0.40 | .667 | 13.5 | .18 |
| 0.45 | .818 | 9.0 | .56 |
| 0.47 | .887 | 7.6 | 1.09 |
| 0.48 | .923 | 7.0 | 1.77 |
| 0.49 | .961 | 6.5 | 3.8 |
| 0.499 | .996 | 6.0 | 41 |

Findings, each labeled.
- (E1) The source of the 1/2 requirement is the union bound over M gates at layer 1, which forces
  the layer-1 degree Delta_1 = Theta(log M) (PROVED-BY-HAND, from the above). Layer 2 then pays
  eta_K(Delta_1) = rho^{Delta_1} = M^{-C_1 ln(1/rho)}; only rho -> 1 makes that a lower-order loss.
  A width that grows slowly does not enter this arithmetic at all: the width only enters through
  D >= 8w. So "width growing slowly" cannot replace degree near n/2.
- (E2) Non-vacuity floor: any CNF has size >= number of clauses >= n/d, so a bound M <= n^a with
  a < 1 is vacuous. The method needs c >= 0.467 for p = 3 (PROVED-BY-HAND from the table; a changes
  with p, worse for larger p). For Tseitin c <= 1/4 + o(1) gives a = 0.017.
  (Consequence: even the hypothetical polynomial-exponent version gives nothing for the actual
  families; the only live version is gamma -> 0.)
- (E3) Restriction does not help: attack B in the plan lowers the ratio (PROVED-BY-HAND earlier);
  in addition, a restriction that makes terms of rank > rho_1 vanish needs a union bound over M
  terms, so rho_1 >= log M, while Pang's depth-1 theorem tolerates r only up to eps log n
  (bound has (D/16n)^{(p-1)r}). So it covers M = n^{O(1)} with a small exponent, again vacuous
  (PROVED-BY-HAND sketch).
- (E4) Trading degree for a different counting argument: the normalized-rank count uses all of V_K.
  If the multiplier f can be restricted to a small family (for example cut-space monomials for
  Tseitin, dimension 2^{V-1}), the effective ratio changes, but multiplication by non-structured
  approximators leaves the family. No version found (CONJECTURE: needs approximators preserving
  the coset structure; first-layer terms which are linear systems might, see C1).
- (E5) The restricted class that the sketch reaches without H is AND/OR over equations (analysis
  doc, B5). Within it, ANDs of F_p-linear equations are special: a conjunction of linear equations
  of rank rho is an affine subspace and its exact indicator is the single polynomial
  1 - prod_{j<=rho}(1 - l_j^{p-1}) of degree (p-1) rho. So no layer-1 approximation, no
  union bound, Delta_1 = (p-1) rho exactly (PROVED-BY-HAND). This is the real "trade": rank of
  the term replaces log M. It leads to C1.
- (E6) MOD gates over layer-1 gates (analysis B5(iv)) remain the first unwritten inference step; it
  is independent of the parameter issue.

## 4. Task 3: candidate theorems, ranked by plausibility

### C2 (most plausible): PC degree of parity systems

Statement. Let p be odd and G connected with odd charge on d-regular graph on V vertices, E edges.
Then max(d, ceil(b13(G)/2)) <= PC_deg_{F_p}(Tseitin_2(G)) <= max(d, ceil((cw(G) + d)/2)).
Consequently D/E in [(2/9)(1 - lambda/d), 1/4 + o(1)] for d = o(sqrt V) regular graphs, and for every
unsatisfiable XOR system of width w = o(sqrt n), D <= (1/4 + o(1)) n.
Status: lower bound proved (2.4), upper bound proved up to rounding (2.5), XOR extension sketched (2.6).
First lemma to attempt: write 2.4 carefully (the class decomposition and closure under x_i), and the
exact rounding in the step cost; then the XOR extension needs only the prefix-weight estimate.
Kill test: a graph with D < max(d, ceil(b13/2)) (none in 84) or D above the chain bound; larger
exact instances via tmodel.py up to V = 16, or a hand counterexample to closure under y_i in 2.4.
Value: closes K2 for parity families, fixes the exact ratio, tells the project to stop looking
for H in Tseitin. Odds correct: about 85 percent.

### C1: depth-2 with rank-bounded linear terms (the restricted class)

Statement. Let p prime, q != p, G a bounded-degree expander, F = Tseitin_q(G) (Boolean-edge or one-hot).
Call Res_rho(lin_p) the dag-like system whose lines are disjunctions of terms, each term a conjunction
of F_p-linear equations (MOD_p gates of literals, any fan-in) of joint rank at most rho, with the
usual resolution/cut/AND-introduction rules on terms. If rho <= eps log n then every refutation of F
has size exp(n^{1 - O(eps)}).
Why plausible. A term of rank <= rho is the single equation g_T = 0 with g_T = 1 - prod(1 - l_j^{p-1}),
degree (p-1) rho, 0/1 valued on the cube. The negation of T is g_T - 1 = 0. Term cut: from C v (g=0)
and D v (g-1=0), the Res(PC_r) linear combination rule gives g - (g - 1) = 1 = 0, deleted as a false
constant. AND-introduction needs the product g_A g_B reduced via x^p = x, which lives at degree
2(p-1) rho, so the target system is Res(PC_r) with r = 2(p-1) rho. Pang's bound
ln S >= D/(32 p^2 r) (D/16n)^{(p-1) r} is large for r <= eps log n and D = Theta(n) (CITED: the
Tseitin D = Omega(n)). Strictly extends Res(k) (k = eps log n, CITED, Pang Cor. 7.5) and Res(lin_p).
Not covered: terms of rank > eps log n, MOD over terms, and cut formulas of depth 2.
First lemma: the simulation Res_rho(lin_p) into Res(PC_{2(p-1)rho}/F_p) with polynomial overhead,
all rules in Pang's system (syntactic weakening, contraction, linear combination, multiplication by
a polynomial of degree <= r, Boolean axioms). Kill test: a rule of the term calculus whose
simulation needs a line of degree above r, or Pang's theorem not allowing the needed r.
Odds: the statement is true and a corollary of Pang, about 65 percent; novelty low-to-moderate (it
may already be implicit in Pang's Res(PC_r) discussion). It is the safest "real depth-2 with MOD
gates" statement.

### C3 (least plausible, high value): a family with ratio above 0.467

Statement (conjecture to test). There is an unsatisfiable family of constant-or-slowly-growing width
CNFs, size poly(n), with PC degree over F_p at least (1/2 - o(1)) n, equivalently at least 0.467 n to
get any non-vacuous exponent. Consequence if true: the Pang depth-2 argument reaches the AND/OR over
equations fragment (analysis B5(i)-(ii), cut and unbounded fan-in still to be written).
First lemma: a general upper bound principle, "a CNF refuted by linear elimination has D <= n/4 + o(n)"
(Section 2.6 for parity; extend to Tseitin mod q != 2 and to systems over Z_q with one-hot encodings;
for those find the analogue of the three-ball rule, q-ball?). Kill test: prove the universal upper bound
for all width-w CNFs (D <= (1/2 - c) n) or exhibit via tmodel-style exact computation that every
algebraically structured family stays below 0.3. Evidence so far: parity families are capped at 1/4,
random 3-CNF is unknown (D = 3 at n <= 12). Odds: under 3 percent.

## 5. Recommendation (no owner tasks)

Treat Tseitin-for-depth-2 via Pang-parameters as dead (K2 for parity, proved up to rounding) and record C2 as a result. If the program continues, the productive branch is C1 (rank-bounded linear terms) and extending the combinatorial PC-degree model to other families (Tseitin mod q, Count_q) to test whether any family beats 1/4.

## 6. Session log (append-only)

- 2026-10-14 prover: pcdeg.py closure algorithm, found the Tseitin composition model, cross-checked
  against linear algebra (23 graphs), verified lower bound formula on 84 graphs, chain upper bounds
  up to V = 300. Drive dropped out mid-session, worktree and scratch survived, scripts copied to
  r4-phase23-scripts/. No Lean, no build, nothing pushed.
