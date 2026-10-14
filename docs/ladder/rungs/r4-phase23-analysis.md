# R4 Phase 2.3 analysis: is the Pang depth-2 route alive?

Status: prose research only. Docs only; no Lean, no build. Nothing here is a proof of any
lower bound. Date 2026-10-14. Branch r4/prover-p23. Author: research prover and auditor.
Follows the top task of r4-phase23-plan.md (Section 4, tasks 1 and 2).

Labels: PROVED-BY-HAND = I derived it on paper in this session (not machine checked).
CITED-CHECKED = text read this session. CITED-UNCHECKED = recalled from literature, not
re-verified. CONJECTURE = my reasoning, unproven. Pang's TeX (arXiv 2610.00837 v1, file
deg--size.tex, 993 lines) was fetched to a scratch folder outside the repo and read for the
sections used here (1, 4, 6, 7 applications, 8 and the proof-search corollary).

Note on numbering: Pang's paper has 8 sections; "Section 8" is the short Conclusions section
(about 40 lines, lines 942-993 of the TeX). The depth-2 discussion is all there is. It is a
heuristic remark, not a theorem, and it gives no inference-preservation argument.

## 0. Bottom line

(A) No. No constant-width (or o(n)-width, polynomial-size) CNF family is known with PC degree
(1/2 - o(1)) n over any F_p, and the best proved ratios are small constants far below 1/2
(Section 2). The scout's calculation is correct in substance (Section 1): a fixed ratio
D/n = 1/2 - gamma excludes depth-2 proofs only of size n^(Theta(1/gamma)), a fixed polynomial,
so the route needs gamma = o(1).
Is the method killed? Not formally. Kill condition K2 (a theorem that every constant-width CNF
has PC degree at most (1/2 - c) n) is not established, and I could not prove it. But the
evidence points the wrong way (Section 2.5): every family I could bound has ratio well under
1/2, hypothesis H is a new open extremal question, and I rate it very unlikely
(CONJECTURE, under 3 percent). Status: alive only as a conditional shell; effectively dormant.

(B) Done, because the method is not formally killed. The first step that does not go through is
not an inference rule: it is the quantitative closing of the dimension count at depth 2 (Step
B6), which needs H. Independently, the inference-preservation part (B4) is unwritten: I
checked by hand that AND-introduction and the "two claims cannot both stand" relation go
through in simple cases, but the cut rule, MOD_p gates over depth-1 gates and the
full-sequent bookkeeping are not derived. So the honest summary is: the algebraic core
extends cleanly to depth 2; the inference layer is unproved; the parameters fail without H.

## 1. Redoing the scout's calculation (task 2, the heuristic of plan Section 2.3)

Setup, from Pang Theorem 4.3 (CITED-CHECKED, and the lemmas it uses, checked by hand below).
Notation: V_k = multilinear polynomials of degree at most k, N_n(k) = sum_{j<=k} C(n,j),
C_D = polynomials with a degree-D PC derivation from Q(F), eta_K(delta) =
(1-1/p) N_n(K-delta)/N_n(K).

Theorem 4.3 as stated is for a family of polynomials g_{nu,i} of degree at most d (any
degree d, with d <= K and (p-1) d t + K + d <= D). The proof needs only: C_D is closed under
multiplication within degree D, contains the Boolean axioms, and g^p - g in C_D. For any
polynomial g of degree d (it is F_p-valued on the cube, so g^p = g there), g^p - g vanishes
on the cube and has degree pd, hence lies in C_D when pd <= D (Boolean reduction, Pang Fact
2.2; PROVED-BY-HAND, I re-read the argument). So Theorem 4.3 and Lemmas 4.1 and 4.2 apply
verbatim with d replaced by the degree of the second-layer inputs (the first-layer
approximators P_T, of degree Delta_1), provided a + K + p Delta_1 <= D. Lemma 4.1 (monotone
normalized rank) is stated for all K <= n: its proof is the graded-order down-closed family
argument and does not use K <= n/3. Only the final arithmetic of Section 6
(N_n(K) <= 2 C(n,K)) uses K <= n/3. This corrects the plan's remark in 3.1 step 3 that the
lemma needs re-proving in the middle range: Section 4 of Pang is fine there (PROVED-BY-HAND,
read in full); only the Section 6 estimate has to be redone.

Two-layer count. First layer: M_1 gates T, equation degree r, d_1 = (p-1) r. Take
t_1 = ceil(ln(2 M_1) / eta_K(d_1)) factors; then M_1 (1 - eta_K(d_1))^{t_1} <= 1/2 and
Delta_1 = (p-1) d_1 t_1 (Pang's conclusion writes (p-1) r t_1; this differs by a factor p-1
that is irrelevant here). Second layer: gates take inputs of degree Delta_1, so
t_2 = ceil(ln(2 M_2) / eta_K(Delta_1)) and Delta_2 = (p-1) Delta_1 t_2. The simulation needs
D >= K + O(Delta_2) (Pang Prop. 5.1 pattern: K + 2 Delta + 2d at depth 1).

Asymptotics. Let K = (1/2 - gamma) n with gamma >> 1/sqrt(n). Then
C(n,K-delta)/C(n,K) = prod_{j<delta} (K-j)/(n-K+j+1) = exp(-delta ln((1-c)/c) + O(delta^2/n))
with c = K/n, and ln((1-c)/c) = 4 gamma + O(gamma^3). The sum N_n(K-delta)/N_n(K) has the
same ratio up to a factor 1 + O(1) as long as 4 gamma delta is not huge, because the partial
sums are geometric tails dominated by their top terms with the same ratio. So
eta_K(delta) = Theta(exp(-4 gamma delta)), matching Pang's exp(-Theta(s delta / n)) with
s = gamma n (CITED-CHECKED). Then eta_K(d_1) = Theta(1) when gamma is small, so
t_1 = Theta(ln M_1), Delta_1 = C_1 ln M with C_1 = Theta(p^2 r), and
eta_K(Delta_1) = M^(-4 gamma C_1 (1+o(1))). Hence
t_2 = M^(4 gamma C_1) polylog(M) and Delta_2 = M^(4 gamma C_1) polylog(M).
The requirement Delta_2 <= D - K <= n - K (and in fact <= n/2) gives
M^(4 gamma C_1) polylog(M) <= n, i.e. log_n M <= (1 - o(1)) / (4 gamma C_1).

So the scout's conclusion stands (PROVED-BY-HAND for the asymptotic form, and the same
form recovered numerically below): with K = (1/2 - gamma) n and gamma a fixed constant,
the depth-2 argument excludes only proofs with at most M <= n^(Theta(1/gamma)) gates. A
super-polynomial bound needs gamma = gamma(n) -> 0, at any rate: gamma = 1/log log n gives
n^(Omega(log log n)). It does not need gamma = O(1/sqrt n); the middle window of width
sqrt n in Pang is the regime where the first-layer exponent costs nothing, a stronger
sufficient condition. Also K <= D - Delta_2, so D/n must exceed 1/2 - gamma by the extra
Delta_2/n. Therefore the true requirement is D >= (1/2 - o(1)) n, with o(1) arbitrarily
slow, and D <= n always (Pang Section 6; PROVED-BY-HAND: for each assignment pick a violated
axiom, multiply by the assignment's literals one at a time, sum; degree n+1 in the clause
encoding and n for the 0/1 axiom form).

Numerical sanity check (a script I ran in the scratch folder, not in the repo): p = 3, r = 1,
n = 10^5, K = (1/2 - gamma) n, M = n^e, crude requirement K + 2 Delta_2 + 2 Delta_1 <= n, all
quantities computed exactly from binomial sums. Largest feasible e: gamma = 0.2 gives 0,
0.1 gives 0.02, 0.05 gives 0.17, 0.02 gives 0.43, 0.01 gives 0.74. This is dominated by
finite-size polylog factors and the constants (p = 3), so it only confirms the shape: e grows
roughly like 1/gamma and is tiny for any moderate gamma. It does not test the asymptotic
constant.

Conclusion for (A) part 2: the scout's heuristic is right. A constant gamma gives a fixed
polynomial exponent only; this is not a super-polynomial bound.

## 2. Best known PC degree / variable ratios and upper bounds (question A)

Convention: n = number of Boolean variables of the CNF, D = least PC degree over F_p with
Boolean axioms. Two universal facts.

U1. D <= n (PROVED-BY-HAND, above).
U2. D <= (maximum clause width in any resolution refutation) + 1. PROVED-BY-HAND sketch: map a
clause C to Q_C, the product of falsifying literal polynomials. A resolution step on x gives
Q_{C v D} equal, modulo the Boolean axioms, to Q_C (Q_D x) + Q_D (Q_C (1-x)): both products
multilinearize to degree at most |vars(C v D)| + 1, and the multiplications can be done one
variable at a time without exceeding that. The initial clauses are axioms. (Standard; CITED-
UNCHECKED as Clegg-Edmonds-Impagliazzo 1996 / Impagliazzo-Pudlak-Sgall 1999.) So any family
with a narrow resolution refutation has small PC degree.

Per family:

- Tseitin mod q, expanders (the primary R4 candidate). Lower bound: linear degree, BGIP 2001
  and Alekhnovich-Razborov 2003 (cited by Pang; CITED-CHECKED that Pang cites them; the
  constants are not stated in Pang and I did not extract them). Certified in this repo:
  `tseitin_bool_degree_Fp` (linear, constant unspecified small). Variables: q|E| in the
  one-hot encoding, so ratio D/n carries a factor 1/q. Upper bound, q = 2, p odd, +-1
  encoding y_e = 1 - 2 x_e, n = E (PROVED-BY-HAND): order the vertices v_1..v_V and let
  P_i be the first i vertices. By induction derive prod_{e in boundary(P_i)} y_e = s(P_i) in
  degree at most max_i |boundary(P_i)| + 1 (multiply the previous line by the factors of the
  next vertex equation, cancelling shared edges first with y^2 = 1). At i = V the product is
  empty and the identity reads 1 = s, the contradiction. Hence D <= cutwidth(G) + 1, and
  D/n <= cutwidth(G)/E. For cubic graphs, pathwidth <= V/6 + o(V) (Fomin-Hoie 2006, CITED-
  UNCHECKED) and cutwidth <= (max degree) x (vertex separation number) give cutwidth <= V/2 =
  E/3 asymptotically (CONJECTURE for the constant, because I did not recheck the pathwidth
  result). For d-regular graphs with large d the prefix boundary of a half-size set is about
  E/2 minus a lower-order term (min bisection of random d-regular graphs is about
  (d/4 - Theta(sqrt d)) V, CITED-UNCHECKED), so this method gives a ratio up to about
  1/2 - Theta(1/sqrt d), tending to 1/2 as d grows. That is only an upper bound for one
  refutation method, not a lower bound. The true PC degree of Tseitin on high-degree
  expanders is not known to me to be near E/2, and the AR/BGIP lower-bound constants are
  small. For fixed-degree expanders the proved lower bound constant is tiny and the cubic
  upper bound is about 1/3.
- Random k-CNF, k = w, density Delta n clauses. Lower bound: AR03, and Ben-Sasson-Impagliazzo
  2010 over characteristic not 2 (Pang cites both): degree >= epsilon(w, Delta) n, with
  epsilon(w, Delta) small and decreasing in Delta (Ben-Sasson-Impagliazzo style bounds scale
  like n / Delta^(1/(w-2)), CITED-UNCHECKED). Upper bound: U2 plus known DPLL/width analyses
  gives ratio decaying in Delta; at the threshold I know no upper bound below 1, and no lower
  bound with epsilon near 1/2 (CONJECTURE: the true constant is far below 1/2; by U2 the
  question is resolution width of random formulas, whose proved lower constants are small).
- Pigeonhole family. Complete PHP_N^{N+1}: degree >= N/2 + 1 (Razborov 1998, CITED-UNCHECKED)
  on N(N+1) variables, ratio O(1/N). Upper bound O(N): over a field with p > N+1,
  s_v = sum_u X_{u,v} satisfies s_v^2 = s_v; with sum_u (1 - sum_v X_{u,v}) = 0 one gets
  S = sum_v s_v = N+1 while S is a sum of N idempotents, so S(S-1)...(S-N) = 0 is a
  contradiction of degree N+1 (PROVED-BY-HAND sketch; small p not handled). Bounded-degree
  boundary expanders (Miksa-Nordstrom, CITED via Pang): degree >= delta s/(2b) on at most bN
  variables, ratio at most delta/(2b^2) times a constant, far below 1/2. And a graph PHP with
  average left degree below 2 is easy, so no pigeonhole variant can be pushed past 1/2.
- 3-colouring (Conneryd et al., via Pang) and bit-PHP: both linear degree on Theta(N)
  variables with small constants; bit-PHP reduces to FPHP(G) of a bounded-degree expander.

So the literature gives, as far as I can verify, ratios in the range of a few percent
(proved lower bounds) and at most a third or so (proved upper bounds for the specific
Tseitin family). Pang himself states (CITED-CHECKED, line ~985): "The difficulty lies in
proving a PC degree lower bound near or above n/2. This is unknown for o(n)-width
polynomial-size CNFs." His theorem's hypothesis D >= 8w also allows width w up to
Theta(n); the width restriction matters for what families exist, not for the proof.

2.5 Assessment of H (a family with D >= (1/2 - o(1)) n).
- No universal upper bound of the form D <= (1/2 - c_w) n for width-w CNFs is known to me, and
  I could not prove one; so K2 is not triggered. A decision-tree argument gives D <= n and
  nothing better: the search problem for Tseitin has decision-tree depth E - O(d), so tree-like
  routes cannot help.
- Tseitin with slowly growing degree is the only family where my upper bound approaches 1/2
  at all, and that bound is for one refutation method.
- Restrictions do not raise the ratio (attack B of the plan reduces to H itself): fixing k
  variables lowers D by at most k and n by exactly k, and (D-k)/(n-k) is non-increasing in k
  for D <= n; a restricted formula is itself a CNF, so any gain would be the existence of a
  better CNF, i.e. H. This kills attack B as a separate method (PROVED-BY-HAND, one line; the
  inequality D(F|rho) >= D(F) - |rho| is the standard direction and I take it as folklore,
  CITED-UNCHECKED).
- Other padding, lifting or XOR-substitution constructions increase n by at least as much as
  they increase D.
Verdict on (A): H is an open extremal question with no supporting evidence. The method is
alive only in the sense that it is not formally killed.

## 3. Re-derivation of Pang's depth-2 argument (question B)

Everything below is relative to Pang's proof for r = 1 pattern and generalizes to degree-r
equations. Let F be an unsatisfiable CNF of width w on n variables, D a degree with
1 not in C_D, and suppose (hypothesis H) D >= K + c_0 Delta_2 + 8w for the K chosen below.

Depth-2 proof system (the object to attack). Formulas: literals, bounded-degree equations
(h = 0) with deg h <= r (these represent depth-1 MOD_p gates when r = 1), AND and OR of
unbounded fan-in over such equations (layer 1, "terms"), then AND and OR of unbounded fan-in
over terms (layer 2), plus negations pushed to equations ((h != 0) is the equation
1 - h^(p-1) = 0, degree (p-1) r). Rules: sequent-calculus rules for AND, OR, cut on depth-2
formulas, weakening, contraction, axioms. Size M = total number of distinct subformulas
(not number of lines: a line can contain unboundedly many gates, so M_1 and M_2 must count
gates, and this is a size convention that has to be fixed; the usual AC0[p]-Frege size counts
symbols, which dominates M).

What Pang's sketch covers: lines that are OR of AND of equations (and by symmetry the dual).
It does not cover MOD_p gates whose inputs are layer-1 gates (their equation would have
unbounded degree), or genuine MOD_p connectives at layer 2. In Pang's sketch T = AND of
equations h_i = 0 (so layer 1 is AND, over depth-1 MOD equations), L = OR of terms T_j.

Steps. Marking: [H] proved by hand, [C] cited from Pang (checked in his text by me this
session), [?] conjecture or not derived, [X] fails or needs H.

B1 Normal form. Sequent proofs of depth at most 2 have all cut formulas of depth at most 2,
and every sequent can be read as an OR of depth-2 formulas and negations. [?] Standard for
depth-d Frege (CITED-UNCHECKED, folklore); I did not rederive it for MOD_p connectives. It
matters because it fixes which gate types occur.

B2 Layer-1 approximators and rank bound. For each term T = AND_i (h_i = 0), g_i = indicator
polynomial of (h_i=0), deg g_i <= d_1 = (p-1) r, choose P_T = prod_{j<=t_1}(1 - q_j^(p-1)),
q_j in the F_p span of the g_i, deg Delta_1. Claim: c_{P_T}(K) <= h_K (1 - eta_K(d_1))^{t_1}.
Status [C]+[H]: this is Pang Theorem 4.3 (Lemmas 4.1, 4.2, Cor. 3.4), which I rechecked line by
line for arbitrary degree-d inputs; fan-in is unbounded and plays no role because the rank of
f -> ([P g_i f])_i into (V_D/C_D)^s is at most dim(V_K / (V_K cap C_D)) regardless of s
(Pang's step "all S maps annihilate C_{<=K}").

B3 Layer-2 approximators and rank bound. For a line or formula L = OR_j T_j, choose
P_L = prod_{nu<=t_2}(1 - Q_nu^(p-1)) with Q_nu in the F_p span of {P_{T_j}}, applying Lemma 4.2
with d = Delta_1 and g_i = P_{T_i}. Requirements: g^p - g in C_D (true: P_T takes values in
{0,1} on the cube, so P_T^p - P_T vanishes on the cube and has degree p Delta_1 <= D), a + K +
p Delta_1 <= D. Status [H] (my verification): the lemmas apply because they are written for
arbitrary polynomials. The one point that is not literally in Pang: in Lemma 4.2 the stacked
map's kernel equality uses multiplication by g_i^(p-2) and g_i^p - g_i in C_D; with g_i = P_{T_i}
both hold. So the rank bound holds with eta_K(Delta_1) in place of eta_K(d).

B4 Common multiplier f. By dimension count over all M_1 + M_2 maps (all annihilate C_{<=K},
joint rank at most (M_1 (1 - eta_K(d_1))^{t_1} + M_2 (1 - eta_K(Delta_1))^{t_2}) h_K < h_K) there is a
multilinear f in V_K, f not in C_D, with f h_i P_T in C_D for all terms and inputs, and
f P_{T_j} P_L in C_D for all lines. Status [H] given B2, B3, and given that the layer-1 P_T are
fixed before the layer-2 choices. This is Pang's displayed inequality in the conclusion
(M_1 (1-eta_K(r))^{t_1} + M_2 (1-eta_K(Delta_1))^{t_2} < 1) with the minor notational fix that
d_1 = (p-1) r should replace r in the first exponent's eta.

B5 Inference preservation (the simulation). One shows by induction over the proof dag that
f P_L in C_D for every line L, ending with the empty line (P = 1) giving f in C_D, a
contradiction. Pang does this for depth 1 (Prop. 5.1, [C]); at depth 2 he states it "extends
given the error relations (f-errors) for each gate" without writing them. My checks:
 (i) AND-introduction for terms: from f(1 - P_{T_A}) and f(1 - P_{T_B}) in C_D (the lines
     asserting T_A and T_B), derive f(1 - P_{T_AB}) in C_D, where T_AB has all the equations of
     both. f(1 - P_{T_AB}) = f(1 - P_A P_B) + f P_A P_B (1 - P_{T_AB}); the first term is a
     combination of the hypotheses, the second is, via 1 - P_{T_AB} = sum_i U_i g_i with
     deg U_i <= Delta_{AB}, a combination of f g_i P_A P_B, each in C_D because f g_i P_A in C_D
     (B4) and C_D absorbs multiplication within degree D. [H] under the degree budget
     K + 2 Delta_1 + Delta_{AB} + d_1 <= D. Fan-in does not enter. Good sign.
 (ii) Two approximators of the same gate cannot both claim: for a term T, the "true claim"
     P_T and a "false claim" P'_T = 1 - prod_nu (1 - w_nu^(p-1)), w_nu in the span of the
     indicators of (h_i != 0), satisfy f P_T P'_T in C_D, since 1 - (1 - P') lies in the ideal of
     the w_nu and f h_i^(p-1) P_T in C_D by B4 (multiply f h_i P_T by h_i^(p-2)). [H] under
     similar degree budgets. This is the relation needed to move a formula across the
     sequent arrow (negation).
 (iii) Cut on a depth-2 formula A, weakening, contraction, OR rules, the dual (AND-of-OR) gate
     type with its own two-sided pair of approximators, and the unbounded-width bookkeeping
     of a line with arbitrarily many depth-2 disjuncts: [?], not derived by me. In (iii) the
     cut needs that the "A false" claim of L_1 and the "A true" claim of L_2 (the line with the
     negated A) combine to f P_{L_3} in C_D, which requires (ii) for the composite gate A
     (a DNF), i.e. an iterate of (ii) through two layers, with the cofactors of the identity
     1 - P_L = sum_j U_{L,j} P_{T_j} having degree up to Delta_2 - Delta_1; likely fine, but each
     case multiplies degree budgets and none is written.
 (iv) MOD_p gates over layer-1 gates: [X/?] the true indicator of (sum_j [T_j]) = c mod p
     has unbounded degree and its relation to the approximated sum sum_j P_{T_j} requires
     that errors of the T_j, which are only controlled one witness at a time, do not
     accumulate over an unbounded number of summands; no argument is given. Pang's remark
     covers only AND/OR layers. For the project's target (depth 2 AC0[p]-Frege with MOD_p
     connectives) this is not a minor omission. It means the sketch as stated, even with H,
     does not reach depth 2 AC0[p]-Frege with MOD connectives at layer 2; it reaches
     depth-2 AND/OR formulas over MOD_p-of-literal equations (Res of DNF/CNF of linear
     equations) only. CONJECTURE for the full system.

B6 Parameters (Step X1: needs H). From Section 1: need D >= K + O(Delta_2) with
Delta_2 = M^(4 gamma C_1) polylog M. To exclude every polynomial size one needs
gamma = o(1) so D >= (1/2 - o(1)) n. [X] Hypothesis H is open, with no known family
(Section 2). For a fixed ratio the conclusion is only M >= n^(Theta(1/gamma)).

First step that does not go through: B6 (it needs H), with B5(iii) and B5(iv) as the first
unwritten inference steps. If one grants H as an assumption, the first step that is not
established is B5(iv) for genuine MOD_p connectives at depth 2, and B5(iii) for cut. The
algebra of B2-B4 and the simple cases B5(i)-(ii) go through.

## 4. Barrier and kill audit

- K1 (quasi-polynomial depth-2 AC0[p]-Frege refutation of the chosen family): no such proof
  known; not triggered.
- K2 (universal PC degree upper bound below n/2): not established; the best I have is the
  Tseitin cutwidth bound (a method-specific upper bound, ratio 1/2 - Theta(1/sqrt d) for large d
  and about 1/3 for cubic) and the PHP bound.
- K3 (consequence check): H would give super-polynomial depth-2 bounds only for the
  AND/OR-over-equations fragment (B5(iv)); no pseudorandom-generator consequence arises
  because the argument is an explicit algebraic approximation for a fragment of Res of DNFs.
- K4 (three failed attempts per method): attack A has now been examined once in full (this
  document) and fails at B6 without H. Attack B is reduced to H (Section 2.5) and is dead as
  a separate method. Attack C is untouched.

Even if H were found, note a structural limit of this route (CONJECTURE): the proof system
reached is a fragment (AND/OR over bounded-degree equations), which is the same system class
as Res(k)-type lines over linear equations: super-polynomial bounds for depth-2 with
AND/OR layers over MOD_p equations would be a strict improvement over Pang depth 1 but
strictly weaker than depth 2 AC0[p]-Frege.

## 5. Recommendation (not a task assignment)

1. Treat the Pang depth-2 route as dormant: the only open item that could revive it is a
   family with D/n >= 1/2 - o(1), and the evidence in Section 2 is against it. Do not spend
   formalization effort on depth 2 until such a family or a proof of H for a named family
   exists.
2. If anyone wants to test H cheaply: Tseitin parity (p odd, n = E) on d-regular expanders
   with d growing slowly; compare PC degree lower bounds (expansion arguments) against the
   cutwidth-type upper bound 1/2 - Theta(1/sqrt d) of Section 2. A lower bound ratio above
   1/2 - O(1/log n) for one family would revive the route; a matching upper bound would settle
   K2 for that family.
3. Meanwhile the depth-1 line (Pang's theorem, already being formalized) is where certified
   progress is available.

## 6. Session log (append-only)

- 2026-10-14 prover: Pang TeX fetched to /private/tmp (outside repo), Section 8 (Conclusions)
  read in full, Sections 4 and 6 and applications re-read. Redid the scout calculation:
  confirmed (Section 1). Question A: no known family near 1/2, method not formally killed
  (no universal upper bound proved), rated under 3 percent. Question B: algebraic core and
  simple inference cases go through by hand; failure at the parameter step without H;
  cut and MOD_p-over-gates inference not derived. Web search for PC degree upper bounds
  for sparse CNFs returned nothing relevant (no theorem found either way for a universal
  (1/2 - c) n bound). No Lean, no build. No claim of a proof.
