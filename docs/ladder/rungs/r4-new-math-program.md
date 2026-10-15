# R4 new-math program: how to explore depth 2 and constant-depth AC0[p]-Frege

Status: research program, prose plus small scripts. No Lean, no builds. Date 2026-10-15, branch r4/newmath.
Reads: r4-frontier.md, r4-phase23-{plan,analysis,program,c1,r3,killtest,overlap}.md, statement-fidelity-dossier.md.
Scripts: r4-phase23-scripts/blockalign.py (+ blockalign_output.txt), r4-phase23-scripts/ub_probe.py (new this session).

Labels: PROVED-BY-HAND (derived on paper, here or in an earlier note, not machine checked), COMPUTED (a script in this repo, run),
CITED-CHECKED (an earlier repo note says it read the abstract or text; I did not re-read), CITED-UNCHECKED (recalled from memory,
not verified; every author/group list below is in this class unless stated), CONJECTURE. Machine-checked Lean facts are named as
"Lean-certified (dossier)", taken from the dossier and r4-frontier.md, not re-run. Odds are my judgment, not measurements.

## 0. Where we stand (one paragraph)

No super-polynomial bound for AC0[p]-Frege at any depth, depth 2 included, is known (CITED-CHECKED, plan Sec 1.1). The repo has
Lean-certified: bounded-depth Frege PHP (mod-free), Count_q with Count_p axioms, PC degree/size for Tseitin mod q over F_p,
tree-like Res(+), Res(lin F_p) tree-like width, and (per dossier) Pang's dag-like Res(lin F_p) Tseitin bound and C1 (depth 2 with
total term rank <= eps log n). The Pang method is a "Razborov-Smolensky for proofs": approximate each line by a product of
degree-Delta rank-reducing factors, find a common multiplier by a dimension count in V_K (multilinear polys of degree <= K) modulo the
PC-degree consequence space C_D. Measured limit of that method: per-round loss theta_1 = N_{n-rho}(K-rho)/N_n(K) ~ (K/n)^rho
(COMPUTED, killtest/overlap, n <= 18), hence rho = O(log n), and depth 2 with unbounded-rank ANDs needs PC degree ratio D/n >= 0.467
(PROVED-BY-HAND arithmetic, program Sec 0) while Tseitin mod 2 has D/n <= 1/4 + o(1) (PROVED-BY-HAND with rounding caveat, program
Sec 2.5, extended to all XOR systems as a sketch). So the method as is cannot reach depth 2; the question is what to do instead.

## 1. Map of techniques and exactly why each stalls at depth 2

Format: what it proves nearby; what it needs; the precise point where it breaks for depth-2 AC0[p]-Frege (lines are depth-2
formulas: OR/AND of MOD_p gates of ORs/ANDs of literals, with cut).

1. Razborov-Smolensky approximation (circuits AC0[p] cannot compute MOD_q, q not a power of p; Lean-certified analogues
   smolensky_parity, smolensky_mod3). Needs: every gate has a low-degree F_p polynomial approximator that errs on few inputs; a
   function with all low-degree approximations erring on many inputs. Why it does not transfer: a proof is not a function. We
   must approximate all lines simultaneously and need the errors to be controlled on the set of points satisfying the axioms
   only, and each inference rule must map approximators to approximators. The error sets of the lines are unions over S lines;
   the union bound costs S times the per-line error, so we need per-line error 1/S, i.e. approximator degree ~ log S. For circuits
   that is fine (degree (log s)^d against a function of degree n). For proofs the polynomial must additionally lie outside the
   consequence space C_D, which is where the PC degree of the formula (Pang) enters; the common multiplier then costs the dimension
   ratio N(K-d)/N(K), which for degree-d approximators is (K/n)^d. At depth 2 the second layer's inputs have degree Delta_1 ~ t_1 rho
   (not rho), so d_2 = Delta_1 and the exponent compounds: size exponent a(c) = 1/(C ln((1-c)/c)) (analysis Sec 1, PROVED-BY-HAND).
   Break point: the union bound over gates forces t_1 ~ ln(M_1)/eta rounds, and eta ~ (K/n)^rho is exponentially small in the term rank.
2. Switching lemmas and bounded-depth Frege (Ajtai; Pitassi-Beame-Impagliazzo; Krajicek-Pudlak-Woods: k-evaluations over random
   restrictions; Lean-certified for PHP mod-free and Count_q with Count_p axioms). Needs: restrictions that collapse depth by
   one with high probability and leave a hard instance. Why it fails with MOD gates: a MOD_p gate (fan-in m) is not simplified by
   fixing a random subset of its inputs: it stays a MOD_p gate of the remaining inputs, so the depth never drops (the "star" count
   bookkeeping of the encoding switching lemma has no analogue). Restrictions keep the formula but the k-evaluation needs a
   decision tree of small depth for each line; a MOD_p of m inputs has decision tree depth m. This is the same wall as for
   AC0[p] circuits, where restrictions are replaced by approximation. PROVED-BY-HAND (structural), CITED for the literature.
3. Degree/rank and Pang-style approximation for Res(lin F_p) (Lean-certified: PC degree and size for Tseitin; Pang per dossier).
   Needs: lines whose negation is a conjunction of equations of total rank <= rho. At depth 2: (a) an AND of unbounded rank has
   no low degree equation; (b) a MOD_p gate over bounded-rank terms IS a single degree (p-1) rho equation (r3 R2, PROVED-BY-HAND),
   so that part is cheap; (c) MOD_q gates, q != p, have no low-degree equation at all (this is Smolensky's separation turned
   against us: we cannot even write the line); (d) cut on a DNF needs its negation, a CNF. Plus the measured (K/n)^rho wall.
4. Feasible interpolation (Krajicek-Pudlak, Pudlak, Bonet-Pitassi-Raz). Works for Res, CP, Res(lin) when lines have monotone/
   low-complexity structure. Closed door at depth >= 2 with MOD gates: bounded-depth Frege does not have it under factoring or
   DH-type assumptions (Bonet-Pitassi-Raz, Bonet-Domingo-Gavalda-Maciel-Pitassi; CITED-UNCHECKED). So no route; it also says that
   proof-size lower bounds at depth 2 cannot come from circuit lower bounds via interpolation.
5. Lifting theorems (Raz-McKenzie, Goos-Pitassi-Watson, de Rezende-Nordstrom-Vinyals; for Res(+): Alekseev-Itsykson STOC 2025,
   CITED-CHECKED abstract in r4-frontier). Lift a width/degree/rank bound of F to size of F o gadget in a system. Works for Res(+)
   because a line is one affine-subspace-membership and a gadget with stifling kills it. At depth 2 a line is a DNF of such
   subspaces, so "rank" of a line (the object the simulation tracks) is not bounded by width of a base object, and bounded-depth
   lifting results stop at depth ~ N log log N for Res(+) (CITED-CHECKED, frontier) which is depth of a decision-DAG, not formula
   depth. Open: what is the right potential for formula depth. Also: lifted formulas are gadget-composed, not Tseitin/PHP themselves.
6. Random restrictions and their failure with MOD gates: see 2. One extra observation (PROVED-BY-HAND, program Sec 2.6 sketch):
   restricting a Tseitin system keeps it an XOR system, and every unsatisfiable XOR system has PC degree <= n/4 + o(n) over odd p,
   so no restriction can raise D'/n' above 1/4. Attack B of plan Sec 3.2 (restrict to raise the ratio) is dead for Tseitin by this
   cap (conditional on the rounding caveat in the program note).
7. Proof complexity generators (Krajicek; Alekhnovich-Ben-Sasson-Razborov-Wigderson pseudorandom generators in proof complexity;
   Razborov's conjectures; CITED-UNCHECKED). Provide candidate hard tautologies tau(g)-formulas for strong systems, with
   hardness conditional on PRG-type assumptions. For AC0[p]-Frege the ingredients are exactly "a function hard for AC0[p]
   circuits" (MOD_q) but one needs the hardness to be provable inside the system; not available. They are a source of candidate
   families, not an attack.
8. Hardness magnification (Oliveira-Santhanam, Chen-Jin-Williams, Pich-Santhanam on magnification in proof complexity;
   CITED-UNCHECKED). A weak lower bound for a sparse/average problem implies a strong one. Proof complexity versions (Pich-
   Santhanam, "Strong co-nondeterministic lower bounds for NP cannot be proved feasibly" and related) say: if the weak lower
   bound could be proved in a feasible theory, so could the strong one, which is a barrier-like warning rather than a method.
   For us: no magnification theorem for AC0[p]-Frege is known to me; the useful reading is "locality barrier": methods that
   work equally well for small-fan-in lines should be re-checked against the known magnification-locality obstruction.
9. Barriers. Natural proofs (Razborov-Rudich): apply to circuit lower bounds against PRF-capable classes; AC0[p] cannot compute
   PRFs (circuit side unconditional, Smolensky), so no natural-proofs barrier for the approximation method at this level
   (plan Sec 3.4; CONJECTURE that none appears; the approximation method is "natural" but against a class below PRF strength).
   Relativization/algebrization analogues for proof systems: none known to me; the method is algebraic and non-relativizing in the
   oracle sense (CITED-UNCHECKED, plan says "none found"). Krajicek's conditional results (arXiv 1311.2501 reduction of AC0[p]-
   Frege to search tasks over low-degree polynomials; ENS / pseudo-solutions arXiv 2609.35927: CITED-CHECKED at abstract level)
   give an equivalent formulation, not a bound, and the pseudo-solution hypothesis with large k has strong consequences (plan
   Sec 1.1; tension noted, not resolved). Impagliazzo-Mouli-Pitassi: constant-depth IPS and AC0[p]-Frege are related, so any
   argument must separate from constant-depth IPS upper bounds (CITED-UNCHECKED). Lu-Santhanam-Tzameret (CITED-CHECKED):
   AC0[p]-Frege cannot prove some constant-depth algebraic circuit lower-bound DNFs; relevant as a source, not a candidate.

Summary of what the map says: every method either needs a union bound that costs a dimension drop exponential in the term rank
(1, 3), a collapse of MOD gates that does not occur (2, 6), a closed door (4), or conditional hypotheses (7, 8, Krajicek). The one
unexplored resource is the structure of the specific formula (Tseitin on an expander): all the data above concern C_D = 0 or generic
families, and the lower bounds so far use Tseitin only through its PC degree.

## 2. How working mathematicians explore a frontier like this

### 2.1 The ladder of restricted systems (what we proved, then what is next)

Each rung: system, status, first lemma. The rule is: climb one rung only when the previous rung's method is understood well enough to
say what breaks.

| # | System | Status | First lemma |
|---|--------|--------|-------------|
| 0 | Bounded-depth Frege, mod-free (PHP, Count_q with Count_p axioms) | Lean-certified | done (switching, k-evaluations) |
| 1 | Tree-like Res(+) | Lean-certified (frontier doc) | done |
| 2 | Tree-like Res(lin F_p) Tseitin | width half Lean-certified; size via dossier Sec 3 | done per dossier |
| 3 | Dag-like Res(lin F_p), Tseitin mod q, p not dividing q (Pang, Khaniki, Braun for bit PHP over +) | Pang Lean-certified per dossier; sources unrefereed, Braun unchecked | done / external |
| 4 | R_rho^p: depth 2, each AND of total rank <= rho = eps log n (C1) | Lean-certified (`c1_main`), conditional on Pang | done |
| 5 | Rung 4 + same-p MOD gates over bounded-rank terms + cut on bounded-rank DNF | prose derivations only (r3 R2, R3), simulation of MOD_p rules unwritten | Lemma M: a MOD_p rule instance (counting identity S_k = sum chi_j) is derivable in PC degree O(rho) with O(N) overhead; test it by hand on S_1, S_2 |
| 6 | Rung 5 with rank up to n^c | blocked by (K/n)^rho wall; CONJECTURE barrier is intrinsic to the method | Lemma E: find any measure replacing dim V_K with ratio n^(-o(1)) per round (direction 3 below) |
| 7 | Depth 2, unbounded-rank ANDs | needs D/n >= 0.467, none known | Lemma H: constant-width CNF with PC degree ratio near 1/2 (analysis; killed for Tseitin by the 1/4 cap) |
| 8 | Depth 2, MOD_q gates (q != p) and MOD_p over ORs | no low-degree equation exists | Lemma Q: an approximation space for MOD_q gates compatible with the cut rule; open and probably needs new idea |
| 9 | Depth 2 AC0[p]-Frege (target) | open | assemble 5-8 |
| 10 | Constant depth AC0[p]-Frege | open | induct on depth with the compound exponent a(c)^depth |

Side toy ladders worth running because their failure data is cheap:
- Res(k) for k = (log n)^2 and k = n^c (subcube lines): the same (K/n)^rho wall without MOD, so progress there is progress on rung 6.
- p = 2 only, depth 2, parity gates of bounded fan-in (PK_2(+) fragments; Garlik-Kolodziejczyk, CITED-CHECKED abstract).
- Tree-like and regular depth-2 variants first (regular Res(+) is known: Efremenko-Garlik-Itsykson, CITED-CHECKED abstract).

### 2.2 Generate and kill conjectures by computer on small cases

What the notes already did well (COMPUTED): exact PC degree by fixpoint linear algebra (n <= ~14); exact optimum of the round-by-round
approximation over all subspaces of F_2^s; dense/sparse overlapping subcube families. Reusable recipe: (i) fix a lemma shape with a
free parameter (rate, ratio); (ii) compute the exact extremum on all instances up to isomorphism for tiny n, then sampled search
(hill climbing) beyond; (iii) record whether the extremum tracks a closed formula (here theta_1); (iv) kill the lemma if one
instance beats the formula by a factor growing with n. Known gap: all runs have C_D = 0 and n <= 18; no Tseitin with PC degree
>= 5 was reachable by dense algebra (killtest Sec 4). To do: sparse/structured linear algebra (rank over GF(2) of bit-matrices
with >= 10^4 columns) so that Tseitin on 18-30 edge variables, with C_D nontrivial, can be tested. This is infrastructure, ranked in 4.

### 2.3 The right invariant

We want a measure mu on lines/sets with: mu(axioms) small; mu(conclusion) <= mu(premises) + mu(premises') (subadditive under each
rule, or at least under the approximated rule); mu(empty line) large for the target formula. Existing instances:
- Width (resolution): subadditive under resolution up to +1; large for PHP/Tseitin by expansion.
- PC degree/dimension (Pang): the "measure" is the rank c_P(K), monotone but its drop per round is only theta_1 = (K/n)^rho.
- Rank of an affine subspace (C1): sub-additive only for bounded rank.
Properties a depth-2 measure must have: (a) assigns bounded value to a MOD_p gate of bounded-rank terms (OK for dimension count);
(b) assigns bounded value to an AND of rank r with value that grows slowly, not exponentially, in r; (c) handles cut on a DNF.
The measured (K/n)^rho is the Hilbert ratio of V_K; any measure that changes this ratio from polynomial in K/n to a ratio that does
not carry the exponent rho would be new. Candidates in 4: block-aligned subspaces W_K (direction 2); the Fourier/cohomological
basis of Tseitin (direction 3); Krajicek's search-tree/pseudo-solution measure (direction 5).

### 2.4 Upper bounds as a research tool (redirect everything)

If depth-2 AC0[p]-Frege has short proofs of Tseitin mod q (p not dividing q) on expanders, every lower-bound attempt on that
family is dead and the effort should move to PHP-type or random-CSP families (kill condition K1 of the plan). Known short proofs:
Tseitin mod p over F_p (same modulus) in Res(lin F_p) (Part-Tzameret/Pang Sec 7.2, CITED-UNCHECKED); weak PHP in quasi-polynomial
bounded-depth Frege (Maciel-Pitassi-Woods, CITED-CHECKED abstract). Not known: short AC0[p]-Frege proofs of onto/bit PHP,
Count_q with p not dividing q, or Tseitin with p not dividing q on expanders. Computed this session (ub_probe.py, COMPUTED,
Tseitin mod 2 with Boolean edges over odd p, upper bound from a vertex ordering, program Sec 2.5): PC degree upper bounds

    ladder 2xm, m = 4..64 (E = 10..190): D_ub = 3 constant         (size bound 2^(O(log E)): polynomial)
    random cubic V = 10, 20, 40, 80, 160 (E = 15..240): D_ub = 3, 4, 6, 11, 19   (about E/12.6; size bound 2^(0.39 E) at V = 160)

That is the depth-1 algebraic picture: cutwidth-bounded Tseitin is easy at every depth, expanders cost exp(cutwidth). A depth-2
proof must beat the cutwidth barrier by exploiting MOD_p gates; Smolensky says AC0[p] gates cannot count mod q, which is why this
is believed impossible, but the proof system could pay for counting by lines rather than by gates, so the belief is not a theorem
(CONJECTURE).

### 2.5 Reading failures as data: what exactly breaks at depth 2

From the notes, in one list (each item is a different potential fix):
1. Union bound over gates: forces degree log S approximators; cost (K/n)^(rho log S) when rho is large; fix = a measure that does not
   see the binomial ratio, or approximators of lower degree (not available for AND of unbounded rank).
2. Unbounded-rank ANDs: a depth-2 line OR_j AND_i eq_ij has terms of rank up to n; the equation of an AND is degree rank (r3 R1).
   Fix = hypothesis H (layered approximators; needs D/n ~ 0.47+), dead for Tseitin, open for other families.
3. MOD_p gates of fan-in > rank: not an obstruction when the inputs are bounded-rank terms (r3 R2, indicators are 0/1, sum is
   degree (p-1) rho). It is an obstruction when the inputs are ORs/unbounded ANDs, or when q != p.
4. Cut on DNF: needs the CNF negation, rank up to s; covered iff the span has dimension <= rho (r3 R3).
5. The disjoint-block adversary is not the real one: it stops being adversarial when rho > 4/delta (s < K); the real adversary is a
   sparse overlapping family with s >> K (killtest Sec 3.3; overlap Sec 2.3: ratio 1.1 to 1.5 theta_1 for the first rounds).
6. Dense (clique-rich) families beat theta_1 by factors 5 to 9 at small K (overlap Sec 2.2): so a structure-dependent lemma exists in
   principle; a uniform one does not (on the evidence).

### 2.6 Community practice

Write up the partial results as stand-alone notes: (i) "depth 2 with bounded-rank terms and MOD_p gates over them" (rung 5; the
only part of depth 2 provable now, modulo Pang's unrefereed status); (ii) the PC-degree cap n/4 for XOR systems (a clean negative
result: program C2); (iii) the (K/n)^rho tightness data as a barrier note. Ask experts exactly three questions: is there a known
constant-width CNF with PC degree ratio above 1/4 over some F_p (Alekhnovich-Razborov type)?; is a short depth-2 AC0[p]-Frege
proof of Tseitin mod q known or ruled out?; is the (K/n)^rho dimension-count loss known to be tight for Res(k)? Groups and names
(all CITED-UNCHECKED, from memory, no verification attempted): Pitassi, Impagliazzo, Tzameret (algebraic proof systems, constant-
depth IPS); Krajicek (reductions, pseudo-solutions); Kolodziejczyk, Garlik (Res(+), PK(+)); Itsykson, Sokolov, Alekseev,
Efremenko, Bhattacharya, Chattopadhyay (Res(+), lifting); Razborov, Santhanam, Oliveira, Pich (barriers, magnification); Beame,
Hastad, Ben-Sasson, Nordstrom, Lauria, Atserias, Muller (bounded depth, switching, width); Part, Khaniki, Pang, Braun (the
dossier's sources; Pang and Braun unrefereed, Braun AI-assisted per the dossier). Do not cite an unrefereed source as
settled; the dossier already tracks this.

## 3. The block-aligned subspace idea and the test I ran

Source of the idea: r4-phase23-overlap.md Sec 5 item 4 (the first-listed "other new method that avoids the rank barrier"), which
follows r4-phase23-r3.md Sec 0 item 6(b) ("replace the dimension count by a measure that does not see the binomial ratio"). I did
not find the phrase "block-aligned" in the notes; I use it for the disjoint-block form below.

Precise statement. Family F of subcube terms g_S = [x_S = 0] (|S| = rho), possibly disjoint blocks. Pang counts in V_K and loses the
Hilbert ratio N(K-rho)/N(K) ~ (K/n)^rho because a multiplication by g_S sends V_{K-rho} into V_K and the image has density (K/n)^rho
in V_K. Replace V_K by the smallest subspace W containing V_K and closed under multiplication by all g_S. Functionally
x_i(1-x_i) = 0, so g_S * m = m g_S if m misses S (else 0), and g_S g_S' = g_{S union S'}. Hence

    W_{K,t} = span{ [x_m = 1][x_U = 0] : |m| <= K, U a union of <= t sets of F, m disjoint from U }  (t multiplications; W_{K,0} = V_K).

Hoped property: the Hilbert ratio dim W_{K-rho,t}/dim W_{K,t} is about K/n (the density of a whole block) instead of (K/n)^rho, so a
common-multiplier count in W would lose only a constant per round. Kill condition (overlap Sec 5.4): W is all of V_K (or of the
ambient space), or the ratio does not improve.

Test (COMPUTED, blockalign.py, GF(2), exact ranks of truth tables on {0,1}^n; output in blockalign_output.txt):

    n=12 rho=2 K=4 disjoint s=6:  V ratio .0995, K/n .333;  t=1,2,3: dim W_K = 2254, 3349, 3635 (of 4096); ratio .175, .267, .349
        dim W_K / N(K+t rho) = .898, .882, .890       (t >= 4: dim 3648 = saturated, ratio .386)
    n=12 rho=2 K=3 cycle s=12:    V ratio .0435;  t=1,2,3: ratio .092, .197, .386;  dim W / N(K+t rho) = .91, .94, .95
    n=12 rho=3 K=4 disjoint s=4:  V ratio .0164;  t=1,2,3: ratio .031, .047, .055; dim W / N(K+t rho) = .53, .49, .49
    n=14 rho=2 K=3 disjoint s=7:  V ratio .0319;  t=1,2: ratio .047, .066; dim W / N(K+t rho) = .65, .51
    n=14 rho=2 K=3 random s=20 (earlier run, not in the saved output): t=1,2: ratio .074, .167

Reading. (a) The ratio does improve with t, from (K/n)^rho toward about K/n, but only because W grows: for rho = 2 at n = 12,
dim W_{K,t} is 88 to 95 percent of N(K + t rho), i.e. W is nearly the whole degree-(K + t rho) space, and the ratio is the V-ratio at
the larger degree. Closure saturates (all of 3648 of 4096 for the disjoint family, t >= 4). So for the budget that matters
(t rounds, each costing degree rho) the aligned subspace gives no structural gain over V_{K+t rho}: this is the "W is all of V_K"
kill in its graded form. (b) For rho = 3 (s = 4 blocks) and n = 14 (s = 7), W is 50 to 65 percent of V_{K+t rho} and the ratio is below the
degree-(K+t rho) ratio; but s is too small there to be adversarial (s < K + t), so this is not evidence for the hoped property.
(c) The test cannot reach the application regime (t_max = delta n/(24 rho) < 1 round at n <= 16).
Verdict: not killed in the strict sense (at rho = 3, n = 14 W is a proper fraction), but the one regime that is adversarial (rho = 2,
s >= 6) shows W essentially equal to the degree-(K+t rho) space. Odds that a block-aligned W gives a rho-free rate: about 5 percent
(CONJECTURE). A better version would take W inside a smaller closed algebra (for example, only multiplication by whole-block
indicators in a Boolean-algebra basis adapted to a fixed block partition, not by arbitrary products), and compare W_{K,t}
to the subspace of functions measurable w.r.t. the block pattern; I did not run that.

## 4. Ranked research directions

Each: precise first question; cheap test on this machine; kill condition; honest odds that the direction produces a new
super-polynomial bound for depth-2 AC0[p]-Frege (odds that it produces a useful partial result in brackets).

### D1. Upper bound first: short depth-2 proofs of Tseitin mod q over F_p

First question. For p = 3, q = 2 (and p = 2, q = 3; p = 5, q = 2), is there, on cubic expanders on V vertices, a family of
depth-2 AC0[p]-Frege refutations of size V^(O(1)) of Tseitin_q (Boolean edge variables)? Natural construction attempt: prove, for each
vertex order, that the partial sums satisfy S_k = (sum of boundary edge values) mod q by a depth-2 formula "boundary count = c"
(a MOD gate over edge variables) and induct. This works iff "boundary count mod q" has a depth-2 AC0[p] description for boundary
size ~V, which is MOD_q of V inputs: exactly Smolensky's lower bound for circuits. Obstruction in proofs: you need not compute it,
only prove consistency between consecutive sums; each step needs a lines of size poly(cut size) unless the cut state is described
by few lines. CONJECTURE: size exp(Omega(cut)) = exp(Omega(V)) for expanders.
Cheap test. (i) Done: ub_probe.py (depth-1 algebraic upper bound by vertex order, table in 2.4). (ii) Next, concrete: exact minimum
size of tree-like and dag-like refutations of Tseitin_2 on K4/prism/K33 in a bounded line language over F_3: lines = OR of at most 2
terms, each term an AND of at most 2 F_3-affine equations, rules = resolution-with-linear-combination, cut on lines; search by
saturation (BFS on lines, width cap) with a SAT solver or a hand-written closure; compare the minimum size with Res(lin F_3) (depth 1)
and with plain resolution. If depth-2 lines give strictly smaller proofs growing slower on the family K4 -> prism -> K33 -> Q3
(V = 4, 6, 6, 8, E = 6, 9, 9, 12), the shape of the savings tells us what the depth-2 trick is. (iii) Prose: write the exact
Tseitin proof via partial sums and count lines per step.
Kill condition. For this direction as a quest for short proofs: exponential growth of the exact minimum over 3 or 4 graphs matches
the depth-1 curve (no savings), i.e. no evidence that depth 2 helps; in that case the upper bound is not found and the direction has
done its job as a sanity check. A genuine poly-size family kills the Tseitin candidate (plan K1) and redirects to PHP-type formulas.
Odds. Poly-size depth-2 proofs exist: 5 percent (CONJECTURE). The search being informative regardless: high.

### D2. Block-aligned subspace W_K (Section 3)

First question. Is there a family of subspaces W_K, closed under multiplication by the lines' terms, with dim W_{K-rho}/dim W_K >=
n^(-o(1)) in the adversarial regime s >> K?
Cheap test. Run (blockalign.py) with sparse overlapping families at n = 14..16 restricted to multiplication by single terms
(t = 1, 2) and compare dim W_{K,t}/N(K+t rho) against the V-ratio at K + t rho. Done above for n <= 14; extend with the
restricted algebra of block-pattern-measurable functions.
Kill condition. dim W_{K,t} >= 0.8 N(K+t rho) in the s >> K regime (W is essentially V_{K+t rho}); already seen for rho = 2.
Odds. 3 to 5 percent (negative so far).

### D3. A native measure for Tseitin: Fourier / cohomological basis

First question. Pang's rank is over monomials of the edge cube, but the Tseitin PC degree proof (Lean TseitinPC.lean) works with the
operator R sending a monomial to the minimum-degree monomial in its class modulo coboundaries. Redo the common-multiplier count
in the quotient by coboundaries: is the density of {g f : deg f <= K - d} in the quotient V_K / (coboundary relations) larger than
(K/n)^rho when g is an indicator of a subspace of the form "sum over a cut"? Heuristic: in the quotient the number of classes of degree
<= K is governed by H^1 (dimension E - V + 1) and lines that are "cut subspaces" may have density (K/E)^(rho') with rho' << rho.
Cheap test. Small graphs (K4, prism, K33, Q3; E = 6..12, p = 2/3): compute the quotient Hilbert function and the kernel fraction of
multiplication by cut-indicators, compare with theta_1 (r3_e1-style; extend r3lib.py).
Kill condition. Kernel fraction in the quotient equals theta_1 up to 1.5x on all four graphs.
Odds. 3 percent for a rho = n^c breakthrough (CONJECTURE); this is the one direction that uses the structure of Tseitin, which every
other measured number ignores. [Useful negative result: high.]

### D4. Write up rung 5: MOD_p gates over bounded-rank terms and cut on DNFs

First question. Lemma M: for a MOD_{p,c} gate of s bounded-rank terms the counting-identity rules (S_k = sum_{j<=k} chi_j, linear)
simulate in Res(PC_r/F_p) at degree O(rho), and cut on a DNF with span rank <= rho simulates by s resolution steps.
Cheap test. Hand derivation for p = 3, s = 3 in prose (five lines); then a script that enumerates the rule instances for p = 2, 3,
s <= 4, rho <= 2 and verifies each by brute force PC degree <= (p-1) rho + O(1) (pcdeg.py).
Kill condition. A rule instance needing degree growing with s (then R2 is wrong, which also corrects the r3 note).
Odds of full depth 2: 0; odds of a correct and publishable partial result (depth 2, rank <= eps log n, MOD_p over bounded-rank
terms, modulo Pang): 55 percent. This is the "failure data" generator: it fixes exactly which depth-2 features cost nothing.

### D5. Krajicek's pseudo-solution / search-tree measure

First question. Read arXiv 2609.35927 in full; state the search-tree property for the Tseitin family (not PHP) as a statement about
decision trees querying F_p-linear maps on low-degree polynomials; test it on small n.
Cheap test. Prose extraction of the hypothesis (plan task 7); a toy computation of the quantity for n <= 10 only if it is
finitely checkable. CITED-CHECKED only at abstract level; the hypothesis may be false (tension with Extended Frege simulation noted).
Kill condition. The hypothesis for k(n) super-polynomial implies UENS does not simulate TC0-Frege while UENS is believed to
simulate EF (plan): if this tension is real, the direction is dead; if it is a misreading, the property is a reformulation, not a method.
Odds. 2 percent.

### D6. Extremal PC degree hunt for non-Tseitin families (Lemma H)

First question. Is there a constant-width CNF with PC degree at least (0.47) n over some F_p? Tseitin mod 2: no (cap 1/4).
Candidates: Tseitin over F_q groups, random k-CNF near threshold, PHP-type with large degree, XOR-AND mixtures.
Cheap test. Dense PC-degree for random 3-CNF with n <= 14 (kt_search.py unfinished; needs sparse linear algebra) and for
structured formulas; the best ratio found so far is about 0.4 at tiny n (Tseitin mod 2 on K5, degree 4 on 10 variables) and
that is a small-n artifact (cap 1/4 asymptotically).
Kill condition. A proof that every constant-width CNF has PC degree <= (1/2 - c)n over every F_p (plan K2). Random 3-CNF SoS/PC
degree decreases with clause density above the threshold (Grigoriev, Schoenebeck type; CITED-UNCHECKED), so the ceiling is near the threshold density.
Odds. 2 percent.

### D7. Lifting for formula depth

First question. Does the Alekseev-Itsykson STOC 2025 game-lifting (width of F -> rank of F o Maj3 in Res(+), depth <= N log log N) extend to
depth-2 formulas with a lifting of "rank" to "rank times depth-2 structure"? Specifically: find a combinatorial game whose value
is monotone under depth-2 MOD_2 inference, p = 2 only.
Cheap test. Prose reading of the paper and the Lean file LiftDup.lean; define the depth-2 Duplicator conditions on a toy (Maj3
composed PHP_3) and check by brute force that a Duplicator for the base survives all depth-2 rule instances.
Kill condition. A depth-2 rule instance (cut on a DNF) that destroys the Duplicator invariant on the toy.
Odds. 4 percent (p = 2 only; generalization to p odd unknown).

### D8. Barrier audit and infrastructure

First question. Which of our measured quantities are properties of the argument form rather than of Tseitin: does any version of
the argument prove a lower bound for a family with a known short AC0[p]-Frege proof (a control)? Controls: Tseitin mod p over F_p;
Count_p. Cheap test: run the exact optimum (kt_opt-style) on the Tseitin-mod-p axiom structure and check that no unconditional
rank argument "proves" hardness. Plus sparse GF(2) linear algebra (bit-packed, 10^4 to 10^5 columns) to reach Tseitin with PC degree 6
(infrastructure for D3 and D6).
Kill condition. A control family obtains a bound (the argument is unsound). Odds of new math: ~0; value: prevents wasted work.

## 5. Recommendation: pursue D1 first, then D4 together with D3

1. D1 (upper bound first). It is the only direction whose outcome redirects the whole program in either case: a short depth-2 proof
   family kills the Tseitin candidate and the lower-bound line; its absence (exact minimum tracks the depth-1 curve on K4, prism,
   K33, Q3) is the first piece of evidence that the depth-2 saving does not exist, and the exact small-case proofs show which
   line shapes would carry it. Cheap: a finite search on E <= 12 variables; the depth-1 curve is already computed.
2. D4 together with D3. D4 is the only direction with a high chance of a finished, correct partial result (probable and
   cheap), and writing the rule simulations is the precise way to learn which depth-2 features are free and which cost the (K/n)^rho
   loss (failure as data, 2.5). D3 is the only candidate that uses the structure of Tseitin rather than the generic dimension count,
   so it is the best shot at a genuinely new measure; run its small-graph kernel-fraction test right after D4 since both reuse
   r3lib.py. D2 stays a documented near-negative; D5 to D8 are tracked, not pursued.

Honest overall odds that this program produces a super-polynomial depth-2 AC0[p]-Frege lower bound (CONJECTURE): below 2 percent in the
next months; about 5 percent that it produces a conclusive structural statement (a short-proof family or a proved barrier) that
decides whether Tseitin is the right candidate.

## 6. Session log (append-only)

- 2026-10-15 scout/prover/auditor (new-math program): read the eight r4 notes and the dossier; wrote blockalign.py (block-aligned
  closure test, exact GF(2) ranks, n <= 14) and ub_probe.py (depth-1 degree upper bound for ladders vs cubic expanders);
  ran both; wrote this note. Block-aligned test: W saturates to 88-95 percent of V_{K+t rho} for rho = 2. No citation re-checked;
  all names and venues above that are not marked CITED-CHECKED are unverified. No Lean, no builds. Nothing pushed.
