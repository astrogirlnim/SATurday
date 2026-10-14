# R4 Phase 2.3, round 3: the rank lemma for affine-subspace indicators (where the rho = Theta(log n) barrier comes from)

Status: research notes, docs and small scripts only. No Lean, no builds. Date 2026-10-14, branch r4/prover-r3.
Follows r4-phase23-c1.md (round 2), r4-phase23-program.md, r4-phase23-analysis.md, and r4-pang-plan.md
Section 2 (layers L0-L8) and Section 10 (Lean status of PangMult, PangPencil, PangDescent).

Labels: PROVED-BY-HAND (derived on paper, not machine checked), COMPUTED (a script in
r4-phase23-scripts/, prefix r3_, run this session), CITED (Pang's paper as summarized in r4-pang-plan.md
Section 2, or the round-2 documents, not re-read in the TeX this session), CONJECTURE.

## 0. Verdict

1. The target as phrased is vacuous. For the Tseitin application D/N = delta is a constant, so Pang's
   factor (D/16N)^((p-1)r) is already exp(-kappa rho) (round 2, kappa = 3(p-1)^2 ln(16/delta)). A lemma
   that "loses only exp(-O(rho))" is what we already have; it moves the barrier by a constant factor and
   not at all in order (PROVED-BY-HAND, Section 2). To reach rho = n^c the loss per round must be at
   most n^(-O(1)) uniformly in rho, i.e. rho-independent in the exponent.
2. The rho-dependent loss is not in the pencil/rank-retention lemma. That lemma (Lean:
   `Pang.pang_rank_retention`, rank_{F_p}(stack)*(p-1) <= p*rank(sum c_i M_i)) loses the constant factor
   (1-1/p), independent of rho. The loss arises in two counting steps, L5 and L4 (Section 1): the gain
   vectors q*f' need f' in V_{K-d}, and the normalized rank is only monotone: c_P(K-d) >= c_P(K) N(K-d)/N(K).
3. Data (Section 3): for the family "disjoint subcubes of codim rho", the best first-round gain equals the
   exact fraction of V_K supported on one subcube, N_{n-rho}(K-rho)/N_n(K) = prod_{j<rho}(K-j)/(n-j)
   (up to lower-order terms), for rho = 1 exactly at n = 12, 13 and every K tested, within factor 1.4 for
   rho = 2. So Pang's gain is tight up to the factor (1-1/p) in round 1 on this family. A uniform per-round
   lemma cannot beat (K/n)^rho. For the Tseitin parameters K = D/4 = delta n/4 this is exp(-Theta(rho)).
4. Hence the hoped lemma, in the only form that would move the barrier (uniform per-round gain at least
   n^(-eps)), is false for a uniform-rate method (computed for n <= 13, rho <= 2, extrapolated by a
   structural argument, CONJECTURE beyond). The true loss looks like exp(-rho ln(n/K)). A non-uniform
   (accelerating) rate is real in later rounds but the early slow phase of the block family lasts about
   n/(2 rho) rounds, which is longer than the degree budget D/(8 d) (Section 4).
5. Corrections to round 2 (Section 5): a MOD_p gate over rank-bounded terms IS a single equation of degree
   (p-1) rho (sum of indicators), so T3 of round 2 was misstated; the real obstruction for depth 2 is
   unbounded rank of the conjunction, which also governs cut on DNF formulas.
6. Recommended next step: stop pursuing the exp(-O(rho)) rank lemma. Either (a) accept the
   rho = O(log n) barrier for C1 and move to the non-uniform / structured question below, or (b) test the
   one structural escape: replace the dimension count (rank) by a measure that does not see the
   binomial ratio, which would amount to a new proof of Pang's size-degree theorem and is unlikely.

## 1. Task 1: exactly where the loss arises

Notation as in r4-pang-plan.md Section 2. d = (p-1) r is the degree bound of the indicator polynomials
g_{L,i} = ML(1 - h^(p-1)) of the equations (h = 0) of a line (r the equation degree). V_k = multilinear
polynomials of degree <= k, N_n(k) = sum_{j<=k} C(n,j), C_D = polynomials with degree-D PC derivations,
c_P(k) = rank of f -> ([P g_i f])_i on V_k into (V_D/C_D)^s.

Chain of the argument, with the loss of each step (CITED from the plan, layers L2-L8):

(a) L2/L3, pencil + Frobenius descent (Cor. 3.4, Lean `pang_rank_retention`): there is c in F_p^s with
    rank(sum c_i M_i) >= (1-1/p) rank_{F_p}(stack of the M_i). Loss: the constant factor (1-1/p).
    Independent of d, rho, K, n. (Lean statement read in r4-pang-plan.md Section 10; I did not open the
    .lean files, and did not need to: the statement is in the plan.)
(b) L5, Lemma 4.2 (onestep): with q = sum c_i g_i, P' = P(1-q^(p-1)), one has
        c_{P'}(K) <= c_P(K) - (1-1/p) c_P(K-d).
    The gain is q*V_{K-d}: multiplying f' in V_{K-d} by q (degree <= d) lands in V_K, which is the domain
    of the common multiplier f (deg f <= K). This is the first source of loss: the pencil lemma is applied
    to the stacked map on V_{K-d}, not on V_K, because f must keep degree <= K. Loss: c_P(K-d) instead of
    c_P(K).
(c) L4, Lemma 4.1 (hilbert): c_P(k)/N_n(k) is nonincreasing in k <= K, so c_P(K-d) >= c_P(K) N_n(K-d)/N_n(K).
    Proof: leading monomials in a graded order, down-closed family, double counting
    (j+1) b_{j+1} <= (n-j) b_j. This is the second source of loss and it is pure counting.
(d) L8 (Section 6 of Pang): K = floor(D/4), N_n(K) <= 2 C(n,K) for K <= n/3, and
    N_n(K-d)/N_n(K) >= (1/2)(D/16n)^d. The ratio C(n,K-d)/C(n,K) = prod_{j<d} (K-j)/(n-K+j+1) is about
    (K/(n-K))^d.
(e) Degree budget: the simulation (L7) needs K + max{2 Delta + 2d, Delta + w} <= D with
    Delta = t(p-1)d, so t = floor(D/(8(p-1)d)) rounds. With eta = (1-1/p)N(K-d)/N(K), the common
    multiplier exists if S(1-eta)^t < 1, giving ln S >= eta t, i.e. the displayed
    ln S >= (D/(32 p^2 r)) (D/(16n))^((p-1) r) (round 2, eq. I1).

So the (D/16n)^((p-1)r) loss is the product of (b) and (c), instantiated by (d). In the form "rank of
multiplication by an indicator g of a codim-rho subspace", the quantity lost is the fraction of V_K of
polynomials that can be written g*f' with deg f' <= K-d, and for a subcube this fraction is exactly the
fraction of V_K supported on the subcube (Section 2.1).

Precise statement of what a "rho-free" lemma would have to say (Lemma H, the needed form): for every
P of the product form and every family g_1..g_s of indicators of F_p-affine subspaces of codim <= rho,
every K >= d = (p-1) rho with room in D, there is q in the F_p-span with
        c_{P(1-q^(p-1))}(K) <= (1 - theta) c_P(K),   theta >= n^(-O(1)) (rho-independent exponent).
Pang proves theta >= (1-1/p) N(K-d)/N(K) = exp(-Theta(rho ln(n/K))).

## 2. The barrier arithmetic

### 2.1 PROVED-BY-HAND: single subcube
Let T = {x_1 = ... = x_rho = 0} on the cube and g its indicator, g = prod (1 - x_i). A multilinear f
vanishes off T iff f = g*f' with f' multilinear in x_{rho+1..n}, and then deg f = rho + deg f' (disjoint
variables, no cancellation). So dim{f in V_K : f = g f} = N_{n-rho}(K-rho), and the rank of f -> g f on V_K
is N_{n-rho}(K). Hence c_g(K-rho)/c_g(K) = N_{n-rho}(K-rho)/N_{n-rho}(K) ~ (K/n)^rho, and the fraction of V_K
killed by the round with q = g is N_{n-rho}(K-rho)/N_n(K). COMPUTED: r3_e1.py gives for n = 10, p = 2, K = 2,3,4,
rho = 1..3: z = dim{f supported on T} = 10, 46, 130 (rho = 1), 1, 9, 37 (rho = 2), 0, 1, 8 (rho = 3),
equal to N_{9}(K-1), N_8(K-2), N_7(K-3). Flatness table (r3_e4.py, exact): ratio
N_{n-rho}(K-rho)/N_{n-rho}(K) at K = n/16:

    n=100  K=10 : rho=1 1.1e-1, rho=2 1.1e-2, rho=4 7.8e-5, rho=8 5.2e-10
    n=1000 K=63 : rho=1 6.7e-2, rho=2 4.4e-3, rho=4 1.9e-5, rho=8 2.7e-10, rho=16 2.4e-20, rho=32 3.2e-42

i.e. exp(-rho ln(n/K)) up to lower-order factors.

### 2.2 PROVED-BY-HAND: the barrier is exp(-Theta(rho)) already
With D = delta N (certified), d = (p-1) r = 3(p-1)^2 rho and K = D/4: eta = exp(-Theta(rho)) with
Theta-constant kappa ln-factor as in round 2. Then ln S >= (D/d) eta ~ N exp(-kappa rho)/rho, which is
N^(Omega(1)) iff rho <= (1-c) ln N / kappa. A better lemma that is still exp(-C' rho) changes kappa to C' and
leaves the barrier at Theta(log n). To get rho = n^c: ln S >= t eta with t <= D/(8d) = n^(1-c)/O(1) forces
eta >= n^(-c'') with small c'' and ln S <= n^(1-c) at best. So the needed per-round gain is
n^(-o(1)): essentially a constant fraction of the rank per round. That is a much stronger requirement than
"exp(-O(rho))" and it is incompatible with 2.1 (Section 3).
(Round 2's suggestion "exp(-rho^(1-c))" would reach rho up to (log n)^(1/(1-c)), polylog, not n^c; this
also corrects the target of round 2 T1.)

## 3. Task 2: numerics

Method (r3lib.py): everything in the function basis on {0,1}^n over F_p; V_K spanned by monomial
functions; indicator of an affine subspace = prod (1 - l^(p-1)) (0/1 valued); c_P(K) = rank of the
stacked map modulo C_D (block-diagonal quotient); the quotient mod C_D uses the closure of pcdeg.py.
Pang round: q ranges over the projective F_p-span (exhaustive when small, 40-60 random samples otherwise),
P' = P * [q = 0]. For C_D = 0 (the Boolean ideal only: any formula with 1 not in C_D, e.g. a satisfiable one)
the stack rank is rank(V_K restricted to the union of supp(P g_i)) (used in r3_e4/e5).

### 3.1 The C_D side (honest negative)
Tseitin_2 over F_3 with Boolean edge variables on K4, prism, K33 (n = 6, 9, 9) and Q3 (n = 12) has PC degree
exactly 3 = the width (COMPUTED, e3pre.py, same for Tseitin_3 over F_2 on K4, prism, K33). So D0 = 2 and C_2 is
trivial at these sizes: the degree grows only for larger graphs than the n <= 13 where dense linear algebra
is feasible. A search for random 3-CNFs with PC degree >= 5 (r3_e3.py) found nothing within the time limit
at n <= 10. Therefore no data with a nontrivial C_D. I did not substitute a synthetic C_D. The C_D = 0 case
is an admissible instance of the abstract lemma (Pang's lemmas hold for any C_D closed under absorption with
g^p - g in C_D), so a counterexample at C_D = 0 to a uniform lemma is a counterexample to the lemma as an
abstract statement, but not to its use for Tseitin, where C_D is large; what it kills is a proof of the lemma
that does not use the Tseitin structure of C_D. This caveat is real and should be kept.

### 3.2 First-round gain, block family (COMPUTED, r3_e5.py, p = 2, C_D = 0)
g_i = indicator of {x_B = 0}, B_i disjoint blocks of rho variables, s = floor(n/rho) blocks. Best gain =
1 - c_1/c_0 over the sampled q, against z/N = N_{n-rho}(K-rho)/N_n(K) (the exact single-term fraction),
against Pang's eta = (1/2)N(K-d)/N(K):

    n=13 rho=1 s=13: K=2 gain .1413 z/N .1413 Pang .0761 | K=3 .2090 .2090 .1217 | K=4 .2736 .2736 .1729
    n=13 rho=2 s=6 : K=2 .0109 .0109 .0054 | K=3 .0370 .0317 .0185 | K=4 .0833 .0613 .0421
    n=13 rho=3 s=4 : K=3 .2884 .0026 .0013 | K=4 .5474 .0101 .0064 (s = 4 is too few terms to be adversarial)
    n=12 rho=1 s=12: K=2 .1519 .1519 ; K=3 .2241 .2241

So for rho = 1, 2 and s >= n/rho the best first-round gain is the single-term fraction, hence Pang's lemma
is tight to the factor (1-1/p) = 1/2 and to a factor at most 1.4 above the exact single-term kernel.
For p = 3 (r3_e1.py) the kernel fractions of dense affine subspaces are smaller than for subcubes
(n = 10, K = 3, rho = 1: 0.057 dense vs 0.261 subcube; rho = 2: 0 vs 0.051), but still above Pang's
bound where Pang's bound is defined (K >= d).

### 3.3 Multi-round trajectory (COMPUTED, r3_e4.py, n = 10, p = 2)
Greedy best-q rounds, c_j trajectory, K = 3:
    rho=1 (s=10): 176,130,93,64,42,26,15,7,3,1,0  (= N_{n-j}(K) exactly: q = g_j, P = x_1...x_j)
    rho=2 (s=5) : 176,165,98,37,1,0
    rho=3 (s=3) : 149,40,14,0
For rho = 1 the rate accelerates (1-K/(n-j) per round) and total rounds = s = n. For rho = 2 the first rounds
gain z/N each (0.06) and the collapse happens only in the last rounds. The number of rounds to reach c < 1 is
at most s in general (P = prod (1-g_j) kills every g_i exactly, PROVED-BY-HAND) and for the block family
about s = n/rho in the data.

### 3.4 Comparison with the hoped bounds
- exp(-O(rho)) hoped: at fixed K/n it is the same as Pang's (Section 2.2).
- n^(-eps) hoped: false for the block family as a first-round (and early-phase) bound, by 3.2.
- Pang's bound is never violated (as it must not be): in every row gain >= Pang eta.

## 4. Task 3: plausibility, conjectured statement, kill test

Verdict: the hoped lemma is not plausible in the form that matters. Reasoning, in order of strength.

(i) PROVED-BY-HAND: the barrier is determined by the per-round uniform gain, and exp(-O(rho)) is already
achieved (Section 2.2).
(ii) COMPUTED + structural: the per-round gain for the block family at rho = 1, 2 equals the single-term
fraction N_{n-rho}(K-rho)/N_n(K) (Section 3.2). Mechanism (PROVED-BY-HAND for the single-g round, CONJECTURE
for best q): excluding the set {q != 0} from the union only removes polynomials supported on subcube-sized
pieces; for rho >= 2 a round with 1 - g removes a codim-rho subcube and kills only polynomials supported
on it.
(iii) CONJECTURE (heuristic): the slow phase lasts about s/2 = n/(2 rho) rounds, while the degree budget is
t = D/(8(p-1)d) = delta n/(24 (p-1)^2 rho) for the C1 translation, smaller than n/(2 rho) whenever delta < 12
(always, delta <= 1/4). So the whole budget lies in the slow phase and the achievable approximation for
the block line L = OR_i [x_{B_i} = 0] (tribes) has rate about N_{n-rho}(K-rho)/N_n(K) per round throughout.
If this extends beyond n <= 13, the loss exp(-rho ln(n/K)) is intrinsic to the method "approximate each line
by a degree-Delta product of rank-reducing factors", not to the proof of the rank lemma. Then even a perfect
rank lemma cannot move the barrier within this method.

Conjectured precise statements (CONJECTURE):
 - C-tight: for p = 2, C_D = 0, the block family with s = n/rho and rho <= K, best first-round gain
   theta_1 satisfies N_{n-rho}(K-rho)/N_n(K) <= theta_1 <= 2 N_{n-rho}(K-rho)/N_n(K).
 - C-barrier: no choice of q-sequences of total degree <= D/8 reduces c below c_0 exp(-t N_{n-rho}(K-rho)/N_n(K))
   by more than a constant factor in the exponent on the block family when rho >= 2 and n >= 4 rho.

Kill test (one-line statement, stronger sizes needed): compute, for p = 2, C_D = 0, the block family at n = 14..16,
rho = 2, 3, K = 2..4, s = n/rho, the exact min over ALL q-sequences of length t (exhaustive q for small s) of
c_t, and check whether c_t/c_0 <= (1 - theta')^t with theta' >= 4 N_{n-rho}(K-rho)/N_n(K). A single
instance with theta' above that, growing with rho, supports the hoped lemma; the data of Section 3 point the
other way (n = 13, rho = 2: gain/z-fraction = 1.0, 1.17, 1.36). A secondary kill test needs a nontrivial C_D:
a Tseitin instance with PC degree >= 6, which needs n >= 18 variables (cubic graph on >= 12 vertices), beyond
dense linear algebra here; a sparse/structured implementation would be needed. I did not do this.

What the true loss looks like (COMPUTED + CONJECTURE): theta_1 ~ prod_{j<rho} (K-j)/(n-j), i.e. exp(-rho ln(n/K)),
the same as Pang's up to the factor (1-1/p) and the lower-order slack in L8. Pang's lemma is essentially tight
as a statement about one round.

Remark (PROVED-BY-HAND, small gain): the indicator of an F_p-affine subspace of codim rho has multilinear degree
at most (p-1) rho (it is prod (1 - l_j^(p-1)) and multilinear reduction does not raise degree). In C1 the
equation is (chi_T - 1 = 0) of degree r = 3(p-1) rho and Pang's d = (p-1) r = 3(p-1)^2 rho overcounts: the
indicator of that equation is chi_T itself, of degree (p-1) rho. Using d_eff = (p-1) rho in Pang's proof (L5,
L6) would lower kappa by up to a factor 3(p-1); L7 still needs the displayed degrees 3(p-1) rho. This requires
re-checking Pang's L6/L7 with d_eff not equal to (p-1) r, which I did not do. It changes constants only.

## 5. Task 4: what remains if a rank lemma worked

Assume Lemma H (a rho-free uniform gain) held up to rho = n^c. Then R_rho^p-type lower bounds exp(n^(1-O(c)))
would follow for lines of bounded-rank terms. What it would still not give:

(R1) Term rank. A depth-2 line OR_j AND_i (eq_ij) has terms of rank up to the fan-in of the AND, up to Theta(n)
     (e.g. ANDs of two literals, spans of size ~n). A rho <= n^c lemma does not cover them. The relevant
     parameter everywhere is the F_p-dimension of span{chi_T-1 : T term} (PROVED-BY-HAND: Claim 1 of round 2
     goes through verbatim for polynomial equations, not only affine forms, with chi_T a product over a
     basis of the span; degree (p-1) * rank * max equation degree). Truly unbounded depth 2 needs the layered
     approximators and hypothesis H of the analysis document (ratio D/n near 1/2) and is untouched.
(R2) MOD_p gates over terms (correction of round 2, T3). PROVED-BY-HAND: a MOD_{p,c} gate whose inputs are
     terms T_1..T_s of rank <= rho is the single polynomial equation sum_j chi_{T_j} - c = 0 of degree
     (p-1) rho, for ANY fan-in s (indicators are 0/1 valued, arithmetic in F_p). The same holds for
     MOD_p over linear equations (degree p-1) and for nested MOD_p over bounded-rank terms (degree grows by
     the factor of the nesting). So same-p MOD gates over bounded-rank terms are not an obstruction at the
     level of the translation to Res(PC_r/F_p); what must still be written is the simulation of the
     sequent-calculus MOD_p rules (recursive counting identities S_k = sum_{j<=k} chi_j, each an equation of
     degree (p-1) rho) in degree O(rho) with O(N) overhead per rule: CONJECTURE that it works (the
     identities are linear), not derived. What fails is a MOD_p gate over ORs or unbounded-rank ANDs: the
     input has degree s, and q != p gates have no low-degree equation at all.
(R3) Cut on depth-2 formulas. A cut on a DNF phi = OR_j T_j needs the other side not-phi = AND_j not-T_j, i.e. a
     conjunction of the s equations (chi_{T_j} = 0), a term of rank dim span{chi_{T_j}}, up to s. So cut on
     phi is covered iff that dimension is <= rho (then it is a cut on a rank-bounded term and the
     disjunction side is a line of s terms). PROVED-BY-HAND for the derivation: with Gamma or phi and
     Gamma' or not-phi, resolving T_1, ..., T_s in turn by (Sem) gives Gamma or Gamma' after s steps,
     provided each step's premise Gamma' or not-T_j is available, which AND-elimination from the term
     not-phi provides (rank <= rho). Full sequent bookkeeping (formulas on both sides, depth-2 negations
     CNF-shaped) is not written; items B5 of the analysis document remain open.
So the honest summary of the dependency: rank-bounded terms of rank n^c needs the (false-as-uniform) lemma;
unbounded rank needs a different idea (hypothesis H); MOD_p over bounded-rank terms and bounded-rank cut are
cheap once the translation is accepted.

## 6. Recommended next step (statement only, no owner task)

Drop the exp(-O(rho)) rank-lemma target. The first candidate worth a day is the multi-round exact optimum of
the kill test in Section 4 at n = 14..16 (C_D = 0), because (iii) is the claim that the barrier is a
property of the method and the data so far are n <= 13. If the optimum over q-sequences also follows
N_{n-rho}(K-rho)/N_n(K), the barrier rho = Theta(log n) is an intrinsic limit of the Pang method and the
remaining route is the layered argument of the analysis document, with its own hypothesis H.

## 7. Session log (append-only)

- 2026-10-14 prover (round 3): read round 1-2 documents and the plan; wrote r3lib.py (rank machinery in
  the function basis), r3_e1 (kernel of 1-g), r3_e2 (greedy rounds), r3_e3 (C_D from PC closure, found no
  usable instance), r3_e4 (flatness table, block family rounds), r3_e5 (first-round gain). Did not open the
  Lean files (statements taken from r4-pang-plan.md Section 10); did not re-read Pang's TeX. No Lean, no builds.
  Nothing pushed.
