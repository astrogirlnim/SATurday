# R4 Phase 2.3, kill test: exact multi-round optimum of Pang-style degree-budgeted approximation (disjoint subcubes)

Status: research notes, docs and small scripts only. No Lean, no builds. Date 2026-10-14, branch r4/prover-kt.
Follows r4-phase23-r3.md (round 3, Section 4 "kill test" and Section 6). Scripts in r4-phase23-scripts/ (prefix kt_).
Labels: COMPUTED (script run this session), PROVED-BY-HAND, CITED (round 3 / Pang as summarized there, not re-read),
CONJECTURE. Scope of every number: p = 2, consequence space C_D = 0, family g_i = [x_{B_i} = 0] with disjoint blocks
B_i of size rho, s = floor(n/rho) blocks, V_K = multilinear polys of degree <= K, c_t(K) = rank of the stacked map after t rounds.

## 0. Plain verdict

1. In the regime where the disjoint-block family is a real adversary (s > K + t, defined in 3.3), the exact optimum over
   ALL t-round q-sequences removes about the single-subcube fraction theta_1 = N_{n-rho}(K-rho)/N_n(K) of the rank per round,
   within a factor 1.0 to 1.4 of it, and the factor does not grow with n or rho in the range tested (COMPUTED, Section 2).
   Pang's eta = (1-1/p) N(K-d)/N(K) is below the optimum by a factor of about 2 (COMPUTED). So the optimum does not beat the
   single-subcube fraction by any n^(eps)-type amount; a lemma with uniform per-round gain n^(-eps) is not available from this family.
2. The optimum is NOT uniform in rounds: after t = s - K rounds (the surviving pattern space A has dimension <= K) the rank
   collapses abruptly (e.g. n=14, rho=2, K=4: c = 1471, 1366, 1262, then 711, 189, 45, 1 at t = 3..6). This is real (COMPUTED, exact at
   n = 12, 14) and is the "accelerating phase" of round 3. It is irrelevant for the barrier iff the degree budget t_max
   is below s - K (3.3, PROVED-BY-HAND arithmetic, CONJECTURE for the asymptotic extrapolation).
3. Verdict on the barrier: for this family the data say the rank barrier rho = Theta(log n) is a limit of the method
   "round-by-round degree-budgeted approximation", not of Pang's counting lemma (consistent with round 3's conjecture C-tight,
   which is supported here to n = 18 for rho = 2, 3 but only in the small window of 3.3). Caveat that matters: disjoint blocks have
   s <= n/rho terms; for rho >= 4/delta they are too few to be adversarial (s < K), so the kill test cannot reach the regime
   rho ~ log n of the actual barrier with this family. The barrier claim at rho ~ log n therefore rests on CONJECTURE (overlapping
   families with s >> K), not on this data.
4. Consequence space (Section 4): nothing learned about the barrier. No formula with PC degree >= 5 was found or finished within
   the dense-linear-algebra budget; the one nontrivial C_D tested (PHP 4 into 3 holes, 12 variables, PC degree 4 > width 3, dim C_3 = 178)
   changes c by at most 1 and exposes that the quotient model is not meaningful for high-degree P.
5. Recommendation: Section 5.

## 1. Method (exact reduction)

PROVED-BY-HAND. For p = 2, C_D = 0 and a point x of the cube let a(x) in F_2^s with a_i = g_i(x). The union of supports of P g_i
is {x : a(x) != 0, P(x) = 1}, and c_P(K) is the rank of V_K restricted to that set. A round with q = c.g (c in F_2^s) has
q(x) = c . a(x), and P' = P [q = 0]. After t rounds with vectors c_1..c_t the surviving points are exactly
U_A = {x : a(x) in A \ {0}}, A = span(c_k)^perp, a subspace of codimension <= t. Conversely every subspace A of codimension t is
reached (choose c_k as a basis of A^perp). Hence

   exact optimum after t rounds = min over subspaces A of F_2^s, codim A = t, of rank(V_K | U_A)      (adaptive = non-adaptive here).

The rank depends on A only up to coordinate permutations (blocks are exchangeable), so kt_opt.py enumerates orbit representatives
of subspaces under S_s (feasible for s <= 7: 43 orbits at most per dimension) and computes each rank over GF(2) exactly.
For s = 8 (n = 16) the orbit enumeration over S_8 was too slow, so kt_opt.py there takes the minimum over the coordinate subspace
(= sequential q = g_i rounds) and 60 random subspaces of each dimension: an UPPER bound on the optimum (SAMPLED).
kt_round1.py computes the exact first-round optimum for any n <= 18: c in F_2^s of weight w gives gain depending only on w,
all w = 1..s are tried (EXACT).
Sanity checks: the t = 1 values agree between kt_opt.py and kt_round1.py; rho = 1 trajectories of round 3 (N_{n-j}(K)) not rerun.

## 2. Data (all COMPUTED)

theta_1 = N_{n-rho}(K-rho)/N_n(K) (single-subcube fraction, round 3 Sec 2.1); eta = (1/2) N_n(K-rho)/N_n(K) (Pang, p=2, d=rho).

### 2.1 Exact multi-round optimum, rho = 2 (kt_opt.py, EXACT over all subspaces)

n = 14, s = 7 (c_0 = 106, 470, 1471 for K = 2, 3, 4):
    K=2 theta_1=.00943 eta=.00472: c_t = 106,105,104,103,102 | 37, 1, 0     (t = 0..7)
    K=3 theta_1=.02766 eta=.01596: c_t = 470,455,440,425 | 186, 45, 1, 0
    K=4 theta_1=.05370 eta=.03603: c_t = 1471,1366,1262 | 711, 189, 45, 1, 0
n = 12, s = 6 (c_0 = 79, 299, 794):
    K=2 theta_1=.01266: 79,78,77,76 | 27, 1, 0
    K=3 theta_1=.03679: 299,286,273 | 132, 27, 1, 0
    K=4 theta_1=.07053: 794,716 | 447, 135, 27, 1, 0
('|' marks the collapse: it occurs at t = s - K in all six rows, i.e. when dim A = K.)

Slow-phase per-round gain, optimum / theta_1:
    n=12: K=2 1.00; K=3 1.18 (t=1), 1.21 (t=2); K=4 1.39 (t=1)
    n=14: K=2 1.00; K=3 1.15; K=4 1.33 (t=1), 1.37 (geometric over t=2)
Pang eta / optimum (n=14): K=3 0.50; K=4 0.50 (t=1: .0360 vs .0714).
In the slow phase c_t is almost exactly c_0 - t * (gain of round 1): the rounds are additive, each removing about one more
"kernel"; this is the structural reason the per-round fraction stays theta_1.

### 2.2 n = 16, rho = 2, s = 8 (SAMPLED upper bound; round 1 EXACT from kt_round1.py)
    K=2 theta_1=.0073: c_t = 137,136,135,134,133,132 | 47, 3, 0           (ratio to theta_1: 1.00)
    K=3 theta_1=.0215: 697,680,663,646,629 | 292, 63, 3, 0                (t=1 exact 1.13)
    K=4 theta_1=.0421: 2517,2381,2246,2112 | 1211, 351, 63, 3, 0          (t=1: 1.28)
Collapse again at t = s - K (sampled values are upper bounds on the optimum).

### 2.3 Exact first round, larger n and rho = 3 (kt_round1.py, EXACT; best gain over all weights w)
    rho=2: n=16 K=2 ratio 1.00, K=3 1.13 | n=18 K=2 1.00, K=3 1.12
    rho=3: n=18 (s=6) K=3 ratio 1.00 (gain .0010 = theta_1), K=4 1.17 (.0047 vs .0040)
    ratio over theta_1 for K = 4, rho = 2 falls with n: 1.39 (n=12), 1.33 (n=14), 1.28 (n=16).
    Outside the window (s too small): n=15, rho=3, s=5, K=4: gain .048 against theta_1 = .0067 (7x), growing to .217 with w;
    n=14..16 with rho = 3, 4 and s = 3..5 collapse in 2-3 rounds (kt_opt.py 14 3, 15 3, 16 4 outputs). These rows have s <= K + 1
    and are not adversarial; I do not use them as evidence.

## 3. Reading the data

### 3.1 Does the optimum follow the single-subcube fraction? (answer to the kill question)
Yes, up to a constant: while dim A > K the optimal gain per round is between 1.0 and 1.4 times theta_1, and Pang's eta is
about 0.5 times the optimum. The earlier claim "Pang tight up to (1-1/p) in round 1" (round 3 Sec 3.2) extends to the multi-round
optimum on this family for n <= 14 exactly and n <= 18 for round 1 (COMPUTED). The constant factor between 1 and 1.4 is weakly decreasing
in n in the one sequence checked (K = 4, rho = 2), and does not increase from rho = 2 to rho = 3 (1.28 vs 1.17 at comparable K/rho).

### 3.2 What beats theta_1: the collapse
After s - K rounds the optimum jumps far above theta_1 per round (rates .2 to .6). Mechanism (CONJECTURE, consistent with all 6 exact
rows): once dim A <= K the surviving pattern set is small enough that V_K already interpolates the remaining points in few dimensions
(rank of V_K on an F_2-subspace pattern set of dimension <= K saturates). This is the acceleration noted in round 3 (iii).

### 3.3 Why the collapse does not rescue the barrier, and why this family cannot see it
PROVED-BY-HAND arithmetic (for the round-2/3 translation parameters, p = 2): the budget is t_max = D/(8 d) with d ~ 3 rho and
K = D/4, D = delta n, so t_max = delta n/(24 rho), and s = n/rho. The collapse needs t >= s - K = n(1/rho - delta/4). So
t_max < s - K iff rho < (4/delta)(1 - delta/24), a constant. For rho below that constant the whole budget lies in the slow phase and the
rate is theta_1 up to constants (COMPUTED data + this arithmetic; extrapolation to large n CONJECTURE). For rho > 4/delta we have
s < K: the disjoint family collapses at once, not because the method is strong but because the family has too few terms. The real
adversary at rho ~ log n has s >> K lines (overlapping subcubes, exponentially many terms in Tseitin lines), which this family does
not model. So: confirmed for disjoint blocks in the window rho <= 3, n <= 18; for rho ~ log n it is a CONJECTURE that overlapping
families behave like the slow phase for the whole budget.

## 4. Consequence-space attempt (what is and is not learned)

COMPUTED (kt_deg.py, exact PC degree via the fixpoint of pcdeg.py): PHP 3 into 2: degree 3; PHP 4 into 3 (12 vars) degree 4 over
F_2 and F_3 (width 3, so degree > width, but not >= 5); Tseitin mod 2 on K5 over F_3 (10 vars) degree 4; Tseitin mod 3 with Boolean edges on K5
over F_2 degree 4 (= width). Random 3-CNF search for PC degree >= 5 (kt_search.py, F_2 and F_3, n = 12, 13, 14, m/n about 5.5-6): the
seeds that pass degree <= 4 are fast; the first seed with degree >= 5 needs the D = 5 closure (N_13(5) = 2380 columns, dense numpy) and
did not finish within a ~25 minute budget; Tseitin mod 2 on K6 (15 vars, expected degree 5 = width) over F_3 also did not finish. No instance with
PC degree >= 5 was obtained (consistent with round 3: needs sparse linear algebra or n >= 18).
With C_3 non-trivial (PHP 4 into 3, p = 2, dim C_3 = 178 of 299), kt_cd.py ran greedy rounds on the 4 pigeon blocks (rho = 3, falsifying subcubes of
the pigeon clauses) with and without the quotient: c = [79,79,52,22,0] vs [78,79,52,22,0] (K=2), [299,190,81,1,0] vs [298,...] (K=3), [13,...] vs [12,...] (K=1).
Learned: (a) the quotient by C_3 changes c by at most 1 in every row, so on this instance the consequence space does not help the approximation at
all; (b) the quotient model of round 3 (rank into V_D/C_D of P g f with P of unbounded degree) is not monotone (c rises 78 -> 79 after a round), a sign
that the model is only meaningful when deg(P g f) <= D, which round 3 does not enforce; I did not fix this. NOT learned: anything about Tseitin or about
the barrier with a large C_D, because no formula with a large PC-degree gap and a big nontrivial C_D fits the dense method. The caveat of round 3
Sec 3.1 stands: C_D = 0 results kill a proof that ignores the Tseitin structure of C_D, not its use.

## 5. Recommendation for deciding depth 2

1. Treat the rho = Theta(log n) rank barrier as established for the Pang method on the one family tested in the one window it can be tested (this note), and
   as CONJECTURE beyond. Do not spend more time on a better uniform rank lemma (agrees with round 3 Sec 6).
2. One more decisive computation before closing: the same exact reduction for OVERLAPPING families. The pattern-space argument of Section 1
   generalizes verbatim (a(x) = (g_i(x))_i, surviving set = patterns in a subspace A), only the symmetry group is smaller. Take all C(n,2) pair-subcubes
   (or a random sparse subfamily with s >> K) at n = 14..16, rho = 2, and compute the best first-round and 2-3-round gain by hill-climbing over A. If the
   gain stays at O(theta_1), the barrier is a limit of the method at the s >> K regime too and the decision is made: depth 2 cannot be obtained
   from this method beyond rho = O(log n).
3. Then decide depth 2 by the structural route of round 3 Sec 5 (hypothesis H of the analysis document: layered approximators, unbounded-rank terms),
   not by tuning Pang's lemma. Depth 2 with bounded-rank terms (rank <= c log n) and the MOD_p gate observation of round 3 R2 remain as the cheap partial result.
4. Consequence-space question is open and needs a sparse or structured linear-algebra implementation (or n >= 18) to get degree >= 6 Tseitin; do not read
   anything about it into this note.

## 6. Session log (append-only)

- 2026-10-14 prover (kill test): wrote kt_opt.py (exact/sampled optimum over subspace A), kt_round1.py (exact first round, n <= 18), kt_deg.py (PC degree of
  PHP and Tseitin instances), kt_search.py (random 3-CNF degree >= 5 search, unfinished), kt_cd.py (greedy with and without C_3 on PHP 4->3). Found and fixed a bug in the
  sampled mode (random generators of too low independence gave larger codimension) before using any n = 16 number. Orbit enumeration for s = 8 abandoned
  (too slow). Nothing pushed. No Lean, no builds.
