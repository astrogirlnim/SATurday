# R4 Phase 2.3, overlap test: Pang-style degree-budgeted approximation on OVERLAPPING subcube families

Status: research notes, docs and small scripts only. No Lean, no builds. Date 2026-10-14, branch r4/prover-ov.
Follows r4-phase23-killtest.md (disjoint blocks) and r4-phase23-r3.md. Scripts in r4-phase23-scripts/ (prefix ov_);
raw outputs in the session scratchpad (outside the repo), key numbers copied below.
Labels: COMPUTED (script run this session), PROVED-BY-HAND, CITED (earlier notes / Pang as summarized there, not re-read),
CONJECTURE. Setting as before: p = 2, C_D = 0, g_S = [x_S = 0] for a rho-subset S, family F = (S_1..S_s), V_K = multilinear
polys of degree <= K, c_t(K) = GF(2)-rank of V_K restricted to the points that survive t rounds, theta_1 = N_{n-rho}(K-rho)/N_n(K),
Pang eta = (1/2) N_n(K-rho)/N_n(K). "Gain" of a round = 1 - c_after/c_before. "Ratio" = gain / theta_1.

## 0. Plain verdict

1. The answer depends on the family, and the adversary gets to choose it. COMPUTED:
   - DENSE overlapping families (all C(n,2) pairs, all C(n,3) triples) beat theta_1 substantially: first-round ratio 5.00 for
     rho = 2, K = 2 at every n = 10, 12, 14, 16 (exact value 5/c_0 against theta_1 = 1/c_0); 3.8 to 4.6 for K = 3, 4;
     9.0 for rho = 3, K = 3 (n = 12, 14). Over rounds the per-round ratio keeps growing (K = 2, n = 16: 5.0, 9.3, 14.5, 21, 31).
     The gain comes from cliques (many rho-subsets inside a small vertex set), Section 3.
   - SPARSE overlapping families with s >> K (cycle, random 3-regular graph, random graphs with 2 to 3 n edges, linear 3-uniform
     triple systems; s = 12 to 40 terms, K = 2 to 4) stay close to theta_1: first-round ratio 1.13 to 1.5 (exact for the cycle,
     n = 12, 14), cumulative per-round rate 1.1 to 2 times theta_1 for the first 3 to 5 rounds, drifting upward with t. These are
     the same numbers as the disjoint family (1.15 and 1.33 at n = 14, K = 3, 4).
2. Verdict on the barrier. For a lemma that must hold uniformly for every family of s >> K terms (which is what the Pang
   method needs), the data say the per-round gain of the best q is still theta_1 up to a small constant on the worst families
   tested, so the rank barrier rho = Theta(log n) is a limit of the method, not just of Pang's counting lemma. A uniform lemma with
   gain n^(-eps) does not exist on the evidence. This is a numerical statement for n <= 16, K <= 4, s <= 40 (sparse) and
   s <= 560 (dense, weakly searched); it is not a proof, and the multiplier on theta_1 is visibly not bounded in the rounds t
   (Section 2.4), so the extrapolation to the asymptotic regime is CONJECTURE.
3. A better lemma may exist only in a structure-dependent form (gain depends on how many terms live inside small vertex sets),
   which cannot rescue the worst case, because sparse families have no such sets. So: close the uniform rank-lemma line.
4. A new, derived constraint on any route that keeps "rate per round = theta_1" (PROVED-BY-HAND arithmetic, Section 4): rho up to
   n^c would need K/n -> 1, i.e. PC degree D with D - K small and D close to n (not n/2). Hypothesis H as stated (D/n -> 1/2) is
   therefore not enough for the layered route under this rate; the route needs a different measure than the dimension count.
5. Recommendation: Section 5.

## 1. Method

Exact reduction of killtest Section 1 holds verbatim for any family (PROVED-BY-HAND there): a point x has pattern
a(x) = (g_j(x))_j in F_2^s; after rounds q_k = c_k . g the survivors are {x : a(x) != 0, c_k . a(x) = 0 for all k}, and the exact
t-round optimum is the minimum over t-dimensional spans <c_1..c_t> of rank(V_K | survivors). The symmetry group is only the
automorphism group of the family, so for overlapping families no orbit enumeration is feasible and the minimum is searched.

Scripts (all in r4-phase23-scripts/, GF(2) rank by big-integer elimination, caches keyed by the survivor set):
- ov_lib.py: family construction (all pairs, all triples, cycle, random 3-regular, random pairs/triples, random linear
  triple system), rank machinery.
- ov_exact_small.py: EXACT first round for all pairs on n = 6, 7: q = edge indicator sum of a graph H; the rank depends only on the
  isomorphism class of H, all 1252 graphs of the networkx atlas on n nodes are tried.
- ov_exact_sparse.py: EXACT first round for any family with s <= 16 (all 2^s - 1 vectors c).
- ov_search.py: SAMPLED search for rounds 1..T. Round t: seeds = single terms, clique-type q (all rho-subsets inside the first m
  variables, m = rho..n), random vectors at densities 1/2, 1/4, 1/10, 1/30; the best 4 seeds are improved by single-term flip
  hill climbing (150 random flips per sweep, up to 3 sweeps); greedy over rounds (round t optimized given rounds 1..t-1).

## 2. Data

### 2.1 EXACT, all pairs, tiny n (ov_exact_small.py, COMPUTED, exact over all graphs)
    n=6: K=2 ratio 5.00 | K=3 5.00 | K=4 3.64    n=7: K=2 5.00 | K=3 4.00 | K=4 3.69
Best graph in every row: the complete graph on 4 vertices. (K close to n is not the asymptotic regime; this only certifies the
mechanism and that no graph beats K4 at these sizes.)

### 2.2 DENSE families, sampled (ov_search.py; each number is a LOWER bound on the best gain, i.e. an upper bound on c_t)
Round-1 ratio to theta_1 (best found; the seed that won was always a clique of 4 vertices for rho = 2, 6 for rho = 3, hill climb added little):
    all pairs (rho = 2): K=2: 5.00 (n=10), 5.00 (12), 5.00 (14), 5.00 (16)
                         K=3: 4.33 (10), 4.45 (12), 4.54 (14), 4.60 (16)
                         K=4: 3.76 (10), 3.96 (12), 4.11 (14)
    all triples (rho = 3): K=3: 9.00 (12), 9.00 (14), 7.00 (16)   K=4: 7.10 (12), 7.25 (14)   K=5: 6.52 (14)
The 7.00 at n = 16 (s = 560 terms) is most likely search weakness (150 flips per sweep over 560 coordinates), not a real drop; I did not
resolve it. Whatever the truth, the sampled values are lower bounds on the best ratio.
Multi-round (greedy), per-round ratio, rho = 2:
    n=16 K=2: 5.0, 9.3, 14.5, 21.2, 30.9 (c_t = 137, 132, 123, 110, 93, 72)
    n=14 K=4: 4.1, 6.3, 8.4, 10.7, 13.9, 15.7, then collapse (c_t = 1471, 1146, 758, 415, 177, 45, 7)
    n=14 rho=3 K=3: 9.0, 22.4, 34.3, 49.7 (c_t = 470, 461, 439, 407, 364)
In the dense family the per-round multiplier on theta_1 grows with t; for small n the collapse to 0 happens in about 5 to 6 rounds,
far before s - K (compare disjoint blocks, where it happens at exactly s - K).

### 2.3 SPARSE overlapping families, sampled (ov_search.py) and exact where marked
Round-1 ratio, then cumulative rate / theta_1 after t rounds (cum rate = 1 - (c_t/c_0)^(1/t)):
    cycle, n=12, K=3 (s=12):   EXACT round 1 ratio 1.18;  K=4 EXACT 1.39        (disjoint blocks, same n, exact: 1.18, 1.39)
    cycle, n=14, K=3 (s=14):   EXACT round 1 ratio 1.15                          (disjoint: 1.15)
    cycle, n=14, K=3 sampled:  ratios per round 1.15, 1.35, 2.06, 1.84, 1.84
    cycle, n=16, K=3 (s=16):   1.13, 1.91, 1.35, 2.13, 1.77        (cum rate at t=5: 1.66 theta_1)
    cubic, n=14, K=3 (s=21):   1.15, 1.19, 1.23, 1.28, then 2.12 at t=5   (cum rate t=4: 1.21 theta_1)
    cubic, n=14, K=4 (s=21):   1.33, 1.65, 1.94, 2.76, 6.5
    cubic, n=16, K=3 (s=24):   1.13, 1.44, 1.27, 1.74, 3.0
    rg30,  n=14, K=3 (s=30):   1.15, 1.35, 2.8, 1.5, 2.1
    rg30,  n=14, K=4 (s=30):   1.33, 1.42, 1.52, 1.91, 5.9
    rg40,  n=16, K=3 (s=40):   1.13, 1.30, 2.3, 3.2, 3.7
    random linear triple system (rho=3), n=14 K=4 (s=26): 1.50, 1.52, 1.28, 2.42, 4.23 ; n=16 K=4 (s=32): 1.43, 1.51, 2.03, 2.50
    random 40 triples, n=14, K=4: 2.08, 1.78
    smaller n (n=12, K=4, cubic s=18): 2.64, 3.05, 4.0, 8.5 ; triple systems n=12, 13 (s=17, 22): 1.4 / 1.9 then 9.8 / 35 at t=2,3 (collapse)
So the first round sits at 1.1 to 1.5 times theta_1 (about 2 to 2.6 when K/n is as large as 1/3 or the system is dense relative to n),
the next two to three rounds at 1.2 to 3, and the ratio then climbs. The small-n triple systems (s = 17, 22 on 12, 13 points) already
collapse at t = 3: they are too dense for n and are not adversarial.

### 2.4 What the data do not show
- The multiplier on theta_1 is not bounded in t. In every family, sparse or dense, it grows with t; the sparse families start at about 1.2
  and reach 5 to 10 after t = 4 to 5 rounds at n = 12 to 14 (t is then about s/3). With n <= 16 I cannot say whether the growth is
  polynomial in t, exponential, or a finite-size effect of the collapse. The degree budget of the application, t_max = delta n/(24 rho),
  is a function of n; at n <= 16 it is below 1 round, so the application regime is entirely out of reach of these sizes.
- K <= 4 and n <= 16 means K/n ranges from 0.13 to 0.4, not the application's delta/4 at large n.

## 3. Why dense families win (mechanism)

COMPUTED fact: for rho = 2, K = 2, the first-round gain of the best clique-type q is exactly 5/c_0 at all n = 10..16 against
theta_1 c_0 = 1. PROVED-BY-HAND consistency check: the clique q = sum_{i<j in C} g_ij, |C| = 4, equals C(z,2) mod 2 with z the number of
zeros among the 4 variables of C; q = 0 keeps z in {0, 1, 4}, i.e. 6 of the 16 patterns of x_C. Degree <= 2 functions on the 16 points
form a space of dimension 11; restricted to 6 points the rank is at most 6, so at least 5 independent quadratics vanish on the
survivors, against 1 for a single term (g_ij itself). (The full identification of the global rank drop with this local count I did not
prove; the computed value 5/c_0 matches it at every n.)
CONJECTURE (heuristic, consistent with 5 for rho = 2 and 9 for rho = 3 at K = rho): for a family containing all rho-subsets of an m-set,
the first-round ratio is about the number of independent degree-rho polynomials on the m coordinates that vanish on the survivor set,
which grows like C(m, rho) when the survivor set is a union of Hamming layers. In the application regime K = delta n/4 this would make a
single round gain constant already for m = O(rho/delta), i.e. exp(O(rho)) terms. So dense, clique-rich families are easy for the method;
no uniform lemma follows because the lemma must also cover families without small dense subfamilies (Section 2.3).

## 4. Consequences for the barrier (what is and is not proved)

(a) PROVED-BY-HAND arithmetic, conditional on the CONJECTURE that the worst family has per-round rate theta_1 = (K/n)^rho (up to constants)
for all t <= t_max. Pang's constraint K + 2 Delta + 2 d <= D with Delta ~ t rho and D <= n gives
ln S >= t (K/n)^rho with K <= D - 2 t rho. Take D = n(1 - o(1)) and t = n/rho^2: (K/n)^rho ~ exp(-rho * 2 t rho / n) = e^(-2),
so ln S >= n/(e^2 rho^2), which is n^(2 eps) for rho = n^(1/2 - eps). With D = n/2 and K = D/4, (K/n)^rho = 8^(-rho) forces rho = O(log n). So
the achievable rho is governed by K/n, and it reaches n^c only if D - K = o(n/rho), D = (1 - o(1)) n.
(b) That is a statement about hypothesis H of r4-phase23-analysis.md in a stronger form: H asks D/n -> 1/2 (rated there as under 3 percent,
CONJECTURE); the rate-theta_1 reading needs D/n -> 1, which no constant-width CNF family is known to reach and which is not
established as impossible either (CONJECTURE, I did not search the literature).
(c) Counterweight: the tested worst families give a multiplier above 1 that grows with t; if it grows exponentially the barrier moves up.
The data cannot decide this.

## 5. Recommendation

1. Close the rank-lemma line in its uniform form (a lemma "for every F_p-affine family of s >> K terms of codim <= rho, some q gains
   n^(-O(1)) independent of rho"). Evidence: disjoint (killtest) and sparse overlapping families (this note) both sit at theta_1 up to
   a small constant for the first rounds; the only families that beat theta_1 are dense ones, which a worst-case lemma cannot assume.
   Keep Pang's lemma and the rho = O(log n) result as the correct statement of the method's reach. This closes the line at the level
   of evidence (numerical, small n), not of proof.
2. Cheap partial result to write (not new method): depth 2 with terms of rank <= c log n and same-p MOD gates over them (r3 Section 5, R2).
3. What the layered / hypothesis-H route would have to look like, and its first lemma. Under the arithmetic of Section 4 any route that
   keeps the dimension count needs D/n close to 1, so its first lemma is an extremal statement, not an approximation lemma:
   First lemma (Extremal PC-degree lemma E): there is a family of constant-width unsatisfiable CNFs on n variables with PC degree over F_p
   at least (1 - o(1)) n (weaker version for H itself: (1/2 - o(1)) n). The first computation is to find the maximum of D(F)/n over
   small constant-width CNFs (Tseitin on small expanders, with the dense-algebra tools kt_deg.py and pcdeg.py for n <= 14), to see whether
   any F has D/n above 1/2; the previous notes found only D = 3, 4 at n = 9 to 15 (killtest Section 4) and never D/n above about 0.4 (Tseitin mod 2 on K5, degree 4 on 10 variables).
   If instead E is false (a theorem that D <= (1/2 - c) n for all constant-width CNF), the dimension-count route is dead and so are H
   and its variants. I do not claim E is plausible; the notes rate H at under 3 percent.
   Second lemma of that route, only if E holds: the per-round rate for the worst family is at least (K/n)^rho (no better is known or
   needed), which is the CONJECTURE C-tight of r3 and is supported only by this note's small data.
4. Other new method that avoids the rank barrier, as a hypothesis to test and kill quickly (CONJECTURE, nothing derived): replace the
   space V_K by a subspace W_K closed under multiplication by the terms of the proof's family and containing the witnesses, whose Hilbert
   ratio dim W_{K-d}/dim W_K does not carry the exponent rho (for blocks, polynomials that are unions of whole blocks give a ratio about
   K/n, not (K/n)^rho). The first lemma would be: for the partition of variables induced by the lines of the proof, W exists with the closure
   property. It is easy for disjoint blocks and unclear for overlapping families; a cheap kill test is to compute the Hilbert ratio of the
   smallest multiplication-closed subspace generated by the g_j and degree-K monomials on the sparse families of Section 2.3 (if it is
   all of V_K, the idea is dead). I did not run this test.
5. Do not read any statement about Tseitin consequence spaces into this note: C_D = 0 throughout.

## 6. Exactness ledger (what could be missed)

EXACT (COMPUTED): ov_exact_small.py all pairs n = 6, 7, K = 2..4, first round (all graphs up to isomorphism, rank exact over GF(2));
ov_exact_sparse.py cycle n = 12 (K = 3, 4) and n = 14 (K = 3), first round over all 2^s - 1 vectors. The run for cycle n = 14, K = 4
was stopped unfinished, as were the dense runs at n = 14 (rho = 3, K = 4, 5; reported rounds only) and n = 16 (rho = 2, K = 2 beyond t = 5; rho = 3 round 1 only).
SAMPLED: every other number, including all multi-round values, all dense n >= 10, all sparse random families. Each is an upper bound on the
true optimum c_t, so each reported gain/ratio is a lower bound on the best gain/ratio. Possible misses: (i) q's outside the seed
families and the 450-flip neighborhood, which would raise the ratio of the sparse families (the main risk to the verdict: the sparse
verdict is "no better q was found by clique seeds, random seeds and hill climbing", checked against exact values in two small cases
(cycle n = 12 and 14, K = 3) where hill climbing equalled the exact optimum); (ii) greedy rounds are not the joint optimum over spans of dimension t; (iii) the rank
is minimized only for the three or four best seeds per round; (iv) one random family per type and size (random seeds fixed to 1);
(v) the dense rho = 3 searches at s >= 364 are weak.
Not tested: rho >= 4, n > 16 (dense linear algebra here limits n to 16 with K <= 3 or 4), p = 3, nontrivial C_D.

## 7. Session log (append-only)

- 2026-10-14 prover (overlap test): wrote ov_lib.py, ov_exact_small.py, ov_exact_sparse.py, ov_search.py; ran dense (all pairs/triples,
  n = 10..16), sparse (cycle, cubic, random pairs and triples, linear triple systems) and exact tiny cases. One safety hook blocked an
  `rm -f $O/*` of scratch output; I did not delete anything and wrote new output to a fresh scratch subdirectory. Nothing pushed. No Lean, no builds.
