# R4 Phase 2.3 plan: depth 2 AC0[p]-Frege

Status: scouting and planning only. Docs only; no Lean, no build, nothing here is a proof.
Date 2026-10-14. Branch r4/scout-p23. Author: research scout and auditor.

Claim labels used throughout:
- PROVED = certified in this repo (Lean, listed in the rung docs).
- CITED-CHECKED = I fetched the abstract or text of the source on 2026-10-14 (or an earlier
  session did, as recorded) and the statement matches. This is not a full read unless stated.
- CITED-UNCHECKED = recalled from working knowledge or a secondary source; verify before use.
- CONJECTURE = my own reasoning or guess; not established.

Sources of fact for this plan: r4-frontier.md, r4-research-plan.md, r4-completion-checklist.md,
r4-pang-plan.md (a full TeX read of Pang by an earlier scout), r4-khaniki-plan.md,
r4-phase22-plan.md, plus web fetches of arXiv/ECCC abstract pages on 2026-10-14. The web
fetches gave abstracts and, for Pang Section 8, a summary of the text by a fetch tool, so
details drawn from them are CITED-CHECKED at abstract level only.

## 0. Bottom line

1. Super-polynomial lower bounds for AC0[p]-Frege of any fixed depth, including depth 2, are open
   (CITED-CHECKED: Garlik-Kolodziejczyk 2018 slides and abstract still state it as the major open
   problem; Lu-Santhanam-Tzameret ITCS 2026 treats it as open). I found no 2026 preprint claiming
   it. Depth 1 (Res(lin F_p), Res(PC_r/F_p)) is the frontier of what is known.
2. Pang's degree-size relation (arXiv 2610.00837) gives exponential dag-like bounds for depth 1.
   Its own conclusion sketches depth 2 and states the sketch closes only if a PC degree lower
   bound "near or above n/2" is available for a constant-width CNF on n variables. That is not
   known (per Pang, CITED-CHECKED at summary level).
3. My heuristic reading (CONJECTURE, own computation from the sketched inequality): with only
   D = c n, c < 1/2 fixed, the depth 2 argument yields a bound only for proofs of size below a
   fixed small power of n, which is not a super-polynomial statement. The needed ratio is
   D/n tending to 1/2 or more. Whether any constant-width CNF has PC degree >= (1/2 - o(1)) n is
   an open question that I could not resolve and that may have a negative answer.
4. Honest verdict: depth 2 is not within reach of the current toolkit. The one concrete route
   (Section 3, attack A) has a quantitative gap that is probably a real obstruction, not
   bookkeeping. Probability of a depth 2 super-polynomial bound from this project in the near term:
   low (CONJECTURE, I would say under 5 percent).

## 1. Literature pass (as of 2026-10-14)

### 1.1 Depth-2 and bounded-depth AC0[p]-Frege: known and unknown

- Open: super-polynomial lower bound for AC0[p]-Frege, any fixed depth >= 2 with MOD_p gates (and
  for p = 2, depth 2 too, as far as I can find). CITED-CHECKED (Garlik-Kolodziejczyk slides,
  ACM TOCL 19(4) 2018 abstract; Lu-Santhanam-Tzameret arXiv 2509.16824 abstract).
- Subsystems with known bounds (Garlik-Kolodziejczyk, "Some subsystems of constant-depth Frege
  with parity", TOCL 2018): tree-like PK(parity) is quasi-polynomially equivalent to constant-depth
  Frege with parity axioms; super-polynomial separation of dag-like PK(parity) from AC0[2]-Frege;
  exponential bounds for a system containing an extension of tree-like Res(lin). CITED-CHECKED
  (abstract). Note they state the technique cannot give super-quasi-polynomial separations.
- Bounded-depth Frege with Count_p axioms (not connectives): exponential for Count_q, q not a
  power of p (Beame-Riis; Buss-Impagliazzo-Krajicek-Pudlak-Razborov-Sgall 1996/97). PROVED here:
  `QP.countq_bdfrege_exp` (CountQ.lean). This is axioms-as-extra-assumptions, a weaker setting than
  MOD_p connectives inside formulas; the gap between them is exactly the open problem.
- Krajicek, "A reduction of proof complexity to computational complexity for AC0[p] Frege
  systems", arXiv 1311.2501: reduces AC0[p]-Frege lower bounds to computational lower bounds for
  search tasks over low-degree polynomials. CITED-CHECKED (title/abstract found by search).
- Krajicek, "Extended Nullstellensatz proof systems", Proc. AMS 152(11), 2024, 4881-4892 (cited
  as [8] in the next item): reduces the AC0[p]-Frege problem to ENS refutations and pseudo-solutions;
  arXiv 2301.10617 is the pseudo-solutions paper. CITED-UNCHECKED beyond the abstract.
- Krajicek, "Pseudo-solutions of polynomial systems and the lower bound problem for AC0[p]-Frege
  systems", arXiv 2609.35927 v2 (28 Sep 2026, revised 30 Sep). Reduces the negated-PHP pseudo-solution
  question to a property of search trees querying linear maps on low-degree polynomials. NO
  unconditional bound; conditional on a probability estimate (Theorem 6.1, size >= k(n) if the
  estimate holds with k^(-O(1))). CITED-CHECKED (abstract and HTML intro summary; the paper was not
  read in full). Single author, no AI statement on the page, unrefereed arXiv preprint. Krajicek
  notes in Section 7 (per the fetch summary) that a super-polynomial k(n) would imply UENS does not
  simulate TC0-Frege, which sits in tension with a remark he cites that UENS simulates Extended
  Frege; so the hypothesis is strong and may be false. Not verified by me.
- Lu-Santhanam-Tzameret, "AC0[p]-Frege Cannot Efficiently Prove that Constant-Depth Algebraic
  Circuit Lower Bounds are Hard", arXiv 2509.16824 (20 Sep 2025), ITCS 2026 (LIPIcs 99).
  Unconditional: a DNF family encoding Permanent hardness has no poly-size AC0[p]-Frege proofs
  infinitely often (hence hard or not a tautology). Not a lower bound for a known-true family; not
  depth 2 specific. CITED-CHECKED (abstract). Relevant as a source of hard-or-false DNFs, not as a
  candidate for us.
- Impagliazzo-Mouli-Pitassi, "The Surprising Power of Constant Depth Algebraic Proofs", LICS 2020
  (ECCC TR19-024): constant-depth IPS/AC0[p]-Frege relations; already in the frontier doc as a
  barrier reference. CITED-UNCHECKED (as in r4-frontier.md; I did not reopen it).
- Govindasamy-Hakoniemi-Tzameret (lower bounds for constant-depth multilinear IPS, FOCS 2022) and
  related: depth-2 multilinear IPS bounds over characteristic zero or large characteristic.
  CITED-UNCHECKED (from a secondary notes page and memory). These are algebraic proof systems,
  not AC0[p]-Frege, and I do not rely on them.
- Maciel-Pitassi: quasi-polynomial simulation of AC0[p] proof systems by depth 3 threshold proofs.
  CITED-UNCHECKED, already in the frontier doc.
- Davis-Robere, "Res(log) Proves Bounded-Depth Frege Lower Bounds", ECCC TR26-055 (10 Apr 2026):
  Res(log) can prove its own bounded-depth Frege lower bounds (reflection-type). Says nothing about
  parity or mod p. CITED-CHECKED (abstract). Metamathematical context only.

### 1.2 Depth 1 (Res(lin F_p), Res(PC_r/F_p), Res(xor)): what is certified and what is claimed

Certified in this repo (PROVED): Smolensky (`smolensky_parity`, `smolensky_mod3`);
`php_bdfrege_superpoly` (mod-free depth d Frege, PHP); `countq_bdfrege_exp`; tree-like Res(xor)
(`treelike_reslin_php`); tree-like Res(lin F_p) for Tseitin mod q (`reslin_tseitin_size`, one-hot,
and the Boolean-edge version via the AR port); `tseitin_bool_degree_Fp`; PC size from degree
(`tseitin_ml_size`). Per the task statement, also certified: Braun's bit PHP bound for dag-like
Res(xor), Khaniki's n^2/log n dag bound (Res(lin F_p), Tseitin mod q), the Alekhnovich-Razborov
exact-formula Tseitin bound. I did not re-audit those status claims; I take them from the
coordinator.

Cited:
- Itsykson-Sokolov (APAL 2020), Efremenko-Garlik-Itsykson (STOC 2024), Alekseev-Itsykson (STOC 2025),
  Bhattacharya-Chattopadhyay(-Dvorak) (CCC 2024, arXiv 2402.04364, 2507.23008), Byramji-Impagliazzo
  (2511.20023), Itsykson-Podolskii-Shekhovtsov (CCC 2026), STOC 2026 "Lower Bounds for
  Near-Quadratic-Depth Resolution over Parities" (Bhattacharya, Byramji, Chattopadhyay,
  Impagliazzo, per the references of arXiv 2609.23015; DOI 10.1145/3798129.3800809): CITED-CHECKED
  as recorded in r4-frontier.md; the STOC 2026 paper's existence re-seen in search results today.
- Braun, arXiv 2609.23015 (19 Sep 2026): exponential dag-like Res(xor) bound for bit PHP. Single
  author, AI-assisted, unrefereed. Status here: ported and proved (per coordinator); the
  literature claim itself remains unrefereed.
- Part-Tzameret (ITCS 2020 / Comput. Complexity 2021, arXiv 1806.09383): tree-like Res(lin F)
  bounds, dag-like for some regimes and different moduli. CITED-CHECKED (r4-phase22-plan.md).
- Khaniki, ECCC TR20-034 (Rev. 3, Jan 2021): dag-like n^(2-o(1)) for Res(PC_d/F) via size-width
  with extension variables. CITED-CHECKED (r4-khaniki-plan.md: ECCC PDF read).
- Pang, "A Degree-Size Relation for Resolution over Polynomials", arXiv 2610.00837 v1 (30 Sep 2026),
  cs.CC. CITED-CHECKED (abstract fetched today; full TeX read by the earlier scout, no error found,
  see r4-pang-plan.md). Author used "ChatGPT-6 Extra High" with targeted questions and discloses
  that "suggestions directed the search materially; only their necessity remains unclear". Single
  author, unrefereed, formalization in progress here. Statement (r = 1 case): CNF of width w on n
  variables, no PC refutation over F_p of degree D, D >= max{32(p-1)^2 r, 8w}: every dag-like
  Res(PC_r/F_p) refutation has ln S >= D/(32 p^2 r) (D/(16n))^((p-1)r). Corollaries listed by the
  abstract: exponential Res(PC_r/F_p) and Res(xor_p) bounds, separations between moduli, improved
  Res(k) bounds up to k = eps log n (Cor. 7.5, per fetch).
  Note: the abstract text mentions "implies super-polynomial AC0[p]-Frege lower bounds from very
  strong PC degree lower bounds"; the body only has the Section 8 remark and a conditional
  depth-2 sketch (next section). Do not cite Pang as having proved any AC0[p]-Frege bound.
- Weak or barrier-like: no Pich-Santhanam-type natural-proofs barrier theorem specific to AC0[p]-Frege
  was located (CITED-UNCHECKED, see 3.3).

### 1.3 Summary table

| System | Best known | Status |
|---|---|---|
| Depth-d Frege (mod free) | exp (PHP, Tseitin) | PROVED PHP super-poly here |
| Bounded depth Frege + Count_p axioms | exp for Count_q | PROVED here |
| Res(lin F_p), Res(PC_r/F_p) dag | exp (Pang, if it holds); n^(2-o(1)) (Khaniki) | Pang unrefereed, formalization underway |
| Res(xor) dag | exp (Braun, unrefereed), bit PHP | ported |
| Depth 2 AC0[p]-Frege | nothing | open |
| AC0[p]-Frege, any depth | nothing | open since the 1980s |

## 2. What Pang gives toward depth 2, and the exact gap

### 2.1 What depth 2 AC0[p]-Frege translates to

Take the sequent calculus with MOD_p connectives (our `FRefutes`). A depth 2 proof has lines
(sequents) whose formulas have depth at most 2 (counting the bottom layer as gates over literals,
the usual convention; depth 2 means two gate layers above literals). Gate types: AND, OR, NOT free,
MOD_p^i of unbounded fan-in.

Depth 1 is lines = disjunction of depth-1 gates over literals. A depth-1 gate is an AND (a term),
an OR (a clause), or a MOD_p gate (a linear equation sum a_i x_i = c over F_p, after repetition of
variables, polynomial fan-in). Res(lin F_p) corresponds to lines that are disjunctions of linear
equations, i.e. OR over depth-1 MOD_p gates, with only resolution-style rules. Res(PC_r/F_p) with
equations of degree r corresponds to disjunctions of bounded-fan-in AND of literals (monomials) and
bounded combinations. Res(k) is k-DNF lines (Pang Fact 7.4, via monomials).

Depth 2 adds, over depth 1, the following, none of which Pang's theorem as stated covers:
(a) Unbounded fan-in AND of depth 1 gates inside a line (a line OR_i AND_j (gate_ij)): a
    DNF of linear equations. Its polynomial encoding has degree growing with the AND fan-in, which
    is unbounded, so it is not Res(PC_r) for fixed r.
(b) MOD_p gates whose inputs are depth 1 gates (for example a mod-p count of how many clauses
    hold): a linear combination of indicator polynomials of degree equal to the child degree.
(c) Cuts on depth 2 formulas and the associated logical rules (introduction of AND and OR in
    sequents), which are not the resolution/linear-combination rules of Res(lin).
(d) Lines whose width (number of depth 1 or depth 2 disjuncts) is unbounded; Res(lin)'s analysis
    handles width through the approximation of the line as an OR, the new feature is that each
    disjunct itself needs an approximator.

Standard facts used (CITED-UNCHECKED, folklore): depth d Frege can be assumed in sequent form with
all cut formulas of depth at most d; a depth 2 proof of a CNF refutation can be put in a form where
every line is a sequent of depth 2 formulas. I have not re-derived the normal form; it is a
precondition to attack A and must be checked.

### 2.2 What is covered

- Depth 1, all rules of Res(PC_r/F_p) for fixed r (Pang, if correct): this subsumes (a) only for
  bounded AND fan-in, and (b) only for bounded child degree. It does not cover the case where
  fan-in grows with n.
- The mechanism is "inference-preserving approximation": each line L is replaced by a
  Razborov-Smolensky style multiplier P_L = prod (1 - q_j^(p-1)) with q_j in the F_p-span of the
  indicators of the disjuncts, and the whole refutation is simulated inside PC at degree
  K + O(Delta). It uses a common multiplier f, found by a dimension count over all S lines
  (Pang L6), with errors measured by the normalized rank ratio eta (Pang L4, L5).

### 2.3 The depth 2 sketch in Pang's Section 8 and the gap (CITED-CHECKED at summary level)

Per the fetched summary of Section 8: first layer T (conjunction of equations h_i = 0, degree
<= r) and second layer L (disjunction of such terms), approximators PT, PL with degrees
Delta1 = (p-1) r t1 and Delta2 = (p-1) Delta1 t2. The dimension count closes if

  M1 (1 - eta_K(r))^t1 + M2 (1 - eta_K(Delta1))^t2 < 1,

with M1, M2 the numbers of first and second layer gates and
eta_K(delta) = (1 - 1/p) N_n(K - delta) / N_n(K), N_n(K) = sum_{j<=K} C(n, j).
Pang's remarks: if K is well below n/2, the degree of the input polynomial at one layer loses
an exponential factor in eta at the next layer; near the middle (K within O(sqrt n) of n/2) eta is
Omega(1) and O(log M) factors per gate suffice, so the approximator degree is O((log M)^depth),
well below sqrt n. The stated obstruction is a PC degree lower bound near or above n/2, which
Pang says is unknown for o(n)-width polynomial-size CNFs. This is a conditional sketch, not a theorem.

My own heuristic computation (CONJECTURE, not checked against the TeX): with K = (1/2 - gamma) n and
Delta1 = c ln S, eta_K(Delta1) is about S^(-4 gamma c). Then t2 is about S^(4 gamma c) ln S and
Delta2 about S^(4 gamma c) polylog S. For Delta2 to fit under K <= n, one needs S below roughly
n^(1/(4 gamma c)). Therefore for fixed gamma > 0 (any constant PC degree ratio D/n < 1/2 after the
usual K ~ D - O(Delta) correction) the argument excludes only proofs of size n^(O(1/gamma)), a fixed
polynomial, not all polynomials. To exclude every polynomial one needs gamma = o(1), i.e. PC
degree >= (1/2 - o(1)) n (with K up to D - O(Delta)). This explains Pang's n/2 threshold.

Exact gap, stated as a list:
G1. A constant-width unsatisfiable CNF family on n variables with PC refutation degree over F_p at
    least (1/2 - o(1)) n. Not known to exist; known linear bounds (Tseitin mod q on expanders,
    AR 2001; random k-CNF; mod q Count) have small constants. PHP has degree about sqrt(#vars)/2
    in the number of variables, far below 1/2. It is open to me whether such a CNF exists at all
    or whether there is an upper bound of the form PC degree <= (1/2 - c_w) n for width w CNFs.
G2. Inference preservation for depth 2 rules, in particular for MOD_p connectives over depth 1
    gates (item b) and for the sequent-calculus logical rules (item c). Pang says the extension
    holds provided "error relations for each gate" are supplied; none is written out.
G3. Unbounded AND fan-in in a depth 1 sub-line (item a): degree, and also dimension counts, depend
    on handling fan-in via approximation of ANDs. The sketch uses (1 - q^(p-1)) factors for
    this; its correctness for AND of m terms with m super-constant is not verified.
G4. A normal form: a depth 2 sequent proof with only depth <= 2 cut formulas, and size accounting
    (number of distinct lines vs M1, M2).
G5. Soundness side: nothing in G1 to G4 uses the MOD_p connective axioms beyond Fm semantics, but
    the theorem is conditional on G1 so it would give "AC0[p]-Frege depth 2 needs size
    2^(n^eps)" only if G1 holds with the right exponent.

## 3. Candidate attack and honest assessment

### 3.1 Attack A: Pang depth-2 inference preservation with a high-degree CNF

Statement aimed at: for a constant-width CNF F on n variables with PC degree >= (1/2 - o(1)) n over
F_p (hypothesis H), every depth 2 AC0[p]-Frege refutation has size >= 2^(n^eps). Plan:
1. Normal form (G4): sequent calculus, depth <= 2 formulas, dag with S lines.
2. Define per-gate approximators for AND/OR over depth 1 and depth 2 gates and MOD_p gates; prove
   inference preservation for all sequent rules (G2, G3) with error sets that are sub-spaces of the
   multilinear space.
3. Common multiplier by dimension count with the two-layer inequality above (needs a clean proof of
   the inequality, including the claim that normalized rank is monotone for K up to the middle:
   Pang L4 covers K <= n/3 only in his parameters; the middle needs a re-proof (the proof in L4
   uses the down-closed family bound, which is believable but N_n(K) <= 2 C(n,K) fails as K tends
   to n/2, so L8 must be redone)).
4. Simulate in PC at degree K + O(Delta2) and conclude with H.
5. Produce a family satisfying H (the hard part).

Step-by-step plausibility:
- Step 1: plausible (standard). CITED-UNCHECKED, easy.
- Step 2 and 3: plausible but real work, since Pang's own ingredients are for r = 1 syntactic
  rules; the depth 2 version of the simulation needs a second-layer line language. I would rate
  "provable if H is given" as moderately plausible (CONJECTURE, maybe 40 percent that a clean
  version exists with some loss in parameters).
- Step 5: the problem. The problem of constructing a constant-width CNF with PC degree
  (1/2 - o(1)) n over F_p is a new question in PC degree lower bounds. Sparse CNFs have
  too few constraints per variable to force degree that high by expansion alone (expansion arguments
  give boundary sizes at most d(1 - ...) relative, Alekhnovich-Razborov style yields r(l/4 - (s-c))
  with the factor 1/4, and the bounds scale like n/(constant) with the constant larger than 2).
  I would rate step 5 as unlikely (CONJECTURE, under 10 percent), and an upper bound
  "PC degree of a width-w CNF on n variables is at most (1/2 - c_w) n" is not excluded.
  This is the main risk.

### 3.2 Attack B: restriction plus Pang

Idea (CONJECTURE, new): use a random restriction (switching lemma style, Hastad) to collapse
the AND/OR layers of a depth 2 proof so that most lines become depth 1 (decision trees of small
depth over MOD_p gates), then apply Pang to the restricted proof. The relevant quantity is the
ratio D'/n' for the restricted formula: a restriction that shrinks n faster than the PC
degree ratio could raise D'/n' towards 1/2. For Tseitin on an expander, fixing a fraction of edges
leaves Tseitin on a subgraph and might preserve linear degree on fewer variables. Problems:
(i) switching lemmas for MOD_p gates do not exist (this is the Razborov-Smolensky obstacle in the
proof setting): MOD gates do not simplify under random restrictions. (ii) Restricted formulas are
no longer the same family. (iii) The raise in ratio is not computed and could be negative.
Plausibility: low (CONJECTURE, under 5 percent) as a proof; it is a cheap exploratory calculation
for the degree ratio question G1 though.

### 3.3 Attack C: Krajicek pseudo-solutions

Attack on the PHP-style statement through his search tree property (arXiv 2609.35927). This is
a conditional program, not an attack we can execute: the hypothesis is the open question
Krajicek states. We can read and track it. Plausibility of this project proving the hypothesis: very
low (CONJECTURE), and note his own remark that the hypothesis with large k implies strong
non-simulation consequences, which is a barrier-like warning.

### 3.4 Barrier checklist (T4.2)

- Natural proofs (Razborov-Rudich) / pseudorandom generators: Pang's argument is an explicit
  algebraic approximation (Razborov-Smolensky for proofs) tied to the PC degree of a specific CNF.
  No natural-proofs obstruction is known at AC0[p] depth 2, since AC0[p] provably cannot compute
  MOD_q (circuit side is unconditional). The Razborov and Krajicek generator conjectures concern
  much stronger systems. CITED-UNCHECKED, structural reading; I record "none found".
- Feasible interpolation: fails for bounded depth Frege under cryptographic assumptions (Bonet,
  Pitassi, Raz and the bounded depth refinements; CITED-UNCHECKED), so interpolation is not an
  available method at depth >= 2 AC0[p]. It is not a barrier to the algebraic route; it is a
  closed door.
- Relativization-type: Razborov-Smolensky already passes through the algebraic method which does
  not relativize in the sense relevant to oracle gates; no known relativization obstruction for
  proof systems specific to this setting. I record "no relativization barrier found", not "proved
  absent".
- Algebrization-type: nothing found.
- Barrier from the AC0[p] proof side: Lu-Santhanam-Tzameret and Krajicek's conditional results
  mean any argument that also covers depth d for all d would imply strong separations; the depth
  2 attack is allowed to fail at depth 3 due to the exponential growth (b log M)^depth.
- Easy families (T4.1 upper bound checks): formulas with short depth 2 AC0[p]-Frege
  proofs cannot be hard for it, so a depth 2 lower bound must avoid them. Known short proofs:
  * Tseitin mod p over F_p (same modulus): polynomial-size Res(lin F_p) proofs (Pang Section 7.2 and
    Part-Tzameret, CITED-UNCHECKED for this repo). So only p does not divide q families are
    candidates.
  * Count_p, parity formulas for p = 2: short in Res(xor) / AC0[2]-Frege. CITED-UNCHECKED.
  * Onto PHP/weak PHP: quasi-polynomial bounded depth Frege proofs for weak PHP (Maciel-Pitassi-Woods,
    already recorded); PHP itself has no short bounded-depth Frege proofs (PROVED here
    super-poly for mod free). With MOD_p connectives PHP proofs are unknown to be short. A
    quasi-polynomial AC0[p]-Frege proof of onto PHP or bit PHP kills the candidate (T4.1). Nothing
    known.
  * Count_q on mod p reasoning (p not dividing q): quasi-polynomial AC0[p]-Frege upper bound unknown
    (would kill).
  * Random k-CNF at linear density: no known short proofs; PC degree is linear (small constant).
- Kill conditions for this plan: (K1) a quasi-polynomial depth 2 AC0[p]-Frege refutation of the chosen
  family (T4.1); (K2) an upper bound of the form "PC degree <= (1/2 - c) n for every constant-width CNF
  of the relevant type" (this kills attack A's step 5 for the whole method, since H is then
  unsatisfiable); (K3) the argument would also prove a statement false or crypto-breaking (T4.2);
  (K4) three failed attempts per method (A, B, C) recorded in the session log, as in the rung doc.

## 4. Ranked next research tasks (no owner tasks)

Each task says what kind of agent it needs. Roles follow the research plan: strong model or
mathematician for constructions and prose proofs, local loop for falsification and bookkeeping.

1. Determine whether G1 can hold. Question: is there, for constant width w and field F_p, an upper
   bound PC degree <= (1/2 - c_w) n for unsatisfiable w-CNFs, or a construction with ratio
   (1/2 - o(1))? Needs a strong model or mathematician; prose, literature search (PC degree upper bounds
   for sparse CNFs, width-degree relations, graph-based Tseitin degree). Highest value: decides kill
   condition K2 and thus the whole attack A.
2. Re-derive the Pang depth-2 sketch in prose with all parameters, from the TeX (source of arXiv
   2610.00837), including the middle-of-the-cube range (the binomial ratio and normalized rank
   lemmas for K near n/2) and the exact exponent in the size bound as a function of gamma. Needs a
   strong model; output: a prose lemma list and an independent check of my heuristic in 2.3.
3. Formulate the depth 2 normal form and rules (G4) and write the inference preservation lemma for the
   MOD_p connective and AND of depth 1 gates (G2, G3) in prose. Strong model. Do this only if task 1
   does not kill.
4. Verify the cited-unchecked entries: Impagliazzo-Mouli-Pitassi, Govindasamy-Hakoniemi-Tzameret,
   Maciel-Pitassi, Krajicek ENS (2024) and 2301.10617, and the Bonet-Pitassi-Raz line for
   interpolation, and look for natural-proof-type barriers for proof systems (Pich-Santhanam). Local
   loop with web access plus a strong model for reading; output: corrected citation block.
5. Track independent confirmation or refutation of Pang (arXiv 2610.00837) and Braun
   (2609.23015): check for comments, errata, replacements, and any independent write-up. Local
   loop; periodic. Unrefereed AI-assisted claims are load-bearing here, so the formalization of
   Pang (already underway) is the main check.
6. Cheap numeric experiment for attack B: compute PC degree ratios for small Tseitin mod q on
   restricted subgraphs (linear algebra over F_p), to see whether D/n can approach 1/2. Local loop
   (falsification run); expected to be inconclusive for asymptotics but can kill intuition.
7. Read Krajicek 2609.35927 in full and extract the exact search tree hypothesis; assess whether
   the project can test it empirically on small n. Strong model for reading; low priority.
8. Hold: do not formalize any depth 2 statement in Lean until tasks 1 and 2 have a prose
   result that passes the barrier audit above (T4.2).

## 5. Session log (append-only)

- 2026-10-14 scout: plan written. No claim of a proof. Gap identified (PC degree near n/2, G1);
  heuristic obstruction stated and flagged as unverified. Web checks done: arXiv 2610.00837 abstract and
  Section 8 summary, arXiv 2609.35927 abstract and intro, arXiv 2509.16824 abstract, ECCC TR26-055
  abstract. Not checked: the full text of Krajicek 2609.35927, Pang's TeX (earlier scout read it),
  all CITED-UNCHECKED entries.
