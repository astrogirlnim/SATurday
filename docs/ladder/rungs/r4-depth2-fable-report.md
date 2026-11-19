# R4 depth 2: research session report (branch r4/depth2-fable)

Date 2026-11-18. Scope: checklist item 2.3 (depth-2 AC0[p]-Frege), the step after Res(lin F_p).
Reads: r4-research-plan.md, r4-completion-checklist.md, r4-phase23-{program,scripts}, r4-new-math-program.md,
r4-phase31-barrier-audit.md, expert-review-proposal.md, proof standards, stop conditions, branch depth2-search.

Labels: LEAN (kernel checked in this session, standard axioms only), HAND (argued on paper here, not machine
checked), COMPUTED (script run in this session), CITED-CHECKED (I read the abstract or a search snippet today),
CITED-MEMORY (recalled, not re-verified today), CONJECTURE (my judgment).

## 0. Bottom line

1. No lower bound for depth-2 AC0[p]-Frege is proved here, and none for the unrestricted depth one case of the
   pinned Lean system either. The open problem is as open as before.
2. What is new and kernel checked: a bridge theorem. A syntactic fragment of the pinned sequent calculus
   `FProof` (formulas of `Fm.depth` at most one, `MOD_p` gates of any fan in, but every `AND` in positive
   position and every `OR` in negative position of fan in at most `rho <= eps ln n`) is simulated line by line
   in the bounded rank calculus `R_rho^p`, with polynomial overhead. With `C1.c1_main_idx` this gives an
   `exp(n^(1 - (kappa+1) eps))` size bound for that fragment on the explicit one-hot Tseitin mod q family,
   `p` not dividing `q`. Main names: `FBridge.frege_to_R`, `FBridge.depth1_rank_frege_tseitin`,
   `FBridge.depth1_rank_frege_tseitin_idx`, non vacuity `FBridge.tseitin_fragment_nonvacuous`.
   This is the first Lean theorem in the repo that quantifies over `FProof` objects containing `MOD_p` gates.
   It answers one point of the Phase 3.1 audit (the C1 row: "no bridge theorem"), for depth one only.
3. Mathematically it is a corollary of Pang's theorem through C1. No new lower bound technique. No novelty claim.
4. A convention finding that matters for the plan (Section 2): in the pinned system, depth is the depth of the
   formulas inside a sequent, and a sequent is itself a disjunction. So `FRefutes p 1` already has lines that
   are DNFs with `MOD_p` atoms. What the literature calls depth-2 AC0[p]-Frege is (up to MOD-over-gate
   formulas) the pin at `d = 1`. The first open case of the pin is therefore `d = 1` without a rank condition.
   It is now stated as the Frontier pin `FBridgeFrontier.depth1_tseitin_target` (intentional sorry).
5. Negative results are in Section 6. The main one: random restrictions cannot remove the rank condition,
   for the same arithmetic reason that the earlier notes found (the exponent stays below 1).

## 1. State of the art (short note)

What is known, nearest first. Every item is a statement about the literature, not about this repo.

- Circuits. AC0[p] circuits need exponential size for MOD_q, q not a power of p (Razborov 1987; Smolensky
  1987). CITED-MEMORY. Formalized in this repo (`smolensky_parity`, `smolensky_mod3`).
- Bounded depth Frege without MOD gates. Exponential bounds for PHP (Ajtai 1988; Pitassi, Beame, Impagliazzo
  1993; Krajicek, Pudlak, Woods 1995) and for Tseitin (Pitassi, Rossman, Servedio, Tan, STOC 2016; Hastad,
  FOCS 2017 and J. ACM 2021; Hastad and Risse, FOCS 2022). CITED-MEMORY. Method: switching lemmas and
  k-evaluations. A MOD_p gate is not simplified by a restriction, so the method stops at MOD gates.
- Counting axioms instead of counting gates. Count_q is hard for bounded depth Frege with Count_p axioms,
  q not a power of p (Ajtai 1990 for parity versus PHP; Beame, Impagliazzo, Krajicek, Pitassi, Pudlak 1996;
  Buss, Impagliazzo, Krajicek, Pudlak, Razborov, Sgall 1997; Beame and Riis 1998). CITED-MEMORY. This is
  the nearest solved neighbor. Axioms are weaker than connectives; the gap is the open problem.
- AC0[p]-Frege itself. No super-polynomial lower bound is known for any prime p at any depth where MOD_p
  gates occur inside formulas. Stated as open in Alekseev and Itsykson (ECCC TR24-128, STOC 2025) and in
  Lu, Santhanam, Tzameret (arXiv 2509.16824, ECCC TR25-134), CITED-CHECKED by search snippet today and in
  the Phase 3.1 audit. Lu, Santhanam, Tzameret show that AC0[p]-Frege has no polynomial size proofs of a
  certain DNF family infinitely often, where it is open whether those DNFs are tautologies. That is not a
  bound for a known tautology.
- Collapse. Buss, Kolodziejczyk, Zdanowski (Trans. AMS 367 (2015) 7517 to 7563; CITED-CHECKED today for
  title, venue and the statement that constant depth proofs with AND, OR and mod p gates translate into
  simpler constant depth proofs with quasipolynomial blowup). From memory, not re-read: the target is depth
  three with a MOD_p gate on top of small conjunctions. I am not sure of the exact normal form. The
  consequence that matters: a strong enough (quasi-polynomial resistant) bound at very small depth would
  already give the full constant depth bound, so "small depth first" is not an easier problem by much.
- Earlier attempts and reductions. Maciel and Pitassi 1997 (towards lower bounds for bounded depth Frege
  with modular connectives) and Maciel and Pitassi 2006 (a conditional lower bound), CITED-MEMORY, titles
  approximate. Krajicek, arXiv 1311.2501 (Proc. AMS 2015): reduction of AC0[p]-Frege lower bounds to
  computational tasks about low degree polynomials, CITED-MEMORY and per the repo notes. Impagliazzo, Mouli,
  Pitassi (LICS 2020): constant depth IPS over F_p simulates AC0[p]-Frege quasi-polynomially (and more),
  CITED-MEMORY, read at snippet level in the Phase 3.1 audit.
- Subsystems with MOD gates of restricted use. Garlik and Kolodziejczyk, "Some subsystems of constant-depth
  Frege with parity" (ACM ToCL 2018), CITED-MEMORY: separations and bounds for fragments where parity gates
  are restricted (for example tree-like, or parities only of small conjunctions). I did not re-read it; it
  is the closest published relative of the fragment in Section 3 and should be compared before any claim.
- Resolution over linear equations (depth one in the literature's count).
  - Tree-like Res(xor): Itsykson and Sokolov (MFCS 2014; APAL 2020). Tree-like Res(lin F_p), Tseitin mod q
    for distinct primes: Part and Tzameret (ITCS 2020; Computational Complexity 2021; arXiv 1806.09383),
    CITED-CHECKED today (abstract level). They state dag-like bounds over finite fields as open.
  - Regular Res(xor): Efremenko, Garlik, Itsykson (STOC 2024), CITED-CHECKED by snippet.
  - Bounded depth (of the dag) Res(xor): Alekseev and Itsykson (STOC 2025); Efremenko and Itsykson
    (arXiv 2507.23008, per the audit); Bhattacharya and Chattopadhyay (STOC 2026, depth N^(2 - eps) for
    lifted Tseitin, per today's search snippet; I did not open the paper). "Depth" there is depth of the
    proof dag, not formula depth.
  - Dag-like, weak bounds: Khaniki (ECCC TR20-034; ToCL 2022 from memory) almost quadratic; a quadratic
    bound at CCC 2026 (per the audit).
  - Dag-like, exponential: Braun, arXiv 2609.23015 (bit PHP, Res(xor), 2^(Omega(n / log^2 n))), and Pang,
    arXiv 2610.00837 ("A Degree-Size Relation for Resolution over Polynomials": linear PC degree implies
    exponential size in resolution over constant degree polynomials over the same prime field). Both
    CITED-CHECKED today: the arXiv pages exist, with these titles and abstracts (Braun v2 of 3 Nov 2026,
    Pang v2 of 24 Oct 2026). Both are unrefereed. Pang's abstract itself lists "an implication of
    super-polynomial AC0[p]-Frege bounds from very strong PC degree lower bounds", which is the conditional
    route the earlier notes call hypothesis H.
- Res(k) (k-DNF resolution, no MOD gates). Segerlind, Buss, Impagliazzo (FOCS 2002) and later Alekhnovich,
  Razborov: bounds for k up to about sqrt(log n / log log n) and, for special formulas, eps log n.
  CITED-MEMORY, parameters approximate. Pang's abstract claims "improved lower bounds for Res(k) up to
  k = eps log n" (CITED-CHECKED).

What blocks depth 2, in one paragraph. A depth-2 line mixes three things: disjunctions of F_p-linear
equations (handled by Pang's approximation with a common multiplier, at rank one), conjunctions of unbounded
width (handled without MOD gates by switching lemmas, which MOD gates destroy), and MOD_p gates over
conjunctions or MOD_q-type counting (no low degree equation at all when the inputs are not affine). The two
working methods do not compose. Restrictions cannot be used to shorten conjunctions because the algebraic
method then needs rank log S, while its loss per unit of rank is a constant factor (K/n) in dimension, which
caps the tolerated rank at eps log n with eps far below 1 (earlier notes, and Section 6 below). The
conditional escape (PC degree ratio near 1/2 for a constant width CNF) is ruled out for Tseitin mod 2 by the
1/4 cap of r4-phase23-program.md (HAND there) and is unknown for every other family.

## 2. A convention check: what "depth" means in the pin

`Fm.depth` counts AND, OR, MOD levels inside one formula. A line of `FProof` is a sequent `Gamma |- Delta`,
semantically the disjunction of the negations of `Gamma` and the members of `Delta`. `FRefutes p d` bounds
the depth of the formulas, not of the sequent. So:

- `FRefutes p 0`: sequents of literals, that is, clauses. Resolution.
- `FRefutes p 1`: disjunctions of literals, ANDs of literals, negated ORs of literals, and MOD_p gates of
  literals and their negations. In the literature's count (a line is one formula) these are depth-2
  formulas: DNFs with F_p-linear atoms. Res(lin F_p) lines and Res(k) lines are both special cases.
- `FRefutes p 2`: adds MOD_p over ANDs, ANDs of MOD gates, and so on.

LEAN: `FBridge.flat_iff_depth` proves that the fragment's formula class `FlatIn V` is exactly
"`Fm.depth <= 1` and variables in `V`", so this reading is checked for the fragment. The off-by-one between
sequent calculus depth and formula depth is standard, but the repo documents call 2.3 "depth 2" and the pin
has `d` as a parameter, and I did not find the correspondence written down. Consequence: the smallest open
instance of the pin is `d = 1`, and it already contains the wide-conjunction difficulty. Card 2.3 in the
literature's sense is roughly the pin at `d = 1` plus the MOD-over-gate part of `d = 2`.

## 3. The route taken and what is proved

Route. Among the candidates (restricted subsystem, hard formula, needed lemma) I chose the restricted
subsystem, because it was the only one where something could be proved in a session, and because the
Phase 3.1 audit named the missing bridge as the reason C1 "is evidence of nothing about AC0[p]-Frege".

File: `theory/Theory/ProofComplexity/FregeRankBridge.lean` (namespace `FBridge`). All LEAN, axioms
propext, Classical.choice, Quot.sound.

Translation. A literal `phi` (a variable under any number of negations) has a value form `vf phi` (affine
over F_p, value 0 or 1 on the cube) and forms `zf s phi` vanishing exactly when `phi` has truth value `s`.
`tr s phi` translates a flat formula with a sign into a set of terms of `R_rho^p`:
- OR of literals, positive: one rank one term per member. Negative: one term, the conjunction "all false".
- AND of literals: dual.
- `MOD_{p,r}` of literals, positive: the single equation `sum of values = r`. Negative: the `p - 1`
  equations `sum = c`, `c != r`. Repeated members give coefficients, so every F_p-linear equation over
  literals is expressible.
A sequent goes to the union `trS` of the negative translations of the antecedent and the positive ones of
the succedent.

Simulation (`step_sim`). Each of the 18 cases of `FStep` is derived in `R_rho^p` from the translated
premises. The points that needed work:
- `MOD_p` counting axioms: from the partition line "sum of values of l is c, for some c in F_p", derived by
  induction on the list with `2p + 3` lines per member (`reach_PT`), one more semantic step gives each of
  the four axioms (`reach_modax`).
- Initial sequents `phi |- phi` for gates (`reach_taut`): AND introduction along the list (`reach_and`)
  from literal tautologies, or the partition line for MOD.
- Cut: for a flat formula one of the two translations is a single term (`tr_single`), so a cut costs
  (number of terms of the other side) + 1 semantic steps (`reach_map`).
- AND right, OR left: AND introduction, where the prefix terms have rank at most the rank of the final term.
Cost: at most `(2p + 8) (w(S) + M)` new lines for a step with conclusion `S`, where `w` is fan in plus one
summed over the sequent and `M` bounds `w` on earlier lines.

Theorems.
- `FBridge.frege_to_R`: if `FProof p F L`, the empty sequent is in `L`, every sequent is flat over `V`
  (some `v0` in `V`), and every translated sequent has rank at most `rho >= 1`, then there is
  `R : RRefutation F V rho p` with `R.S <= |L| (2p + 8) (2 W)`, `W` the total weight (`fW L`).
- `FBridge.flat_frege_tseitin` and `FBridge.depth1_rank_frege_tseitin`: for primes `p` not dividing `q >= 2`,
  `eps > 0` with `(kappa p q + 1) eps < 1`, for every `M` there is a cubic graph on `n >= M` vertices such
  that for every charge `b`, every `1 <= rho <= eps ln n` and every `L` with `FRefutes p 1 (tcnf G q b) L`,
  all variables among those of the formula (`fvars phi` in `tVars G q`) and the syntactic rank condition
  `RankS rho` on every sequent:
  `exp(n^(1 - (kappa+1) eps)) <= |L| (2p + 8) 2 (fSize L + |L|)`.
- `FBridge.depth1_rank_frege_tseitin_idx`: the same for all `m >= m0` on the explicit family `cubFam m`
  (`n = 8 m^2`) with the explicit charge `tseitinCharge1`, together with unsatisfiability of the instance and,
  for `q + 3 <= rho <= eps ln n`, existence of a refutation inside the fragment.
- Non vacuity: `FBridge.fragment_nonvacuous` (any unsatisfiable CNF with clause width at most `rho` and
  variables in `V` has a refutation in the fragment; proof: the resolution simulation of `AC0pFrege.lean`
  re-run with an invariant, `sim_resolution_inv`) and `FBridge.tseitin_fragment_nonvacuous`.
- `RankS rho S`: for every formula of the antecedent `RankOK rho false`, of the succedent `RankOK rho true`,
  where `RankOK` flips the sign under negation and requires fan in at most `rho` for an AND with sign true
  and an OR with sign false; no condition on MOD gates or on the other two cases.

Reading of the statement, for a reviewer.
- It is a lower bound on lines plus symbols: the right side is at most `(4p + 16) (fSize L + |L|)^2`.
  `fSize` alone does not bound the number of lines (empty sequents have size zero), so `|L|` is kept.
- Shape: the first two theorems are "for every M there is n >= M"; the indexed one is "for all m >= m0" on
  one explicit family with gaps of a factor at most 2 between consecutive sizes.
- Constants: `kappa` is about 24.7 for (p, q) = (3, 2), so `eps < 1/25.7` and `rho >= q + 3 = 5` needs
  `ln n >= 129`. The statement is asymptotic only. This is inherited from `c1_main`.
- The statement quantifies over all charges `b` in the first two theorems, satisfiable ones included
  (vacuous there). The indexed theorem fixes an unsatisfiable instance.
- The variable condition (no variables outside the formula) is a real restriction of the statement. It is
  harmless in spirit (substitute 0 for other variables) but that reduction is not formalized.

## 4. What the theorem does not show (red team of my own result)

Audit questions of r4-phase31-barrier-audit.md, Section 1.
- Q0 (what it exploits): PC degree of Tseitin mod q over F_p through Pang's method, as packaged in C1. The
  bridge adds only a syntactic simulation.
- Q1 (equal systems): the fragment is defined on the pinned calculus by syntactic conditions, so the
  statement is about that calculus. It is not closed under the calculus' own derived rules: a cut on a wide
  AND leaves the fragment. A fragment is not a proof system in the Cook-Reckhow sense unless the conditions
  are decidable, which they are here (depth, fan in, variables), so this one is. Whether it is polynomially
  equivalent to a named system is not proved. HAND, unproved: it contains resolution (LEAN, from the non
  vacuity proof), it should p-simulate Res(lin F_p) with coefficients written in unary and Res(k) for
  `k <= rho`, and it is simulated by `R_rho^p` (LEAN).
- Q2 (short proof control): the theorem needs `p` not dividing `q`. For `q = p` the hypothesis fails, as it
  must: Tseitin mod p has short Res(lin F_p) proofs.
- Q3 (pseudorandomness): no circuit is extracted. No flag.
- Strength: the bound is not new mathematics. Pang's abstract already claims Res(k) up to `k = eps log n`
  and Res(PC_r / F_p). The content here is that the bound now applies to proofs written in the pinned
  sequent calculus with native MOD_p rules, kernel checked.
- Distance to the target: the fragment excludes exactly the hard part, wide conjunctions in positive
  position. A depth one refutation may use ANDs of fan in n^c, and nothing here says anything about them.

## 5. Experiment: started in error, stopped, no result

Plain record. Before I had the board context I copied the `d1_*.py` scripts from branch depth2-search and
started a small bounded grid (Tseitin mod 2 on K4, atoms over F_3, at most 10 derived lines, cap 240 s per
instance, cost estimate recorded beforehand: below 10^5 variables and 10^6 clauses per instance, at most 70
minutes of wall clock). The coordinator then told me that this search direction was stopped by the owner on
2026-10-27 and must not be restarted. I killed the run at once, removed the scripts from this branch again
(they remain only on depth2-search), and did not rerun anything.

What the partial log shows (COMPUTED, 36 instances finished before the kill, kept only in the session
scratch directory, not in the repo): for lines that are ORs of 1, 2 or 3 single F_3-affine atoms, and for
lines of one term with two atoms, there is no semantic refutation with at most 7 derived lines; the
instances with 8 to 10 lines that finished all timed out. No refutation was found in any class. This is not
a result and supports no conclusion in either direction. Nothing in this report depends on it.

## 6. Negative results and dead ends

1. Removing the rank condition by a random restriction fails (HAND; agrees with item E3 of
   r4-phase23-program.md, redone here for the fragment). A restriction that fixes whole edges of the one-hot
   Tseitin instance keeps MOD_p gates of literals as MOD_p gates of literals, and falsifies an AND of `w`
   literals except with probability about `c^(w/2q)` for a constant `c < 1`. A union bound over `S` terms
   leaves terms of width `O(log S)`, so the restricted proof lies in the fragment with `rho = C log S`. The
   theorem needs `rho <= eps ln n'` with `eps < 1/(kappa + 1)`, where `n'` is the size of the restricted
   instance. That gives a statement only for `S <= n'^(eps / C')`, and the exponent is below 1 (at most about 0.04
   for (3, 2)). A CNF has at least that many clauses, so the statement is
   vacuous. To make this work one needs the rank tolerance `eps` to be an arbitrary constant, that is, a
   per-rank loss tending to 1, which is the `(K/n)^rho` wall of the earlier notes. Counted as one failed
   attempt of method M1 in the audit's bookkeeping only if the owner treats it as new; it is the same
   arithmetic as before, so I record it as a confirmation, not a new attempt.
2. The bridge does not extend to cut formulas outside the fragment. In `step_sim` the cut case needs one of
   the two translations of the cut formula to be a single term of rank at most `rho`. For a wide AND the
   single term has rank up to its width. This is the exact line where a depth one proof leaves the fragment.
3. `MOD_p` over conjunctions (`Fm.depth` 2) is not reachable through `R_rho^p` as defined: its lines are
   disjunctions of conjunctions of affine equations, and "the number of true terms is r mod p" is a
   polynomial equation of degree about `(p-1)^2 rho`, not a conjunction of affine equations. It needs the
   degree-r version of the calculus (Pang's Res(PC_r)), which the repo has only for `r = 1` plus the special
   indicator family of C1. Not attempted.
4. No new hard family. I did not find, and did not search for, a constant width CNF with PC degree ratio
   above 1/4. Hypothesis H stays unknown.
5. No upper bound either. I did not find a short depth-2 refutation of Tseitin mod q, and the stopped run
   of Section 5 is not evidence in either direction.
6. Literature tension resolved. A search snippet today (a 2026 paper summary) calls general dag-like
   Res(xor) lower bounds "the remaining open problem", while the repo relies on Braun and Pang. I checked
   the two arXiv pages directly: both exist with the titles and claims the dossier attributes to them, dated
   after the snippet's source. So there is no contradiction, only two unrefereed preprints that newer
   surveys have not absorbed. The caveat in the expert review proposal stands.

## 7. Open target and the single best next step

Frontier pin (intentional sorry, `FregeDepth1Frontier.lean`, namespace `FBridgeFrontier`):
`depth1_tseitin_target`: for every `c` there is `m0` such that for all `m >= m0` every `L` with
`FRefutes p 1` of the explicit Tseitin instance has `(8 m^2)^c < fSize L + |L|`. Open. No evidence beyond the
fragment. It is the pin `r4_target` at `d = 1` for one candidate family, without the two side conditions.

Best next step (one item): generalize `c1_main` from terms that are conjunctions of affine equations to
lines whose disjuncts are arbitrary 0/1-valued polynomial indicators of degree at most `d` on the cube, with
the two semantic rules unchanged. The step lemmas of `C1Sim.lean` are already stated for an arbitrary index
type with a family of indicator polynomials, so this is mostly a change of definitions. With it, the bridge
of this session extends, by the same case analysis, to `Fm.depth` 2 formulas that are MOD_p gates over
conjunctions of rank at most `rho` (rung 5 of r4-new-math-program.md). That would be a kernel checked bound
for a fragment that uses MOD_p gates over gates, which is the feature that separates AC0[p]-Frege from
Res(lin). It would still not touch wide conjunctions.

What would count as real progress beyond that (CONJECTURE): any argument that tolerates rank `C log n` for
every constant `C` (then restrictions give all of depth one for polynomial size), or a constant width family
with PC degree ratio near 1/2. I have no idea for either.

## 8. Session log

- Read the plan, checklist, Phase 2.3 notes, Phase 3.1 audit, expert proposal, standards, stop conditions.
  Checked branch depth2-search: scripts only, no recorded results.
- Chose the bridge route. Wrote `FregeRankBridge.lean` in six parts, each checked with `lake env lean`
  against the primary checkout's build (worktrees have no `.lake`). Commits were small.
- Added non vacuity, the indexed theorem, the depth characterization, and the Frontier pin.
- Verified by web: the Braun and Pang arXiv pages, the Buss, Kolodziejczyk, Zdanowski reference, the Part and
  Tzameret abstract. Everything else in Section 1 marked CITED-MEMORY is unverified.
- Started a K4 grid with the d1 scripts, then stopped it on the coordinator's instruction (Section 5).
- Board context received mid-session: "depth 2 beyond log n rank" is closed by the owner as a limit of the
  method, and the d1 search is stopped. The bridge route of Section 3 is neither of these: it does not try to
  pass log n rank, it transports the existing bounded rank theorem into the pinned calculus. Section 6 item 1
  agrees with the owner's closure and adds no new attempt. The block-aligned subspace idea was not touched
  (r4-new-math-program.md Section 3 already records a near negative test).
- Merge: see the handback message and `git log` for the merge commit. Nothing pushed.
