# R4 step 2.4: research session report (branch r4/ac0p-fable)

Date 2026-11-18. Scope: checklist item 2.4, constant depth AC0[p]-Frege (the pin `AC0pFregeFrontier.r4_target`).
Reads: r4-research-plan.md, r4-completion-checklist.md, r4-phase31-barrier-audit.md, r4-depth2-fable-report.md,
expert-review-proposal.md, proof standards, stop conditions, `FregeRankBridge.lean`, `FregeDepth1Frontier.lean`,
`C1Sim.lean` and the C1 chain.

Labels: LEAN (kernel checked in this session, standard axioms only), HAND (argued on paper here, not machine
checked), CITED-CHECKED (I read the abstract today), CITED-MEMORY (recalled, not re-verified), CONJECTURE (my
judgment).

## 0. Bottom line

1. No lower bound for AC0[p]-Frege is proved here, at any depth. The open problem is as open as before.
2. What is new and kernel checked:
   - A calculus `PIC` (`PolyIndCalc.lean`): lines are disjunctions of arbitrary 0/1 valued polynomials over F_p
     of degree at most `d` (the previous session's recommended generalization of `R_rho^p`), with the same
     size bound as `C1.c1_main` on one-hot Tseitin mod q, for `d = (p-1) rho`, `rho <= eps ln n`
     (`PIC.pic_main`, `PIC.pic_main_idx`).
   - A bridge for every formula depth (`FregeDegBridge.lean`): a refutation in the pinned sequent calculus
     `FProof`, with no bound on `Fm.depth`, in which every translated term has syntactic degree at most `d`,
     is simulated line by line in `PIC` (`FDeg.frege_to_PIC`). Hence the size bound
     `exp(n^(1 - (kappa+1) eps)) <= |L| * 10 * 2 (fSize L + |L|)` for such refutations
     (`FDeg.lowdeg_frege_tseitin`, `FDeg.lowdeg_frege_tseitin_idx`). The fragment contains MOD_p gates over
     conjunctions, conjunctions of MOD_p gates, and nestings of these to any constant depth, as long as the
     degree stays at most `(p-1) eps ln n`. It contains the flat rank fragment of the previous session
     (`FDeg.degS_of_rankS`).
3. Mathematically this is still a corollary of Pang's degree-size method (resolution over polynomials of
   bounded degree). No new lower bound technique. No novelty claim.
4. The map is sharper. For this method the parameter is degree, not depth. MOD_p gates cost a factor `p-1` per
   nesting level whatever their fan in. The only thing excluded is an `AND` in positive position, an `OR` in
   negative position, or any `AND`/`OR` below a MOD_p gate, whose fan ins add up to more than `(p-1) eps ln n`.
   Section 5 says where the degree enters and why it stops at `eps ln n`.
5. One step further that I argued on paper and did not formalize (Section 6, HAND): a wide `AND` in positive
   position can be expanded into one line per member. This extends the fragment to sequents with unbounded fan
   in conjunctions in positive position, provided the number of such conjunctions per sequent is small (the
   product of their fan ins is below the exponential bound). It is the CNF expansion and not a new idea.
6. New Frontier pin (intentional sorry): `FDegFrontier.log2_degree_target`, the same statement at degree
   `(log_2 n)^2`. Open.

## 1. What I did, in order

- Read the documents. Agreed with the previous session's next step and took it as the starting point.
- Generalized `C1.claim_step` (it asked for 0/1 values of the whole indicator family, the proof uses it only
  for the resolved index). This is the only change to an existing file.
- Wrote `PolyIndCalc.lean`: the calculus, soundness, the simulation in polynomial calculus, the degree-size
  relation, the Tseitin bounds. The proofs of `C1Sim`, `C1DegSize`, `C1Params` go through with the indicator
  family replaced by the identity on polynomials; the real-number chain (`C1.real_chain`) is reused as is.
- Then, instead of extending the flat bridge by one more formula shape (MOD_p over small conjunctions), I
  wrote a new bridge that is recursive in the formula. This turned out simpler than the flat bridge, because a
  MOD_p gate is now one term (its value polynomial) and no partition line is needed.
- Checked the Buss, Kolodziejczyk, Zdanowski abstract (Section 5.3).
- Thought about wide conjunctions (Sections 5 and 6). Did not restart the closed directions (rank beyond
  log n through restrictions; the d1 small-graph search).

## 2. The calculus PIC (LEAN)

File `theory/Theory/ProofComplexity/PolyIndCalc.lean`, namespace `PIC`. Axioms propext, Classical.choice,
Quot.sound.

- A term is a polynomial `g` over `ZMod p`. `PIC.Ind V d g`: values in {0, 1} on the Boolean cube, total degree
  at most `d`, variables in `V`. A line is a finite set of terms, read as "some term has value 1".
- Rules (`PIC.PInfer`): clause axioms (one literal indicator per literal), excluded middle `{g, 1 - g}` for any
  `g`, weakening, and the semantic term rule with one premise (`g1` implies `g3` on the cube) or two premises
  (`g1` and `g2` imply `g3` on the cube); `g3 = 0` stands for the empty conclusion.
- `PIC.PRefutation Phi V d p`: a dag of lines, every term of every line an indicator of degree at most `d` over
  `V`, last line empty. Size is the number of nodes.
- `PIC.PRefutation.unsat`: soundness.
- `PIC.pic_simulation`, `PIC.pic_degree_size`, `PIC.pic_size_exp`, `PIC.pic_exp_of_degree`: the Pang layers for
  this calculus. `PIC.pic_tseitin_exp_idx`, `PIC.pic_tseitin_exp'`: `2^(n / cCR p q d) <= S` on Tseitin.
- `PIC.pic_main`: primes `p` not dividing `q >= 2`, `eps > 0`, `(kappa p q + 1) eps < 1`. For every `M` there
  is a cubic graph on `n >= M` vertices such that for every charge `b`, every `1 <= rho <= eps ln n`, every
  `R : PRefutation (tcnf G q b) (tVars G q) ((p-1) rho) p` has `exp(n^(1 - (kappa+1) eps)) <= R.S`.
- `PIC.pic_main_idx`: the same for all `m >= m0` on the explicit family `cubFam m`, `n = 8 m^2`.

Reading. `R_rho^p` is the special case where every term is the indicator of a conjunction of affine equations
of rank at most `rho` (degree `(p-1) rho`). The embedding of `R_rho^p` into `PIC` is not formalized; the
containment that matters for the Frege statement is formalized at the Frege level (`FDeg.degS_of_rankS`).
Constants are those of `c1_main`: `kappa` is about 24.7 for (p, q) = (3, 2), so the degree bound is about
`0.078 ln n` there. The statement is asymptotic only.

## 3. The bridge for all depths (LEAN)

File `theory/Theory/ProofComplexity/FregeDegBridge.lean`, namespace `FDeg`.

Definitions.
- `val p phi`: the value polynomial. Variable `x_i`; `NOT` is `1 - v`; `AND` is the product of the member
  values; `OR` is `1 - prod (1 - v)`; `MOD_{p,r}` is `1 - (sum of member values - r)^(p-1)`.
  `FDeg.eval_val`: on the cube it is 1 if `phi` is true and 0 otherwise (for every formula, any depth).
- `pd p phi`: syntactic degree. Variable 1; `NOT` unchanged; `AND`/`OR` the sum of the member degrees;
  `MOD_p` is `(p-1)` times the largest member degree. `FDeg.deg_val`: `totalDegree (val p phi) <= pd p phi`.
- `trL p s phi`: the translation of `phi` with sign `s` into a list of terms whose disjunction says "`phi` has
  truth value `s`". An `OR` with sign true is split into the translations of its members, an `AND` with sign
  false dually, `NOT` flips the sign, and every other case gives the single term `val` or `1 - val`.
- `td p s phi`: the largest syntactic degree of a term of `trL p s phi`.
- `trS p S`: antecedent formulas with sign false, succedent formulas with sign true.
- `DegS p d S`: `td <= d` for every formula of the sequent with its sign. `VarS V S`: variables in `V`.

Theorems.
- `FDeg.tr_form`: every term of the translation is `val` or `1 - val` of a subformula of degree at most `td`,
  with variables of `phi`, and implies that `phi` has truth value `s`.
- `FDeg.reach_split`: for a formula of degree at most `d`, the line "translation of `phi` with sign `s`, or the
  single term of the opposite sign" is derivable with at most `5 size(phi) - 2` lines.
- `FDeg.step_sim`: each of the 18 cases of `FStep` is derived in `PIC` with at most `10 (w(S) + M)` new lines,
  `w` the total formula size plus one, `M` a bound on `w` of earlier lines.
- `FDeg.frege_to_PIC`: if `FProof p F L`, the empty sequent is in `L`, and every sequent satisfies `DegS p d`
  and `VarS V`, then there is `R : PRefutation F V d p` with `R.S <= |L| * 10 * 2 W`, `W = sum of w`.
- `FDeg.lowdeg_frege_tseitin`: for every `M` there is a cubic graph on `n >= M` vertices such that for every
  charge, every `1 <= rho <= eps ln n` and every `L` with `FProof`, empty sequent, `VarS (tVars G q)` and
  `DegS p ((p-1) rho)`: `exp(n^(1 - (kappa+1) eps)) <= |L| * 10 * 2 (fSize L + |L|)`.
- `FDeg.lowdeg_frege_tseitin_idx`: for all `m >= m0` on `cubFam m` with the explicit charge: the instance is
  unsatisfiable; for `q + 3 <= rho <= eps ln n` the fragment contains a refutation; and for every depth `D`
  every `L` with `FRefutes p D` in the fragment satisfies the bound.
- `FDeg.degS_of_rankS`: a flat sequent with the rank condition `RankS rho` of the previous session satisfies
  `DegS p ((p-1) rho)`. So the new theorem covers the old fragment (with constant 10 in place of `2p + 8`).
- `FDeg.td_mod_le`: a MOD_p gate over members of degree at most `k` has `td <= (p-1) k` in both positions.

How the 18 rules are simulated.
- Clause axiom: the `PIC` axiom. `phi |- phi`: two splittings and one semantic step.
- The four constant axioms: a term that is 1 on the cube, two lines.
- The four MOD_p defining axioms: excluded middle for the value of the MOD gate in the antecedent, the
  splitting of `phi`, one semantic step. Soundness of the step is taken from `fstep_sound`.
- Weakening, `NOT` left and right, `AND` left, `OR` right: one weakening (the translations are nested).
- Cut: for one of the two signs the translation is a single term (`FDeg.tr_single`), and every term of the
  other translation excludes it, so the cut costs (number of terms) + 1 semantic steps.
- `AND` right, `OR` left: merge each premise's translation of the member into its single term, then product
  introduction along the list (`FDeg.reach_gate`, `FDeg.reach_prod`).

What is in the fragment, by example (d = (p-1) rho).
- All of the previous flat fragment.
- `MOD_p` of any fan in over conjunctions of at most `rho` literals, in either position (`Fm.depth` 2).
- A conjunction of at most `rho` MOD_p gates of literals in positive position (`Fm.depth` 2).
- `MOD_p` over `MOD_p` over literals, any fan ins, if `(p-1)^2 <= (p-1) rho` (`Fm.depth` 2), and so on.
- A positive `OR`, or a negative `AND`, of any fan in over any of the above.

## 4. Red team of my own result

- Q0 (what it exploits): PC degree of Tseitin mod q over F_p through Pang's method. The bridge is syntactic.
- Q1 (equal systems): the fragment is defined on the pinned calculus by a decidable syntactic condition. It is
  not closed under cut on a formula of high degree. Whether it is polynomially equivalent to a named system
  is not proved. HAND: it should be polynomially equivalent to resolution over polynomial equations of degree
  O(log n) (Pang's Res(PC_d)) up to the encoding of polynomials as formulas; one direction is LEAN
  (`frege_to_PIC`), the other is not attempted.
- Q2 (short proof control): needs `p` not dividing `q`, inherited. The existence of short refutations of
  Tseitin mod p inside the fragment is not formalized.
- Q3: no circuit is extracted.
- Vacuity: the indexed theorem carries a refutation inside the fragment (at depth one, from the previous
  session's resolution simulation). I did not exhibit a refutation that uses a depth two formula in an
  essential way; the theorem quantifies over all refutations of all depths in the fragment, which is the
  content.
- Strength: Pang's abstract already claims Res(PC_r / F_p) bounds. The content here is that the bound applies
  to proofs written in the pinned sequent calculus with native MOD_p rules at any formula depth, kernel
  checked. A reviewer should read it as "Res(PC_d) with d = O(log n), stated for the pin's syntax".
- Distance to the target: Section 5.

## 5. What blocks constant depth AC0[p]-Frege (the map)

### 5.1 The Frege side is no longer an obstacle

After `frege_to_PIC`, every formula of every depth is one term or is split, and each rule costs polynomially
many `PIC` steps. The only hypothesis is the degree condition. So the target for a family `F_n` would follow
from a `PIC` size bound at the degree that general proofs need. The whole difficulty is now one parameter of
one algebraic statement: the degree `d` tolerated by `PIC.pic_degree_size`.

### 5.2 Where the degree enters

In the chain `pic_degree_size`, `pic_size_exp`, `pic_exp_of_degree` the degree `d` enters polynomially
everywhere except in one place, `Pang.Nn_ratio`: `N(n, K) <= (1 + lam^d) N(n, K - d)`, where `N(n, K)` counts
multilinear monomials of degree at most `K` and `lam` is about `n / K`. The size bound is
`2^(n / (C d (1 + lam^d)))`. With `K <= D / 4` and `D` the PC degree (a small constant fraction of `n` for
Tseitin), `lam` is a constant above 1 and the bound is trivial once `d > log n / log lam`. This is the
`(K/n)^rho` wall of the earlier notes, now with `d` in place of `(p-1) rho`. To tolerate `d = (log n)^C` one
needs `N(n, K - d) / N(n, K)` bounded below, that is `K >= n/2 - O(n/d)`, that is PC degree ratio
`1/2 - o(1)` for a constant width CNF. This is hypothesis H of the earlier notes in its strongest form. For
Tseitin mod 2 the ratio is capped at 1/4 (HAND, r4-phase23-program.md). I add no new attempt to method M1.

### 5.3 What degree would be enough (CITED-CHECKED at abstract level)

Buss, Kolodziejczyk, Zdanowski (Trans. AMS 367 (2015) 7517 to 7563; abstract read today on the first author's
page): constant depth proofs with AND, OR and mod p gates translate, with quasipolynomial blowup, into proofs
with formulas of depth three "in which the top level is Boolean, the middle level consists of mod p gates,
and the bottom level subformulas are small conjunctions"; a depth two version uses refutations from weak
surjective pigeonhole principles. I could not read the body (no PDF text tool in this session), so the exact
line format is NOT checked. Two readings:
- If a line is a sequent of MOD_p gates over conjunctions of polylog many literals (top level Boolean = the
  sequent itself), then every line satisfies `DegS p ((p-1) (log n)^C)`, and R4 for a family would follow from
  a `PIC` bound of super quasipolynomial strength at degree `(log n)^C`, plus a formalization of the collapse.
- If a line may contain a wide conjunction of MOD_p gates in positive position, the degree is unbounded and
  the reduction needs Section 6 as well, or fails.
Deciding between the two readings is a one hour literature task and I recommend it (Section 8).

### 5.4 Sanity check on the upper side (HAND)

At degree `d = n` the calculus `PIC` has polynomial size refutations of Tseitin mod q: a term may be the
indicator of "the charge of the first k vertices is c", and consecutive states are related by a constant
number of semantic steps. So any `PIC` lower bound must fail somewhere between `eps log n` and `n`. This
particular upper bound needs degree linear in the cut size, because MOD_q of m bits has F_p degree
proportional to m. So a bound at degree `n^delta` is not excluded by it. No T4.1 trigger.

## 6. Wide conjunctions in positive position: an extension argued on paper (HAND, not formalized)

Observation. A sequent `Gamma |- Delta, AND(psi_1, ..., psi_w)` is equivalent to the `w` sequents
`Gamma |- Delta, psi_i`. So translate a sequent into a set of `PIC` lines: an `AND` in positive position of
degree above `d` contributes the union of the line sets of its members (one member is chosen per line), an
`OR` in positive position contributes all unions of one choice per member, dually for negative positions,
and a formula of degree at most `d` is treated as in Section 3. The number of lines of a sequent is the size
of its CNF over low degree atoms; call it `B(S)`.

Claim (HAND). Each `FStep` is simulated for every line of the conclusion from the lines of the premises:
- `AND` right for an expanded conjunction costs nothing (the conclusion lines are the premise lines).
- `AND` left, weakening, `NOT`: weakening of each line.
- `phi |- phi`: every line contains a pair from one member and follows from the member's lines by weakening.
- Cut on an expanded `AND(psi_i)`: the negative side is one line containing the negative translations of all
  members; resolve the members one at a time against the `w` positive lines. For nested formulas this is an
  induction on the formula, with cost polynomial in the number of lines of the two premises.
- MOD_p axioms: a member of a MOD gate inside the fragment has degree at most `d`, so nothing is expanded.
Result: a `PIC` refutation of size at most `|L| * poly * max_S B(S)`, hence
`exp(n^(1 - (kappa+1) eps)) <= |L| * poly(size) * max_S B(S)`.

What it would give. Sequents may contain `AND` gates of unbounded fan in in positive position (and `OR` in
negative position), as long as the product of the fan ins of the wide gates in one sequent stays below the
exponential bound. For instance at most `n^(1 - delta) / log n` conjunctions of polynomial fan in per sequent,
for a `delta` above `(kappa+1) eps`. This removes the phrase "no wide conjunction in positive position" from
the description of the fragment and replaces it by "not too many wide conjunctions in one line".

What it would not give. A line that is a DNF with `n` or more wide terms; a wide gate below a MOD_p gate. It
does not combine with random restrictions to give all of depth one: after a restriction the surviving
conjunctions have width `C log S`, there may be `S` of them in a line, and the expansion costs
`(C log S)^S`. So the owner's closure of "beyond log n rank" stands.

I checked the cut case and the nested case on paper only. It is the CNF expansion, with the one point that
the `PIC` bound is exponential and can pay for it. I did not formalize it because it needs a second
translation (lists of lines per sequent) and a second pass over the 18 rules, which did not fit the session.

## 7. Negative results and dead ends

1. I looked for a way to use the fact that positive `OR` and negative `AND` are free. Polarity is semantic
   (`NOT` flips it), so a wide positive conjunction cannot be moved to the free side. Dead.
2. Approximating a wide conjunction by a low degree polynomial with an error set (Razborov and Smolensky) and
   letting the common multiplier vanish on the error set: the multiplier lives in a space of dimension about
   `binom(n, <= K)` and the error set has size about `S 2^(n - l)`, so one needs `l` linear in `n` unless `K`
   is near `n/2`. This is hypothesis H again (Section 5.2). Not a new attempt, same arithmetic as R1.
3. The embedding of `R_rho^p` into `PIC` (making `c1_main` a corollary of `pic_main`) is not formalized. It is
   routine and has no bearing on the Frege statements.
4. The Buss, Kolodziejczyk, Zdanowski normal form is checked at abstract level only (Section 5.3).
5. No new hard family, no upper bound. Nothing computed. No solver or search was run.
6. Housekeeping note: git prints "non-monotonic index" for an AppleDouble sidecar
   `.git/objects/pack/._loose-*.idx` on the external drive. It is noise from the drive, commits succeed; I did
   not delete it.

## 8. Open target and the single best next step

Frontier pin (intentional sorry, `FregeDegFrontier.lean`, namespace `FDegFrontier`): `log2_degree_target`. For
every `c` there is `m0` such that for all `m >= m0` every refutation of the explicit Tseitin instance in the
low degree fragment with degree bound `(log_2 n)^2`, at any depth, has `(8 m^2)^c < fSize L + |L|`. Open. It is
implied by the R4 pin for this family and is the smallest instance of the degree wall.

Best next step (one item): formalize Section 6. Define the line-set translation, redo `step_sim` for it, and
state the Tseitin bound with the factor `max_S B(S)`. It is known mathematics, it fits the existing files
(`reach_map2`, `reach_split`, `reach_gate` are reusable), and it gives the first kernel checked bound for
proofs in the pinned calculus that use conjunctions of unbounded fan in in positive position.

Strategic question that decides whether the degree route can reach R4 at all (not a formalization task): read
the body of Buss, Kolodziejczyk, Zdanowski and settle the two readings of Section 5.3. If the first reading
holds, R4 for a family is equivalent in difficulty to one algebraic statement, the `PIC` degree-size relation
at degree `(log n)^C`, and the only known handle on that is a constant width family with PC degree ratio
`1/2 - o(1)`. I have no idea for such a family (CONJECTURE: none of the standard families has it).

## 9. Session log

- Worktree `SATurday-wt/ac0p-fable`, branch `r4/ac0p-fable`. Files checked one by one with `lean` against the
  primary checkout's build; commits small.
- New files: `PolyIndCalc.lean`, `FregeDegBridge.lean`, `FregeDegFrontier.lean`. Changed: `C1Sim.lean`
  (`claim_step` hypothesis weakened, three call sites), `Theory.lean` (imports),
  `scripts/accepted_declarations.txt` (14 declarations).
- Web: one search and one page fetch for the Buss, Kolodziejczyk, Zdanowski abstract
  (https://mathweb.ucsd.edu/~sbuss/ResearchWeb/TodaAndParityFrege). Everything else cited is from the earlier
  reports and marked there.
- Merge: see the handback message and `git log` for the merge commit. Nothing pushed.
