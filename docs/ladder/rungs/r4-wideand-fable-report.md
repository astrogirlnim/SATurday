# R4 step 2.4: wide conjunctions and the depth 3 normal form (branch r4/wideand-fable)

Date 2026-11-19. Scope: checklist item 2.4, constant depth AC0[p]-Frege, continuing
r4-ac0p-fable-report.md. Two tasks: (1) formalize Section 6 of that report (expansion of wide
conjunctions in positive position), (2) settle the line format of the Buss, Kolodziejczyk, Zdanowski
normal form.
Reads: r4-ac0p-fable-report.md, r4-depth2-fable-report.md (bottom line and section list), proof standards,
stop conditions, `PolyIndCalc.lean`, `FregeDegBridge.lean`, `FregeDegFrontier.lean`, `AC0pFrege.lean`, and the
body of the Buss, Kolodziejczyk, Zdanowski paper (Sections 1, 2.1, 5, 6; text extracted from the PDF).

Labels: LEAN (kernel checked in this session, standard axioms only), HAND (argued on paper here, not machine
checked), CITED-READ (I read the passage in the paper today), CITED-MEMORY (recalled, not re-verified),
CONJECTURE (my judgment).

## 0. Bottom line

1. No lower bound for AC0[p]-Frege is proved here, at any depth. The open problem is as open as before.
2. Task 1 is done and kernel checked (`FregeWideAnd.lean`, namespace `FWide`), with one change against the
   target statement: the factor is `B^2`, not `B`. A refutation in the pinned sequent calculus `FProof`, of
   any formula depth, in which a positive `AND` (negative `OR`) of degree above `d` is expanded into its
   members, every remaining term has degree at most `d`, and every sequent expands into at most `B` lines,
   is simulated in `PIC` with at most `|L| * 12 * 2W * B^2` lines (`FWide.wide_frege_to_PIC`). Hence on the
   explicit family `cubFam m`, all `m >= m0`, `d = (p-1) rho`, `q + 3 <= rho <= eps ln n`:
   `exp(n^(1 - (kappa+1) eps)) <= |L| * 24 (fSize L + |L|) * B^2` (`FWide.wide_frege_tseitin_idx`), with
   unsatisfiability and non vacuity. The square comes from cut: its cost is the product of the numbers of
   lines of its two premises (Section 2.4). I do not know how to get `B` and I do not think it matters.
3. Task 2 is settled by reading the paper (Section 4). Both readings of the previous report occur, for two
   different theorems:
   - Their depth 3 normal form (Theorem 43, system `PCK^1_p`, dag like, no extra axioms): a line may contain
     any number of conjunctions of unbounded fan in over MOD_p gates. Such lines are NOT inside `DegS` at
     polylog degree. They are inside the expanded fragment `XDegS` of this session, but with `B` unbounded.
   - Their depth 2 form (Theorem 45, system `PCK^0_p`, tree like, with extra axioms from a weak surjective
     pigeonhole principle): every formula is a literal, a small conjunction or disjunction of literals, or one
     MOD_p gate over small conjunctions. These lines ARE inside `DegS` at polylog degree.
4. Consequence for the plan (Section 5). The paper's own table puts dag like `PCK^0_p` (which is the format
   of `DegS`, so of the Frontier pin `FDegFrontier.log2_degree_target`) at the level of the theory
   `T^2_2` with parity, above the levels for which the authors knew lower bounds in 2015. And it puts tree
   like `PCK^0_p` at the level of polylog degree polynomial calculus. So for tree like refutations the degree
   wall of `PIC` should not exist (HAND, Section 5.2). This is the recommended next formalization.

## 1. What I did, in order

- Read the reports and the Lean files. Designed the expansion so that it reuses `step_sim` instead of
  redoing the 18 rules: a sequent is expanded into a list of sequents of the old fragment ("selections").
- Wrote `FregeWideAnd.lean` in three parts (definitions, identity and cut, step simulation and bounds). Each
  part was checked with `lean` against the build of the primary checkout before the commit.
- Downloaded the paper from the first author's page and extracted the text with PyMuPDF (`fitz`), which is
  installed in the local Python. Read the definitions and the theorems that matter.
- Did not restart the closed directions (rank beyond log n by restrictions, the d1 small graph search, the
  three methods that failed on 2026-10-27). Nothing computed, no solver run.

## 2. The expansion (LEAN)

File `theory/Theory/ProofComplexity/FregeWideAnd.lean`, namespace `FWide`. Axioms propext,
Classical.choice, Quot.sound.

### 2.1 Definitions

- `sels p d s phi`: the list of selections of `phi` with sign `s` at threshold `d`.
  Variable and MOD gate: the formula itself. `NOT`: selections of the member with the other sign.
  `AND` with sign true: the formula itself if `pd <= d`, otherwise all selections of all members (one line
  per member). `AND` with sign false: one selection per member, all combinations (`List.sections`).
  `OR` is dual.
- `xtd p d s phi`: the largest syntactic degree of a term of a selection (a recursive function, like `td`).
- `selsS p d S`: selections of a sequent (antecedent with sign false, succedent with sign true).
  `BS p d S`: their number. `XDegS p d S`: `xtd <= d` for every formula with its sign.
  `XDegS` is a syntactic, decidable condition.

A selection is an ordinary sequent. The `PIC` lines of `S` are `trS p S'` for `S'` in `selsS p d S`, with
`trS` the one line translation of `FregeDegBridge.lean`. This is the CNF of the sequent over atoms of degree
at most `d`.

### 2.2 Basic facts

- `FWide.sels_self`: a formula with `pd <= d` is its only selection. `FWide.sels_of_td`: the same if
  `td p s phi <= d`.
- `FWide.sels_props`: a selection has `td <= xtd`, variables among those of `phi`, size at most that of `phi`.
- `FWide.sels_pos`: every formula has a selection. `FWide.BS_eq`: `BS` is the product over the formulas of
  the sequent of their numbers of selections.
- `FWide.sel_seq_props`: a selection of a sequent in `XDegS` lies in `DegS`, with no larger weight.
- `FWide.xtd_le_td`, `FWide.xdegS_of_degS`, `FWide.BS_of_degS`: the old fragment `DegS` is contained in the
  new one, with `B = 1`. So `wide_frege_tseitin_idx` implies `FDeg.lowdeg_frege_tseitin_idx` up to the
  constant.
- `FWide.xtd_and_true_le`: a positive `AND` of any fan in over members of the fragment is in the fragment.
- `FWide.wide_and_example`: the sequent `|- AND(x_1, ..., x_w)`, `w > d >= 1`, is in `XDegS`, has `BS = w`,
  and is not in `DegS`. So the new fragment is strictly larger.

### 2.3 The simulation

- `FWide.sel_fstep`: if `S` follows from `prev` by a rule and `S'` is a selection of `S`, then either the
  rule is the axiom `phi |- phi`, or it is cut, or `S'` follows by a rule of the same calculus from the
  selections of the sequents of `prev`. In words: selections commute with 16 of the 18 rules. For `AND` right
  on an expanded conjunction the selection of the conclusion is a selection of one premise (weakening by
  nothing). For the MOD_p axioms the member formula has degree at most `d`, so nothing is expanded.
- `FWide.reach_id`: the axiom `phi |- phi`. For selections `phi1`, `phi2` of `phi` with opposite signs the
  line containing both translations is derived with at most `10 |phi|` lines, by induction on `phi` (at an
  expanded gate, follow the member that `phi2` was selected from).
- `FWide.reach_xcut`: cut on an expanded formula. Given, for every selection of `phi` with either sign, a
  line contained in `Y` plus the translation of that selection, a line contained in `Y` is derived with at
  most `2 |phi| * b_true(phi) * b_false(phi)` lines, `b_s` the number of selections with sign `s`. Induction
  on `phi`; at an expanded gate the members are resolved one at a time (`FWide.cut_list`), at a formula of
  degree at most `d` it is the old cut (`reach_map2`).
- `FWide.xstep_sim`: all selections of the conclusion of one step, with at most `12 (w(S) + M) B^2` new
  lines. The 16 rules go through `FDeg.step_sim` applied to the selection.
- `FWide.wide_frege_to_PIC`: the bridge, `R.S <= |L| * 12 * (W + W) * B^2`, `W` the total weight.
- `FWide.wide_frege_tseitin`: for every `M` a cubic graph on `n >= M` vertices, every charge, every
  `1 <= rho <= eps ln n`, every `L` with `FProof`, the empty sequent, `VarS`, `XDegS p ((p-1) rho)` and
  `BS <= B` for all sequents: `exp(n^(1 - (kappa+1) eps)) <= |L| * 24 (fSize L + |L|) * B^2`.
- `FWide.wide_frege_tseitin_idx`: the same for all `m >= m0` on `cubFam m` with the explicit charge; the
  instance is unsatisfiable; for `q + 3 <= rho <= eps ln n` the fragment contains a refutation (the depth one
  refutation of the earlier sessions, with `B = 1`); the bound holds for every depth `D` and every `B`.

### 2.4 Why `B^2` and not `B`

A cut with conclusion `Gamma |- Delta` has premises with `b * b_true(phi)` and `b * b_false(phi)` lines,
`b = BS(Gamma |- Delta)`. Each of the `b` conclusion lines costs `2 |phi| b_true b_false`, in total
`2 |phi| * (b b_true) * b_false <= 2 |phi| B^2`. The cross term is real for the derivation I use: for
`phi = AND(psi_1, psi_2)` the negative side has `n_1 n_2` lines and the derivation repeats the cut on `psi_2`
once for every negative selection of `psi_1`. In the lower bound the square only replaces `log B` by
`2 log B`. The statement is: the expansion is affordable when `2 ln B` stays below `n^(1 - (kappa+1) eps)`.

### 2.5 Red team of my own result

- It is the CNF expansion. Known mathematics, no new idea, no novelty claim. Mathematically still a
  corollary of Pang's degree-size method.
- The fragment is defined on the pinned calculus by a decidable syntactic condition plus the numeric
  parameter `B`. It is not closed under cut in general and is not shown equivalent to a named system.
- Non vacuity: the indexed theorem carries a refutation in the fragment, but that refutation has `B = 1` and
  is the old depth one object. I did not exhibit a refutation of Tseitin that uses a wide conjunction in an
  essential way. `wide_and_example` only shows that the fragment contains sequents outside `DegS`.
- What it does not give is unchanged from Section 6 of the previous report: a line with many wide
  conjunctions (a DNF with `n` wide terms in positive position has `B` exponential in `n`), and anything
  wide below a MOD_p gate. It does not combine with restrictions.
- The wall is where it was: degree at most `(p-1) eps ln n` for every term.

## 3. What failed or was dropped

1. The target with factor `B` (linear). Not reached, see 2.4. Not attempted further.
2. A non vacuity witness with `B > 1` for Tseitin. Not attempted.
3. `lake env lean` took 20 minutes of wall clock for one file on the external drive (4 seconds of CPU; lake
   checks every package repository first). I called the toolchain's `lean` binary with `LEAN_PATH` set by
   hand instead (about one to three minutes per check). No `lake update`, no Mathlib change.

## 4. The Buss, Kolodziejczyk, Zdanowski normal form (CITED-READ)

Source: S. Buss, L. Kolodziejczyk, K. Zdanowski, "Collapsing modular counting in bounded arithmetic and
constant depth propositional proofs", Trans. AMS (preprint from the first author's page,
https://mathweb.ucsd.edu/~sbuss/ResearchWeb/TodaAndParityFrege/modcounting-ams.pdf, 46 pages). I read
Section 1, Section 2.1 (Definitions 1, 2, 4, 11, 12, 13), Section 5 (Theorems 42, 43, 45 and the proof of
45) and Section 6 up to the proof of Theorem 46. I did not read Sections 2.2 to 4 (the arithmetic and the
Paris-Wilkie translations), so I rely on the theorem statements and not on their proofs.

### 4.1 What the paper defines

- `PK+p` (their Definition 1): a Tait style calculus. A line is a cedent, a set of formulas read as a
  disjunction. Formulas are built from literals with unbounded fan in AND, OR, and connectives "count is `k`
  mod p" and their complements. Rules: weakening, cut, AND, OR, five kinds of initial cedents for the
  counting connectives.
- A `+p^-` formula: one counting connective (or its complement) applied to conjunctions of literals.
  `Sigma_0 = Pi_0` are the `+p^-` formulas; `Pi_{i+1}` is a `Sigma_i` formula or an AND of `Sigma_i`
  formulas; `Sigma_{i+1}` dually.
- `PCK^i_p` (Definition 2): the subsystem in which every formula of every cedent is a literal, a conjunction
  or disjunction of literals, or a `Pi_i` or `Sigma_i` formula of the above kind.
- Sigma-size `S` (Definition 4): size at most `S` and every conjunction or disjunction of literals that
  occurs as a subformula has at most `log S` literals.
- There is a polynomial variant `PCK^i_Fp` (Definitions 11 to 13) whose atoms are multilinear polynomials
  over F_p, with Sigma-size `S` meaning size at most `S` and degree below `log S`.

### 4.2 The collapse theorems

- Theorem 42: a `Sigma_j(+p^-)` formula of Sigma-size `S` with a depth `d` proof in `PK+p` of size `S` has a
  `PCK^j_p` proof of Sigma-size `S^(log^e S)`, `e` depending on `d`.
- Theorem 43 (the depth 3 normal form of the abstract): if the formula is an OR of ANDs of `Sigma_1`
  formulas (a CNF is of this form, a literal being a counting gate over one conjunction of one literal),
  the corresponding set of cedents has a `PCK^1_p` refutation of Sigma-size `S^(log^e S)`. Dag like, no
  extra axioms.
- Theorem 45 (the depth 2 form): for an OR of ANDs of `+p^-` formulas there is a tree like `PCK^0_p`
  refutation, of Sigma-size `S^(log^e S)`, of the cedents together with cedents `f(u) != c`, `u < t`, where
  `f` is a function of the class `PV_2` relativized to parity P (it depends on `d`, the formula and the
  proof), and `c` is given by new variables. These express an instance of the weak surjective pigeonhole
  principle.

### 4.3 The line format, against `DegS`

With Sigma-size `S' = S^(log^e S)` the bottom conjunctions have at most `log S' = log^(e+1) S` literals.
Translate a cedent as a sequent with empty antecedent. Then:

- literal, small conjunction, small disjunction of literals: degree at most `log^(e+1) S`.
- a counting gate over small conjunctions, or its complement: degree at most `(p-1) log^(e+1) S`
  (`FDeg.td_mod_le`).
- a `Sigma_1` formula (OR of counting gates) in a cedent: the positive OR is split, degree as above.
- a `Pi_1` formula (AND of counting gates, unbounded fan in) in a cedent: a positive AND of degree
  (fan in) times `(p-1) log^(e+1) S`. Not in `DegS` unless the fan in is small.

So:

- `PCK^0_p` lines (Theorem 45) are inside `DegS` at degree `(p-1) log^(e+1) S`. First reading of the
  previous report, but only for the tree like system with the extra pigeonhole cedents.
- `PCK^1_p` lines (Theorem 43) are not inside `DegS`. They are inside `XDegS` at the same degree, with
  `BS` equal to the product of the fan ins of the `Pi_1` formulas of the cedent. The number of such formulas
  per cedent is not bounded in the paper, so `B` is not controlled. Second reading of the previous report.

What I did not check: that their rules and counting axioms translate into the 18 rules of the pin (they
have complement connectives and multiset arguments; the pin has `NOT` and four MOD_p axioms). Only the line
format is settled. A formal reduction would also need the collapse itself, which is a bounded arithmetic
argument and far outside this repo.

### 4.4 The table of the paper (their Section 6)

The paper lists what remains of the hierarchy after the collapse, each theory with its proof system:
`PV_1` with parity: polylog degree Nullstellensatz. `T^1_2` with parity: polylog degree polynomial calculus,
and tree like `PCK^0_p`. `APC_1` with parity: polylog degree Nullstellensatz plus the weak pigeonhole
axioms for `PV_1`. `T^2_2` with parity: tree like `PCK^1_p`, and dag like `PCK^0_p`. `APC_2` with parity
(which equals all of `T_2` with parity): tree like `PCK^0_p` plus the weak pigeonhole axioms for `PV_2`.
The best independence results they state (Theorem 46) are for `T^1_2` with parity and for `PV_1` with
parity plus the weak pigeonhole principle for `PV_1` functions that make no parity queries.

## 5. What this means for R4 (the map, updated)

### 5.1 Where the repo's theorems sit

- `FDeg.lowdeg_frege_tseitin_idx` is a bound for dag like proofs with lines in the `PCK^0_p` format, at
  bottom fan in `eps ln n` instead of polylog, any size. In the paper's table dag like `PCK^0_p` with polylog
  fan in is the level of `T^2_2` with parity, for which the paper states no lower bound. So the Frontier pin
  `FDegFrontier.log2_degree_target` (degree `(log_2 n)^2`) is, up to the syntax of the rules, the first open
  level of that table. CONJECTURE: it is a recognized open problem and not a formalization gap. (Pang's
  2026 result is the `eps ln n` case; I have not re-read it today, CITED-MEMORY.)
- `FWide.wide_frege_tseitin_idx` reaches into `PCK^1_p`: lines with a few `Pi_1` formulas. A full bound for
  dag like `PCK^1_p` at Sigma-size beyond quasipolynomial would give R4 for the family through Theorem 43
  (HAND, modulo 4.3). That needs unbounded `B` and polylog degree. Both are walls.

### 5.2 Tree like refutations should have no degree wall (HAND)

The table equates tree like `PCK^0_p` with polylog degree polynomial calculus. The direct reason, in the
terms of this repo: for a tree like `PIC` refutation with terms of degree at most `d`, let `D(v)` be the
least degree of a polynomial calculus refutation of the CNF together with "every term of the line at `v` is
zero". At a semantic step with premises `L_1` (smaller subtree) and `L_2`: multiply the refutation below
`L_1` by `1 - g_1` to derive `1 - g_1` in degree `D_1 + d`; since `g_1 g_2 (1 - g_3)` vanishes on the cube,
derive `g_2 = g_2 (1 - g_1) + g_1 g_2` in degree `max(D_1 + d, 3d)`; then use the refutation below `L_2`.
So `D(v) <= max(D_small + d, D_big, 3d)`, hence `D(root) <= d log_2 S + max(w, 3d)` for tree size `S`. With
polynomial calculus degree `c n` for Tseitin (in the repo: `tseitin_bool_degree_Fp_idx`) this gives
`S >= 2^((c n - w - 3d) / d)`: exponential for every `d` up to `n^(1 - delta)`. This is the tree like
size-width argument of Ben-Sasson and Wigderson with degree in place of width (CITED-MEMORY for the
original). I checked the three steps on paper only. If right, it is the first statement in this line of
work that passes the `eps ln n` degree wall, for tree like proofs.

What it would and would not give. It would give a kernel checked exponential bound for tree like
refutations in the `DegS` format at polylog (indeed polynomial) degree. With Theorem 45 the remaining
distance to R4 for a family would be exactly: a polynomial calculus degree bound that survives the weak
pigeonhole cedents `f(u) != c` for functions `f` in `PV_2` with parity. The paper proves such a survival
only for `PV_1` functions without parity queries and for the pigeonhole principle, with a switching lemma.
So this does not make R4 easier. It names the open statement in the form the literature has it.

Two cautions. (a) The pinned calculus has no tree like notion; `FProof` is a list. A tree like statement
needs a definition (for example a tree of sequents with the same 18 rules). (b) The bridge `frege_to_PIC`
reuses lines (the cut uses one premise once per term), so the tree like statement should be proved for
sequent trees directly through `D(v)`, not through the dag like bridge.

## 6. Open targets and the single best next step

No new Frontier pin in this session. The open pin of the previous session stands:
`FDegFrontier.log2_degree_target`.

Best next step (one item): formalize Section 5.2. Define tree like derivations for `PIC` (or directly for
the sequent calculus restricted to `DegS`), prove `D(root) <= d log_2 S + max(w, 3d)` with the existing
polynomial calculus layer (`CD`, `cnfAx`), and state the Tseitin bound for tree like refutations at degree
up to `n^(1 - delta)` on `cubFam m`. It is known mathematics, it uses only the degree bound already in the
repo, and it is the first kernel checked bound past the `eps ln n` wall, at the level the paper's table calls
`T^1_2` with parity. After it, the honest statement of the distance to R4 is the one in 5.2.

Not recommended: formalizing the collapse of Section 4 (bounded arithmetic, far outside the repo), and
pushing `B` (the many wide conjunctions case is the rank wall again).

## 7. Session log

- Worktree `SATurday-wt/wideand-fable`, branch `r4/wideand-fable`. New file `FregeWideAnd.lean` (1370 lines). Changed: `Theory.lean` (one import), `scripts/accepted_declarations.txt` (new block).
  No existing theorem file was edited.
- Web: one page fetch and one PDF download from mathweb.ucsd.edu (the paper above). Nothing else.
- Merge: see the handback message and `git log` for the merge commit. Nothing pushed.
