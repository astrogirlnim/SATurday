# R4 step 2.4: the tree-like degree-size relation (branch r4/treedeg-fable)

Date 2026-11-19. Scope: checklist item 2.4, continuing r4-wideand-fable-report.md, Section 5.2 and
Section 6 (its recommended next step). Task: formalize the tree-like degree-size relation for the
polynomial indicator calculus `PIC`, combine it with the polynomial calculus degree bound for Tseitin,
and state the result for tree-like proofs in the pinned sequent calculus if reachable.
Reads: r4-wideand-fable-report.md, r4-ac0p-fable-report.md and r4-depth2-fable-report.md (bottom lines),
proof standards, stop conditions, `PolyIndCalc.lean`, `FregeDegBridge.lean`, `AC0pFrege.lean`,
`PangAbsorb.lean`, `PangCube.lean`, `C1Sim.lean`, `TseitinIndexed.lean`, `ReviewNonvacuity.lean`.

Labels: LEAN (kernel checked in this session, axioms propext, Classical.choice, Quot.sound),
HAND (argued on paper here, not machine checked), CITED-MEMORY (recalled, not re-verified),
CONJECTURE (my judgment).

## 0. Bottom line

1. No lower bound for AC0[p]-Frege is proved here, tree-like or dag-like, at any depth. R4 is as open
   as before.
2. The HAND argument of Section 5.2 of the previous report is correct and is now LEAN, in the stated
   form: a tree-like `PIC` refutation with `s` nodes and terms of degree at most `d`, of a CNF of
   width at most `w`, gives a polynomial calculus refutation over F_p of degree at most
   `d * clog2(s) + max(w, 3d)` (`PICT.tree_pc_degree_clog`). No change of constants was needed.
3. The same bound is LEAN for tree-like proofs in the pinned sequent calculus (the 18 rules of
   `FStep`, MOD_p gates, formulas of any depth) inside the fragment `DegS p d`
   (`FTree.tree_frege_pc_degree`). This needed a tree-like notion (`FTree.TProof`, Section 3.1) and a
   direct proof per rule, not the dag-like bridge.
4. With `tseitin_bool_degree_Fp_idx`: for primes `p` not dividing `q >= 2` and every `delta > 0` there is
   `m0` such that for all `m >= m0`, `n = 8 m^2`, one-hot Tseitin mod `q` on `cubFam m` with the explicit
   charge is unsatisfiable, and every tree-like refutation with terms of degree `d`,
   `1 <= d <= n^(1 - delta)`, has at least `2^(n^delta / (2624 q))` nodes. For `PIC`:
   `PICT.pic_tree_main_idx`, with a refutation for every `d >= 1`. For the sequent calculus:
   `FTree.frege_tree_main_idx`, with a refutation for every `d >= q + 3`.
5. This is the first kernel checked statement in this line of work beyond the degree wall
   `(p-1) eps ln n` of `pic_main_idx`, `lowdeg_frege_tseitin_idx` and `wide_frege_tseitin_idx`. It is
   for tree-like refutations only. It is known mathematics (the tree-like size-width argument of
   Ben-Sasson and Wigderson with degree in place of width, CITED-MEMORY). No novelty is claimed.
6. The dag-like Frontier pin `FDegFrontier.log2_degree_target` is untouched and open. No new pin.

## 1. What I did, in order

- Read the reports and the Lean files. Fixed the measure: for a line `L`, `Ref Phi L D` says that
  degree `D` polynomial calculus refutes the clauses of `Phi` together with `g = 0` for every term
  `g` of `L` (`PICT.Ref`, with the existing `Pang.CD` and `cnfAx`).
- Wrote `PICTree.lean` (tree-like `PIC`): three general lemmas on `C_D`, the rule lemmas, the tree
  induction, the tree into dag embedding, non vacuity, Tseitin in natural number and real form.
- Wrote `FregeTree.lean` (tree-like sequent calculus): splitting and validity lemmas in polynomial
  calculus, the cut and the gate lemma, the step lemma for the 18 rules, the tree induction, tree
  into dag, non vacuity from resolution, Tseitin.
- Every file was checked with the toolchain `lean` against the build of the primary checkout before
  each commit, and `#print axioms` was run on the main theorems. The gate ran on the staged merge.
- Did not restart the closed directions. Nothing computed, no solver run, no web access.

## 2. Tree-like `PIC` (LEAN)

File `theory/Theory/ProofComplexity/PICTree.lean`, namespace `PICT`.

### 2.1 Definitions

- `PICT.TDer Phi V d L s`: tree-like derivation of the line `L` with `s` nodes. Three constructors
  (leaf, one premise, two premises), each carrying an instance of the existing rule relation
  `PIC.PInfer` and the condition that all terms of the line are indicators of degree at most `d`
  over `V`. So the rules are exactly those of `PIC`.
- `PICT.Ref Phi L D`: `1` is in `C_D` of `cnfAx Phi` together with the terms of `L`.

### 2.2 Lemmas on `C_D`

- `PICT.cd_mono`: monotone in axioms and degree.
- `PICT.cd_subst`: axioms may be replaced by derived polynomials, no degree increase.
- `PICT.cd_deduct` (deduction): if `f` is derived in degree `D` from `Ax` and one more axiom `h`
  that is 0/1 valued on the cube with degree at most `d`, then `(1 - h) f` is derived from `Ax` in
  degree `D + d`.

### 2.3 Rules

- `PICT.ref_init`: the line of a clause `C` of `Phi` is refuted in degree `|C|`.
- `PICT.ref_taut`: excluded middle, degree `d`.
- `PICT.ref_of_derive`: if all terms of `L1` are derived below `L'`, a refutation below `L1` gives
  one below `L'` (weakening is the trivial case).
- `PICT.ref_sem1`: one premise semantic rule, degree `max(D1, 2d)`.
- `PICT.ref_sem2`: two premise semantic rule, deduction on the first premise:
  degree `max(D1 + d, D2, 3d)`. The identity used is
  `g2 = g2 (1 - g1) + g1 g2 (1 - g3) + g1 g2 g3`.

### 2.4 Main statements

- `PICT.tder_ref`: a tree with at most `2^k` nodes below `L` gives `Ref Phi L (d k + c)` for every
  `c >= max(w, 3d)`. Induction on the tree; at a two premise node the deduction is done on the
  smaller subtree, which has at most `2^(k-1)` nodes.
- `PICT.tree_pc_degree`, `PICT.tree_pc_degree_clog`: the degree bound for refutations.
- `PICT.tree_size_of_degree`: if degree `D0` does not refute `Phi` then
  `2^((D0 - max(w, 3d)) / d) <= s`.
- `PICT.tder_to_prefutation`: a tree-like refutation with `s` nodes is a `PIC.PRefutation` (the
  dag-like object of `PolyIndCalc.lean`) with at most `s` nodes. `PICT.TDer.unsat`: soundness.
- `PICT.tder_of_unsat`: every unsatisfiable CNF over `V` has a tree-like refutation for every
  `d >= 1` (from completeness of resolution, existence only).
- `PICT.pic_tree_tseitin_idx`: for `m >= tseitinFloor p q`, every charge, every `d >= 1`:
  `2^((D0 - max(q+3, 3d)) / d) <= s`, `D0 = (((n-2)/1312 - q(q+3)) / (q-1))`, `n = 8 m^2`.
- `PICT.tree_exp_arith`: the arithmetic. `m0` is the maximum of `1312 q (q^2 + 4q + 2)` and the
  ceiling of `(2624 q (q+7))^(1/delta)`; then `D0 >= n / (1312 q)` (`PICT.D0_ge`) and the exponent
  is at least `n^delta / (2624 q)` for `d <= n^(1 - delta)`.
- `PICT.pic_tree_main_idx`: the statement of item 4 above.

## 3. Tree-like sequent calculus (LEAN)

File `theory/Theory/ProofComplexity/FregeTree.lean`, namespace `FTree`.

### 3.1 The tree-like notion

`FTree.TProof p F P S s` has one constructor: the sequent `S` follows by the pinned step relation
`FStep p F prev S` from the sequents of a list `prev`, every member `T` of `prev` has its own subtree
with `sz T` nodes, `P S` holds, and `s` is one plus the sum of `sz` over the list. `P` is the
fragment. So the rules are literally the 18 rules of `FProof`; only the reuse of derived sequents
is removed.

- `FTree.tproof_to_fproof`: a tree-like derivation with `s` nodes gives a list `L` with
  `FProof p F L`, containing `S`, with at most `s` lines, all lines in `P`. So a lower bound for
  `FProof` in a fragment implies the one for `TProof`, and `TProof` is not a new proof system.
- `FTree.TProof.unsat`, `FTree.TProof.mono` (the fragment may be enlarged).
- Not proved: the converse (an `FProof` in which every line is used at most once yields a `TProof`
  of the same size). I see no obstacle, it was not needed.
- Size is the number of sequents (nodes), not the number of symbols. A lower bound on nodes is the
  stronger statement.

### 3.2 Why not through the bridge

`FDeg.frege_to_PIC` simulates a cut by using one premise once per term of the cut formula, and the
`AND` right rule has one premise per member. A tree would be unfolded with a multiplicative blow up.
Instead the measure `Ref F (trS p S) D` is bounded at every node directly (`FTree.step_ref`), for a
pivot premise `Ts`: all premises in degree `D'`, all premises except the pivot in degree `D0`,
`D0 + d <= D'`, `3d <= D'`, `w <= D'`. The 18 rules fall into five groups.

- Clause axiom: `ref_init`, degree `w`.
- The nine other premise free rules (identity, the constants, the four MOD_p axioms): the sequent is
  valid, has at most three formulas and each has `pd <= d`. `FTree.split_cd` derives the single
  term `sg s (val phi)` from the terms of the translation in degree `pd phi` (induction on the
  formula), and `FTree.valid_ref` closes with the product of the complements, which vanishes on the
  cube. Degree `3d`.
- Weakening, the two negation rules, `AND` left, `OR` right: the translation of the premise is a
  subset of the translation of the conclusion.
- Cut on `phi`: `pd phi <= d` because `phi` occurs with both signs. `FTree.cut_core`: deduction on
  the premise that is not the pivot, with the indicator `sg s (val phi)`; the terms of the other
  premise exclude it. Degree `max(D0 + d, D', 3d)`.
- `AND` right and `OR` left (any number of premises): the gate is one product term `u` of degree
  at most `d` in the conclusion. `FTree.gate_core`: for every member except the pivot member,
  deduction gives `1 - x_psi`; `FTree.gate_absorb` then gives `y (1 - u)` for every term `y` of the
  pivot premise (or for `y = 1` if no premise is the pivot), by a telescoping product in which the
  pivot factor is removed on the cube.

`FTree.tproof_ref` is the induction: the pivot is a premise with the largest subtree
(`FTree.exists_pivot`); every other premise has at most half of the nodes.

### 3.3 Main statements

- `FTree.tree_frege_pc_degree`: tree-like refutation, at most `2^k` nodes, all sequents in
  `DegS p d`, CNF of width at most `w`: polynomial calculus refutation of degree
  `d k + max(w, 3d)`. No condition on the variables of the proof (`VarS` is not needed) and none on
  the depth.
- `FTree.tree_frege_size_of_degree`.
- `FTree.tproof_of_unsat`: an unsatisfiable CNF has a tree-like refutation inside `DegS p d` for
  every `d >= 1` that is at least the clause width. A clause is represented by a sequent of
  variables (negated variables on the left); resolution is one cut; the clause axiom is unpacked by
  `OR` left and a cut on the clause formula, and this cut is the reason for `d >= width`.
- `FTree.frege_tree_tseitin_idx`, `FTree.frege_tree_main_idx`: the statement of item 4.

## 4. Red team of my own result

- It is a corollary of the polynomial calculus degree bound already in the repo plus a standard
  tree-like argument. Nothing new mathematically.
- Tree-like here is a real restriction. For Frege systems of constant depth, tree-like and dag-like
  proofs simulate each other with one more level of depth (Krajicek, CITED-MEMORY), but that
  simulation carries conjunctions of earlier lines, which are wide conjunctions and leave `DegS`.
  So the theorem says nothing about dag-like proofs in `DegS`, and nothing about tree-like proofs
  outside `DegS`. CONJECTURE: tree-like `DegS` at polylog degree is strictly weaker than dag-like
  `DegS` at the same degree; the table of Buss, Kolodziejczyk, Zdanowski places them at different
  levels (previous report, Section 4.4).
- The fragment is the same syntactic `DegS` as before: a positive `OR` and a negative `AND` are
  split, MOD_p gates have any fan in, everything else adds degrees. A wide conjunction in positive
  position is not covered (the expansion of `FregeWideAnd.lean` is not combined with trees here).
- Non vacuity for the sequent calculus starts at `d >= q + 3`. For `1 <= d < q + 3` the bound of
  `frege_tree_main_idx` is true but I do not exhibit a refutation, so it is stated separately from
  the existence clause. For `PIC` existence holds for every `d >= 1`.
- The witness refutations come from resolution and have no size control. I did not prove an upper
  bound that matches `2^(n^delta / (2624 q))`.
- The bound is in nodes and degenerates for `d` above `n^(1 - delta)`; for `d` of order `n` it
  gives nothing, as it must (degree `n` polynomial calculus refutes everything).
- `m0` depends on `delta` through `(2624 q (q+7))^(1/delta)` and on `tseitinFloor p q`. It is not a
  small number.

## 5. What failed or was dropped

1. Nothing in the plan failed. The first design for the sequent calculus (unfold the dag-like
   bridge) was dropped on paper for the reason in 3.2 before any Lean was written.
2. Not attempted: wide conjunctions (the `XDegS` fragment) in trees; the converse of
   `tproof_to_fproof`; an upper bound; hypothesis sequents other than clauses (Section 6).
3. Practical: `lean -o` needs the input file below the working directory, and an olean placed under
   a second `Theory` directory on `LEAN_PATH` shadows the primary build. I kept scratch oleans under
   another root name in the scratchpad.

## 6. The map, and the single best next step

Where this sits (previous report, Sections 4 and 5). In the table of Buss, Kolodziejczyk and
Zdanowski, tree-like `PCK^0_p` is at the level of polylog degree polynomial calculus. The theorem
here is the repo's version of the easy direction of that equivalence, for the pinned rules: tree-like
`DegS` refutations give low degree polynomial calculus refutations. Their Theorem 45 reduces constant
depth proofs to tree-like `PCK^0_p` refutations from the clauses together with extra cedents that
express a weak surjective pigeonhole principle. Clauses of `F` are the only hypotheses of `FStep`, so
the extra cedents are not covered by the statement here unless they are narrow clauses.

Best next step (one item): the relative version. Allow a set `H` of hypothesis sequents as leaves
of `TProof`, each with at most `k` translated terms of degree at most `d`, and prove that a
tree-like refutation with `s` nodes gives a polynomial calculus refutation, of degree
`d log2 s + max(w, k d, 3d)`, of `cnfAx F` together with the polynomials `prod (1 - g)` over the
terms `g` of each hypothesis. HAND: only a new leaf case is needed, by the telescoping of
`FTree.one_sub_prod_list`. Then the distance from the tree-like theorem to R4 for a family is one
explicit statement: a polynomial calculus degree lower bound for Tseitin together with those
pigeonhole polynomials. That statement can then be pinned in a Frontier namespace with the right
shape, and compared with what the paper proves (functions in `PV_1` without parity queries, by a
switching lemma). I did not pin it now because the hypothesis family is not defined in the repo.

Not recommended: more constants or more fragments of the dag-like bound; the open dag-like pin needs
a new idea, not more formalization.

## 7. Session log

- Worktree `SATurday-wt/treedeg-fable`, branch `r4/treedeg-fable`. New files `PICTree.lean` and
  `FregeTree.lean`. Changed: `Theory.lean` (two imports), `scripts/accepted_declarations.txt` (new
  block), `docs/ladder/r4-completion-checklist.md` (one paragraph under 2.4). No existing theorem
  file was edited.
- No web access. Nothing pushed.
- Merge: see the handback message and `git log` for the merge commit.
