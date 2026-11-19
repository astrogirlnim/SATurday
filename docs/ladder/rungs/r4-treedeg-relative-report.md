# R4 step 2.4: the relative tree-like degree-size relation (branch r4/treedeg-relative)

Date 2026-11-19. Scope: checklist item 2.4, the "single best next step" of
`r4-treedeg-fable-report.md` (Section 6): allow hypothesis sequents as leaves of tree-like proofs and
carry them through the degree-size relation.
Reads: `r4-treedeg-fable-report.md`, `PICTree.lean`, `FregeTree.lean`, `AC0pFrege.lean` (soundness),
`FregeDegBridge.lean` (`trS`, `DegS`).

Labels: LEAN (kernel checked in this session, axioms propext, Classical.choice, Quot.sound),
HAND (argued on paper, not machine checked), CITED-MEMORY (recalled, not re-verified),
CONJECTURE (my judgment).

## 0. Bottom line

1. No lower bound for AC0[p]-Frege is proved here, tree-like or dag-like. R4 is as open as before.
2. LEAN: the measure of the tree-like files is now relative to an arbitrary base axiom set
   (`PICT.RefA A L D`: `1` is in `C_D` of `A` together with the terms of `L`); `PICT.Ref Φ` is the
   case `A = cnfAx Φ`, by definition. Every previous theorem keeps its name and statement; the rule
   lemmas are restated as one-line corollaries of their relative forms.
3. LEAN: tree-like proofs in the pinned sequent calculus with hypothesis leaves
   (`FTree.TProofH p F H P S s`). A tree-like refutation of `F` plus `H` with at most `2^K` nodes,
   all sequents in `DegS p d`, `F` of width at most `w`, every hypothesis with at most `k` translated
   terms, gives a polynomial calculus refutation over F_p of `cnfAx F` together with the polynomials
   `∏_{g ∈ trS S} (1 - g)` for `S ∈ H`, of degree `d K + max(w, max(k d, 3 d))`
   (`FTree.tree_frege_pc_degree_hyp`, with `clog` and size-from-degree forms).
4. Not done: the Frontier pin for Tseitin plus Buss–Kolodziejczyk–Zdanowski style weak pigeonhole
   hypotheses. The hypothesis family was not defined (Section 4).
5. Known mathematics (the tree-like size-width argument of Ben-Sasson and Wigderson with degree in
   place of width, relativized to extra axioms, CITED-MEMORY). No novelty is claimed.

## 1. What I did

- Read the previous report and both Lean files. Planned on paper: only the leaf case is new; the
  step lemma only needs the clause axiom case to know that `clausePoly C` is a base axiom.
- `PICTree.lean`: introduced `RefA`, rewrote `Ref` as `RefA (cnfAx Φ)`, and generalized the measure
  lemmas to `RefA`. Kept the old names as corollaries.
- `FregeTree.lean`: generalized the core lemmas to `RefA` with a base `A ⊇ cnfAx F`, kept the old
  names as corollaries, added the hypothesis section.
- Checked both files with the toolchain `lean` against the primary build (scratch oleans for the
  two changed modules), then the gate on the merge.
- Nothing computed, no solver run, no web access.

## 2. Relative measure in `PICTree.lean` (LEAN)

- `PICT.RefA`, `PICT.Ref` (now `RefA (cnfAx Φ)`), `PICT.ref_iff_refA`, `PICT.refA_mono` (monotone
  in base and degree).
- Relative rule lemmas: `PICT.ax_memA`, `PICT.refA_init` (hypothesis `clausePoly C ∈ A`),
  `PICT.refA_taut`, `PICT.refA_of_derive`, `PICT.g3_propsA`, `PICT.refA_sem1`, `PICT.refA_sem2`.
  The proofs are the old ones with `cnfAx Φ` replaced by `A`; nothing in them used that the base
  consists of clauses except the clause axiom case.
- Old names `ax_mem`, `ref_init`, `ref_taut`, `ref_of_derive`, `g3_props`, `ref_sem1`, `ref_sem2`:
  same statements, proved from the relative forms.
- `PICT.tder_refA`: the tree bound of `tder_ref` over any base `A ⊇ cnfAx Φ`. A `PIC` tree has no
  hypothesis leaves, so this is monotonicity only.

## 3. Hypothesis leaves in `FregeTree.lean` (LEAN)

### 3.1 Relative core

`FTree.valid_refA`, `FTree.refA_of_derive'`, `FTree.ded_lineA`, `FTree.cut_coreA`,
`FTree.gate_coreA`, `FTree.step_refA` (extra argument `cnfAx F ⊆ A`). The old `valid_ref`,
`ref_of_derive'`, `ded_line`, `cut_core`, `gate_core`, `step_ref` are corollaries with unchanged
statements, and `tproof_ref`, `tree_frege_pc_degree` and everything after them are unchanged.

### 3.2 Definitions

- `FTree.TProofH p F H P S s`: as `TProof`, with a second constructor `hyp`: a sequent `S ∈ H` with
  `P S` is a leaf with one node.
- `FTree.hypPoly p S = ∏_{g ∈ trS p S} (1 - g)`, `FTree.hypAx p H = {hypPoly p S | S ∈ H}`.
- `FTree.eval_hypPoly_eq_zero`: on a cube point the hypothesis polynomial vanishes iff some term of
  the translation is `1`. This is the sense in which `hypPoly p S = 0` says "S holds" in the
  convention of `Ref`, where the axiom `g = 0` for a term `g` says that term is false.
- `FTree.hypAx_empty`: no hypotheses, no extra axioms.

### 3.3 Statements

- `FTree.TProof.toH`: every `TProof` is a `TProofH` for every `H`, with the same size.
- `FTree.TProofH.sound`, `FTree.TProofH.unsat`: an assignment satisfying `F` and every sequent of `H`
  satisfies every derived sequent; so a refutation of `F` plus `H` shows that no assignment satisfies
  both. (By `fstep_sound`.)
- `FTree.hyp_refA` (the new leaf case): if `hypPoly p S ∈ A`, `S ∈ DegS p d` and `trS p S` has at
  most `k` terms, then `RefA A (trS p S) (k d)`. Proof: `FTree.one_sub_prod_list` on the list of
  terms derives `1 - ∏ (1 - g)` from the terms in degree `d · #terms`, and adding the axiom
  `∏ (1 - g)` gives `1`.
- `FTree.tproofH_refA`: tree induction, the node case is the old one with `step_refA`, the leaf case
  is `hyp_refA`.
- `FTree.tree_frege_pc_degree_hyp`: `s ≤ 2^K` gives
  `PCD (cnfAx F ∪ hypAx p H) (d K + max w (max (k d) (3 d))) 1`.
- `FTree.tree_frege_pc_degree_hyp_clog`: the same with `K = clog2 s`.
- `FTree.tree_frege_size_of_degree_hyp`: if degree `D0` does not refute `cnfAx F ∪ hypAx p H`, every
  such tree has at least `2^((D0 - max w (max (k d) (3 d))) / d)` nodes.

### 3.4 Remarks

- `k` counts terms of the translation `trS` (a finite set of polynomials), not formulas of the
  sequent. A sequent whose formulas are all in split positions (positive OR, negative AND) can have
  more terms than formulas.
- The hypotheses must themselves lie in `DegS p d` (the fragment condition holds at every node).
  For a hypothesis that is a narrow clause this is the old clause-axiom situation; the new content
  is for hypotheses whose translation is a product polynomial `∏ (1 - g)` of degree `k d`.
- `PIC` trees (`TDer`) were not given hypothesis leaves; only monotonicity in the base was added.
  HAND: the same leaf lemma applies verbatim with a line in place of `trS p S`.

## 4. What was not done: the Frontier pin

The intended pin: a polynomial calculus degree lower bound over F_p for one-hot Tseitin mod `q`
together with the hypothesis polynomials of a family `H` of weak surjective pigeonhole instances as
in Buss, Kolodziejczyk and Zdanowski, Theorem 45 (CITED-MEMORY: there, constant depth Frege proofs
with MOD_p gates are converted into tree-like polylog degree refutations of `F` together with
instances of the onto weak pigeonhole principle for functions computed by low degree / shallow
objects over the variables of `F`). I did not state it, for these reasons:

1. The family is not defined in the repo, and I do not have the exact encoding of the instances
   (domain and range sizes, how the function is given, how a range element is witnessed). A pin
   with a guessed encoding could be false or vacuous for the wrong reason, which is worse than no
   pin.
2. With the relative theorem the shape is now fixed: for a set `H` of sequents in `DegS p d` with at
   most `k` terms each, it suffices to prove
   `¬ PCD (cnfAx (tcnf (cubFam m) q b) ∪ hypAx p H) D0 1` for `D0` polynomially large in `n`.
   Combined with `tree_frege_size_of_degree_hyp` this gives exponential size for tree-like
   refutations of Tseitin plus `H`. Whether `H` must be restricted (and how) is exactly the open
   part: if `H` may contain arbitrary low degree polynomials, `hypAx p H` can contain `1` itself
   (a contradictory hypothesis), so a pin must say that every hypothesis is satisfiable together
   with something, or that `H` comes from the BKZ construction.
3. The previous report's comparison point stands: BKZ prove what they need by a switching lemma
   for `PV_1` functions without parity queries; the repo has no such object.

## 5. What failed

Nothing in the plan failed. One elaboration fix: `refA_init ⟨C, hC, rfl⟩` needs `(A := cnfAx Φ)`
when the expected type is `Ref Φ ...`, since the anonymous constructor does not see through the
definition. Compilation of a changed module against the primary build needs a scratch olean tree
with symlinks to every other module (Lean resolves the root `Theory` once, not per module).

## 6. The single best next step

Define the hypothesis family of BKZ Theorem 45 in the repo, as a set of sequents in `DegS p d`
with a stated term bound `k`, from the paper (not from memory), and check that each instance is
satisfiable over the cube (so `hypAx` does not contain a trivial contradiction). Then pin, in a
Frontier namespace, `¬ PCD (cnfAx (Tseitin) ∪ hypAx p H) D0 1` with `D0` polynomial in `n`, and use
`FTree.tree_frege_size_of_degree_hyp` to state the conditional consequence for tree-like proofs.
This needs the paper in hand; it is a definition task, not a proof task.

## 7. Session log

- Worktree `SATurday-wt/treedeg-relative`, branch `r4/treedeg-relative`. Changed:
  `PICTree.lean`, `FregeTree.lean`, `scripts/accepted_declarations.txt` (new block),
  `docs/ladder/r4-completion-checklist.md` (one paragraph under 2.4). No new Lean file, so
  `Theory.lean` is unchanged.
- No web access. Nothing pushed.
