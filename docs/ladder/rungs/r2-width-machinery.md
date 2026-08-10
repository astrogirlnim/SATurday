# R2: Width Machinery and More Families

Status: prose_accepted
Lean home: theory/Theory/ProofComplexity/Width.lean and SizeWidth.lean (item 1
merged); FinGraph.lean and Tseitin.lean (item 2 width machine merged, including
heawoodGraph_expansion); CSExpansion.lean (item 2 CS width machine certified under
clause-set pin restated 2026-08-09; existence `exists_cs_clause_expanding_3cnf`
still Frontier)

## Statement

1. Ben-Sasson-Wigderson width-size tradeoff in general form: short resolution
   refutations imply narrow refutations; quantitative version.
2. Width lower bounds, hence size lower bounds, for: random k-CNF at suitable
   clause density (Chvatal-Szemeredi) and Tseitin contradictions over expander
   graphs.

The precise Lean level form of item 1, together with its non vacuity witness,
gap list, and module plan, is pinned in the 2026-08-04 prove entry of the session
log below (target names `bsw_width_of_fatCount` and `bsw_size_lower_bound`).

## Why this rung

The width method is the workhorse of resolution lower bounds; formalizing it in
general form turns R1-style results into a reusable machine. Expander-based Tseitin
bounds introduce the expansion toolkit needed at higher rungs.

## Falsification test

Calibration only: falsifier proof-size curves for random k-CNF around the
threshold density and for Tseitin instances; curves must match the known theory
(exponential at the relevant densities).

## Barrier notes

Same as R1: no applicable wall at resolution level. Expansion arguments are the
technique most likely to survive upward, worth auditing for reuse at R3 and R4.

## Session log (append-only)

- 2026-08-03 reboot: rung proposed.
- 2026-08-03 falsify (early smoke calibration, budgets enforced): Tseitin
  odd-charge on the 3-regular circulant, n = 6..16 even, all UNSAT within
  milliseconds with proof lines in the tens to low hundreds; random 3-CNF at
  density 5, n = 20..44 step 4: 5 UNSAT, 2 SAT (small-n fluctuation near the
  threshold, expected and recorded honestly). Two conclusions for rung design:
  the circulant chord graph is not a strong expander, so the R2 Tseitin family
  must switch to genuine expanders (random 3-regular with expansion check, or an
  explicit Ramanujan-style construction) before hardness curves mean anything;
  and the random 3-CNF density should rise toward 5.5 or n should grow before it
  is used as a hardness calibration family. Ledger: search/logs/falsifier_runs.jsonl.

- 2026-08-04 adopt: rung opened to active by R1 certification
  (path A honest-rate close). Next: prove cycle to pin the BSW size-width statement and Lean module split.

- 2026-08-04 prove (pin the Ben-Sasson and Wigderson size versus width tradeoff):
  PARTIAL to SUCCESS on the core statement, with one open numeric constant in the
  rate corollary. Prose only, no Lean written this cycle. Details follow.

  ### Statement restated with all quantifiers explicit

  All objects live in namespace `SATurday.ProofComplexity` and use the existing
  resolution calculus of `theory/Theory/ProofComplexity/Resolution.lean`:
  `Literal` (fields `var : ℕ`, `pos : Bool`), `Clause := Finset Literal`,
  `CNF := Finset Clause`, `resolvent`, the inductive `Derivation F C` with
  constructors `hyp` and `res`, `Derivation.size`, `Derives`, `Refutable`,
  `clauseVars`, `cnfVars`.

  Measures to be introduced (all new, none of these names exists anywhere in
  the tree today; verified by ripgrep over theory and docs):

  - `cnfWidth (F : CNF) : ℕ := F.sup Finset.card`, the initial width.
  - `Derivation.lines : Derivation F C -> Finset Clause`, all clauses occurring
    in the proof tree, mirroring the existing `MonoDeriv.lines` in
    `MonotoneCalculus.lean`.
  - `Derivation.width : Derivation F C -> ℕ`, the maximum of `Finset.card` over
    the nodes of the tree, defined by the same recursion as `Derivation.size`.
  - `Derivation.fatCount (t : ℕ) : Derivation F C -> ℕ`, the number of tree
    nodes whose clause has `card > t`, counted with multiplicity.
  - `Derivation.fatLitCount (t : ℕ) (l : Literal) : Derivation F C -> ℕ`, the
    number of fat nodes whose clause contains `l`, counted with multiplicity.
  - `cnfLits (F : CNF) : Finset Literal`, both polarities of every variable of
    `F`, so `(cnfLits F).card = 2 * (cnfVars F).card`.
  - `assignOne (x : ℕ) (b : Bool) : ℕ -> Option Bool`, the single variable
    partial assignment, fed to the existing `restrictClause` and `restrictCNF`.
  - `fatShrink (N t m : ℕ) : ℕ := m - (t * m / N + 1)` with truncated natural
    subtraction and floor division.
  - `fatSteps (N t : ℕ) : ℕ -> ℕ` by well founded recursion,
    `fatSteps N t 0 = 0` and `fatSteps N t m = 1 + fatSteps N t (fatShrink N t m)`
    for `m` positive, terminating because `fatShrink N t m < m` for positive `m`.

  Pinned core statement (target name `bsw_width_of_fatCount`):

  for every `F : CNF`, every `t : ℕ`, and every refutation
  `pi : Derivation F (emptyClause)` there exists a refutation
  `pi' : Derivation F (emptyClause)` with

      pi'.width <= cnfWidth F + t + fatSteps (2 * (cnfVars F).card) t (pi.fatCount t)

  where `emptyClause` denotes the Lean literal `(∅ : Clause)`. The quantifier
  order matters and is deliberate: the narrow refutation depends on the given
  refutation, because the fat count of the given refutation is what pays for the
  width. Nothing uniform over all refutations is claimed.

  Pinned rate corollary (target name `bsw_size_lower_bound`), stated in the
  contrapositive direction that the ladder actually consumes: for every
  `F : CNF` and every `W : ℕ`, if every refutation of `F` has width at least `W`,
  then every refutation `pi` of `F` satisfies

      2 ^ ((W - cnfWidth F) * (W - cnfWidth F) / (c * (cnfVars F).card)) <= pi.size

  with `c` an explicit natural constant. The honest position taken here, learned
  from the R1 close, is that `c` is NOT claimed yet. The argument below supports
  some explicit `c` in the range 8 to 24 depending on how the arithmetic is
  packaged, and the exact value is pinned only when the Lean proof compiles.
  No asymptotic Omega notation appears in the pinned statement.

  ### Non vacuity

  Two separate checks, per docs/p-vs-np-proof-standards.md statement hygiene.

  1. The quantified set of objects is nonempty. Witness: `phpCNF n` from
     `theory/Theory/ProofComplexity/PHP.lean`, with `phpCNF_unsat n` and
     `phpCNF_refutable n` both already certified. So unsatisfiable formulas with
     resolution refutations exist, and `Derivation (phpCNF n) (∅ : Clause)` is
     inhabited (a term is extracted from `Refutable` through choice, which is on
     the allowed axiom list).
  2. The conclusion is not implied by the trivial width bound. The trivial bound
     is `pi.width <= 2 * (cnfVars F).card`, because every literal of every line
     lies over a variable of `F` by the existing `derivation_clauseVars_subset`.
     Informativeness therefore requires an instance with
     `cnfWidth F + t + fatSteps (2 * (cnfVars F).card) t (pi.fatCount t)`
     strictly below `2 * (cnfVars F).card`. Witness family to be added at
     formalization time: `chainCNF n`, the implication chain
     `{x 0}`, `{not x 0, x 1}`, ..., `{not x (n-1), x n}`, `{not x n}`, which is
     unsatisfiable, has `cnfWidth = 2`, has an explicit unit propagation
     refutation of size `2 * n + 1` all of whose lines have card at most 2, and
     therefore has `fatCount t = 0` for `t = (cnfVars F).card = n + 1`. The
     pinned bound then reads `2 + (n + 1) + 0 = n + 3`, strictly below the
     trivial `2 * (n + 1)` for every `n` at least 2. Target name for this check:
     `bsw_bound_beats_trivial`.

  ### The one argument developed, in full

  Fix `F`, fix the fat threshold `t`, write `N := 2 * (cnfVars F).card` and
  `m := pi.fatCount t`. Induction is well founded on the pair `(m, N)` ordered
  lexicographically with `m` primary.

  Step 1 (base case, `m = 0`). No node of `pi` has card above `t`, and every
  `hyp` node is a clause of `F`, so every node has card at most
  `max (cnfWidth F) t`, which is at most `cnfWidth F + t`. Take `pi' := pi`.
  Since `fatSteps N t 0 = 0`, the bound holds. Nothing else is needed, and in
  particular no separate base case on the variable count is required, because a
  fat node has at least one literal and hence forces `cnfVars F` to be nonempty
  whenever `m` is positive.

  Step 2 (averaging, `m` positive). Every literal of every line of `pi` lies in
  `cnfLits F` by `derivation_clauseVars_subset`, and `(cnfLits F).card = N`.
  Summing card over fat nodes and exchanging the two sums gives

      sum over l in cnfLits F of (pi.fatLitCount t l)
        = sum over fat nodes of card
        > t * m,

  the strict inequality because each fat node has card strictly above `t`. The
  same sum is also at least `m`, since each fat node has at least one literal.
  Hence there exists a literal `l` in `cnfLits F` with
  `pi.fatLitCount t l >= t * m / N + 1`, using that a natural number strictly
  above the rational `t * m / N` is at least the floor plus one, and using the
  second inequality to cover the degenerate case `t = 0`. This is the same
  pigeonhole shape as the existing `exists_popular_grid_literal` and
  `sum_card_eq_sum_hitCount` in `MatchingRestriction.lean`, so those proofs are
  the template. Target name: `exists_popular_literal`.

  Step 3 (the true branch). Restrict by `rho1 := assignOne l.var l.pos`, which
  sets `l` to true. Every clause containing `l` is satisfied, hence killed by
  the existing `restrictClause`. Applying the strengthened restriction lemma to
  `pi` yields a refutation `pi1` of `restrictCNF rho1 F` whose every node is a
  subclause of the restriction of the corresponding node of `pi`. Consequences:
  `pi1.width <= pi.width`, and more importantly
  `pi1.fatCount t <= m - pi.fatLitCount t l <= fatShrink N t m`, because every
  fat node containing `l` disappears and every surviving node contributes at
  most one node. Also `cnfVars (restrictCNF rho1 F)` is a strict subset of
  `cnfVars F`, since `l.var` is removed, so the new `N1` is at most `N - 2`,
  and `cnfWidth (restrictCNF rho1 F) <= cnfWidth F` because restriction only
  removes literals. The induction hypothesis applies because the fat count
  strictly dropped, and yields a refutation of `restrictCNF rho1 F` of width at
  most `cnfWidth F + t + fatSteps N1 t (pi1.fatCount t)`, which is at most
  `cnfWidth F + t + fatSteps N t m - 1` by monotonicity of `fatSteps` in the
  variable budget and in the count together with the defining equation.

  Step 4 (reintroducing the falsified literal). No line of any derivation over
  `restrictCNF rho1 F` mentions `l.var`, because `restrictClause` keeps only
  literals with `rho1` undefined on their variable. Therefore every resolution
  step of the branch refutation pivots on a variable different from `l.var`, and
  inserting the complementary literal `negLit l` into every line commutes with
  the resolvent operation. Replacing each hypothesis by the clause of `F` it came
  from and pushing the complementary literal through gives a derivation from `F`
  of some clause contained in the singleton of `negLit l`, of width at most one
  more than the branch width, hence at most `cnfWidth F + t + fatSteps N t m`.
  If that clause is empty the whole construction is finished. Target name:
  `exists_derivation_add_lit`.

  Step 5 (the false branch). Restrict by `rho0 := assignOne l.var (not l.pos)`.
  The restricted derivation has fat count at most `m`, and the variable budget
  again drops, so the induction hypothesis applies on the lexicographic second
  component and yields a refutation of `restrictCNF rho0 F` of width at most
  `cnfWidth F + t + fatSteps N0 t m`, which is at most
  `cnfWidth F + t + fatSteps N t m`.

  Step 6 (grafting). Every clause of `restrictCNF rho0 F` is either a clause of
  `F` or a clause of `F` with the single literal `l` deleted. In the second case
  it is exactly the resolvent of that clause of `F` with the singleton clause of
  `negLit l` on the variable `l.var`, which is derivable from `F` by step 4 with
  width at most `max (cnfWidth F) (cnfWidth F + t + fatSteps N t m)`. Grafting
  those derivations under the step 5 refutation produces a refutation of `F` of
  width at most `cnfWidth F + t + fatSteps N t m`, closing the induction. The
  existing `derives_trans` in `Resolution.lean` performs exactly this graft at
  the proposition level and therefore loses the width, so a width tracking
  variant is required. Target name: `exists_derivation_graft_width`.

  Step 7 (from the core statement to the rate). Two purely arithmetic facts turn
  the core statement into the pinned corollary and are deliberately isolated from
  the combinatorics. First, `fatSteps N t m` is bounded by roughly
  `(N / t + 1) * (Nat.log 2 m + 1)`, because one step multiplies the count by at
  most `1 - t / N`, so a block of about `N / t` steps at least halves it. This is
  the same packaging that R1 used for its rate through `growth_block` and
  `growth_pow`, so those proofs are the template. Second,
  `pi.fatCount t <= pi.size`, since fat nodes are a subset of nodes. Combining,
  a width lower bound `W` gives, for every `t`,
  `W <= cnfWidth F + t + (N / t + 1) * (Nat.log 2 (pi.size) + 1)`, and choosing
  `t` as half of `W - cnfWidth F` yields the quadratic over linear exponent of
  the pinned corollary. The constant `c` is exactly what this optimisation
  produces and is left open on purpose.

  ### Gap list

  1. `exists_derivation_restrict_width`: the existing `derivation_restrict_sub`
     in `MatchingRestriction.lean` gives only the conclusion subclause and the
     size bound. The BSW induction needs the same induction carrying two more
     invariants, namely that every node of the produced derivation is a subclause
     of the restriction of some node of the original at the same tree position,
     which yields both the width bound and the fat count bound. Gap class:
     routine but heavy, roughly the size of the existing 100 line proof again.
  2. `exists_derivation_add_lit`: pushing the complementary literal back through a
     derivation. Needs the auxiliary fact that variables assigned by `rho` are
     absent from `cnfVars (restrictCNF rho F)`, target name
     `notMem_cnfVars_restrictCNF_of_assigned`, and the commutation of `resolvent`
     with inserting a literal on a different variable. Gap class: routine.
  3. `exists_derivation_graft_width`: width tracking substitution of hypotheses.
     Gap class: routine.
  4. `fatSteps` monotonicity. Monotonicity of `fatShrink` in the count requires
     `t <= N`, because with `t` above `N` the floor term can jump by more than one
     per unit increase of the count. In the application this is harmless, since
     `t > N` forces `fatCount t = 0` and the base case applies, but the Lean
     lemmas must carry the hypothesis. Gap class: routine, found by the
     adversarial pass below.
  5. `fatSteps_le_log` and the resulting explicit constant `c`. Gap class:
     routine but laborious, and the constant is unpinned until the proof
     compiles. This is the only place where the pinned corollary is not yet a
     definite statement.
  6. `chainCNF` and `bsw_bound_beats_trivial`: the explicit non vacuity family
     with its explicit width 2 refutation term. Gap class: routine.
  7. Well founded recursion on the lexicographic pair. Lean needs an explicit
     termination measure; the natural choice is
     `(pi.fatCount t, (cnfVars F).card)` with `Prod.Lex`. Gap class: routine,
     but this is the step most likely to cost time in practice.

  No gap is classified hard or unknown. Every external result used is Ben-Sasson
  and Wigderson 2001, marked known, with the discrete reformulation through
  `fatShrink` and `fatSteps` marked adaptation. No new axiom is introduced.

  ### Self adversarial pass

  1. Quantifier order. The narrow refutation depends on the given refutation.
     Stating it the other way round, one width bound valid for all refutations
     with the fat count of the best one, would be a different and unproved claim.
     The pinned statement is the per proof version.
  2. Does the argument secretly prove something known false. The known optimality
     results of Bonet and Galesi say the square root shape cannot be improved to
     a logarithm. The argument produces the factor `N / t`, which is exactly what
     blocks that improvement, so no contradiction with known separations arises.
  3. Does it prove something as hard as the summit. No. The statement is a
     tradeoff, not a lower bound, and it is a 2001 theorem.
  4. The PHP sanity check, and this is the single most important thing learned
     this cycle. Instantiating the pinned corollary at `phpCNF n` gives
     `cnfVars` of size `n * (n + 1)`, so the exponent is a width gap of order `n`
     squared over `n` squared, that is order one. The corollary is therefore
     vacuous on PHP, which independently reconfirms the R1 route decision
     recorded on 2026-08-03 to use Beame and Pitassi counting rather than the
     width method for PHP. R2 must therefore be validated on Tseitin over genuine
     expanders and on random k CNF, where the variable count is linear in the
     width gap, and never on PHP.
  5. Off by one on fatness. Fat means card strictly above `t`. The base case then
     bounds width by `max (cnfWidth F) t` which is below `cnfWidth F + t`, so the
     inequality direction is safe. The `+ 1` inside `fatShrink` is justified by
     the second averaging inequality and is what makes the recursion terminate.
  6. Truncated natural subtraction. `fatShrink` saturates at zero, which only
     makes `fatSteps` smaller, which would make the pinned statement stronger, so
     it must be checked rather than assumed. It is safe because the only use of
     `fatShrink` is as an upper bound on the fat count after restriction, and an
     upper bound of zero is the base case.
  7. Hidden uniformity. The popular literal depends on the proof and on `t`. No
     uniform or constructive choice of literal is claimed.
  8. Tautological lines. `Derivation` permits a line containing both polarities of
     a variable. Restriction kills such a line whenever the variable is assigned,
     and the trivial width bound used for the non vacuity check is `2 *` the
     variable count precisely to accommodate them. No step assumes lines are non
     tautological.

  ### Barrier pass

  Relativization, natural proofs, and algebraization: not applicable, this is a
  syntactic combinatorial statement about resolution derivations and does not
  simulate machines, does not construct a property of Boolean functions, and does
  not use low degree extension. Feasible interpolation death: not applicable, no
  interpolation is used. Automatability death (Atserias and Muller 2019):
  relevant and checked. The size versus width tradeoff is the engine of the
  width based automatization algorithm, but it yields time of the form n to the
  power order square root of n log S, which is not polynomial, so nothing here
  contradicts non automatability of resolution. Simulation order: resolution sits
  below Res(k), cutting planes, and bounded depth Frege, all of which polynomially
  simulate it, so an R2 result never transfers upward by itself. This is a rung at
  resolution level, so no wall blocks it.

  ### Lean module plan

  Two new modules, no duplication of existing functionality. Verified before
  planning that the only width machinery in the tree today is
  `MonotoneWidth.lean`, which is the PHP specific monotone transform, and that
  the generic restriction machinery already lives in `MatchingRestriction.lean`
  and is reused rather than rewritten.

  1. `theory/Theory/ProofComplexity/Width.lean`, importing
     `Theory.ProofComplexity.MatchingRestriction`. Contents: `cnfWidth`,
     `cnfLits`, `Derivation.lines`, `Derivation.width`, `Derivation.fatCount`,
     `Derivation.fatLitCount`, `assignOne`, the elementary lemmas
     (`Derivation.concl_mem_lines`, `Derivation.lines_card_le_size`,
     `Derivation.fatCount_le_size`, `width_le_of_fatCount_zero`,
     `cnfWidth_restrictCNF_le`, `notMem_cnfVars_restrictCNF_of_assigned`,
     `cnfVars_restrictCNF_ssubset`), the pigeonhole `exists_popular_literal`, and
     the three structural lemmas `exists_derivation_restrict_width`,
     `exists_derivation_add_lit`, `exists_derivation_graft_width`.
  2. `theory/Theory/ProofComplexity/SizeWidth.lean`, importing
     `Theory.ProofComplexity.Width`. Contents: `fatShrink`, `fatSteps` and their
     monotonicity, `bsw_width_of_fatCount`, `fatSteps_le_log`,
     `bsw_size_lower_bound`, `chainCNF` with its explicit refutation, and
     `bsw_bound_beats_trivial`.

  Both modules are added to `theory/Theory.lean` after
  `Theory.ProofComplexity.MonotoneCalculus`, and every accepted declaration is
  appended to `scripts/accepted_declarations.txt` under an R2 header. Nothing in
  the certified R0 and R1 modules is edited, so the axiom gate keeps its current
  green state while R2 is built. Estimated size: 900 to 1500 lines of Lean, so
  the formalize cycles should take Width.lean measures and
  `exists_derivation_restrict_width` first, since everything else depends on it.

  Artifacts: this rung memory entry only, no Lean and no test files written.
  Human gate pending: accept_prose for the pinned core statement and the module
  plan. Next recommended action: formalize, starting with the measures and
  `exists_derivation_restrict_width` in `Width.lean`.

- 2026-08-04 human gate accept_prose: APPROVED by session decision ("go").
  Status set to prose_accepted. Pinned core `bsw_width_of_fatCount`, rate
  corollary shape with open constant `c`, discrete `fatShrink`/`fatSteps`
  packaging, and the Width.lean then SizeWidth.lean module plan are accepted
  for formalization. Most important thing learned: human approval unblocks the
  first Width.lean cluster without reopening the PHP rate chase.

- 2026-08-04 formalize (Width.lean measures and restrict-width transport):
  SUCCESS. New module `theory/Theory/ProofComplexity/Width.lean` imported from
  Theory.lean. Certified cluster (24 declarations in
  scripts/accepted_declarations.txt): cnfWidth, cnfLits, cnfLits_card,
  assignOne, assignOne_self, assignOne_ne, Derivation.lines,
  Derivation.concl_mem_lines, Derivation.lines_card_le_size, Derivation.width,
  Derivation.fatCount, Derivation.fatLitCount, Derivation.fatCount_le_size,
  Derivation.width_hyp_le_cnfWidth, width_le_of_fatCount_zero,
  cnfWidth_restrictCNF_le, notMem_cnfVars_restrictCNF_of_assigned,
  cnfVars_restrictCNF_subset, cnfVars_restrictCNF_ssubset_assignOne,
  card_le_of_subset, resolvent_subset_of_subset,
  exists_derivation_restrict_width, exists_restrict_refutation_width.
  Gate green after adding the cluster. Gap 1 from the prove entry
  (exists_derivation_restrict_width) is closed. Remaining Width.lean gaps:
  exists_popular_literal, exists_derivation_add_lit,
  exists_derivation_graft_width. SizeWidth.lean still unstarted.
  Most important thing learned: the size-only derivation_restrict_sub
  induction lifts cleanly once resolvent_subset_of_subset makes the fat and
  width inequalities definitional rather than rewriting through Option.
  Pending human gate merge_certified. Next: formalize exists_popular_literal
  and the add_lit / graft width lemmas, or start SizeWidth.lean measures.

- 2026-08-04 human gate merge_certified: APPROVED by session decision ("go").
  Width.lean first cluster (24 declarations) accepted into the accepted tree.
  Gate remains green. R2 stays prose_accepted. Next: formalize
  exists_popular_literal then add_lit and graft_width.

- 2026-08-04 formalize (popular literal, add_lit, graft_width): SUCCESS.
  Closed the three remaining Width.lean structural gaps from the prove entry:
  exists_popular_literal (via fatCardSum double counting),
  exists_derivation_add_lit (subset invariant through complementary unit),
  exists_derivation_graft_width (width-tracking derives_trans).
  Ten new accepted declarations. Gate green. Width.lean module plan items
  for measures, restrict-width, popular literal, add_lit, and graft are all
  closed. SizeWidth.lean (fatShrink, fatSteps, bsw_width_of_fatCount) remains.
  Most important thing learned: add_lit must keep the invariant
  C' ⊆ insert complementary C rather than literally inserting into every
  line, so preimage clauses of F can be used as hypotheses without
  weakening. Pending human gate merge_certified. Next: formalize
  SizeWidth.lean.

- 2026-08-04 human gate merge_certified: APPROVED by session decision ("go").
  Popular literal / add_lit / graft_width cluster accepted. R2 stays
  prose_accepted. Next: formalize SizeWidth.lean.

- 2026-08-04 formalize (SizeWidth.lean fatShrink fatSteps kill-lit drop): SUCCESS.
  New module `theory/Theory/ProofComplexity/SizeWidth.lean` imported from
  Theory.lean. Certified cluster (12 declarations): fatShrink, fatShrink_lt,
  fatSteps, fatSteps_zero, fatSteps_of_pos, fatShrink_le_self,
  Derivation.fatLitCount_le_fatCount, Derivation.concl_card_le_cnfLits,
  Derivation.fatCount_eq_zero_of_lits_le, exists_derivation_restrict_kill_lit,
  exists_restrict_refutation_kill_lit, fatCount_kill_le_fatShrink.
  Gate green. Deferred to next cycle: bsw_width_of_fatCount induction,
  fatSteps_le_log, bsw_size_lower_bound, chainCNF non vacuity.
  Most important thing learned: kill-lit fat drop needs the outer Nat
  subtraction rewritten additively with Nat.le_sub_iff_add_le; omega cannot
  reason through a compound subtracted RHS as a single atom.
  Pending human gate merge_certified. Next: formalize bsw_width_of_fatCount.

- 2026-08-04 human gate merge_certified: APPROVED by session decision ("go").
  SizeWidth first cluster (12 declarations, commit ed09d55) accepted into the
  accepted tree. R2 stays prose_accepted. Next: formalize bsw_width_of_fatCount.

- 2026-08-04 formalize (bsw_width_of_fatCount core induction): SUCCESS.
  Closed the pinned core tradeoff in SizeWidth.lean via lex induction on
  (fatCount, vars.card) with over-approximating literal budget N. New accepted
  declarations (9): fatShrink_mono_N, fatShrink_le_fatShrink_succ,
  fatShrink_mono_m, fatSteps_mono_m, mem_cnfVars_of_mem_cnfLits,
  cnfLits_card_le_of_vars_subset, exists_derivation_false_branch_clause,
  bsw_width_of_fatCount_aux, bsw_width_of_fatCount. Gate green.
  Remaining SizeWidth gaps: fatSteps_le_log, bsw_size_lower_bound (open
  constant c), chainCNF and bsw_bound_beats_trivial.
  Most important thing learned: over-approximating N in the auxiliary
  statement lets the false branch keep the same fatSteps budget while the
  lex second component (variable count) supplies termination when fatCount
  does not drop.
  Pending human gate merge_certified. Next: formalize fatSteps_le_log and
  the rate corollary, or the chainCNF non vacuity witness.

- 2026-08-04 human gate merge_certified: APPROVED by session decision ("go").
  SizeWidth bsw_width_of_fatCount cluster (9 declarations, commit f649a53)
  accepted into the accepted tree. R2 stays prose_accepted. Next: formalize
  fatSteps_le_log and bsw_size_lower_bound.

- 2026-08-04 formalize (fatSteps_le_log rate arithmetic): PARTIAL to SUCCESS on
  the log bound, rate corollary still open. New accepted declarations (12):
  fatBlock, le_mul_fatBlock, div_fatBlock_le_mul_div, iterate_fatShrink_le,
  iterate_fatShrink_anti, fatSteps_le_add_iterate, fatBlock_mul_half_succ_div_ge,
  fatShrink_iterate_fatBlock_le_half, fatSteps_le_log, bswRateConst,
  Derivation.size_pos, bsw_width_log_bound. Gate green. Verified
  cnfLits_card = 2 * (cnfVars).card from Width.lean; bsw_width_of_fatCount uses
  that equality. Pinned reserved constant bswRateConst = 24 for the eventual
  size corollary, but bsw_size_lower_bound itself did not finish this cycle
  (loose Nat packaging of Delta^2/(c n) versus log2 size loses a factor past
  the honest 8 to 24 range without tighter casework). Intermediate
  bsw_width_log_bound records the usable width versus log size form.
  Remaining SizeWidth gaps: bsw_size_lower_bound with pinned c, chainCNF and
  bsw_bound_beats_trivial.
  Most important thing learned: the half block argument needs t < N for the
  per step drop lower bound; the t = N wipe is a one line separate case.
  Pending human gate merge_certified. Next: finish bsw_size_lower_bound at
  bswRateConst = 24, or ship chainCNF non vacuity.

- 2026-08-04 human gate merge_certified: APPROVED by session decision ("go").
  SizeWidth fatSteps_le_log cluster (12 declarations, commit 5a8b14f) accepted
  into the accepted tree: fatBlock, le_mul_fatBlock, div_fatBlock_le_mul_div,
  iterate_fatShrink_le, iterate_fatShrink_anti, fatSteps_le_add_iterate,
  fatBlock_mul_half_succ_div_ge, fatShrink_iterate_fatBlock_le_half,
  fatSteps_le_log, bswRateConst, Derivation.size_pos, bsw_width_log_bound.
  R2 stays prose_accepted. Next: formalize bsw_size_lower_bound at
  bswRateConst = 24, or chainCNF non vacuity.

- 2026-08-04 formalize (bsw_size_lower_bound at bswRateConst = 24): SUCCESS.
  Closed the pinned rate corollary in SizeWidth.lean. New accepted declarations
  (4): Derivation.width_le_cnfLits_card, delta_mul_fatBlock_le,
  bsw_delta_sq_le_of_width_log, bsw_size_lower_bound. Gate green. Pinned
  constant c = bswRateConst = 24. Packaging: half-gap t = Δ/2 into
  bsw_width_log_bound yields Δ^2 ≤ 16 n (log2 S + 1); case split on log lands
  the floor quotient Δ^2/(24 n) at most log2 S, hence 2^(...) ≤ S via
  Nat.le_log_iff_pow_le. Verified cnfLits_card = 2 * (cnfVars).card.
  Remaining SizeWidth gaps: chainCNF and bsw_bound_beats_trivial (non vacuity
  witness). Most important thing learned: the odd-gap Nat loss that blocked the
  prior cycle is absorbed by the log case split (log ≤ 1 forces e ≤ 1; log ≥ 2
  recovers the factor-two slack against 24), so c = 24 compiles without
  weakening the pinned statement shape.
  Pending human gate merge_certified. Next: formalize chainCNF and
  bsw_bound_beats_trivial.

- 2026-08-04 human gate merge_certified: APPROVED by session decision ("go").
  SizeWidth bsw_size_lower_bound cluster (4 declarations, commit 66b011e)
  accepted into the accepted tree: Derivation.width_le_cnfLits_card,
  delta_mul_fatBlock_le, bsw_delta_sq_le_of_width_log, bsw_size_lower_bound.
  Pinned rate constant c = bswRateConst = 24. R2 stays prose_accepted.
  Next: formalize chainCNF and bsw_bound_beats_trivial.

- 2026-08-04 formalize (chainCNF non vacuity and bsw_bound_beats_trivial):
  SUCCESS. Closed the pinned SizeWidth non vacuity witness in SizeWidth.lean.
  New accepted declarations (30): chainUnitPos, chainUnitNeg, chainImpl,
  chainCNF, membership and resolvent lemmas, chainDeriveUnitPos,
  chainRefutation, card and width lemmas, Derivation.width_eq_cast,
  Derivation.fatCount_eq_cast, Derivation.fatCount_eq_zero_of_width_le,
  chainRefutation_fatCount_eq_zero, chainCNF width and vars lemmas,
  chainCNF_unsat, chainCNF_refutable, bsw_bound_beats_trivial.
  Gate green. For every n ≥ 2 the BSW bound on chainRefutation is n+3,
  strictly below the trivial ceiling 2*(n+1). Pinned witness is the
  implication chain (not PHP), matching the prove entry adversarial note that
  the rate corollary is vacuous on PHP. Item 1 of the rung statement (BSW
  size-width tradeoff plus non vacuity) is now fully formalized. Item 2
  (width lower bounds for expander Tseitin and random k CNF) remains open.
  Most important thing learned: an explicit width-2 unit propagation term
  makes fatCount zero at t = |vars|, so the informativeness check is a pure
  arithmetic comparison once cnfWidth and cnfVars are computed.
  Pending human gate merge_certified. Next: merge then prove or audit for
  item 2 width lower bounds scaffolding.

- 2026-08-04 human gate merge_certified: APPROVED by session decision ("go").
  SizeWidth chainCNF non vacuity cluster (30 declarations) accepted into the
  accepted tree. R2 item 1 (BSW core, rate at c=24, non vacuity) is merged.
  Rung status stays prose_accepted because item 2 (expander Tseitin and
  random k CNF width lower bounds) is not yet pinned or formalized.
  Next recommended action: prove (pin width lower bound statements and Lean
  module plan for genuine expanders / random k CNF), or audit the completed
  BSW package before opening item 2.

- 2026-08-04 prove (pin R2 item 2: expander Tseitin and random k CNF width
  lower bounds): SUCCESS on the pin. Prose only, no Lean written this cycle.
  Prior falsify honesty is baked into the pin: the 3 regular circulant used by
  search/benchmarks/proof_complexity_families.py is a calibration graph only and
  is NOT an expander witness for hardness. Details follow.

  ### Files and names verified before this pin (no duplicates)

  Lean ProofComplexity tree today (all existing; none invented as duplicates):
  Resolution.lean, PHP.lean, CriticalAssignments.lean, ClauseComplexity.lean,
  MonotoneWidth.lean, MatchingRestriction.lean, MonotoneCalculus.lean,
  Width.lean, SizeWidth.lean. Root importer: theory/Theory.lean.
  Ripgrep over theory and docs found zero hits for: tseitinCNF, HasExpansion,
  edgeBoundary, HasCSExpansion, petersenGraph, tseitinWidthDiv, csWidthDiv,
  FinGraph, oddCharge. Python family generators exist only under
  search/benchmarks/proof_complexity_families.py (tseitin_cnf, random_kcnf) and
  are empirical calibration, not Lean certificates. Archive EncodingTactics
  tseitin_correct is circuit encoding, unrelated, and stays archived.
  docs/file_structure.md was searched and does not exist in this workspace;
  structure is taken from the live ProofComplexity directory listing above.
  Reused certified consumers: cnfWidth, Derivation.width, bsw_size_lower_bound,
  bswRateConst from Width.lean and SizeWidth.lean.

  ### Action choice

  rung: r2-width-machinery
  action_type: prove
  target: item 2 width lower bounds for expander Tseitin and CS expanding k CNF
  rationale: item 1 BSW machine is merged; item 2 still needs Lean level pins
  before any formalize of families or expansion lemmas.

  ### Statement restated with all quantifiers explicit

  All objects live in namespace SATurday.ProofComplexity and use the existing
  resolution calculus of Resolution.lean (Literal, Clause, CNF, Derivation,
  Derivation.size, Derivation.width, Refutable, cnfVars, cnfWidth).

  #### (A) Lightweight graphs and expansion (new module FinGraph.lean)

  Target definitions (none exist today):

  - `FinEdge (n : ℕ) := { e : Fin n × Fin n // e.1 < e.2 }`, unordered edge as
    an ordered pair with the lesser endpoint first.
  - `FinGraph (n : ℕ) := Finset (FinEdge n)`, simple undirected graph on
    vertex set `Fin n`.
  - `incident (G : FinGraph n) (v : Fin n) : Finset (FinEdge n)`, edges of `G`
    that contain `v`.
  - `degree (G : FinGraph n) (v : Fin n) : ℕ := (incident G v).card`.
  - `IsRegular (G : FinGraph n) (d : ℕ) : Prop := ∀ v, degree G v = d`.
  - `edgeBoundary (G : FinGraph n) (S : Finset (Fin n)) : Finset (FinEdge n)`,
    edges of `G` with exactly one endpoint in `S`.
  - `HasExpansion (G : FinGraph n) (α : ℕ) : Prop` means: for every
    `S : Finset (Fin n)`, if `S.Nonempty` and `2 * S.card ≤ n`, then
    `α * S.card ≤ (edgeBoundary G S).card`.
    Integer factor `α` is deliberate (no rationals on the critical path). Graphs
    with fractional expansion below 1 are reported by `α = 0` and give a vacuous
    width claim; the pin never pretends the circulant meets a positive `α`.

  Explicit small witness (non vacuity of expansion, not of the whole R2 summit):

  - `petersenGraph : FinGraph 10`, the Petersen graph on 10 vertices (3 regular,
    15 edges), encoded by an explicit `Finset` of `FinEdge 10` literals.
  - Target lemma `petersenGraph_regular : IsRegular petersenGraph 3`.
  - Target lemma `petersenGraph_expansion : HasExpansion petersenGraph 1`,
    proved by finite enumeration over subsets of `Fin 10` of size 1 through 5.
    Class: routine but heavy. This is the honest replacement for the circulant:
    expansion is checked, not assumed from chord drawings.

  Existence for large n (optional later cluster, not required to start
  formalize):

  - `exists_3regular_expander : ∀ N, ∃ n ≥ N, ∃ G : FinGraph n,
      Even n ∧ IsRegular G 3 ∧ HasExpansion G 1`, marked known via the
    probabilistic method for random 3 regular graphs (Bollobas / Friedman style
    existence), adaptation into Lean. Gap class: hard. Formalize cycles may ship
    Petersen first and defer infinite families.

  Anti cheat note: `tseitin_edges` in the Python falsifier (cycle plus diametral
  chords) is NOT claimed to satisfy `HasExpansion _ 1`. The 2026-08-03 falsify
  session already showed soft proof sizes on that family; the Lean pin refuses
  to launder that graph into an expander hypothesis.

  #### (B) Tseitin CNF and width lower bound (new module Tseitin.lean)

  Charge and formula:

  - `Charge (n : ℕ) := Fin n → Bool` (equivalently `Fin 2`, Boolean parity).
  - `oddCharge (χ : Charge n) : Prop := (Finset.univ.filter χ).card % 2 = 1`.
  - `edgeVar {n} (e : FinEdge n) : ℕ`, a canonical injection from edges into
    variable indices (for example `e.val.1 * n + e.val.2`).
  - `parityClause {n} (evars : List ℕ) (signs : List Bool) : Clause`, one
    width `evars.length` clause forbidding one failing XOR assignment.
  - `vertexParityClauses (G : FinGraph n) (χ : Charge n) (v : Fin n) : CNF`,
    the `2^(d-1)` clauses encoding XOR of incident edge variables equal to
    `χ v`, for `d = degree G v`.
  - `tseitinCNF (G : FinGraph n) (χ : Charge n) : CNF :=` union over vertices
    of `vertexParityClauses`.

  Pinned unsatisfiability (parity, no expansion used):

  - Target name `tseitinCNF_unsat`: for every `n`, every `G : FinGraph n`, and
    every `χ` with `oddCharge χ`, `¬ Satisfiable (tseitinCNF G χ)`.
  - Target name `tseitinCNF_refutable`: same hypotheses imply
    `Refutable (tseitinCNF G χ)`, via existing `resolution_complete`.

  Pinned width lower bound (the item 2 core for family (a)):

  - Reserved natural `tseitinWidthDiv : ℕ := 2` (same packaging style as
    `bswRateConst`; adjust only if the Lean proof forces a larger explicit
    divisor, never silently).
  - Target name `tseitin_expander_width_lower_bound`:
    for every `n : ℕ`, every `G : FinGraph n`, every `χ : Charge n`, every
    `α : ℕ`, if `oddCharge χ` and `HasExpansion G α`, then for every
    refutation `d : Derivation (tseitinCNF G χ) (∅ : Clause)`,

        (α * n) / tseitinWidthDiv ≤ d.width

    Quantifier order: expansion and odd charge are hypotheses on the instance;
    the width bound is universal over refutations. No claim is made for graphs
    that fail `HasExpansion`.

  Size corollary (no new rate arithmetic; reuse item 1):

  - Target name `tseitin_expander_size_lower_bound`: under the same hypotheses,
    every refutation `d` satisfies the `bsw_size_lower_bound` conclusion with
    `W := (α * n) / tseitinWidthDiv`, that is

        2 ^ ((W - cnfWidth (tseitinCNF G χ)) * (W - cnfWidth (tseitinCNF G χ)) /
              (bswRateConst * (cnfVars (tseitinCNF G χ)).card)) ≤ d.size

    For `IsRegular G 3` one has `cnfWidth (tseitinCNF G χ) = 3`, and variable
    count equals `|E|`. Informativeness requires
    `W > 3`, hence `α * n > 3 * tseitinWidthDiv`. With the pinned divisor 2 and
    `α ≥ 1` this holds for all `n ≥ 7`, so Petersen (`n = 10`, `α = 1`) is in
    the informative range once `petersenGraph_expansion` is certified.

  #### (C) CS expansion for k CNF and width lower bound (new module CSExpansion.lean)

  Combinatorial hypothesis (Chvatal and Szemeredi style boundary form, discrete):

  - `clauseSupport (C : Clause) : Finset ℕ := clauseVars C` (already have
    `clauseVars`).
  - `cnfSupport (F : CNF) : Finset ℕ := cnfVars F`.
  - `HasCSExpansion (F : CNF) (k β α : ℕ) : Prop` means: `cnfWidth F ≤ k`, and
    for every `S : Finset ℕ` with `S ⊆ cnfVars F`, if `S.Nonempty` and
    `β * S.card ≤ (cnfVars F).card`, then every clause of `F` that is entirely
    supported on `S` contributes to a boundary count satisfying
    `α * S.card ≤ (boundaryClauses F S).card`, where
    `boundaryClauses F S` is the set of clauses of `F` that touch `S` and also
    touch its complement inside `cnfVars F`. (Exact boundary encoding is part of
    the first formalize cluster; the pin freezes the inequality shape and the
    parameters, not a floating prose synonym.)

  Pinned width lower bound (family (b)):

  - Reserved natural `csWidthDiv : ℕ := 2`.
  - Target name `cs_expansion_width_lower_bound`:
    for every `F : CNF` and parameters `k β α`, if `HasCSExpansion F k β α`
    and `Refutable F`, then for every refutation
    `d : Derivation F (∅ : Clause)`,

        (α * (cnfVars F).card) / (csWidthDiv * β) ≤ d.width

    Again the bound is conditional on a discrete expansion hypothesis. No seeded
    DIMACS instance from the falsifier is hereby declared hard.

  Existence at suitable density (separate from the width machine):

  - Target name `exists_cs_expanding_3cnf`:
    for every `N`, there exist `n ≥ N`, `F : CNF`, and parameters with
    `k = 3`, `β = 4`, `α = 1` (exact constants to be locked when the
    probabilistic calculation is formalized) such that
    `(cnfVars F).card = n`, `HasCSExpansion F 3 β α`, `¬ Satisfiable F`,
    and `(α * n) / (csWidthDiv * β) > cnfWidth F`.
  - Density guidance from falsify: calibration used density 5.0 and saw SAT
    at small `n`; the existence proof should target density at least 5.5
    (above the satisfiability threshold ~4.267 for 3 CNF) with `n` large
    enough that the CS expansion event holds. Marked known
    (Chvatal and Szemeredi 1988; Ben Sasson and Wigderson 2001 packaging),
    adaptation into Lean. Gap class: hard.

  Size corollary: target name `cs_expansion_size_lower_bound`, identical reuse
  of `bsw_size_lower_bound` with
  `W := (α * (cnfVars F).card) / (csWidthDiv * β)`.

  ### Non vacuity (statement hygiene)

  Four separate checks; none may be skipped.

  1. Odd charge Tseitin instances exist and are unsatisfiable without expansion:
     any `G` on `n ≥ 1` with `χ` sending one vertex to true and the rest false
     has `oddCharge χ`. Witness term to build at formalize time:
     `oddCharge_single (n) (v : Fin n)`. Combined with `tseitinCNF_unsat`, the
     quantified set of unsatisfiable Tseitin CNFs is nonempty. This alone does
     NOT make the width lower bound informative.
  2. Expansion hypothesis is inhabited by a checked graph: `petersenGraph` with
     `petersenGraph_expansion : HasExpansion petersenGraph 1`. Circulant is
     excluded. Until Petersen expansion is certified in Lean, the width theorem
     may still be proved conditionally; the informative instance is not claimed
     certified.
  3. Width bound beats initial width on that witness: with `α = 1`, `n = 10`,
     `tseitinWidthDiv = 2`, the pinned lower bound is 5, while
     `cnfWidth (tseitinCNF petersenGraph χ) = 3` for 3 regular Petersen, and
     the trivial ceiling is `2 * |E| = 30`. Target name
     `tseitin_petersen_width_beats_cnfWidth`.
  4. CS expanding unsatisfiable 3 CNFs exist for infinitely many sizes:
     `exists_cs_expanding_3cnf`. Small falsifier seeds at density 5.0 are NOT
     witnesses (some were SAT). No concrete DIMACS file is cited as a theorem
     witness.

  ### The one argument developed in full (Tseitin boundary to width)

  Fix `G : FinGraph n`, `χ` with `oddCharge χ`, and `α` with `HasExpansion G α`.
  Write `F := tseitinCNF G χ`. The argument is the Ben Sasson and Wigderson
  cut sensitive width argument for Tseitin (known, 2001), packaged against
  `Derivation.width` rather than against proof size directly; size then follows
  from the already certified `bsw_size_lower_bound`.

  Step 1 (linear algebra over GF(2)). Each vertex constraint is an affine
  equation on incident edge variables. Summing all vertex equations yields
  the identity `0 = sum χ`, because each edge appears twice. Hence
  `oddCharge χ` implies unsatisfiability. This is `tseitinCNF_unsat` and does
  not use expansion. Gap class once encoded with `ZMod 2` sums: routine.

  Step 2 (partial assignments as cuts). For a set `S : Finset (Fin n)` of
  vertices, let `ρ_S` be any partial assignment to the edges inside `S` that
  satisfies all vertex constraints of vertices whose entire star lies in the
  assigned region, if such an assignment exists. The standard Tseitin fact is
  that the XOR system restricted to `S` is consistent if and only if the total
  charge on `S` equals the parity of the assigned cut edges. Consequently, when
  the charge on `S` is odd relative to a fixed global solution attempt, every
  total extension fails, and every resolution refutation of `F` must "pay for"
  the cut. Target intermediate name: `tseitin_cut_parity`.

  Step 3 (clause to cut complex). Following Ben Sasson and Wigderson, associate
  to each clause `C` appearing in a refutation a critical vertex set
  `complex(C) ⊆ Fin n` consisting of those vertices whose local parity
  constraint is falsified by a minimal partial assignment that falsifies `C`
  and satisfies as many vertex constraints as possible. The empty clause has
  complex equal to the full vertex set (or a nonempty odd charge component).
  Hypothesis clauses of `F` have complex size at most 1. Resolution of two
  clauses yields a complex contained in the union of the parent complexes.
  Target name: `tseitin_complex_res_subset`.

  Step 4 (expansion forces wide clauses). Because complexes grow from size 1
  hypotheses to a complex of size greater than `n / 2` at the empty clause,
  every refutation contains some line `C` whose complex `S := complex(C)`
  satisfies `0 < S.card ≤ n / 2` and whose resolvent parent crosses the
  threshold, or more cleanly (BSW packaging): some line has
  `n / 4 ≤ S.card ≤ n / 2` (the exact threshold constants are part of
  `tseitinWidthDiv` bookkeeping). For such an `S`, every literal of `C` that
  mentions an edge variable outside the cut can be removed by restriction
  arguments already in MatchingRestriction.lean style, and the surviving
  essential literals must include a distinct edge variable for each edge of
  `edgeBoundary G S`. Therefore

      (edgeBoundary G S).card ≤ C.card ≤ d.width

  Apply `HasExpansion G α` to get `α * S.card ≤ d.width`. With
  `S.card ≥ n / tseitinWidthDiv` (the threshold chosen in the complex growth
  argument), conclude
  `(α * n) / tseitinWidthDiv ≤ d.width`.
  Target name: `tseitin_expander_width_lower_bound`.

  Step 5 (size). Invoke certified `bsw_size_lower_bound` with
  `W := (α * n) / tseitinWidthDiv`. No new rate constant is introduced.

  The random k CNF half of item 2 uses the same complex growth skeleton with
  `HasCSExpansion` supplying the boundary inequality in place of
  `HasExpansion`. Developing both in full would duplicate the skeleton; the
  CS case is therefore recorded as the same argument with the clause boundary
  substituted, and its first formalize cluster is the definition of
  `boundaryClauses` plus `cs_expansion_width_lower_bound` after Tseitin
  lands. External citations: Urquhart 1987 (Tseitin expanders), Chvatal and
  Szemeredi 1988 (random CNF), Ben Sasson and Wigderson 2001 (width packaging).
  All marked known; discrete `HasExpansion` / `HasCSExpansion` packaging marked
  adaptation. No new axiom.

  ### Gap list

  1. `FinGraph` API and `edgeBoundary` lemmas (symmetry, degree sum, handshaking).
     Gap class: routine.
  2. `petersenGraph` explicit edge set plus `petersenGraph_regular` and
     `petersenGraph_expansion` by finite check. Gap class: routine but heavy.
  3. `tseitinCNF` construction and `tseitinCNF_unsat` via GF(2) summation.
     Gap class: routine.
  4. `tseitin_complex_*` bridge from clauses to vertex sets (the semantic heart).
     Gap class: hard (first real formalization risk on item 2).
  5. Threshold arithmetic locking `tseitinWidthDiv = 2` (or raising it explicitly
     if the complex argument needs `n/4`). Gap class: routine once gap 4 is
     clear; constant may increase but must stay explicit.
  6. `tseitin_expander_size_lower_bound` as a one liner over
     `bsw_size_lower_bound`. Gap class: routine.
  7. `HasCSExpansion` / `boundaryClauses` definitions matching the Tseitin
     complex argument. Gap class: hard (shared skeleton, new bookkeeping).
  8. `exists_cs_expanding_3cnf` probabilistic method. Gap class: hard; may lag
     many cycles after the conditional width theorem.
  9. `exists_3regular_expander` infinite family. Gap class: hard; Petersen
     unblocks informative non vacuity without it.
  10. Falsifier upgrade (outside Lean accept tree): add an expander backed
      Tseitin generator (reject circulant for hardness curves; keep circulant
      only as a soft smoke). Gap class: routine engineering, not a theorem gap.

  Gaps 4 and 7 are the only hard mathematical formalization gaps on the
  conditional width theorems. Gaps 8 and 9 are existence gaps and must not block
  proving the conditional machines.

  ### Self adversarial pass

  1. Quantifier order. Width lower bounds are conditional on expansion
     hypotheses. Stating "every Tseitin formula needs linear width" without
     expansion would be false (path graphs and circulants are easy). The pin
     refuses that strengthening.
  2. Circulant laundering. The falsifier family is explicitly not a witness.
     Any future formalize that instantiates `HasExpansion` on the circulant
     without a proof is a cheat and fails the adversarial bar.
  3. Vacuous rate on dense graphs. If degree grows with `n`, then `cnfWidth`
     can exceed `W` and `bsw_size_lower_bound` becomes vacuous (exponent zero).
     The pin therefore targets bounded degree expanders (degree 3) and records
     the inequality `W > cnfWidth` as a separate non vacuity lemma.
  4. Random seeds are not theorems. Seed 42 at density 5.0 produced SAT for
     some small `n` in falsify logs; citing those files as hard instances would
     be false. Existence is asymptotic and probabilistic.
  5. Does the argument prove something summit hard. No. It is a 1987 through
     2001 resolution theorem, below R3 systems.
  6. Automatability. Linear width lower bounds plus BSW give exponential size,
     still consistent with Atserias and Muller non automatability (which rules
     out polynomial time proof search, not the existence of lower bounds).
  7. Off by one on `n/2` versus `2 * S.card ≤ n`. The `HasExpansion` predicate
     uses the inclusive half size convention matching Finset cardinal arithmetic
     in Lean; the complex threshold constants feed `tseitinWidthDiv` and must
     be re checked when gap 4 is formalized.
  8. Connectivity. Odd charge unsat does not need connectivity. Width via
     complexes needs care on disconnected graphs: expansion on each component
     with odd charge. The pin assumes the expansion hypothesis globally, which
     already forbids sparse cuts; disconnected graphs with an isolated odd
     charge vertex have `edgeBoundary` empty for that singleton and fail
     `HasExpansion α` for every positive `α`. Safe.
  9. Trivial width ceiling. `Derivation.width_le_cnfLits_card` gives width at
     most `2 * |E|`. The pinned linear lower bound is below that ceiling for
     all parameters in range, so the statement is not crushed by the trivial
     upper bound.

  ### Barrier pass

  Relativization, natural proofs, algebraization: not applicable (syntactic
  resolution width). Feasible interpolation death: not used. Automatability
  death: checked above. Simulation order: results stay at resolution; they do
  not transfer to Res(k), cutting planes, or Frege by themselves. Rung remains
  below R3, so no R3 plus barrier audit is required before formalize of this
  pin. (Reuse of expansion at R4 is flagged for a future audit when that rung
  opens; not a blocker now.)

  ### Lean module plan (edit existing tree, no duplicate families)

  Add three modules after SizeWidth in `theory/Theory.lean`. Do not edit
  certified R0 or R1 modules. Do not recreate Width.lean or SizeWidth.lean.

  1. `theory/Theory/ProofComplexity/FinGraph.lean`
     Imports: `Theory.ProofComplexity.Resolution` (for Finset style only; no
     derivation facts required). Contents: `FinEdge`, `FinGraph`, `incident`,
     `degree`, `IsRegular`, `edgeBoundary`, `HasExpansion`, elementary lemmas,
     `petersenGraph`, `petersenGraph_regular`, `petersenGraph_expansion`.
  2. `theory/Theory/ProofComplexity/Tseitin.lean`
     Imports: `Theory.ProofComplexity.FinGraph`, `Theory.ProofComplexity.Width`,
     `Theory.ProofComplexity.SizeWidth`. Contents: `Charge`, `oddCharge`,
     `edgeVar`, `tseitinCNF`, `tseitinCNF_unsat`, `tseitinCNF_refutable`,
     complex lemmas, `tseitinWidthDiv`, `tseitin_expander_width_lower_bound`,
     `tseitin_expander_size_lower_bound`,
     `tseitin_petersen_width_beats_cnfWidth`.
  3. `theory/Theory/ProofComplexity/CSExpansion.lean`
     Imports: `Theory.ProofComplexity.Width`, `Theory.ProofComplexity.SizeWidth`.
     Contents: `boundaryClauses`, `HasCSExpansion`, `csWidthDiv`,
     `cs_expansion_width_lower_bound`, `cs_expansion_size_lower_bound`,
     and later `exists_cs_expanding_3cnf`.

  First formalize cluster (smallest, unblocks the rest): FinGraph API plus
  `edgeBoundary` lemmas plus the explicit `petersenGraph` construction (not yet
  the expansion enumeration if time is short; expansion check is cluster 1b).
  Second cluster: `tseitinCNF` and `tseitinCNF_unsat`. Third: complex argument
  and `tseitin_expander_width_lower_bound`. CS modules follow after Tseitin
  width lands, reusing the complex pattern.

  Accepted declarations are appended under a new R2 item 2 header in
  scripts/accepted_declarations.txt only after merge_certified gates.

  Artifacts: this rung memory entry only; no Lean and no test files written.
  Status: success (complete pin; hard gaps remain but are named).
  Pending human gate: accept_prose for the item 2 pin and module plan (recorded
  in session jsonl; not awaited in chat per user blanket continue).
  Next recommended action: formalize FinGraph.lean (FinEdge, FinGraph,
  edgeBoundary, HasExpansion, petersenGraph).

- 2026-08-04 formalize (FinGraph cluster 1, plus Tseitin CNF scaffold): SUCCESS.
  Files verified before edits (no duplicates): existing ProofComplexity modules
  Resolution, PHP, CriticalAssignments, ClauseComplexity, MonotoneWidth,
  MatchingRestriction, MonotoneCalculus, Width, SizeWidth only; ripgrep found
  zero FinGraph, FinEdge, edgeBoundary, HasExpansion, petersenGraph, tseitinCNF,
  oddCharge in theory/. docs/file_structure.md absent; structure from live tree.
  Created theory/Theory/ProofComplexity/FinGraph.lean and Tseitin.lean; wired in
  theory/Theory.lean after SizeWidth.

  FinGraph decls: FinEdge, FinGraph, finEdgeOf, incident, degree, IsRegular,
  edgeBoundary, HasExpansion, mem_incident_iff, incident_subset,
  mem_edgeBoundary_iff, edgeBoundary_subset, edgeBoundary_empty,
  edgeBoundary_univ, edgeBoundary_sdiff_univ, FinEdge.ne_endpoints,
  edgeBoundary_singleton, HasExpansion.degree_ge, petersenGraph,
  petersenGraph_card, petersenGraph_regular. Expansion of Petersen NOT claimed
  (deferred; no placeholder proof). native_decide rejected by axiom gate;
  card and regularity use decide.

  Tseitin scaffold decls: Charge, oddCharge, oddCharge_single,
  oddCharge_single_odd, edgeVar, edgeVar_injective, parityForbidClause,
  vertexParityClauses, tseitinCNF, mem_tseitinCNF_iff,
  clauseVars_parityForbidClause_subset. Unsat and width bound not in this cycle.

  Axiom gate: PASS (scripts/check_axioms.sh). merge_certified auto-recorded per
  user blanket after green gate.
  Artifacts: FinGraph.lean, Tseitin.lean, Theory.lean,
  scripts/accepted_declarations.txt.
  Next recommended action: formalize petersenGraph_expansion (cluster 1b) or
  tseitinCNF_unsat (cluster 2 remainder).

- 2026-08-04 formalize (petersenGraph_expansion and tseitinCNF_unsat): SUCCESS.
  Files verified before edits (no duplicates): FinGraph.lean, Tseitin.lean,
  Width.lean, SizeWidth.lean, Resolution.lean, Theory.lean,
  scripts/accepted_declarations.txt, this rung md. Ripgrep confirmed target
  names petersenGraph_expansion and tseitinCNF_unsat were absent as theorems.
  docs/file_structure.md absent; structure from live ProofComplexity tree.

  Cluster 1b: `petersenGraph_expansion : HasExpansion petersenGraph 1` via
  kernel `decide` over Fin 10 powersets (maxRecDepth raised; no native_decide).
  Honest alpha note: pin alpha = 1 KEPT. Computational check shows min cut
  ratios (3,2,5/3,1.5,1) by size 1..5; alpha = 2 has hundreds of violations,
  so the prove-pin constant is tight and correct, not weakened.

  Cluster 2b: `tseitinCNF_unsat` and `tseitinCNF_refutable` by double counting:
  trueIncident fibers, local parity from forbidding clauses, sum of true
  incident cards = 2 * true edges (even), hence total charge even, contradicting
  oddCharge. Supporting decls: trueIncident, not_clauseSat_parityForbidClause,
  cnfSat_vertexParity_charge, sum_trueIncident_card, sum_charge_even_of_cnfSat.

  Axiom gate: PASS. merge_certified auto-recorded per user blanket.
  Remaining gaps: tseitin_complex_* bridge, tseitin_expander_width_lower_bound,
  size corollary, CSExpansion module, exists_3regular_expander.
  Next recommended action: formalize tseitin complex / width lower bound.

- 2026-08-04 formalize (Tseitin complex bridge cluster 3): PARTIAL SUCCESS.
  Files verified before edits (no duplicates): FinGraph.lean, Tseitin.lean,
  Width.lean, SizeWidth.lean, Resolution.lean, MatchingRestriction.lean,
  Theory.lean, scripts/accepted_declarations.txt, this rung md. Ripgrep found
  no prior tseitin_complex_*, tseitinWidthDiv, cutCovered modules. Extended
  existing Tseitin.lean and FinGraph.lean only.

  FinGraph: connectivity API FinGraph.Adj, Reachable, IsConnected, component,
  edgeBoundary_component, HasExpansion.isConnected (alpha ≥ 1 ⇒ connected).

  Tseitin complex cluster: tseitinWidthDiv := 4 (pin started at 2; raised
  explicitly because set-union growth extracts medium complexes of size at
  least n/4), chargeParity, clauseEdges, clauseFalsify, vertexParitySat,
  cutParity, hypVertex, Derivation.tseitinComplex, pinned
  tseitin_complex_res_subset, tseitin_complex_entails, hyp boundary and
  cutCovered lemmas, tseitin_medium_complex_expands (uses HasExpansion for
  real), exists_medium_tseitin_complex (from full-complex refutations),
  tseitin_width_ge_alpha_mul_quot (bridge: medium + cutCovered ⇒
  α * (n / tseitinWidthDiv) ≤ width).

  Axiom gate: PASS. Full pinned tseitin_expander_width_lower_bound NOT closed:
  still need (1) refutation complex = univ, (2) cutCovered on medium lines
  (not just hypotheses), (3) assemble into the named width LB. With divisor 4,
  Petersen floor is 2 which does not beat cnfWidth 3, so
  tseitin_petersen_width_beats_cnfWidth stays open pending sharper extraction
  or an honest divisor-2 argument.
  Most important thing learned: derivation-support complexes give clean
  res_subset and medium extraction; the hard gap is cut coverage for
  intermediate resolvents, not the growth arithmetic.
  Pending human gate merge_certified (auto per user blanket after green gate).
  Next: prove or formalize cutCovered for derived lines, then
  tseitin_complex_eq_univ, then tseitin_expander_width_lower_bound.

- 2026-08-04 human gate merge_certified: APPROVED by session decision (user blanket
  continue, auto after axiom gate PASS). Tseitin complex bridge cluster accepted
  into the accepted tree. R2 stays prose_accepted. Next: formalize cutCovered for
  intermediate lines and tseitin_complex_eq_univ toward
  tseitin_expander_width_lower_bound.

- 2026-08-04 formalize (semantic complexes, cutCovered, complex=univ, width LB):
  SUCCESS. Kept FinGraph adjEdge helpers; rewrote Tseitin complexes as semantic
  erase-minimal vertex sets (Derivation.tseitinComplex) so cutCovered holds on
  every derived line via BSW flip (cutCovered_of_eraseMinimal,
  tseitin_complex_cutCovered). Proved tseitin_complex_eq_univ on connected graphs
  by cut-edge repair: proper sets have nonempty boundary and are parity-sat
  (exists_vertexParitySat_of_ne_univ), so only univ implies empty.
  Assembled tseitin_expander_width_lower_bound and size corollary from expansion
  (alpha ≥ 1 ⇒ connected). Honest form α * (n / tseitinWidthDiv) with
  tseitinWidthDiv = 4. Petersen floor 2 does not beat cnfWidth 3
  (tseitin_petersen_floor_not_gt_cnfWidth3). Zero sorry. Axiom gate PASS.
  Most important thing learned: syntactic hyp-union complexes break cutCovered
  under resolution; erase-minimal semantic complexes restore it and close univ.
  Pending human gate merge_certified (auto per user blanket after green gate).
  Next: CSExpansion random k-CNF width or sharper medium extraction if a
  Petersen beats-width claim is desired.

- 2026-08-04 human gate merge_certified: APPROVED by session decision (user blanket
  continue, auto after axiom gate PASS). Semantic Tseitin width LB cluster
  accepted into the accepted tree. R2 stays prose_accepted. Next: CSExpansion
  or audit the divisor-4 honesty gap versus pin form (α*n)/div.

- 2026-08-06 formalize (sharp medium floor, Heawood scaffold, CSExpansion API):
  SUCCESS (partial on full non-vacuity). Files verified before edits (no
  duplicates): FinGraph.lean, Tseitin.lean, Width.lean, SizeWidth.lean,
  Theory.lean, this rung md; CSExpansion.lean did not exist and was created per
  pin. Ripgrep confirmed no prior HasCSExpansion, boundaryClauses, csWidthDiv,
  heawoodGraph, tseitinMediumFloor.

  Tseitin: sharpened medium extraction to tseitinMediumFloor n = (n/2+2)/2;
  width and size LBs now use the sharp floor; coarse α*(n/tseitinWidthDiv)
  kept as corollary. Regular-degree cnfWidth lemmas certified.
  FinGraph: heawoodGraph (GP(7,2)) construction, card 21, 3-regular, singleton
  boundary. HasExpansion heawoodGraph 1 deferred: kernel decide over Fin 14
  stalled (16+ min); no fake claim. Numeric non-vacuity:
  tseitin_heawood_width_beats_cnfWidth (floor 4 > cnfWidth 3); coarse Heawood
  and Petersen floors still do not beat under div 4. Conditional
  tseitin_heawood_width_ge_four_of_expansion recorded.

  CSExpansion.lean first cluster: clauseSupport, cnfSupport, boundaryClauses,
  HasCSExpansion, csWidthDiv, csWidthFloor, statement shapes
  CSExpansionWidthLowerBoundStatement / Size, floor-zero trivial case,
  singleton_mem_boundaryClauses. Full cs_expansion_width_lower_bound (complex
  growth) not closed this cycle.

  Axiom gate PASS. Zero sorry. merge_certified auto per user blanket.
  Most important thing learned: sharp BSW union floor lifts Heawood numeric
  beat to 4>3, but full expander non-vacuity still needs a finishing
  HasExpansion proof on n≥14 (decide too heavy as written).
  Next: heawoodGraph_expansion (combinatorial or lighter kernel) then
  cs_expansion_width_lower_bound complex bridge.

- 2026-08-06 human gate merge_certified: APPROVED by session decision (user
  blanket continue, auto after axiom gate PASS). Sharp medium floor, Heawood
  scaffold, and CSExpansion API cluster accepted. R2 stays prose_accepted.

- 2026-08-09 formalize (heawoodGraph_expansion and unconditional Heawood apps):
  SUCCESS. Card-stratified Finset decide stalled; replaced with bitmask kernel
  check `(List.range 16384).all heawoodMaskExpanding` via `decide` (not
  native_decide), bridged by finsetToMask, bitCount, and list cut equality.
  Certified `heawoodGraph_expansion : HasExpansion heawoodGraph 1`.
  Tseitin: unconditional `tseitin_heawood_width_ge_four`,
  `tseitin_heawood_size_lower_bound`, `tseitin_heawood_width_floor_gt_cnfWidth`
  (sharp floor 4 beats cnfWidth 3). CSExpansion: boundary complement lemma and
  alpha-zero floor packaging. Axiom gate PASS. Zero sorry.
  Most important thing learned: Fin 14 Finset decide thrash; Nat bitmask
  List.all decide finishes in minutes when only one lean job runs.
  Next: formalize `cs_expansion_width_lower_bound` complex bridge and
  `exists_cs_expanding_3cnf`.

- 2026-08-09 human gate merge_certified: APPROVED by session decision (user
  blanket continue, auto after axiom gate PASS). Heawood expansion cluster
  accepted. R2 stays prose_accepted (item 2 CS width LB still open).

- 2026-08-09 formalize (CS complex infrastructure toward
  cs_expansion_width_lower_bound): PARTIAL. Accepted: csSubCNF, csImplies,
  IsEraseMinimalCSComplex, chooseEraseMinimal, Derivation.csComplex with
  hyp or res indexing, csComplex_subset_cnfSupport, csComplex_res_subset,
  csSubCNF_unsat_of_eraseMinimal_empty, size packaging from a width oracle.
  Frontier (sorry, quoted for next cycle):
  `boundaryCovered_of_eraseMinimal`, `exists_medium_cs_complex`,
  `CSExpansionFrontier.cs_expansion_width_lower_bound`,
  `exists_cs_expanding_3cnf`. Axiom gate PASS on accepted decls.
  Most important thing learned: CS empty-clause complex gives unsat sub-CNF
  for free; the hard gap is the clause-crossing flip that injects boundary
  clauses into derived-clause variables (Tseitin used edgeVar injectivity).
  Next: formalize boundaryCovered_of_eraseMinimal then medium extraction.

- 2026-08-09 human gate merge_certified: APPROVED by session decision (user
  blanket continue, auto after axiom gate PASS). CS complex infrastructure
  cluster accepted. R2 stays prose_accepted.

- 2026-08-09 formalize (BSW clause-set complexes and coverage): PARTIAL to
  SUCCESS on the coverage cluster. Accepted: `clauseSetBoundary`,
  `csClauseImplies`, erase-minimal axiom complexes, flip lemmas,
  `clauseSetBoundary_subset_clauseVars` (OR sensitivity plus critical
  assignment), card bound, `Derivation.csClauseComplex` with hyp or res
  indexing, `cs_clause_complex_boundary_le_width`, medium extraction
  `exists_medium_cs_clause_complex_of_large`. Frontier (sorry): variable-side
  `boundaryCovered_of_eraseMinimal`, pinned
  `CSExpansionFrontier.cs_expansion_width_lower_bound` (bridge gap between
  variable-side `HasCSExpansion` and axiom-set boundary), 
  `exists_cs_expanding_3cnf`. Axiom gate PASS.
  Most important thing learned: random k-CNF width uses axiom-set measure μ
  and variables in exactly one axiom, not variable-set `boundaryClauses`;
  pinning the width LB still needs clause expansion or a reduction, plus
  matchability so μ(empty) is large.
  Next: bridge HasCSExpansion to clause-set expansion or restate the pin,
  then close width LB and existence.

- 2026-08-09 human gate merge_certified: APPROVED by session decision (user
  blanket continue, auto after axiom gate PASS). BSW clause-set coverage
  cluster accepted. R2 stays prose_accepted (pinned CS width LB still open).

- 2026-08-09 formalize (BSW matchability and clause-set width LB): SUCCESS on
  the clause-set packaging. Accepted: `IsCSMatchable`, `HasCSClauseExpansion`,
  `csClauseWidthFloor`, `csClauseComplex_card_gt_of_matchable`,
  `exists_medium_cs_clause_complex_thresh`,
  `cs_clause_expansion_width_lower_bound`, size corollary via BSW.
  Frontier unchanged for pinned names: variable-side
  `CSExpansionFrontier.cs_expansion_width_lower_bound` under `HasCSExpansion`,
  and `exists_cs_expanding_3cnf`. Axiom gate PASS.
  Most important thing learned: the informative CS width machine is matchability
  plus axiom-set boundary expansion; the pin's variable-side `boundaryClauses`
  hypothesis is a different combinatorial object and needs a separate reduction
  or a pin restatement.
  Next: inhabit `IsCSMatchable` and `HasCSClauseExpansion` (existence), or
  reduce pinned `HasCSExpansion` to the clause-set machine.

- 2026-08-09 human gate merge_certified: APPROVED by session decision (user
  blanket continue, auto after axiom gate PASS). Clause-set width LB cluster
  accepted. R2 stays prose_accepted (pinned HasCSExpansion name and existence
  still open).

- 2026-08-09 audit (CS expansion pin versus certified BSW packaging): SUCCESS
  with an adverse hygiene verdict on item 2 family (b). Checklist:
  1. Relativization: not applicable (syntactic resolution width).
  2. Natural proofs analogue: not applicable at resolution.
  3. Algebraization: not applicable.
  4. Interpolation death: not applicable.
  5. Simulation order: respected (resolution only).
  6. Statement hygiene: FAIL on the CS pin shape. The 2026-08-04 pin froze
     `HasCSExpansion` with variable cut `boundaryClauses`. Ben-Sasson and
     Wigderson (and the lecture packaging used for random k-CNF) use axiom-set
     measure μ and `clauseSetBoundary` (variables in exactly one axiom of a
     minimal implying set), plus matchability of small axiom sets. Lean now
     certifies that packaging as `IsCSMatchable`, `HasCSClauseExpansion`, and
     `cs_clause_expansion_width_lower_bound`. Variable-side
     `boundaryCovered_of_eraseMinimal` is not the BSW coverage lemma and is
     false for the empty clause on erase-minimal variable complexes. Chasing
     `CSExpansionFrontier.cs_expansion_width_lower_bound` under the frozen
     variable-side hypothesis is therefore the wrong critical path.
  7. Stop conditions: `exists_cs_expanding_3cnf` under variable-side expansion
     has been deferred as hard probabilistic across multiple formalize cycles;
     an informative finite witness search for the clause-set hypotheses also
     failed at small n (needs expander-scale bipartite expansion). Do not spend
     another formalize cycle on the variable-side Frontier name.
  Strongest objection: the pin and the certified machine disagree on the
  combinatorial object. Remedy: prove-cycle pin restatement that adopts
  `IsCSMatchable` and `HasCSClauseExpansion` (and `csClauseWidthFloor`) as the
  R2 item 2 CS targets, keeps `exists_cs_expanding_3cnf` but restated for those
  hypotheses, and demotes variable-side `HasCSExpansion` to an optional lemma
  or deletes it from the critical path.
  Next: prove (restate CS pin to clause-set packaging).

- 2026-08-09 prove (restate R2 item 2 CS pin to clause-set BSW packaging):
  SUCCESS. Prose only; no Lean this cycle. Supersedes the 2026-08-04 variable-side
  `HasCSExpansion` / `boundaryClauses` pin for family (b), per the 2026-08-09
  audit. The width machine under the restated pin is already certified in
  `CSExpansion.lean`; this cycle freezes names and quantifiers only.

  ### Restated statement (all quantifiers explicit)

  Namespace `SATurday.ProofComplexity`. Objects from Resolution.lean and the
  certified CSExpansion.lean API.

  Definitions (already in Lean; pin adopts these names):

  1. `clauseSetBoundary (G : Finset Clause) : Finset ℕ` is the set of variables
     that appear in the support of exactly one clause of `G`.
  2. `IsCSMatchable (F : CNF) (r : ℕ)` means: for every `G : Finset Clause`, if
     `G ⊆ F` and `G.card ≤ r`, then `Satisfiable G`.
  3. `HasCSClauseExpansion (F : CNF) (r α : ℕ)` means: for every `G : Finset Clause`,
     if `G ⊆ F` and `r / 2 ≤ G.card` and `G.card ≤ r`, then
     `α * G.card ≤ (clauseSetBoundary G).card`.
  4. `csClauseWidthFloor (r α : ℕ) := α * (r / 2)`.

  Width lower bound (critical path; certified):

  - Target name `cs_clause_expansion_width_lower_bound` (already proved):
    for every `F : CNF` and every `r α : ℕ`, if `IsCSMatchable F r` and
    `HasCSClauseExpansion F r α` and `2 ≤ r`, then for every
    `d : Derivation F (∅ : Clause)`,
    `csClauseWidthFloor r α ≤ d.width`.
  - Size corollary name `cs_clause_expansion_size_lower_bound` (already proved):
    same hypotheses imply the BSW size lower bound at
    `W := csClauseWidthFloor r α`.

  Argument core (known, Ben-Sasson and Wigderson 2001; adaptation already in Lean):
  matchability forces every erase-minimal axiom complex for the empty clause to
  have size greater than `r`; medium extraction yields a derived clause whose
  complex `G` satisfies `(r + 1) / 2 ≤ G.card ≤ r`; clause-set expansion gives
  `α * G.card ≤ (clauseSetBoundary G).card`; coverage
  `clauseSetBoundary_subset_clauseVars` gives
  `(clauseSetBoundary G).card ≤ C.card ≤ d.width`.

  Existence (still open; restated target):

  - Target name `exists_cs_clause_expanding_3cnf` (replaces
    `exists_cs_expanding_3cnf` on the critical path):
    for every `N : ℕ`, there exist `n ≥ N`, `F : CNF`, and `r α : ℕ` such that
    `(cnfVars F).card = n`, `cnfWidth F ≤ 3`, `α = 1`, `r = n / 4` (constants
    may be tightened when the probabilistic calculation is fixed), 
    `IsCSMatchable F r`, `HasCSClauseExpansion F r α`, `¬ Satisfiable F`, and
    `cnfWidth F < csClauseWidthFloor r α`.
  - Classification: known (Chvatal and Szemeredi; Ben-Sasson and Wigderson),
    adaptation into Lean. Gap class: hard. Small n searches found no informative
    witness; expect expander-scale random 3-CNF.

  Demoted (not on the critical path):

  - Variable-side `HasCSExpansion`, `boundaryClauses`, `csWidthFloor`, and
    Frontier `cs_expansion_width_lower_bound` under those names. They may remain
    as optional API, but no further formalize cycles should target them unless a
    later prove cycle reopens a reduction.

  ### Non vacuity under the restated pin

  1. Width machine inhabited conditionally: any `F` meeting matchability and
     clause-set expansion with `2 ≤ r` yields a width lower bound for every
     refutation (certified).
  2. Informative instance: requires `exists_cs_clause_expanding_3cnf` so that
     `cnfWidth F < csClauseWidthFloor r α` for infinitely many sizes. Open.
  3. Tseitin Heawood remains the certified informative witness for family (a);
     it does not substitute for CS existence.

  ### Gap list

  1. Probabilistic existence of matchable expanding unsatisfiable 3-CNFs at
     scale `n` with informative floor. Gap class: hard.
  2. Locking exact constants (`r = n / 4`, density) to a published calculation.
     Gap class: routine once a reference inequality is chosen.
  3. Optional cleanup: move obsolete variable-side Frontier theorems out of the
     critical path documentation only. Gap class: routine.

  ### Self-adversarial pass

  - Quantifiers: width LB is universal in refutations and conditional on
    discrete hypotheses; no claim that a fixed DIMACS seed is hard.
  - Off by one: medium extraction uses `(r + 1) / 2` while expansion asks
    `r / 2 ≤ G.card`; in natural numbers `(r + 1) / 2 ≥ r / 2`, so the handoff
    is safe (already checked in Lean).
  - Hidden uniformity: existence must produce one `F` per `N` with both
    matchability and expansion; failing either breaks informativeness.
  - Does not secretly claim NP versus coNP or climb past resolution.
  - Barrier audit: resolution level; classical barriers not applicable.

  Most important thing learned: restating the pin removes a false critical path
  without inventing new math; the remaining CS work is existence only.
  Next: formalize `exists_cs_clause_expanding_3cnf` (or a finite informative
  witness if one appears), else begin R5 bridge formalization in parallel.

- 2026-08-09 human gate accept_prose: APPROVED by session decision (user
  blanket continue). Restated CS clause-set pin accepted for formalization of
  remaining existence only. R2 stays prose_accepted.
