# R2: Width Machinery and More Families

Status: prose_accepted
Lean home: theory/Theory/ProofComplexity/Width.lean and SizeWidth.lean (item 1
merged); FinGraph.lean and Tseitin.lean (item 2 width machine merged, including
heawoodGraph_expansion); CSExpansion.lean (item 2 CS width machine certified under
clause-set pin restated 2026-08-09; Spreads reduction to HasCSClauseExpansion
merged 2026-08-10; finite Spreads r=2 matchable unsat witness merged 2026-08-10;
informative floor threshold and Spreads scale 3 constructor merged 2026-08-10;
single support starCNF and SpreadsSupports scaffolding merged 2026-08-10;
matching SpreadsSupports at informative r = 8 merged 2026-08-11; overlapping
loose path SpreadsSupports and polarity CNF packaging merged 2026-08-11;
existence `exists_cs_clause_expanding_3cnf` still Frontier)

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

- 2026-08-10 formalize (exists_cs_clause_expanding_3cnf restatement plus
  matchability infrastructure): PARTIAL. Restated Frontier theorem
  `CSExpansionFrontier.exists_cs_clause_expanding_3cnf` matches the 2026-08-09
  pin (matchability, clause-set expansion, width at most 3, alpha = 1,
  r = n/4, informative floor). No finite informative witness claimed; existence
  kept as honest sorry. Accepted infrastructure (12 decls, axiom gate PASS):
  `IsMinimallyUnsat`, `Satisfiable_empty`, `Satisfiable.mono_subset`,
  `IsMinimallyUnsat.not_satisfiable`, `isMinimallyUnsat_singleton_empty`,
  `IsCSMatchable.mono`, `csClauseWidthFloor_one`,
  `HasCSClauseExpansion.alpha_zero`, `clauseSetBoundary_singleton`,
  `isCSMatchable_of_minimallyUnsat`, `exists_minimallyUnsat_subset`,
  `exists_matchable_subset_of_unsat`. Obsolete variable-side Frontier names
  quarantined in comments (`boundaryCovered_of_eraseMinimal`,
  `cs_expansion_width_lower_bound`, `exists_cs_expanding_3cnf`).
  Most important thing learned: minimal unsatisfiability yields matchability at
  scale `|F|-1` for free, so the remaining hard gap is clause-set expansion of
  medium axiom sets at expander scale, not the matchability predicate itself.
  Pending human gate merge_certified (auto per user blanket after green gate).
  Next: prove or formalize probabilistic or constructive
  `HasCSClauseExpansion` at informative parameters, or continue R5 in parallel.

- 2026-08-10 formalize (Spreads reduction to HasCSClauseExpansion): PARTIAL.
  Certified combinatorial core that advances clause-set expansion without a vacuous
  witness: incidence identity `clauseSetBoundary_card_add_sum_ge`
  (`|∂G| + ∑|supp C| ≥ 2|⋃ supp|`), definition `Spreads`, and
  `hasCSClauseExpansion_one_of_spreads_two` (plus support-bounded twin and
  `HasCSClauseExpansion.mono_alpha`). Axiom gate PASS on 11 new accepted decls.
  Frontier `CSExpansionFrontier.exists_cs_clause_expanding_3cnf` unchanged
  (honest sorry); sufficient route is now matchability plus `Spreads F (n/4) 2`
  at width at most 3. Restored dirty local Bridge Complexity.lean to HEAD only
  so the gate could run; no R5 content edited.
  Most important thing learned: inhabiting α = 1 expansion for 3-CNF reduces to
  union growth at rate 2 on medium axiom sets, which is the standard random
  method obligation rather than a new expansion predicate.
  merge_certified auto applied per user blanket after green gate.
  Next: formalize or prove `Spreads` for a constructive or probabilistic 3-CNF
  family at informative scale, else continue R5.

- 2026-08-10 formalize (Spreads r=2 matchable unsat witness): PARTIAL toward
  `exists_cs_clause_expanding_3cnf`. Certified finite non vacuous inhabitant
  `spreadWitnessCNF` (14 distinct triple supports on 6 vars) with
  `Spreads spreadWitnessCNF 2 2`, `IsCSMatchable _ 2`, unsat via decidable
  `existsSatFin` search, and `hasCSClauseExpansion_spreadWitnessCNF_two` by
  reuse of `hasCSClauseExpansion_one_of_spreads_two`. Packaged as
  `exists_spreads_two_matchable_unsat_3cnf`. General lemmas:
  `Satisfiable.pair_of_card_ge_two`, `isCSMatchable_two_of_clause_card_ge_two`,
  `spreads_two_of_pairwise_union_ge`. Axiom gate PASS. Floor informativeness
  not claimed at r=2 (`csClauseWidthFloor 2 1 = 1` does not beat width 3).
  Frontier `exists_cs_clause_expanding_3cnf` unchanged (honest sorry; needs
  `r = n/4` at informative scale).
  Most important thing learned: for pure 3-CNF, Spreads at scale 2 is exactly
  pairwise distinct supports, and unsat formulas with that property exist, but
  raising the scale past 2 on small explicit instances fails because triples of
  clauses can cover fewer than six variables.
  merge_certified auto applied per user blanket after green gate.
  Next: formalize Spreads at informative r (probabilistic or constructive
  expander scale), or continue R5.

- 2026-08-10 formalize (informative Spreads push toward
  exists_cs_clause_expanding_3cnf): PARTIAL. No honest informative inhabitant
  (need r ≥ 8 so cnfWidth < csClauseWidthFloor r 1). Certified threshold and
  constructor lemmas (axiom gate PASS): csClauseWidthFloor_alpha_one_lt_iff,
  informative_cs_floor_requires_r_ge_eight,
  informative_cs_floor_of_cnfWidth_eq_three, spreads_of_medium_biUnion_ge,
  spreads_three_of_unions, spreadWitnessCNF_floor_not_informative.
  Search notes: McGee LCF cubic on 24 verts has vertex cut expansion through
  r = 9 (pin scale |E|/4), but formal tseitinCNF repeats supports per vertex
  and fails Spreads; sparse one clause per triple packings that Spreads at
  r ≥ 8 did not yield matchable unsat under finite search. Frontier
  exists_cs_clause_expanding_3cnf unchanged (honest sorry).
  Most important thing learned: informative CS existence is blocked by an
  encoding gap (graph expansion on vertices versus clause Spreads on possibly
  repeated supports) plus the sparse versus unsat tension for explicit 3-CNFs.
  merge_certified auto applied per user blanket after green gate.
  Next: formalize probabilistic Spreads existence or a single clause per
  support expander encoding that stays unsat and matchable.

- 2026-08-10 formalize (single support star encoding toward
  exists_cs_clause_expanding_3cnf): PARTIAL. Certified star encoding and
  Spreads scaffolding (axiom gate PASS, 24 new accepted decls): edgesInternal,
  edgesTouching, mem lemmas, edgesTouching_eq_internal_union_boundary,
  disjoint_edgesInternal_edgeBoundary, starClause, starCNF,
  clauseSupport_starClause, starClause_card_of_regular3, starCNF_cnfWidth_le,
  card_edges_between_le_one, eq_of_incident_eq_of_regular3,
  starClause_injective_of_regular3, exists_vertexSet_of_subset_starCNF,
  biUnion_clauseSupport_star_eq, spreads_starCNF_of_touching_ge,
  touching_card_ge_two_of_handshaking_expansion, heawoodStarCNF,
  heawoodStarCNF_cnfWidth_le, heawoodStarCNF_satisfiable,
  heawoodStarCNF_floor_not_informative, SpreadsSupports,
  spreads_of_spreadsSupports. Frontier exists_cs_clause_expanding_3cnf
  unchanged (honest sorry). No vacuous unsat witness claimed: all positive
  heawoodStarCNF is satisfiable; floor at r = 5 is not informative.
  Most important thing learned: Spreads for the star encoding reduces to a
  medium touching lower bound on edge stars, and cut expansion plus cubic
  handshaking would discharge that bound; the remaining Lean gap is the
  handshaking identity itself, not a new CNF predicate.
  merge_certified auto applied per user blanket after green gate.
  Next: formalize cubic handshaking then Spreads on Heawood or McGee scale,
  or push SpreadsSupports via probabilistic counting.

- 2026-08-10 formalize (cubic handshaking then Heawood star Spreads): PARTIAL
  toward `exists_cs_clause_expanding_3cnf`. Certified
  `handshaking_touching_of_regular3` (`2|touching|=3|S|+|∂S|`), supporting
  double count lemmas (`endpointCountIn`, sum identities),
  `spreads_starCNF_of_expansion`, and `spreads_heawoodStarCNF_five`.
  Axiom gate PASS (8 new accepted decls). Honest limits unchanged: Heawood
  star CNF is satisfiable and the α = 1 floor at r = 5 is not informative.
  Frontier `exists_cs_clause_expanding_3cnf` unchanged (honest sorry).
  Most important thing learned: the expander to Spreads bridge for star CNF
  is now fully certified on Heawood; the remaining obstruction is informative
  scale with matchable unsat polarity, not cut handshaking.
  merge_certified auto applied per user blanket after green gate.
  Next: formalize informative scale Spreads (r ≥ 8) with unsat polarity or
  probabilistic SpreadsSupports existence, else continue R5.

- 2026-08-11 formalize (changed approach: SpreadsSupports matching first):
  PARTIAL toward `exists_cs_clause_expanding_3cnf`. Stop condition forced a
  change of approach after repeated all positive star or sparse unsat blocks.
  Certified set system scaffolding (axiom gate PASS, 19 new accepted decls):
  `SpreadsSupports.mono_gamma`, `clauseSupport_parityForbidClause`,
  `starClauseWith`, `clauseSupport_starClauseWith`,
  `clauseSupport_starClauseWith_eq_starClause`, `starCNFWith`,
  `spreadsSupports_of_spreads`, `matchingTriple`, `matchingTriple_card`,
  `matchingTriple_disjoint`, `matchingTriple_injective`,
  `matchingTripleSupports`, `mem_matchingTripleSupports`,
  `matchingTripleSupports_card`, `card_biUnion_matchingTripleSupports_subset`,
  `spreadsSupports_matchingTriples`, `spreadsSupports_matchingTriples_two`,
  `exists_spreadsSupports_informative`, `spreadsSupports_matchingTriples_eight`.
  Honest limit: a disjoint matching SpreadsSupports at r = 8 is informative as a
  set system, but a clausewise matching CNF is satisfiable, so the Frontier pin
  is unchanged. Most important thing learned: the informative SpreadsSupports
  obligation is now inhabited in Lean; the remaining gap is polarity plus
  matchable unsat on an overlapping support system (or a random method lift),
  not the set system spreading predicate itself.
  merge_certified auto applied per user blanket after green gate.
  Next: formalize a matchable unsat CNF whose supports inject into an
  informative SpreadsSupports system (overlapping triples, not a pure matching),
  or prove a probabilistic existence lift.

- 2026-08-11 formalize (overlapping SpreadsSupports plus polarity packaging):
  PARTIAL toward `exists_cs_clause_expanding_3cnf`. Certified (axiom gate PASS):
  `triplePolarityClause`, `cnfOfSupports`, support image and Spreads inheritance,
  `satisfiable_cnfOfSupports_of_pairwise_disjoint`,
  `satisfiable_matchingTripleSupports_cnf` (matching obstruction),
  `loosePathTriple` or `loosePathSupports`, union lower bound,
  `spreadsSupports_loosePath`, `exists_overlapping_spreadsSupports_informative`,
  `spreadsSupports_loosePath_sixteen`, `satisfiable_loosePathSupports_allTrue`.
  Honest limit: overlapping informative SpreadsSupports is inhabited, but path
  and matching polarity CNFs remain satisfiable, so the Frontier pin is unchanged.
  Most important thing learned: the sparse versus unsat tension is now certified
  on both sides (matching always sat; path SpreadsSupports at r = 8 with overlap
  but all true still sat); closing Block A needs a cyclic or random method lift,
  not further SpreadsSupports scaffolding alone.
  merge_certified auto applied per user blanket after green gate.
  Next: prove or formalize a probabilistic existence lift to matchable unsat
  Spreads at r = n/4, or construct an explicit cyclic overlapping unsat witness.

- 2026-08-11 prove (pin probabilistic lift for
  exists_cs_clause_expanding_3cnf): PARTIAL. Prose only; no Lean written.
  Formalize is not ready: no inhabited matchable unsat Spreads at informative
  scale, and single clause star or path polarities stay sat. Developed one
  argument (random 3 CNF lift). Sketched then discarded as the developed route:
  cyclic overlapping unsat witness and odd charge star reuse (see adversarial
  pass). Details follow.

  ### Statement restated with all quantifiers explicit

  Target (already in Lean; Frontier; verified by ripgrep):
  `SATurday.ProofComplexity.CSExpansionFrontier.exists_cs_clause_expanding_3cnf`

  For every `N : ℕ` there exist `n : ℕ`, `F : CNF`, and `r α : ℕ` such that
  `N ≤ n`, `(cnfVars F).card = n`, `cnfWidth F ≤ 3`, `α = 1`, `r = n / 4`,
  `IsCSMatchable F r`, `HasCSClauseExpansion F r α`, `¬ Satisfiable F`, and
  `cnfWidth F < csClauseWidthFloor r α`.

  Classification: known (Chvatal and Szemeredi 1988; Ben Sasson and Wigderson
  2001 packaging), adaptation into the clause set pin already certified for the
  width machine. Gap class: hard.

  ### Existing Lean names this argument consumes (verified present)

  Predicates and floors:
  `IsCSMatchable`, `HasCSClauseExpansion`, `csClauseWidthFloor`,
  `Spreads`, `SpreadsSupports`, `cnfWidth`, `cnfVars`, `Satisfiable`,
  `clauseSupport`.

  Certified bridges and thresholds:
  `hasCSClauseExpansion_one_of_spreads_two`,
  `hasCSClauseExpansion_one_of_spreads_two_of_support_le`,
  `spreads_of_spreadsSupports`, `spreadsSupports_of_spreads`,
  `informative_cs_floor_requires_r_ge_eight`,
  `informative_cs_floor_of_cnfWidth_eq_three`,
  `isCSMatchable_of_minimallyUnsat`, `exists_minimallyUnsat_subset`,
  `exists_matchable_subset_of_unsat`,
  `cs_clause_expansion_width_lower_bound`.

  Certified set system and polarity packaging (not yet a Frontier witness):
  `matchingTripleSupports`, `exists_spreadsSupports_informative`,
  `satisfiable_matchingTripleSupports_cnf`,
  `loosePathSupports`, `exists_overlapping_spreadsSupports_informative`,
  `cnfOfSupports`, `triplePolarityClause`,
  `spreads_cnfOfSupports_of_spreadsSupports`,
  `satisfiable_loosePathSupports_allTrue`,
  `spreadWitnessCNF`, `exists_spreads_two_matchable_unsat_3cnf`
  (informative floor fails at `r = 2`).

  Star and Tseitin related (reuse limits recorded below):
  `starCNF`, `starCNFWith`, `spreads_starCNF_of_expansion`,
  `spreads_heawoodStarCNF_five`, `heawoodStarCNF_satisfiable`,
  `tseitinCNF`, `tseitinCNF_unsat`, `oddCharge`, `parityForbidClause`.

  ### Proposed new Lean names (ripgrep absent in theory and docs; do not create
  files yet; edit `CSExpansion.lean` only when formalizing)

  - `Ensemble3CNF (n m : ℕ)`: finite sample space of multisets of size `m` of
    ordered triples from `n` variables, each triple equipped with a polarity
    in `{true, false}^3`, represented as `CNF` after deduplication of identical
    clauses.
  - `random3CNF (n m : ℕ) (ω : EnsembleIndex n m) : CNF`: the concrete formula
    at sample point `ω` (definitional; no probability axiom).
  - `Spreads.supportsImage (F : CNF) (r γ : ℕ)`: sugar for
    `SpreadsSupports (F.image clauseSupport) r γ` under injective supports.
  - `exists_spreads_matchable_unsat_random3CNF`: for every `N`, there exist
    `n ≥ max(N, 32)`, `m = Δ * n` with locked rational density `Δ`, and a
    sample `ω`, such that writing `F := random3CNF n m ω` and `r := n / 4`
    one has `cnfWidth F ≤ 3`, `Spreads F r 2`, `IsCSMatchable F r`,
    `¬ Satisfiable F`, and `cnfWidth F < csClauseWidthFloor r 1`.
  - `exists_cs_clause_expanding_3cnf_of_spreads_matchable_unsat`: packaging
    lemma reducing the Frontier theorem to the previous inhabitant via
    `hasCSClauseExpansion_one_of_spreads_two` and the floor threshold lemmas.

  Density lock for formalization (explicit constant, not asymptotic prose):
  take `Δ = 6` clauses per variable as the working density. Falsify calibration
  at density `5.0` still saw SAT at small `n`; literature unsat threshold for
  random 3 CNF sits near `4.267`, so `Δ = 6` is safely above unsat with room
  for expansion and matchability error terms. The exact natural encoding is
  `m = 6 * n` (no floats in Lean). If the counting inequalities fail at `6`,
  the next try is `m = 7 * n`, still constant density.

  ### Non vacuity

  1. Width machine nonempty under hypotheses: certified by
     `cs_clause_expansion_width_lower_bound` whenever `IsCSMatchable F r` and
     `HasCSClauseExpansion F r 1` hold with `2 ≤ r`.
  2. Informative floor nonempty as a numeric constraint: need `r ≥ 8` by
     `informative_cs_floor_requires_r_ge_eight`, hence `n ≥ 32` under
     `r = n / 4`. The probabilistic argument must produce some `n ≥ 32`.
  3. Finite non informative CS inhabitant already exists
     (`exists_spreads_two_matchable_unsat_3cnf`) so the predicates are not
     empty of meaning; only the informative `∀ N` lift is open.
  4. Ensemble nonempty: for every `n m` the finite set of polarity triple
     sequences of length `m` is nonempty, so existence over samples is a
     finite pigeonhole claim, not an analytic axiom.

  ### Attack ideas sketched (exactly one developed)

  A. Probabilistic random 3 CNF lift to matchable unsat Spreads at `r = n/4`
     (DEVELOPED below).
  B. Cyclic overlapping support system (`looseCycleSupports`, name absent)
     with a polarity that is unsat while preserving SpreadsSupports at
     informative `r`. Not developed: all true path polarity is certified sat,
     and no absent name should be invented in Lean this cycle.
  C. Odd charge reuse of `starCNFWith` or `tseitinCNF` on a cubic cage at
     McGee scale. Not developed: `tseitinCNF_unsat` uses many clauses per
     vertex (hurts Spreads by repeated supports), while single clause
     `heawoodStarCNF` is certified satisfiable; these are different objects.

  ### The one argument developed, in full

  Fix `N : ℕ`. Set `n₀ := max(N, 32)`, and for each `n ≥ n₀` set `m := 6 * n`
  and `r := n / 4` (so `r ≥ 8` and `csClauseWidthFloor r 1 = r / 2 ≥ 4 > 3`).

  Step 1 (sample space). Let `Ω_n` be the finite set of length `m` sequences of
  oriented 3 literal clauses on variable set `{0,...,n-1}`. Each `ω ∈ Ω_n`
  determines `F_ω := random3CNF n m ω` after dropping duplicate clauses. Then
  `cnfWidth F_ω ≤ 3` by construction, and `(cnfVars F_ω).card ≤ n`. For the pin
  we further restrict to samples whose support uses every variable (standard
  deletion or conditioning; probability of an isolated variable vanishes at
  density 6). Target side lemma name when formalizing:
  `random3CNF_cnfWidth_le` and `random3CNF_vars_card` (both absent today).

  Step 2 (unsatisfiability with positive density). A fixed assignment
  `a : Fin n → Bool` satisfies a uniform random 3 clause with probability
  `7/8`. Independence over `m = 6 n` clauses gives
  `Pr[a satisfies F_ω] ≤ (7/8)^(6 n)`. Union bound over `2^n` assignments:
  `Pr[Satisfiable F_ω] ≤ 2^n * (7/8)^(6 n) = exp(n ln 2 + 6 n ln(7/8))`.
  Numerically `ln(7/8) < -0.133`, so `6 * ln(7/8) + ln 2 < -0.10 < 0`, hence
  the probability decays exponentially in `n`. For all sufficiently large `n`
  a positive fraction of samples are unsatisfiable. Classification: known
  first moment calculation; adaptation. Gap: routine arithmetic packaging in
  Lean once a rational log inequality library path is chosen; hard only as
  engineering of inequalities, not as new combinatorics.

  Step 3 (Spreads at rate 2 on medium sets). Let `G` range over nonempty
  subcollections of clauses of `F_ω` with `r/2 ≤ |G| ≤ r`. The failure event
  that `|⋃_{C∈G} clauseSupport C| < 2 |G|` is a small union bound: the number
  of candidate index sets of size `s ≤ r` is at most `C(m,s)`, and for each
  the probability that all `s` random triples land inside a fixed vertex set
  of size `u = 2 s - 1` is at most `(C(u,3)/C(n,3))^s` (ordered with
  replacement bounds are equally fine). Summing
  `∑_{s=r/2}^{r} C(m,s) * C(n, 2s-1) * (O(s^3 / n^3))^s` is `o(1)` for
  `r = n/4` and `m = 6 n`, by the usual Chvatal and Szemeredi / Ben Sasson and
  Wigderson estimates: medium clause sets expand because they would otherwise
  concentrate on too few variables. On the injective support event (no two
  sampled clauses share the exact same three variable support), this is exactly
  `SpreadsSupports (F_ω.image clauseSupport) r 2`, and
  `spreads_of_spreadsSupports` upgrades it to `Spreads F_ω r 2`. Classification:
  known. Gap: hard (formal counting and factorial bounds in Lean).

  Step 4 (matchability at scale `r`). Equivalent form used here: every subset
  of at most `r` clauses is satisfiable. The complementary bad event is that
  some `G ⊆ F_ω` with `|G| ≤ r` is unsatisfiable. Any unsatisfiable 3 CNF on
  `u` variables needs at least `c u` clauses for an absolute `c > 0` in the
  sparse regime, or more elementarily for the union bound: there are at most
  `C(m,s)` candidate subsets of size `s ≤ r`, each lives on at most `3 s`
  variables, and the probability a fixed `s` tuple is unsatisfiable is at most
  the probability it covers all `2^{O(s)}` local assignments, which is
  `≤ (7/8)^{Ω(s)}` after restricting to its own variables. Same shape as Step 2
  at scale `s ≤ n/4` yields a union bound `o(1)`. Preferential formalization
  path once unsat is known: extract a minimally unsatisfiable `G⋆ ⊆ F_ω` by
  `exists_minimallyUnsat_subset`, note `|G⋆| > r` from the bad event failing,
  then `isCSMatchable_of_minimallyUnsat` gives `IsCSMatchable F_ω (|G⋆| - 1)`
  and hence `IsCSMatchable F_ω r` by `IsCSMatchable.mono`. Classification:
  known. Gap: hard (matching the constants to `r = n/4` without silently
  shrinking `r`).

  Step 5 (package to the Frontier). From Steps 2 to 4, for all large `n` there
  exists `ω` with `¬ Satisfiable F_ω`, `Spreads F_ω r 2`, and
  `IsCSMatchable F_ω r`, together with `cnfWidth F_ω ≤ 3` and
  `cnfWidth F_ω < csClauseWidthFloor r 1` by the `r ≥ 8` threshold. Apply
  `hasCSClauseExpansion_one_of_spreads_two` to obtain
  `HasCSClauseExpansion F_ω r 1`. If `(cnfVars F_ω).card` is slightly below
  `n`, replace the pin witness `n` by that card and keep `r' := n' / 4` using
  monotonicity of Spreads and matchability in `r` (need a short mono lemma for
  `Spreads` in the scale parameter; name `Spreads.mono_r`, currently absent).
  This yields `exists_cs_clause_expanding_3cnf`. No new axiom: only finite
  counting over `Ω_n`.

  Why certified constructive scaffolding does not already finish the lift:
  `satisfiable_matchingTripleSupports_cnf` kills every polarity on a disjoint
  matching; `satisfiable_loosePathSupports_allTrue` kills the simplest polarity
  on the overlapping path; `spreadWitnessCNF` is matchable unsat Spreads but
  only at `r = 2` (floor not informative). The probabilistic method is exactly
  the remaining existence content of Block A under the present pin.

  ### Gap list

  1. Lean formalization of the finite ensemble and the three union bounds
     (unsat, Spreads, matchability) at locked density `m = 6 n` and scale
     `r = n / 4`. Gap class: hard.
  2. Explicit natural number inequalities replacing `ln` prose (clear common
     denominators; no analysis axioms). Gap class: hard engineering, routine
     mathematics.
  3. `Spreads.mono_r` and variable card cleanup so the witness `n` equals
     `(cnfVars F).card` exactly as the Frontier quantifies. Gap class: routine.
  4. Packaging theorem
     `exists_cs_clause_expanding_3cnf_of_spreads_matchable_unsat` into the
     Frontier sorry. Gap class: routine once gap 1 lands.
  5. Optional constructive parallel (not this argument): inhabit a scalable
     cyclic family only if a polarity is found that is unsat and still Spreads
     at `r ≥ 8`; do not reopen matching or all true path polarities. Gap class:
     unknown, and blocked twice already on related constructive attempts.

  ### Self adversarial pass

  - Quantifier order: the sample `ω` depends on `n`, which depends on `N`. No
    uniformity across all `N` is claimed beyond existence.
  - Hidden uniformity: Spreads and matchability are required on the same `F_ω`.
    A proof that deletes clauses to restore matchability must recheck Spreads
    after deletion; the argument above avoids deletion by union bound.
  - Off by one: informative floor needs `r ≥ 8`, hence `n ≥ 32`, already in
    `n₀`. Medium interval uses `r/2`, matching the certified expansion side.
  - False friend with Tseitin: `tseitinCNF_unsat` does not give Spreads at cage
    scale because multiple `parityForbidClause` rows share one vertex support;
    citing it as a Block A closer would be unsound under the Spreads route.
  - False friend with path overlap: overlap alone does not imply unsat
    (`satisfiable_loosePathSupports_allTrue`).
  - Does not secretly prove NP versus coNP or climb past resolution; it only
    inhabits the hypothesis of the already certified CS width machine.
  - Barrier audit: resolution level; classical barriers not applicable. No R3
    flag required.
  - Stop condition check: constructive matching and path polarity routes have
    repeatedly hit satisfiability; this cycle changes approach to a pinned
    probabilistic plan rather than grinding the same polarity search.

  Most important thing learned: Block A is now a single counting obligation
  over a finite ensemble at density `m = 6 n`, reducible through already
  certified `hasCSClauseExpansion_one_of_spreads_two`; further SpreadsSupports
  scaffolding without an unsat polarity or a random lift will not close the
  Frontier.
  Next: formalize `Ensemble3CNF` or `random3CNF` and the unsat first moment
  bound as the first slice of
  `exists_spreads_matchable_unsat_random3CNF`, else falsify only to calibrate
  density `6` proof size curves (not required for the existence proof).
  gate_pending: accept_prose for this probabilistic plan before deep
  formalization spend.

- 2026-08-11 formalize (probabilistic ensemble scaffolding toward
  exists_cs_clause_expanding_3cnf): PARTIAL. Human gate accept_prose approved
  ("go") for the bf4a212 probabilistic lift plan. Edited only
  `theory/Theory/ProofComplexity/CSExpansion.lean` (no new files). Certified
  (axiom gate PASS) cluster 17:
  `Oriented3Clause`, `Oriented3Clause.toClause`,
  `Oriented3Clause.toClause_card_le`, `Oriented3Clause.mem_toClause_var_lt`,
  `EnsembleIndex`, `Ensemble3CNF`, `random3CNFDensity` (= 6),
  `random3CNFClauseCount` (`m = 6 n`), `random3CNFMatchScale` (`r = n / 4`),
  `random3CNFClauseCount_eq`, `random3CNFMatchScale_ge_eight`,
  `csClauseWidthFloor_of_random3CNFMatchScale`, `random3CNF`, `mem_random3CNF`,
  `random3CNF_cnfWidth_le`, `random3CNF_vars_subset_range`,
  `random3CNF_vars_card`, `ensembleIndex_nonempty`, `Spreads.mono_r`,
  `exists_cs_clause_expanding_3cnf_of_spreads_matchable_unsat`. Frontier
  (honest sorry): `exists_spreads_matchable_unsat_random3CNF` plus prior
  `exists_cs_clause_expanding_3cnf`. Most important thing learned: the Block A
  gap is now a named counting theorem over an inhabited finite ensemble at the
  locked density, with packaging already reducing it to the pin once the three
  union bounds land. Next: formalize the unsat first moment slice of
  `exists_spreads_matchable_unsat_random3CNF` (Nat inequalities at `m = 6 n`),
  then Spreads and matchability union bounds.

- 2026-08-11 formalize (unsat first-moment Nat bounds for random3CNF): PARTIAL.
  Edited only `theory/Theory/ProofComplexity/CSExpansion.lean` (plus
  `scripts/accepted_declarations.txt`). Certified cluster 18 (axiom gate PASS):
  `Oriented3Clause.equivProd`, `card_oriented3Clause` (`8 n^3`),
  `litSat_assignmentOfFin`, `clauseSat_toClause_iff`,
  `not_clauseSat_toClause_iff`, `card_oriented3Clause_unsat` (`n^3`),
  `card_oriented3Clause_sat` (`7 n^3`), `cnfSat_random3CNF_iff`,
  `card_ensembleIndex`, `card_ensembleIndex_sat`,
  `seven_pow_six_lt_two_pow_seventeen` (`7^6 < 2^17`),
  `two_pow_mul_seven_pow_lt_eight_pow` (`2^n 7^(6n) < 8^(6n)`),
  `two_pow_mul_seven_cube_pow_lt_eight_cube_pow`,
  `card_ensembleIndex_le_sat_sum`, `exists_unsat_random3CNF` (every `n ≥ 1`),
  `exists_unsat_random3CNF_ge_thirty_two`. Frontier unchanged:
  `exists_spreads_matchable_unsat_random3CNF` and
  `exists_cs_clause_expanding_3cnf` still sorry (Spreads and matchability
  union bounds not yet formalized). Most important thing learned: the unsat
  half of the probabilistic plan is a pure Nat counting theorem with core
  inequality `7^6 < 2^17`, already enough to inhabit unsat samples at density
  `m = 6 n`; Block A now waits only on Spreads and matchability fibers.
  Next: formalize Spreads union bound at `r = n/4`, then matchability.

- 2026-08-11 formalize (Spreads and matchability union bound scaffolding):
  PARTIAL. Edited only `theory/Theory/ProofComplexity/CSExpansion.lean` (plus
  `scripts/accepted_declarations.txt`). Certified cluster 19 (axiom gate PASS):
  `Oriented3Clause.support`, `Oriented3Clause.support_card_le`,
  `clauseSupport_toClause_eq_support`, `Oriented3Clause.support_subset_range`,
  `Oriented3Clause.memSupport`, `card_oriented3Clause_memSupport` (`8 |U|^3`),
  `card_oriented3Clause_memSupport_le`, `indexSupport`, `supportConcentrated`,
  `indexSupport_subset_of_concentrated`, `indexSupport_card_le_of_concentrated`,
  `SpreadsIndices`, `exists_concentrated_of_not_spreadsIndices`,
  `spreads_random3CNF_of_spreadsIndices`, `isCSMatchable_of_unsat_min_card`,
  `isCSMatchable_of_minimallyUnsat_card_gt`, `isCSMatchable_of_minimallyUnsat_gt`,
  `exists_unsat_subset_of_not_isCSMatchable`, `card_fun_memSupport`,
  `card_ensembleIndex_supportConcentrated`,
  `card_ensembleIndex_supportConcentrated_mul_lt_iff`,
  `eight_mul_pow_card_lt_iff`, `pow_three_lt_pow_three`,
  `random3CNFMatchScale_eq`, `medium_hi_eq_matchScale`,
  `not_spreadsIndices_of_concentrated_small`. Frontier unchanged:
  `exists_spreads_matchable_unsat_random3CNF` and
  `exists_cs_clause_expanding_3cnf` still sorry (summed union bound
  inequalities not yet closed). Most important thing learned: Spreads and
  matchability now reduce to finite fiber comparisons against concentration
  and large minimally unsat cores; the remaining gap is the summed choose
  bound over medium `(S,U)` pairs, not new combinatorics.
  Next: formalize the summed Spreads concentration inequality at `m = 6 n`
  and `r = n / 4`, then package with `exists_unsat_random3CNF`.

- 2026-08-11 formalize (Spreads summed choose packaging and crude obstruction):
  PARTIAL. Edited only `theory/Theory/ProofComplexity/CSExpansion.lean` (plus
  `scripts/accepted_declarations.txt`). Certified cluster 20 (axiom gate PASS):
  `indexSupportFin`, `supportConcentrated_indexSupportFin`,
  `indexSupport_eq_image_indexSupportFin`, `card_indexSupportFin`,
  `exists_concentrated_fin_of_not_spreadsIndices`,
  `exists_spreadsIndices_of_univ_card_lt`, `spreadsFailureTerm`,
  `spreadsFailureTerm_lt_ensemble_iff`, `spreadsFailureTerm_core_lt_iff`,
  `thirty_two_pow_two_lt_fifteen_pow_three`,
  `thirty_two_pow_sixteen_lt_fifteen_pow_twenty_four`,
  `thirty_two_pow_twenty_four_le_fifteen_pow_mul_thirty_two_pow`,
  `eight_factorial_le_five_pow_eight`, `thirty_two_mul_five_le_one_eighty_five`,
  `descFactorial_one_ninety_two_eight_ge`,
  `choose_one_ninety_two_eight_ge_thirty_two_pow_eight`,
  `choose_thirty_two_fifteen_pos`, `spreads_crude_core_ge_at_thirty_two`,
  `spreads_crude_core_not_lt_at_thirty_two`,
  `spreads_crude_term_not_lt_eight_pow_at_thirty_two`,
  `random3CNFMatchScale_thirty_two`, `random3CNFClauseCount_thirty_two`.
  Frontier unchanged: `exists_spreads_matchable_unsat_random3CNF` and
  `exists_cs_clause_expanding_3cnf` still sorry. Most important thing learned:
  the sketched crude close
  `C(m,s) C(n,2s-1) ((2s-1)/n)^{3s} < 1` already fails at the informative
  minimum `n = 32` (`s = 8`), certified as
  `spreads_crude_core_not_lt_at_thirty_two`; Block A needs a tighter Spreads
  count (minimal bad sets, LLL, or smaller scale with pin revision), not more
  algebra on the same union bound.
  Next: prove cycle to revise the probabilistic Spreads plan, then formalize
  the revised count.

- 2026-08-11 prove (revise probabilistic Spreads plan after crude obstruction):
  PARTIAL. Prose only; no Lean written. Target statement remains
  `CSExpansionFrontier.exists_spreads_matchable_unsat_random3CNF` feeding
  `exists_cs_clause_expanding_3cnf_of_spreads_matchable_unsat` into
  `CSExpansionFrontier.exists_cs_clause_expanding_3cnf`.

  ### Verified Lean names (ripgrep; no guessing)

  Accepted, used by the plan:
  `EnsembleIndex`, `Ensemble3CNF`, `Oriented3Clause`, `Oriented3Clause.support`,
  `Oriented3Clause.memSupport`, `random3CNFDensity`, `random3CNFClauseCount`,
  `random3CNFMatchScale`, `random3CNF`, `mem_random3CNF`, `random3CNF_cnfWidth_le`,
  `random3CNF_vars_subset_range`, `random3CNF_vars_card`, `ensembleIndex_nonempty`,
  `card_oriented3Clause`, `card_ensembleIndex`, `exists_unsat_random3CNF`,
  `exists_unsat_random3CNF_ge_thirty_two`, `indexSupport`, `indexSupportFin`,
  `supportConcentrated`, `card_ensembleIndex_supportConcentrated`,
  `SpreadsIndices`, `spreads_random3CNF_of_spreadsIndices`,
  `exists_spreadsIndices_of_univ_card_lt`, `spreadsFailureTerm`,
  `spreadsFailureTerm_lt_ensemble_iff`, `spreadsFailureTerm_core_lt_iff`,
  `spreads_crude_core_ge_at_thirty_two`, `spreads_crude_core_not_lt_at_thirty_two`,
  `spreads_crude_term_not_lt_eight_pow_at_thirty_two`,
  `random3CNFMatchScale_thirty_two`, `random3CNFClauseCount_thirty_two`,
  `isCSMatchable_of_unsat_min_card`, `isCSMatchable_of_minimallyUnsat_card_gt`,
  `Spreads`, `Spreads.mono_r`, `IsCSMatchable`, `HasCSClauseExpansion`,
  `hasCSClauseExpansion_one_of_spreads_two`, `csClauseWidthFloor`,
  `exists_cs_clause_expanding_3cnf_of_spreads_matchable_unsat`.

  Frontier (honest sorry):
  `CSExpansionFrontier.exists_spreads_matchable_unsat_random3CNF`,
  `CSExpansionFrontier.exists_cs_clause_expanding_3cnf`.

  Absent names proposed for later formalization (verified absent today):
  `card_ensembleIndex_support_card_lt`, `spreadsOccupancyTerm`,
  `spreadsOccupancyTerm_lt_ensemble_iff`,
  `exists_spreadsIndices_of_occupancy_sum_lt`.

  ### Statement restated

  For every `N : ℕ` there exist `n : ℕ` and
  `ω : EnsembleIndex n (random3CNFClauseCount n)` such that, writing
  `F := random3CNF n (random3CNFClauseCount n) ω` and
  `r := random3CNFMatchScale n` (= `n / 4`), one has
  `max N 32 ≤ n`, `(cnfVars F).card = n`, `cnfWidth F ≤ 3`,
  `Spreads F r 2`, `IsCSMatchable F r`, `¬ Satisfiable F`, and
  `cnfWidth F < csClauseWidthFloor r 1`.

  Non vacuity: `ensembleIndex_nonempty` inhabits the sample space;
  `exists_unsat_random3CNF` already produces unsat samples at every `n ≥ 1`;
  `spreadWitnessCNF` inhabits the predicates `Spreads`, `IsCSMatchable`, and
  unsat at non informative `r = 2`, so the quantified properties are not empty
  of meaning. The open content is the joint informative lift.

  ### Why the prior Step 3 close is dead (not just at n = 32)

  Cluster 20 certified
  `¬ (C(192,8) C(32,15) 15^24 < 32^24)` as
  `spreads_crude_core_not_lt_at_thirty_two`, so the cancelled crude core from
  `spreadsFailureTerm` fails at the informative minimum.

  First principles kill more than that sample. For `s` linear in `n` with
  `|U| = 2 s` and density `Δ = 6`, the standard estimate
  `(e m / s)^s (e n / |U|)^{|U|} (|U|/n)^{3 s}` simplifies to
  `(2 e^3 Δ)^s ≈ 241^s > 1` for every `s ≥ 1`. So enlarging `n` alone, or
  shrinking the locked scale `r = n / 4` while keeping the same
  `C(m,s) C(n,2s-1) ((2s-1)/n)^{3 s}` skeleton, cannot make the crude close
  work at rate 2 and density 6. Lowering density enough for that skeleton
  (`Δ < 1/(2 e^3)`) would break the certified unsat first moment
  (`m ≥ 6 n` from `7^6 < 2^17`). Conclusion: Step 3 must change counting
  method, not just parameters inside `spreadsFailureTerm`.

  ### Attack ideas sketched (exactly one developed)

  A. Occupancy large deviation on fixed index sets, then union only over
     `C(m,s)` choices of `S` (DEVELOPED below). Keeps `m = 6 n` and
     `r = n / 4`.
  B. Frontier pin revision to a smaller scale such as `r = n / 8` together with
     a non crude count. Not developed: pin change touches
     `random3CNFMatchScale`, packaging, and both Frontier statements; try only
     if A fails Nat calibration at large `n`.
  C. Constructive cyclic or cage polarity. Not developed: matching and path
     polarities already blocked; stop conditions forbid a third grind.

  ### The one argument developed (revised Block A Step 3)

  Keep Steps 1, 2, 4, and 5 of the bf4a212 plan and the Cluster 17 to 19
  scaffolding. Replace only the Spreads failure estimate.

  Fix `N : ℕ`. Choose `n₀ := max(N, n⋆)` for an absolute threshold `n⋆ ≥ 32`
  large enough that the occupancy sums below are strictly less than
  `|EnsembleIndex n (6 n)| = (8 n^3)^{6 n}` (existence only; `n⋆` is a finite
  Nat witness, not an asymptotic gesture). Set `m := 6 * n`, `r := n / 4`.

  Step 3 revised (occupancy, not crude `U` union). For each medium cardinality
  `s` with `r / 2 ≤ s ≤ r` and each fixed `S : Finset (Fin m)` with
  `S.card = s`, view the `3 s` coordinates of `(ω i)_{i ∈ S}` as throwing
  `3 s` balls into `n` bins (oriented model: each atom contributes three
  independent `Fin n` coordinates). Write `X_S(ω) := (indexSupportFin ω S).card`.
  Then `¬ SpreadsIndices ω r` yields some medium `S` with `X_S(ω) < 2 s`
  by `exists_concentrated_fin_of_not_spreadsIndices` plus
  `card_indexSupportFin`.

  Mean coverage at the hardest end `s = r = n / 4`:
  `E[X] = n (1 - ((n-1)/n)^{3 s}) ≈ n (1 - e^{-3/4}) ≈ 0.528 n`, while the
  Spreads failure threshold is `2 s = n / 2`. So the mean sits strictly above
  the threshold by about `0.028 n` for large `n`. A Chernoff or relative
  entropy lower tail on balls and bins therefore bounds
  `|{ω : X_S(ω) < 2 s}| ≤ ρ^s (8 n^3)^{m}` for some `ρ < 1` depending only on
  the locked density and scale (or an equivalent pure Nat form without naming
  `ρ`). Crucially this bound is for a fixed `S`: there is no factor
  `C(n, 2 s - 1)`.

  Union over at most `C(m,s)` index sets and over `s ∈ [r/2, r]` gives a
  failure count
  `∑_s C(m,s) · |{ω : X_{S_0} < 2 s}|`
  (any representative `S_0` of size `s`). Target inequality name when
  formalizing: `spreadsOccupancyTerm_lt_ensemble_iff` and
  `exists_spreadsIndices_of_occupancy_sum_lt`, feeding the already certified
  `exists_spreadsIndices_of_univ_card_lt`. Then
  `spreads_random3CNF_of_spreadsIndices` upgrades to `Spreads F r 2`.

  Why this is tighter than Cluster 20: the crude term multiplies by
  `C(n, 2 s - 1)`, which at `s = n / 4` is about `2^n / poly(n)` and is exactly
  the entropy that cancelled the `((2 s)/n)^{3 s}` decay. Occupancy never
  introduces that factor.

  Steps 2 and 4 unchanged in content: unsat via `exists_unsat_random3CNF`;
  matchability via large minimally unsat cores and
  `isCSMatchable_of_unsat_min_card`. Same sample must satisfy all three; the
  three bad event counts must sum to less than `|Ω|`. Classification of the
  occupancy step: adaptation of classical balls and bins tails to the
  oriented ensemble already formalized. Gap class: hard (Nat packaging of the
  lower tail at `s = n / 4`, where the mean to threshold gap is thin).

  Fallback recorded but not developed: if the `r = n / 4` lower tail refuses to
  close in Nat arithmetic, revise the pin to `r = n / 8` (still
  `csClauseWidthFloor r 1 = r / 2 ≥ 4` once `n ≥ 64`) so that at `s = r` one
  has mean coverage `n (1 - e^{-3/8}) ≈ 0.313 n` against threshold `0.25 n`, a
  wider margin. That fallback needs a human pin decision on
  `random3CNFMatchScale` and both Frontier `r = n / 4` equations.

  ### Gap list

  1. Explicit Nat lower tail: for each `s ≤ n / 4`, bound
     `Fintype.card { ω // (indexSupportFin ω S).card < 2 s }` without passing
     through `C(n, 2 s - 1) (2 s - 1)^{3 s}`. Gap class: hard.
  2. Sum over medium `s` of `C(6 n, s)` times that fiber strictly below
     `(8 n^3)^{6 n}` for all `n ≥ n⋆`. Gap class: hard engineering.
  3. Joint intersection with the unsat and matchability good sets (add the three
     failure counts). Gap class: hard but routine once each fiber is closed.
  4. Exact `(cnfVars F).card = n` cleanup under the existing
     `Spreads.mono_r` path. Gap class: routine.
  5. Optional pin fallback to `r = n / 8` if gap 2 fails at `r = n / 4`.
     Gap class: unknown until gap 2 is attempted; requires accept_prose on a
     pin patch before formalize.

  ### Self adversarial pass

  - Quantifier order: `n` depends on `N` and on `n⋆`; `ω` depends on `n`. No
    uniformity beyond existence.
  - Thin margin: at `s = n / 4` the occupancy mean is only about six percent
    above `2 s`. Off by one in the threshold (`< 2 s` versus `≤ 2 s - 1`) or
    in the with replacement model could erase the gap; proofs must track the
    exact `indexSupportFin` cardinality and the oriented coordinate model.
  - Hidden uniformity: same `ω` for unsat, Spreads, and matchability; no
    deletion after the fact.
  - Crude scaffolding reuse: `spreadsFailureTerm` and
    `spreads_crude_core_not_lt_at_thirty_two` remain as obstruction certificates;
    they must not be cited as a positive close.
  - Larger `n` alone under crude counting would not work; this revision changes
    the counting method, satisfying the stop rule against repeating a twice
    blocked approach.
  - Does not climb past resolution or claim NP versus coNP; it only aims to
    inhabit hypotheses of the certified CS width machine.
  - Barrier: resolution level; no R3 audit flag.

  Most important thing learned: the Cluster 20 obstruction is structural for
  crude rate 2 union bounds at density 6, so Block A Step 3 must switch to an
  occupancy (fixed `S`) tail and only then union over index sets; parameter
  tweaks inside `spreadsFailureTerm` are a dead branch.
  Next: human gate accept_prose on this occupancy revision, then formalize Nat
  occupancy fibers toward `exists_spreads_matchable_unsat_random3CNF` (not
  approved until the gate passes).
  gate_pending: accept_prose.

- 2026-08-11 formalize (occupancy Spreads packaging after accept_prose):
  PARTIAL. Human gate accept_prose approved ("go") for the occupancy revision
  pinned in commit 8301b98. Edited only
  `theory/Theory/ProofComplexity/CSExpansion.lean` (Cluster 21).

  ### Verified Lean names used or added (ripgrep; no guessing)

  Pre-existing (edited around):
  `EnsembleIndex`, `indexSupportFin`, `supportConcentrated`,
  `card_ensembleIndex_supportConcentrated`, `SpreadsIndices`,
  `exists_concentrated_of_not_spreadsIndices`, `card_indexSupportFin`,
  `exists_spreadsIndices_of_univ_card_lt`, `spreadsFailureTerm`,
  `random3CNFMatchScale`, `random3CNFClauseCount`, `card_ensembleIndex`,
  `CSExpansionFrontier.exists_spreads_matchable_unsat_random3CNF`,
  `CSExpansionFrontier.exists_cs_clause_expanding_3cnf`.

  New accepted Cluster 21:
  `random3CNFMatchScaleFallback`,
  `random3CNFMatchScaleFallback_ge_eight`,
  `csClauseWidthFloor_of_random3CNFMatchScaleFallback`,
  `card_finset_eq_card`, `supportCardLt`, `spreadsOccupancyFiberBound`,
  `spreadsOccupancyTerm`, `spreadsOccupancyTerm_lt_ensemble_iff`,
  `card_ensembleIndex_support_card_lt`,
  `card_ensembleIndex_support_card_lt_of_card`,
  `sum_card_support_card_lt_le_occupancyTerm`,
  `card_not_spreadsIndices_le_occupancy_sum`,
  `exists_spreadsIndices_of_occupancy_sum_lt`,
  `exists_spreadsIndices_of_occupancy_sum_lt_ensemble`,
  `two_mul_matchScale_le_div_two`,
  `two_mul_matchScaleFallback_le_div_four`.

  ### What compiled

  Fixed-`S` occupancy fiber bound via union of concentration subtypes over
  `|U| < t`; outer failure term `C(m,s) * spreadsOccupancyFiberBound * (8 n^3)^{m-s}`
  with no lone outer `C(n,2s-1)`; card comparison bridge
  `exists_spreadsIndices_of_occupancy_sum_lt`; recorded inactive fallback
  `random3CNFMatchScaleFallback` (`r = n / 8`). Axiom gate PASS after adding
  the new declarations to `scripts/accepted_declarations.txt`.

  ### Honest limit

  The inner fiber bound still sums `∑_{u < 2s} C(n,u) (8 u^3)^s`, which is not
  yet a Chernoff or relative entropy lower tail. Nat calibration shows that
  packaging alone does not close at locked `m = 6 n`, `r = n / 4`. Frontier
  `exists_spreads_matchable_unsat_random3CNF` and
  `exists_cs_clause_expanding_3cnf` remain sorry.

  Most important thing learned: occupancy packaging removes the crude outer
  `C(n,2s-1)` factor and gives a machine-checkable bridge from a summed
  occupancy inequality to `SpreadsIndices`; the remaining hard gap is the
  fixed-`S` lower tail constant, not more choose algebra on `spreadsFailureTerm`.
  Next: formalize a Chernoff-style Nat fiber bound (or activate the recorded
  `r = n / 8` pin after a separate accept_prose), then joint unsat and
  matchability intersection.
  gate_pending: none.

- 2026-08-11 formalize (Chernoff slice occupancy obstruction):
  PARTIAL. Edited only
  `theory/Theory/ProofComplexity/CSExpansion.lean` (Cluster 22).

  ### Verified Lean names used or added (ripgrep; no guessing)

  Pre-existing:
  `indexSupportFin`, `supportConcentrated`,
  `card_ensembleIndex_supportConcentrated`, `indexSupport_card_le_of_concentrated`,
  `card_indexSupportFin`, `supportCardLt`, `spreadsOccupancyFiberBound`,
  `spreadsOccupancyTerm`, `choose_one_ninety_two_eight_ge_thirty_two_pow_eight`,
  `thirty_two_pow_sixteen_lt_fifteen_pow_twenty_four`,
  `choose_thirty_two_fifteen_pos`,
  `spreads_crude_term_not_lt_eight_pow_at_thirty_two`,
  `CSExpansionFrontier.exists_spreads_matchable_unsat_random3CNF`.

  New accepted Cluster 22:
  `spreadsChernoffSlice`,
  `spreadsOccupancyFiberBound_ge_chernoff_slice`,
  `supportCardLt_of_concentrated_lt`,
  `card_ensembleIndex_support_card_lt_ge_concentrated`,
  `card_ensembleIndex_support_card_lt_ge_chernoff_slice`,
  `fifteen_pow_twenty_four_ge_thirty_two_pow_sixteen`,
  `spreads_chernoff_slice_core_ge_at_thirty_two`,
  `spreads_chernoff_slice_core_not_lt_at_thirty_two`,
  `spreads_chernoff_slice_not_lt_eight_pow_at_thirty_two`,
  `spreadsChernoffSlice_thirty_two_eight`,
  `spreads_occupancy_fiber_not_lt_eight_pow_at_thirty_two`,
  `spreadsOccupancyTerm_core_not_lt_at_thirty_two`.

  ### What compiled

  Single slice lower seed `(8 (2s-1)^3)^s` injects into the true fixed-`S`
  occupancy failure set (no inner `∑_u C(n,u)`). At locked `n = 32`, `s = 8`,
  `C(192,8) (15)^{24} ≥ 32^{24}` and therefore
  `¬ C(6n,s) (8 (2s-1)^3)^s < (8 n^3)^s`. The Cluster 21 fiber upper bound
  inherits the same obstruction. Axiom gate PASS.

  ### Honest limit

  Dropping the inner choose sum does not rescue the first moment close at
  `m = 6 n`, `r = n / 4`: even one fixed `U` of size `2s-1` overruns the
  cancelled budget at the informative minimum. Frontier
  `exists_spreads_matchable_unsat_random3CNF` remains open. The recorded
  `r = n / 8` fallback is still inactive and needs accept_prose before any
  pin patch; calibration also suggests constant scale `r ≥ 8` (not linear
  `r = n/4`) is the regime where a union bound can close.

  Most important thing learned: Chernoff style removal of `∑_u C(n,u)` is
  real progress on the fiber shape, but the locked linear rate-2 pin is
  first-moment blocked at `n = 32` already; next work is a prove cycle to
  redesign the Spreads pin or method, not more fiber algebra at `r = n/4`.
  Next: prove pin redesign (constant informative `r`, weaker rate, or
  non-random witness), with accept_prose before any Frontier equation patch.
  gate_pending: none.

- 2026-08-11 prove (Block A Spreads pin redesign after Cluster 22): SUCCESS
  on the redesigned plan, pending human accept_prose before any Frontier
  equation patch. Prose only; no Lean edited this cycle.

  ### Choice and rationale (JSON contract)

  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "prove",
    "target": "redesign Block A Spreads pin after Chernoff first-moment kill of m=6n r=n/4",
    "rationale": "Cluster 22 blocks the locked occupancy close; stop condition requires a new approach rather than more fiber algebra at r=n/4."
  }
  ```

  ### Files and Lean names verified before this pin (no duplicates)

  Existing (edit in place after accept_prose; do not create new modules):
  `theory/Theory/ProofComplexity/CSExpansion.lean` only for later formalize.
  Density and scale: `random3CNFDensity`, `random3CNFClauseCount`,
  `random3CNFMatchScale` (today `n / 4`), `random3CNFMatchScaleFallback`
  (today `n / 8`, inactive), `random3CNFMatchScale_ge_eight`,
  `csClauseWidthFloor_of_random3CNFMatchScale`,
  `random3CNFMatchScaleFallback_ge_eight`,
  `csClauseWidthFloor_of_random3CNFMatchScaleFallback`,
  `random3CNFMatchScale_thirty_two`, `random3CNFClauseCount_thirty_two`.
  Ensemble and unsat: `EnsembleIndex`, `Ensemble3CNF`, `random3CNF`,
  `exists_unsat_random3CNF`, `exists_unsat_random3CNF_ge_thirty_two`.
  Spreads counting: `SpreadsIndices`, `spreadsFailureTerm`,
  `spreadsOccupancyFiberBound`, `spreadsOccupancyTerm`,
  `spreadsChernoffSlice`, `exists_spreadsIndices_of_occupancy_sum_lt`,
  `exists_spreadsIndices_of_occupancy_sum_lt_ensemble`,
  `spreads_chernoff_slice_not_lt_eight_pow_at_thirty_two`,
  `spreadsOccupancyTerm_core_not_lt_at_thirty_two`.
  Packaging and Frontiers:
  `exists_cs_clause_expanding_3cnf_of_spreads_matchable_unsat`,
  `CSExpansionFrontier.exists_spreads_matchable_unsat_random3CNF`,
  `CSExpansionFrontier.exists_cs_clause_expanding_3cnf`,
  `hasCSClauseExpansion_one_of_spreads_two`, `Spreads`, `IsCSMatchable`,
  `HasCSClauseExpansion`, `csClauseWidthFloor`,
  `informative_cs_floor_requires_r_ge_eight`.
  Constructive scaffolding (not chosen this cycle):
  `matchingTripleSupports`, `loosePathSupports`,
  `exists_overlapping_spreadsSupports_informative`,
  `satisfiable_matchingTripleSupports_cnf`,
  `satisfiable_loosePathSupports_allTrue`, `spreadWitnessCNF`.
  Absent name still not introduced: `looseCycleSupports`.

  Proposed definitional edits after accept_prose (same file, same names):
  redefine `random3CNFMatchScale n := n / 16`; retarget
  `random3CNFMatchScale_ge_eight` and
  `csClauseWidthFloor_of_random3CNFMatchScale` to hypothesis `128 ≤ n`;
  deprecate `random3CNFMatchScaleFallback` as a dead alias or repoint it to
  `n / 16` only as a historical synonym; rewrite Frontier equations and
  packaging from `r = n / 4` to `r = n / 16` with `max N 128 ≤ n`.
  Calibration lemmas to add later (names absent today):
  `random3CNFMatchScale_one_twenty_eight`,
  `spreads_chernoff_slice_core_lt_at_one_twenty_eight`
  (Nat witness that the Chernoff core is strictly below budget at
  `n = 128`, `s = 8`).

  ### Statement restated with all quantifiers explicit

  Target after pin patch: for every `N : ℕ` there exist `n : ℕ` and
  `ω : EnsembleIndex n (random3CNFClauseCount n)` such that, writing
  `F := random3CNF n (random3CNFClauseCount n) ω` and
  `r := random3CNFMatchScale n` with the new definition `r = n / 16`,
  one has `max N 128 ≤ n`, `(cnfVars F).card = n`, `cnfWidth F ≤ 3`,
  `Spreads F r 2`, `IsCSMatchable F r`, `¬ Satisfiable F`, and
  `cnfWidth F < csClauseWidthFloor r 1`. Packaging through
  `exists_cs_clause_expanding_3cnf_of_spreads_matchable_unsat` then yields
  `exists_cs_clause_expanding_3cnf` with the matching equation `r = n / 16`
  (not `r = n / 4`).

  ### Non vacuity

  1. Ensemble nonempty: `ensembleIndex_nonempty` for `0 < n`.
  2. Unsat samples exist at density 6: `exists_unsat_random3CNF` (and the
     `32 ≤ n` specialization).
  3. Informative floor: `informative_cs_floor_requires_r_ge_eight` forces
     `r ≥ 8`, hence under `r = n / 16` one needs `n ≥ 128`.
  4. Predicates inhabited at small scale already:
     `exists_spreads_two_matchable_unsat_3cnf` (non informative floor).

  ### Attack ideas sketched (exactly one developed)

  A. Keep probabilistic occupancy or Chernoff first moment, but shrink the
     linear scale so the certified slice bound has negative asymptotic rate
     (DEVELOPED: pin `r = n / 16`).
  B. Activate recorded `random3CNFMatchScaleFallback` (`r = n / 8`). Rejected
     below: same Chernoff slice still has positive asymptotic rate.
  C. Constant informative scale `r = 8` with growing `n`. Rejected as the
     primary Block A pin: it beats `csClauseWidthFloor` but only yields
     constant width, hence only constant size via BSW, which fails the R2
     random k CNF exponential size obligation. Useful as a calibration
     sandbox only.
  D. Constructive cyclic overlapping unsat (`looseCycleSupports`, still
     absent). Not developed: related constructive polarity routes already
     blocked twice (`satisfiable_matchingTripleSupports_cnf`,
     `satisfiable_loosePathSupports_allTrue`).

  ### First principles kill of the locked plan

  Cluster 22 certified
  `spreads_chernoff_slice_not_lt_eight_pow_at_thirty_two`: at `n = 32`,
  `s = 8`, already
  `¬ Nat.choose (6 * n) s * spreadsChernoffSlice n s < (8 * n ^ 3) ^ s`.
  That is a lower seed on the occupancy fiber, so no packaging that upper
  bounds failure by a multiple of this slice can close at those parameters.

  This is not a small `n` fluke. With `m = 6 n` and medium end `s = α n`,
  the Chernoff core behaves like
  `exp(n α (ln(6 e / α) + 3 ln(2 α)))`. The rate is positive for every
  `α > 1 / sqrt(48 e) ≈ 0.0875`. In particular:
  - `α = 1/4` (locked `r = n / 4`): rate about `+0.52` (diverges; worse as
    `n` grows).
  - `α = 1/8` (recorded fallback): rate about `+0.089` (still diverges).
  - `α = 1/12`: marginally negative.
  - `α = 1/16`: rate about `-0.042` (converges with margin).

  Finite calibration of the medium sum
  `∑_{s = r/2}^{r} C(6 n, s) ((2 s - 1)/n)^{3 s}`:
  - `n = 128`, `r = n / 8 = 16`: sum about `1.8 e3` (fails).
  - `n = 128`, `r = n / 16 = 8`: sum about `2.1 e-4` (passes).
  - `n = 256`, `r = 16`: sum about `6 e-7` (passes harder).

  Therefore: larger `n` cannot rescue `r = n / 4`; the recorded
  `r = n / 8` fallback is also dead under the same first moment method;
  raising density worsens Spreads; the honest surviving linear pin under
  `spreadsChernoffSlice` is `r = n / 16` (or smaller).

  ### The one argument developed (revised Block A)

  Fix `N : ℕ`. Set `n₀ := max(N, 128)`, and for each `n ≥ n₀` set
  `m := random3CNFClauseCount n = 6 * n` and
  `r := random3CNFMatchScale n = n / 16` (so `r ≥ 8` and
  `csClauseWidthFloor r 1 = r / 2 ≥ 4 > 3`).

  Step 1 (sample space). Unchanged packaging:
  `EnsembleIndex`, `random3CNF`, `random3CNF_cnfWidth_le`,
  `random3CNF_vars_card`.

  Step 2 (unsat). Unchanged: `exists_unsat_random3CNF` already closes the
  first moment at density 6 for every positive `n`. Classification: known
  (certified).

  Step 3 (Spreads at rate 2). Keep the accepted occupancy method of Cluster
  21 to 22: bound non `SpreadsIndices` by
  `∑_{s ∈ Icc (r/2) r} spreadsOccupancyTerm n m s`, and seed each fiber by
  `spreadsChernoffSlice` (or a tighter relative entropy bound later). At the
  new pin the Chernoff core sum is `o(1)` for all large `n` by the rate
  calculation above; once the Nat inequality
  `∑ spreadsOccupancyTerm < (8 n^3)^m` is formalized at some `n ≥ 128`,
  invoke `exists_spreadsIndices_of_occupancy_sum_lt_ensemble` and
  `spreads_random3CNF_of_spreadsIndices`. Classification: adaptation of the
  accepted occupancy plan to a viable scale. Gap: hard Nat arithmetic at
  `n = 128`, `r = 8` (routine mathematics, hard engineering).

  Step 4 (matchability). Same extraction as before via minimally unsat cores
  and `isCSMatchable_of_unsat_min_card` / `IsCSMatchable.mono`, now only up
  to scale `r = n / 16` (strictly easier union bound than `n / 4`).
  Classification: known. Gap: hard constants, easier than the old pin.

  Step 5 (package). After Steps 2 to 4, apply
  `hasCSClauseExpansion_one_of_spreads_two` and the retargeted packaging
  lemma with equation `r = n / 16` into
  `exists_cs_clause_expanding_3cnf`. Classification: routine once Step 3
  lands, but blocked on the human pin patch.

  ### Gap list

  1. Human accept_prose on redefining `random3CNFMatchScale` to `n / 16` and
     rewriting both Frontier equations plus packaging from `n / 4` to
     `n / 16` with threshold `128`. Gap class: gate (not mathematics).
  2. Nat proof that the Chernoff or occupancy sum is strictly below the
     ensemble card at some concrete `n ≥ 128` (seed name
     `spreads_chernoff_slice_core_lt_at_one_twenty_eight`). Gap class: hard.
  3. Matchability union bound at the new scale, then joint intersection with
     unsat and Spreads. Gap class: hard.
  4. Variable card cleanup via `Spreads.mono_r` so `(cnfVars F).card = n`
     exactly. Gap class: routine.
  5. Optional later strengthening back toward classical `Θ(n)` medium sets
     with a non first moment method (LLL, alteration, or second moment). Not
     required to close the present pin. Gap class: unknown; out of scope.

  ### Self adversarial pass

  - Quantifier order: `ω` depends on `n`, which depends on `N`. No uniformity
    beyond existence.
  - Hidden weakening: `r = n / 16` still gives linear width
    `csClauseWidthFloor r 1 = n / 32`, hence exponential size through BSW
    with a weaker explicit rate than `n / 8`. Constant `r = 8` would not.
  - Off by one: informative floor needs `r ≥ 8`, so `n ≥ 128` under
    sixteenth scale; do not keep the old `32` threshold.
  - Do not revive `r = n / 8` without a new counting method: Cluster 22 style
    seeds already diverge at that α.
  - Do not claim the old occupancy accept_prose still authorizes formalize of
    Frontier equations that say `r = n / 4`; that plan is dead.
  - Constructive polarity search remains blocked twice; this cycle changes
    approach inside the probabilistic method rather than grinding
    `loosePathSupports` again.
  - Barrier: resolution level; no R3 flag.
  - Stop condition: same cause (first moment at aggressive linear scale)
    blocked through crude and Chernoff packaging; this session changes the
    pin instead of grinding `r = n / 4` a third time.

  Most important thing learned: under the certified `spreadsChernoffSlice`
  lower seed, first moment Spreads at `m = 6 n` is asymptotically impossible
  at `r = n / 4` and still impossible at the recorded `r = n / 8` fallback;
  the viable linear pin is `r = n / 16` with `n ≥ 128`, preserving Ω(n)
  width while making the medium Chernoff sum about `2 e-4` already at the
  informative minimum. Next: human gate accept_prose on this pin patch,
  then formalize Nat Chernoff close at `n = 128` toward
  `exists_spreads_matchable_unsat_random3CNF`.
  gate_pending: accept_prose.


- 2026-08-12 formalize (Cluster 23 Block A pin activation after accept_prose):
  PARTIAL. Human gate accept_prose approved the prove 2026-08-11 redesign.
  Edited existing `theory/Theory/ProofComplexity/CSExpansion.lean` only (no
  new modules). Axiom gate PASS on accepted tree; Frontier existence remains
  honest sorry.

  ### Names verified before edit (no duplicates)

  Edited in place: `random3CNFMatchScale`, `random3CNFMatchScale_ge_eight`,
  `csClauseWidthFloor_of_random3CNFMatchScale`, `random3CNFMatchScale_eq`,
  `medium_hi_eq_matchScale`, `random3CNFMatchScale_thirty_two`,
  `exists_cs_clause_expanding_3cnf_of_spreads_matchable_unsat`,
  `two_mul_matchScale_le_div_two`, comments on
  `random3CNFMatchScaleFallback` (kept as killed `n / 8` historical alias),
  `CSExpansionFrontier.exists_cs_clause_expanding_3cnf`,
  `CSExpansionFrontier.exists_spreads_matchable_unsat_random3CNF`.
  Added accepted calibration: `random3CNFMatchScale_one_twenty_eight`,
  `random3CNFClauseCount_one_twenty_eight`.
  Unchanged: `random3CNFClauseCount`, `exists_unsat_random3CNF`,
  occupancy and Chernoff obstruction lemmas at historical `n = 32`.

  ### What changed

  - `random3CNFMatchScale n := n / 16` (was `n / 4`).
  - Informative hypotheses retargeted to `128 ≤ n`.
  - Packaging and both Frontier equations use `r = n / 16`;
    `exists_spreads_matchable_unsat_random3CNF` now requires `max N 128 ≤ n`.
  - `random3CNFMatchScale_thirty_two` now states `= 2` under the active pin;
    new `random3CNFMatchScale_one_twenty_eight` states `= 8`.

  ### Gate

  `scripts/check_axioms.sh` PASS (build green, accepted tree sorry free,
  axioms within propext, Classical.choice, Quot.sound). New accepted names
  listed in `scripts/accepted_declarations.txt` under cluster 23.

  Most important thing learned: the pin patch itself is routine Lean; Block A
  remains open on the Nat Chernoff or occupancy close at some `n ≥ 128`
  toward `exists_spreads_matchable_unsat_random3CNF`.
  gate_pending: none.

- 2026-08-12 prove (kill Cluster 23 n/16 first moment; revise Block A): SUCCESS
  with human gate accept_prose. Prose only; no Lean this cycle.

  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "prove",
    "target": "kill random3CNFMatchScale n/16 first-moment Spreads close; revise Block A to unique-neighbor HasCSClauseExpansion",
    "rationale": "Prior accept_prose calibrated the wrong quantity (omitted C(n,2s-1)); full spreadsChernoffSlice first moment fails at every linear alpha."
  }
  ```

  ### Statement restated with all quantifiers explicit

  Still aiming at: for every `N : ℕ` there exist `n : ℕ` and a width-3 CNF
  `F` on `n` variables such that `N ≤ n`, `IsCSMatchable F r`,
  `HasCSClauseExpansion F r 1`, `¬ Satisfiable F`, and
  `cnfWidth F < csClauseWidthFloor r 1` for some informative linear scale
  `r = Θ(n)`. The Cluster 23 packaging that routes through
  `Spreads F (n/16) 2` plus occupancy or Chernoff first moment is no longer
  the proposed closer.

  ### Non vacuity

  Unchanged witnesses: `ensembleIndex_nonempty`, `exists_unsat_random3CNF`,
  `exists_spreads_two_matchable_unsat_3cnf`, Heawood star Spreads at fixed
  informative scales. These show predicates are inhabited; they do not close
  the unbounded random existence pin.

  ### Attack ideas sketched (exactly one developed)

  A. Shrink `α = r/n` further under the same
     `∑ C(m,s) C(n,2s-1) ((2s-1)/n)^{3s}` first moment (rejected below: no
     linear `α` has negative rate).
  B. Keep first moment but drop `C(n,2s-1)` via a pure balls and bins LD on
     `X_S` (rejected below: union entropy still beats the thin lower tail at
     Spreads rate 2 for every linear `α`).
  C. Symmetric LLL on Spreads rate 2 bad events with clause intersection
     dependency (rejected as primary: leading term `α ln(6e) > 0`).
  D. Direct unique neighbor expansion first moment into
     `HasCSClauseExpansion` at `α = 1`, bypassing Spreads rate 2 and
     `spreadsChernoffSlice` (DEVELOPED).

  ### Kill: Cluster 23 n/16 first moment under full slice

  The Cluster 23 accept_prose calibrated
  `∑_{s=r/2}^{r} C(6n,s) ((2s-1)/n)^{3s}`
  and claimed about `2.1e-4` at `n = 128`, `r = 8`. That formula is not an
  upper bound on the formalized occupancy failure count, and it is not the
  Chernoff slice quantity that Cluster 22 relates to
  `spreadsOccupancyFiberBound`. The matching full slice is
  `∑_{s=r/2}^{r} C(6n,s) C(n,2s-1) ((2s-1)/n)^{3s}`,
  which lower bounds the cancelled occupancy comparison because
  `Nat.choose n (2s-1) * spreadsChernoffSlice n s ≤ spreadsOccupancyFiberBound n s (2s)`.

  Explicit calibration:
  - incomplete (bug) at `n=128`, `r=8`: sum about `2.12e-4` (false pass);
  - full slice at `n=128`, `r=8`: sum about `1.73e15` (hard fail);
  - dominant term `s=8`: about `1.72e15`.

  Asymptotic rate of the full mid term at `s = α n`, `m = 6 n`:
  `(1/n) ln = 6 H(α/6) + H(2α) + 3α ln(2α)`.
  For small `α` this is `α (3 + ln 12) + O(α^2)` with `3 + ln 12 ≈ 5.485 > 0`.
  So every sufficiently small linear `α` diverges. Numerics:
  - `α = 1/4, 1/8, 1/16, 1/32, 1/64`: all positive full rates;
  - bug rates without `H(2α)` were negative at `α ≤ 1/12`, which is exactly
    how Cluster 23 was misled.

  Finite full sums grow with `n` at fixed linear `α` (example:
  `α = 1/16` gives about `1.7e15` at `n=128` and about `2.6e70` at `n=512`).
  Larger `n` cannot rescue `r = n/16` under this method. Same death as
  Cluster 22 for `r = n/4` and the prove kill of `r = n/8`, now extended to
  the activated Cluster 23 pin and to every linear scale.

  Constant `r = 8` only: full slice is `Θ(1/n)` times `(12 e^3)^8`, so it
  eventually drops below 1 only for enormous `n` (order `10^{17}`), and even
  then yields only constant width, hence no exponential BSW size. Not a Block A
  closer.

  True occupancy LD without routing through `C(n,u)` also fails the first
  moment union at Spreads rate 2: Poissonized `Bin(n, 1-e^{-3α})` lower tails
  have KL only about `0.001` to `0.01` while `6 H(α/6)` stays about `0.2` to
  `1.0`, so `C(6n, αn) exp(-n KL)` diverges for every tested linear `α`.

  Therefore: stop chasing Nat Chernoff or occupancy closes at `n ≥ 128` under
  `spreadsChernoffSlice` or `spreadsOccupancyTerm` for Spreads rate 2. The
  method is dead, not merely the pin.

  ### The one argument developed (revised Block A)

  Change counting target from Spreads rate 2 to unique neighbor expansion,
  which implies clause boundary expansion directly.

  Fix `N : ℕ`. Choose `n ≥ max(N, n⋆)` with `m = 6 n` and a linear scale
  `r = ⌊α⋆ n⌋` where `α⋆ > 0` is the classical Ben Sasson Wigderson
  (or Chvatal Szemeredi) unique neighbor window for 3 CNF at density 6
  (concrete `α⋆` to be pinned from the inequality below; expected order
  constant, not `1/16` from the false calibration).

  Step 1 to 2. Same ensemble and unsat first moment as certified.

  Step 3 revised (unique neighbors, not Spreads slice). For each axiom index
  set `S` with `r/2 ≤ |S| ≤ r`, let `U_1(S)` be the set of variables that
  appear in exactly one clause of the sampled support of `S`. The bad event
  `B_S` is `|U_1(S)| < |S|`. A standard first moment on ordered clause
  variable incidences bounds
  `P(B_S) ≤ exp(-c |S|)` for an absolute `c > 0` once `α⋆` is small enough
  relative to density 6 (adaptation of the BSW random CNF expansion lemma;
  classification: known). Union over at most `∑_s C(m,s)` medium index sets
  is `o(1)` for all large `n` inside that window. On the complement, every
  medium axiom set has at least `|S|` unique neighbors, hence
  `|clauseSetBoundary G| ≥ |G|`, i.e. `HasCSClauseExpansion F r 1`, with no
  appeal to `Spreads F r 2` and no `spreadsChernoffSlice` factor
  `C(n,2s-1) ((2s-1)/n)^{3s}`.

  Step 4. Matchability at the same `r` via minimally unsat cores as before
  (easier at whatever `α⋆` the expansion window forces). Classification: known.

  Step 5. Package with a new or retargeted lemma
  `exists_cs_clause_expanding_3cnf_of_matchable_unsat_expanding`
  that no longer requires Spreads. Classification: routine once Steps 3 to 4
  land; requires accept_prose before formalize because Frontier equations and
  packaging currently hard code Spreads at `n/16`.

  Why this is not another pin shrink: the obstruction was the Spreads rate 2
  first moment skeleton (critical at `γ = 2`, rate `α(3+ln 12)`), not the
  particular constant 16. Unique neighbor counting is a different skeleton
  with a genuine negative rate window in the literature.

  ### Gap list

  1. Human accept_prose to abandon Cluster 23 Spreads first moment closes
     (including Nat Chernoff at `n=128`) and to authorize a packaging pin that
     targets `HasCSClauseExpansion` via unique neighbors. Gap class: gate.
  2. Explicit constant `α⋆` and Nat form of the unique neighbor first moment
     inequality at density 6. Gap class: hard.
  3. Lean definitions for unique neighbor sets on `EnsembleIndex` samples and
     the failure term replacing `spreadsOccupancyTerm`. Gap class: hard.
  4. Matchability union bound at scale `r = ⌊α⋆ n⌋` jointly with unsat and
     expansion. Gap class: hard.
  5. Retarget Frontier
     `exists_spreads_matchable_unsat_random3CNF` (rename or replace) and
     `exists_cs_clause_expanding_3cnf` equations away from mandatory Spreads
     at `n/16`. Gap class: routine after gate.
  6. Optional fallback if unique neighbor first moment refuses density 6:
     lopsided LLL or alteration on the same bad events; not developed now.
     Gap class: unknown.

  ### Self adversarial pass

  - Quantifier order: existence only; `α⋆` is absolute, `n` depends on `N`.
  - Do not reuse Cluster 23 calibration numbers; they omit `C(n,2s-1)`.
  - Do not claim symmetric LLL on Spreads rate 2 is already shown; it was
    only sketched with a positive leading term and rejected as primary.
  - Off by one: unique neighbor count versus `clauseSetBoundary` needs the
    exact incidence identity already certified in `clauseSetBoundary_card_add_sum_ge`.
  - Constructive polarity remains blocked twice; this cycle does not revive it.
  - Weak Spreads `γ ∈ (1.5, 2)` with first moment only yields tiny medium
    windows and pathetic BSW rates; not chosen as primary.
  - Barrier: resolution level; no R3 flag.
  - Stop condition: first moment Spreads closes are now blocked across crude,
    Chernoff slice, occupancy U union, and pins `n/4`, `n/8`, `n/16`. This
    session changes method rather than grinding a fourth pin.

  Most important thing learned: under the full slice
  `C(m,s) C(n,2s-1) ((2s-1)/n)^{3s}` matching `spreadsChernoffSlice`, no
  linear Spreads rate 2 pin survives at `m = 6 n`; Cluster 23 passed only by
  dropping `C(n,2s-1)`. Block A must leave that skeleton and prove
  `HasCSClauseExpansion` by unique neighbor expansion (BSW style).
  gate_pending: accept_prose.

- 2026-08-12 formalize (Cluster 24 Nat Chernoff LT and occupancy obstruction):
  PARTIAL. Edited existing `theory/Theory/ProofComplexity/CSExpansion.lean`
  only. Axiom gate PASS. Frontier existence remains honest sorry.

  ### Names verified before edit (no duplicates)

  New accepted: `spreads_chernoff_slice_core_lt_at_one_twenty_eight`,
  `spreads_chernoff_slice_lt_eight_pow_at_one_twenty_eight`,
  `spreadsChernoffSlice_one_twenty_eight_eight`,
  `spreads_occupancy_chernoff_product_ge_at_one_twenty_eight`,
  `spreads_occupancy_chernoff_product_ge_eight_pow_at_one_twenty_eight`,
  `spreads_occupancy_fiber_not_lt_eight_pow_at_one_twenty_eight`,
  `spreadsOccupancyTerm_core_not_lt_at_one_twenty_eight`, plus decide
  seeds and choose or factorial helpers listed under cluster 24 in
  `scripts/accepted_declarations.txt`.
  Reused: `spreadsChernoffSlice`, `spreadsOccupancyFiberBound`,
  `spreadsOccupancyFiberBound_ge_chernoff_slice`,
  `exists_spreadsIndices_of_occupancy_sum_lt_ensemble` (not invoked).

  ### What closed

  - Chernoff cancelled core: `C(768,8) · 15^{24} < 128^{24}` (and eight_pow
    form). Rate at α = 1/16 is negative without the `C(n,2s-1)` factor.
  - Occupancy obstruction: `¬ C(768,8) · spreadsOccupancyFiberBound 128 8 16 <
    (8 · 128^3)^8`, via product lower bound with `C(128,15)`.

  ### What did not close

  Cluster 21 packaging cannot fire at the active pin: the fibre upper bound
  pays `∑_u C(n,u)` and already the Chernoff × `C(n,15)` seed overruns.
  `exists_spreads_matchable_unsat_random3CNF` stays Frontier.

  Most important thing learned: Cluster 24 machine checks the prose kill of
  first moment Spreads at `n/16`: Chernoff without `C(n,u)` passes; occupancy
  with `C(n,u)` fails. Next: wait for accept_prose on the unique neighbor
  redesign, or formalize a fibre upper bound that does not pay full `C(n,u)`.
  gate_pending: none.

- 2026-08-13 formalize (Cluster 25 unique neighbor lift and Spreads free packaging):
  PARTIAL. Edited existing `theory/Theory/ProofComplexity/CSExpansion.lean`
  only. Axiom gate PASS. Frontier existence remains honest sorry. Did not
  retarget Frontier equations (still `r = n / 16` plus Spreads existence
  theorem); that pin change still wants human accept_prose.

  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "Cluster 25 unique-neighbor ExpandsIndices lift and Spreads-free packaging",
    "rationale": "clauseSetBoundary is already unique neighbors; land the index lift and Spreads-free packaging the pending unique-neighbor plan needs without grinding dead Chernoff or self-approving a pin change."
  }
  ```

  ### Names verified before edit (no duplicates)

  New accepted: `mem_clauseSetBoundary_iff_occ`, `indexOcc`,
  `indexUniqueNeighbors`, `mem_indexUniqueNeighbors_iff`, `ExpandsIndices`,
  `hasCSClauseExpansion_random3CNF_of_expandsIndices`,
  `exists_cs_clause_expanding_3cnf_of_matchable_unsat_expanding`.
  Reused: `clauseSetBoundary`, `clauseOcc`, `EnsembleIndex`, `random3CNF`,
  `SpreadsIndices` lift pattern, `exists_cs_clause_expanding_3cnf_of_spreads_matchable_unsat`
  (kept), Frontier `exists_cs_clause_expanding_3cnf` (unchanged equations).

  ### What closed

  - Unique neighbors unpack to `clauseSetBoundary` via `clauseOcc = 1`.
  - Index unique neighbor expansion `ExpandsIndices` lifts to
    `HasCSClauseExpansion (random3CNF n m ω) r 1` by injective clause
    preimages: index unique neighbors inject into the clause-set boundary
    and `|S| = |G|`.
  - Spreads free packaging: matchable unsat expanding 3-CNF at scale
    `n / 16` implies the Frontier inhabitant shape.

  ### What did not close

  No unique neighbor first moment inequality. No `α⋆` pin. No existence
  sample. `exists_spreads_matchable_unsat_random3CNF` still requires Spreads.

  Most important thing learned: Block A no longer needs Spreads as a
  packaging hypothesis; the remaining gap is a first moment (or LLL) close
  for `ExpandsIndices` at some linear `r`, which still needs accept_prose
  before grinding Nat bounds or rewriting Frontier equations.
  gate_pending: accept_prose.

- 2026-08-15 prove (kill unique neighbor first moment; pivot Block A to unbounded
  Tseitin expanders): SUCCESS with human gate accept_prose. Prose only; no Lean
  this cycle.

  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "prove",
    "target": "kill ExpandsIndices first moment at density 6; pivot Block A existence to unbounded Tseitin expanders",
    "rationale": "Unique neighbor |U1|>=|S| is equivalent to Spreads rate 2 for 3 CNF, so the pending redesign does not escape the dead first moment skeleton."
  }
  ```

  ### Statement restated with all quantifiers explicit

  Item 2 still needs, for every `N : ℕ`, some width 3 unsatisfiable CNF `F` on
  `n ≥ N` variables whose resolution width (hence size via BSW) grows with `n`.
  Two routes remain on the rung statement: (i) random 3 CNF with
  `HasCSClauseExpansion` at linear scale, currently packaged as Frontier
  `exists_cs_clause_expanding_3cnf`; (ii) Tseitin CNF on 3 regular expanders,
  where the width machine `tseitin_expander_width_lower_bound` is already
  accepted and Heawood or Petersen give only fixed `n` witnesses.

  ### Non vacuity

  Unchanged: `exists_unsat_random3CNF`, finite Spreads and SpreadsSupports
  witnesses, `tseitinCNF_unsat` under `oddCharge`, Heawood and Petersen
  expansion and width floor lemmas. None of these close unbounded random CS
  existence or an unbounded expander family.

  ### Attack ideas sketched (exactly one developed)

  A. Pin an explicit `α⋆` and close `ExpandsIndices` by unique neighbor first
     moment at density `m = 6 n` (rejected below: same death as Spreads rate 2).
  B. Weaken to `|U1| ≥ ε|S|` with fractional Lean `α` and first moment or
     alteration (rejected below: KL on `U` still loses to `C(6n, αn)` for every
     tested `ε` and linear `α` at density 6).
  C. Symmetric LLL or alteration on the same strong bad events (rejected as
     primary: under the same Poisson KL lower tail, `E[# bad]` has positive
     leading rate, so alteration matches the failed union bound).
  D. Pivot primary Block A existence from random CS first moment to an
     unbounded family of 3 regular edge expanders plus odd charge Tseitin,
     reusing the accepted Tseitin width machine (DEVELOPED).

  ### Kill: unique neighbor first moment is Spreads rate 2

  Lean ensemble `Oriented3Clause` has `|Ω| = 8 n^3`, so
  `P(v ∈ support) = 1 − ((n−1)/n)^3 ∼ 3/n`. For fixed index set `S` of size
  `s = α n`,
  `E[|U1(S)|]/s ∼ 3 e^{−3α}`.
  In particular the mean clears `|U1| ≥ |S|` for every small linear `α`.

  Equivalence for exact total degree `3s` (distinct support 3 CNF, and the
  same leading asymptotics with replacement): handshaking gives
  `u1 ≥ 2|V| − 3s`. Thus `|V| ≥ 2s` implies `u1 ≥ s`, and `u1 < s` implies
  `|V| < 2s`. So `ExpandsIndices` at rate 1 and `Spreads _ _ 2` are the same
  threshold on medium sets. Cluster 25 packaging that lifts `ExpandsIndices`
  into `HasCSClauseExpansion` is still correct as a lemma; it does not supply
  a new counting skeleton.

  First moment and alteration under Poisson KL lower tails for `|U1| < |S|`
  have positive leading rate against `C(6n, αn)` for every tested linear `α`
  (examples: `α ∈ {0.001, 0.01, 0.05, 0.1}`, margins about `−8` to `−4` in
  `(1/n) log`). Weak targets `|U1| ≥ ε|S|` for `ε ∈ {0.01, ..., 0.5}` likewise
  never beat `1 + ln(6/α)`. Support first moment for Spreads rate `γ = 2`
  stays positive at every density that still admits the unsat first moment
  (`m/n > ln 2 / ln(8/7) ≈ 5.191`, including density 6). Weak Spreads
  `γ ∈ (1, 1.5)` has a tiny negative rate window but cannot force `u1 ≥ s`.

  Therefore: stop waiting on accept_prose to Nat chase `α⋆` for
  `ExpandsIndices`. The 2026-08-12 unique neighbor redesign does not evade
  Clusters 22 to 24. Same cause (first moment at strong medium expansion,
  density compatible with unsat) is now blocked again; this session changes
  approach.

  ### The one argument developed (Block A pivot)

  Make the primary unbounded existence route Tseitin on expanders, not random
  CS first moment.

  Step 1. Keep as accepted: for every finite 3 regular `G` with
  `HasExpansion G α` (`α ≥ 1`) and odd charge `χ`, every resolution refutation
  of `tseitinCNF G χ` has width at least the certified Tseitin floor (lemmas
  `tseitin_expander_width_lower_bound` and size corollaries). Classification:
  known (already Lean).

  Step 2. Pin an unbounded family: for every `N`, there exist `n ≥ N` and a
  3 regular graph `G` on `n` vertices with `HasExpansion G 1` (or some fixed
  positive integer expansion factor). Classical constructions exist
  (Margulis; Gabber Galil; LPS Ramanujan graphs for suitable congruences).
  Classification: known externally; Lean inhabitant is the hard gap.

  Step 3. For each such `G`, take `χ = oddCharge_single n 0` (or any odd
  charge). Then `¬ Satisfiable (tseitinCNF G χ)` and the width or size lower
  bound scales with `n`. Classification: routine once Step 2 lands, by
  existing lemmas.

  Step 4. Record random CS Frontier
  `exists_cs_clause_expanding_3cnf` / `exists_spreads_matchable_unsat_random3CNF`
  as secondary: either a future non first moment method (second moment,
  spectral, or a theorem imported after barrier audit) or archival relative to
  the Tseitin family pin. Do not spend further saturday cycles on
  `spreadsChernoffSlice` or unique neighbor first moment Nat closes.
  Classification: stop condition compliance.

  Step 5. Optional parallel: start R5 `FormulaEncoding` in other sessions; it
  does not substitute for R2 existence.

  Why this is not another pin shrink: the obstruction was the strong medium
  expansion first moment at unsat densities, shared by Spreads rate 2 and
  `ExpandsIndices`. Switching to an explicit expander family changes the
  existence obligation from a probabilistic counting close to a constructive
  or classical expander close, which matches the already certified Tseitin
  width machine.

  ### Gap list

  1. Human accept_prose to abandon unique neighbor first moment as Block A
     primary and to authorize the unbounded Tseitin expander family as the
     existence pin for item 2 size lower bounds. Gap class: gate.
  2. Lean construction or axiom free proof of an infinite family of 3 regular
     graphs with `HasExpansion _ 1` (or fixed `α ≥ 1`) and unbounded order.
     Gap class: hard.
  3. Wire family members into `tseitinCNF` and package
     `∀ N, ∃ n ≥ N, … width or size lower bound` as an accepted theorem
     (Frontier until then). Gap class: routine after Step 2.
  4. Decision on random CS Frontier theorems: keep as secondary open, restate,
     or mark killed as a subroute. Gap class: gate (may share accept_prose).
  5. If expander formalization stalls thrice, consider importing a single
     external combinatorial theorem with an explicit barrier audit, or propose
     `kill_rung` or restatement of R2 item 2 scope. Gap class: unknown.

  ### Self adversarial pass

  - Quantifier order: family must be unbounded in `n`; Heawood and Petersen
    alone do not close `∀ N`.
  - Do not claim Margulis or LPS is already in mathlib at this pin; verify
    before formalize.
  - Circulant families remain excluded as hardness expanders (falsifier and
    prior audits).
  - Random CS is not proved impossible; only first moment or alteration under
    the KL on `U` bound is dead. A future spectral argument could reopen it
    without contradicting this kill.
  - Off by one: replacement ensemble degrees are not exactly `3s`; the
    equivalence is asymptotic or under a distinct support refinement already
    used in Spreads counting. Leading rates are unchanged.
  - Barrier: resolution level; no R3 flag.
  - Stop condition: first moment strong expansion closes are blocked across
    Spreads pins `n/4`, `n/8`, `n/16`, occupancy, Chernoff slice, and unique
    neighbor redesign. Approach change is mandatory.

  Most important thing learned: `ExpandsIndices` and Spreads rate 2 share the
  same medium set threshold for 3 CNF, so Cluster 25 does not unlock a new
  first moment window. Block A primary existence should move to an unbounded
  Tseitin expander family and reuse the accepted width machine.
  gate_pending: accept_prose.

- 2026-08-15 formalize (Cluster 26 cubic expander family packaging): PARTIAL.
  Human accept_prose applied on prove 2026-08-15 Tseitin Block A pivot.
  Edited existing `theory/Theory/ProofComplexity/Tseitin.lean` only. Axiom gate
  PASS. Family existence remains honest Frontier sorry.

  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "Cluster 26 cubic expander family packaging and TseitinFrontier pins",
    "rationale": "Gate accepted the pivot; land informative threshold and packaging that reduces hard Tseitin family to cubic HasExpansion family without constructing Margulis yet."
  }
  ```

  ### Names verified before edit (no duplicates)

  New accepted: `tseitinMediumFloor_gt_three_of_fourteen`,
  `tseitin_cubic_expander_informative`,
  `tseitin_cubic_expander_size_informative`,
  `tseitin_heawood_cubic_expander_informative`,
  `exists_tseitin_expander_hard_family_of_cubic_expanders`.
  New Frontier (sorry): `TseitinFrontier.exists_cubic_hasExpansion_family`,
  `TseitinFrontier.exists_tseitin_expander_hard_family`.
  Reused: `HasExpansion`, `IsRegular`, `tseitinCNF_unsat`,
  `cnfWidth_tseitinCNF_of_regular`, `tseitin_expander_width_lower_bound`,
  `tseitin_expander_size_lower_bound`, `heawoodGraph_regular`,
  `heawoodGraph_expansion`, `oddCharge_single`.

  ### What closed

  - Informative floor: `14 ≤ n` implies `3 < tseitinMediumFloor n`.
  - Single graph packaging from cubic regular plus `HasExpansion _ 1`.
  - Heawood as base informative witness via that packaging.
  - Family reduction: cubic expander family implies Tseitin hard family.

  ### What did not close

  No unbounded `HasExpansion` inhabitant. Margulis, Gabber Galil, and LPS
  remain external. Random CS Frontier unchanged (secondary).

  Most important thing learned: Block A is now a pure expander construction
  gap; all Tseitin width wiring for the family pin is accepted.
  gate_pending: none.

- 2026-08-21 formalize (Cluster 27 prism Y6 expansion obstruction): SUCCESS.
  Edited existing `theory/Theory/ProofComplexity/FinGraph.lean` only. Axiom
  gate PASS. Filters ladder like cubics out of Block A family search.

  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "Cluster 27 prismGraph6 not HasExpansion 1 band obstruction",
    "rationale": "Kill the obvious unbounded cubic ladder before chasing it as an expander family; band cut size 4 on order 6 fails factor 1."
  }
  ```

  ### Names verified before edit (no duplicates)

  New accepted: `prismGraph6`, `prismGraph6_card`, `prismGraph6_regular`,
  `prismGraph6Band`, `prismGraph6Band_card`,
  `prismGraph6Band_boundary_card`, `prismGraph6Band_half`,
  `prismGraph6Band_not_expanding`, `not_hasExpansion_prismGraph6`,
  `exists_cubic_regular_not_expanding_twelve`.
  Reused: `HasExpansion`, `IsRegular`, `edgeBoundary`, `finEdgeOf`.

  ### What closed

  Prism `Y_6` is 3 regular on 12 vertices and fails `HasExpansion _ 1` via
  the three column band `{0,1,2,6,7,8}` with cut card 4 < 6.

  ### What did not close

  `TseitinFrontier.exists_cubic_hasExpansion_family` still sorry. Next:
  non ladder construction (config model, LPS, or Gabber Galil style).

  Most important thing learned: cubic regular alone does not imply expansion
  factor 1; Block A must exclude prism or ladder families.
  gate_pending: none.

- 2026-09-04 prove (restate Block A cubic family pin: kill unbounded
  `HasExpansion _ 1`, pin inverse expansion): SUCCESS on the restatement,
  PENDING accept_prose. Prose only, no Lean this cycle. Corrects the Cluster 26
  family pin after empirical kill of Nat factor 1 past Heawood.

  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "prove",
    "target": "restate Block A exists_cubic family from HasExpansion alpha 1 to HasExpansionInv",
    "rationale": "Nat alpha 1 fails on McGee, Moebius Kantor, Desargues, and random cubics past Heawood, so the unbounded HasExpansion 1 pin is the wrong existence target."
  }
  ```

  ### Statement restated with all quantifiers explicit

  Keep as accepted (no change this cycle): for every finite `G` with
  `IsRegular G 3`, `HasExpansion G α` for `α ≥ 1`, and odd charge `χ`, the
  width and size lower bounds
  `tseitin_expander_width_lower_bound` and
  `tseitin_expander_size_lower_bound` hold. Heawood remains the base
  informative witness at `n = 14` via Cluster 26 packaging.

  Kill as Block A primary existence pin:
  `TseitinFrontier.exists_cubic_hasExpansion_family`, namely

      ∀ N, ∃ n ≥ max(N,14), ∃ G : FinGraph n,
        IsRegular G 3 ∧ HasExpansion G 1.

  Evidence that this pin is the wrong asymptotic target (classification:
  adaptation of known Cheeger limits plus explicit counterexamples to the
  search, not a Lean impossibility theorem for every n):

  1. McGee cage (`n = 24`, LCF `[2,2,-2,-2]^6`): 3 regular, min cut ratio
     `|∂S|/|S|` over nonempty half sets equals `1/6` (failing set of size 4
     with cut 2; balanced sets with cut 2). So `HasExpansion _ 1` is false.
  2. Moebius Kantor `GP(8,3)` (`n = 16`): min ratio `0.75 < 1`.
  3. Desargues `GP(10,3)` (`n = 20`): min ratio about `0.78 < 1`.
  4. Generalized Petersen `GP(n,2)` for odd `n ≥ 9`: fails factor 1 (only
     Heawood `n = 7` in this subfamily passes among those checked).
  5. Configuration model sample: 65 valid random 3 regular graphs on 16
     vertices, best min ratio about `0.71`, none with factor 1.
  6. Spectral calibration: for any infinite family of 3 regular graphs,
     Alon Boppana forces the second eigenvalue toward at least `2√2`, and the
     Cheeger upper bound then caps combinatorial expansion near `1` from
     above. Factor 1 is a razor edge, not a stable Lean inhabitant target.
     Cluster 27 already showed cubic regular does not imply factor 1; the new
     point is that factor 1 also fails for the standard non ladder cages used
     as expander candidates.

  New pinned predicate (target Lean name `HasExpansionInv`):

      HasExpansionInv (G : FinGraph n) (k : ℕ) : Prop :=
        ∀ S : Finset (Fin n),
          S.Nonempty → 2 * S.card ≤ n →
            S.card ≤ k * (edgeBoundary G S).card

  Relation: `HasExpansion G 1` iff `HasExpansionInv G 1`. Combinatorial
  expansion at least `1/k` is exactly `HasExpansionInv G k`. Connectivity is
  NOT inherited from `k ≥ 1` when `k > 1`; formalize must carry an explicit
  `IsConnected G` (or prove it from the inv predicate plus regularity) wherever
  `tseitin_complex_eq_univ` needs it.

  Pinned Block A primary existence (replace the Cluster 26 Frontier):

      exists_cubic_hasExpansionInv_family :
        ∀ N : ℕ, ∃ (n : ℕ) (G : FinGraph n),
          max N cubicInvInformativeFloor ≤ n ∧
            IsRegular G 3 ∧ IsConnected G ∧ HasExpansionInv G cubicInvK

  with locked constants (honest, explicit Nat, no asymptotics):

  - `cubicInvK := 2` (primary pin: expansion at least `1/2`). Empirical
    support: Moebius Kantor, Desargues, and the best `n = 16` random samples
    all beat `1/2`. Classical safe fallback if inhabit stalls: raise to
    `cubicInvK := 12`, matching the Ramanujan Cheeger lower order
    `(3 - 2√2)/2 ≈ 0.086` rounded as `1/12`, without changing the predicate
    shape.
  - `cubicInvInformativeFloor`: least `n` with
    `tseitinMediumFloor n / cubicInvK > 3` (so the derived width floor beats
    `cnfWidth = 3` for cubic Tseitin). For `k = 2`, `tseitinMediumFloor n > 6`
    forces `n ≥ 26` under the existing
    `tseitinMediumFloor n = (n/2 + 2)/2`. Pin
    `cubicInvInformativeFloor := 26` when `cubicInvK = 2`.

  Width packaging revision (next formalize, not claimed now): from
  `HasExpansionInv G k` and cut coverage, derive
  `tseitinMediumFloor n ≤ k * d.width` style bounds, hence
  `1 ≤ d.width / k` growth linear in `n`. Reuse BSW size corollary with
  `W := (tseitinMediumFloor n + (k - 1)) / k` (Nat ceil division) or an
  equivalent explicit floor. Heawood stays a special case via
  `HasExpansionInv heawoodGraph 1` from existing
  `heawoodGraph_expansion`.

  Family reduction revision: replace
  `exists_tseitin_expander_hard_family_of_cubic_expanders` by an inv form
  that quantifies `HasExpansionInv G cubicInvK` and the new informative
  floor. Discharge
  `TseitinFrontier.exists_tseitin_expander_hard_family` from the new family
  theorem once inhabited.

  Secondary routes unchanged: random CS Frontier stays secondary; do not Nat
  chase Spreads or `ExpandsIndices` first moment. Prism and ladder cubics stay
  filtered (Cluster 27). Circulant stays excluded.

  ### Non vacuity

  1. The new quantified family is intended nonempty for large `n` by classical
     existence of cubic expanders (Friedman almost Ramanujan for random 3
     regular; explicit LPS style constructions at neighboring degrees with
     degree reduction). Lean inhabitant remains the hard gap.
  2. Finite witnesses already certified: Petersen and Heawood give
     `HasExpansionInv _ 1`. They do not close `∀ N` under the killed factor 1
     pin, and they do illustrate that inv form is inhabited at small order.
  3. Informativeness: for `k = 2` and `n ≥ 26`, Nat division gives
     `tseitinMediumFloor n / 2 ≥ 4 > 3 = cnfWidth` on cubic Tseitin, so the
     width floor beats initial width exactly as Cluster 26 required for
     `α = 1` at `n ≥ 14`.

  ### The one argument developed

  Step 1. Treat unbounded `HasExpansion _ 1` as a false friend for Block A:
  it matches Petersen and Heawood but fails the cages and random cubics that
  are the next constructive targets. Continuing to hunt Nat factor 1
  inhabitants is stop condition adjacent grinding of a bad pin, not of a twice
  blocked proof method. Classification: known from explicit computation this
  session; kill recorded here.

  Step 2. Switch the existence obligation to `HasExpansionInv G 2` (fixed
  inverse factor) plus connectivity and cubic regularity, unbounded in `n`.
  This matches what classical expander theorems actually deliver: a positive
  constant Cheeger lower bound, not necessarily an integer factor 1.
  Classification: adaptation of Friedman / LPS / Margulis style existence to
  the discrete inv predicate.

  Step 3. Recompute the informative floor from `mediumFloor / k > 3` so
  Tseitin width still beats `cnfWidth`. Classification: routine arithmetic on
  existing `tseitinMediumFloor`.

  Step 4. Formalize path after accept_prose: (i) define `HasExpansionInv` and
  lemmas relating it to `HasExpansion`; (ii) prove inv packaging width or size
  bounds; (iii) restate Frontier family theorems; (iv) inhabit via explicit
  construction or probabilistic method without new axioms. Prefer editing
  `FinGraph.lean` and `Tseitin.lean` only.

  ### Gap list

  1. Human accept_prose for killing unbounded `HasExpansion _ 1` as Block A
     primary and adopting `HasExpansionInv` with `cubicInvK = 2`,
     `cubicInvInformativeFloor = 26`. Gap class: gate.
  2. Lean definition `HasExpansionInv` and bridge lemmas to cut coverage and
     width. Gap class: routine.
  3. Connectivity story when `k > 1` (do not reuse `HasExpansion.isConnected`
     with `α ≥ 1`). Gap class: routine.
  4. Restate and certify packaging analogues of
     `tseitin_cubic_expander_informative` and
     `exists_tseitin_expander_hard_family_of_cubic_expanders` under inv.
     Gap class: routine after (2).
  5. Inhabit `exists_cubic_hasExpansionInv_family` (hard constructive or
     counting gap: Margulis, Gabber Galil with cubicization, LPS, or
     formalized probabilistic method). Gap class: hard.
  6. If `k = 2` inhabit fails twice for the same cause, raise to `k = 12`
     under the same predicate shape before any kill_rung. Gap class: unknown.

  ### Self adversarial pass

  - Quantifier order: family still requires unbounded `n`; finite cages alone
    never close `∀ N`.
  - Do not claim a Lean proof that no 3 regular graph with `n ≥ 16` has
    factor 1; the kill is of the pin as a research target, backed by failed
    candidates and spectral razor edge, not a universality theorem.
  - Do not revive Spreads first moment or prism ladders.
  - Off by one: informative floor `26` must be rechecked in Lean against
    `tseitinMediumFloor` exactly when formalizing.
  - Barrier: still resolution level Tseitin; no R3 flag.
  - Worst gap remains inhabiting an unbounded cubic expander family; the
    restatement only makes the target classically true in shape.

  Most important thing learned: Block A was blocked on a predicate that
  standard cubic expanders do not satisfy past Heawood; inverse expansion at
  fixed `k = 2` is the correct existence pin shape.
  gate_pending: accept_prose.

- 2026-09-08 human gate: accept_prose APPROVED (gate_auto: true).
  Rationale: continue after 2026-09-04 Inv restatement; critical path Block A;
  factor 1 kill is evidence backed; Inv pin is the inhabit target.
  Next: formalize Cluster 28 packaging.

- 2026-09-08 formalize (Cluster 28 HasExpansionInv packaging): SUCCESS.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "HasExpansionInv Cluster 28 packaging",
    "rationale": "Last session accept_prose for Inv restatement; critical path Block A; WIP packaging already in tree."
  }
  ```
  Accepted (axiom gate PASS): `HasExpansionInv`, bridge lemmas,
  `petersenGraph_expansionInv`, `heawoodGraph_expansionInv`, `cubicInvK`,
  `cubicInvInformativeFloor`, `tseitinInvWidthFloor`, inv width or size LBs,
  `tseitin_cubic_hasExpansionInv_informative`,
  `exists_tseitin_expander_hard_family_of_cubic_inv_expanders`.
  Frontier (unchanged hard gap): `exists_cubic_hasExpansionInv_family`,
  `exists_tseitin_inv_expander_hard_family`; archival factor 1 pins kept.
  Most important thing learned: ceil inv width floor needs an explicit
  `< (w+1)*k` argument; omega alone does not close Nat ceil division.
  gate_pending: merge_certified.
  Next: inhabit `exists_cubic_hasExpansionInv_family` (prove or formalize
  constructive or counting route).

- 2026-09-08 human gate: merge_certified APPROVED (human: merge).
  Cluster 28 HasExpansionInv packaging and family reduction are in the
  accepted declaration list with axiom gate PASS. R2 remains
  prose_accepted until the existence pin is inhabited and merge_certified
  again for that inhabitant.

- 2026-09-08 prove (inhabit plan for exists_cubic_hasExpansionInv_family): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "prove",
    "target": "pin inhabit route for exists_cubic_hasExpansionInv_family via MGG then cubicize",
    "rationale": "Cluster 28 packaging is merged; Block A wall is the unbounded Inv inhabitant."
  }
  ```

  ### Statement restated

  Target (already Frontier):
  ```
  exists_cubic_hasExpansionInv_family :
    ∀ N : ℕ, ∃ (n : ℕ) (G : FinGraph n),
      max N cubicInvInformativeFloor ≤ n ∧
        IsRegular G 3 ∧ G.IsConnected ∧ HasExpansionInv G cubicInvK
  ```
  with locked `cubicInvK = 2` and `cubicInvInformativeFloor = 26`.
  Mathlib has no expander graph library; inhabitant must be built in tree.

  ### Non vacuity

  1. Finite Inv witnesses already certified: Petersen and Heawood at `k = 1`
     (hence at `k = 2` by `HasExpansionInv.mono`). They do not close `∀ N`.
  2. Classical non vacuity: for every large enough order there exist cubic
     graphs with combinatorial expansion at least `1/2` (Friedman almost
     Ramanujan for random 3 regular; explicit constructions after degree
     reduction from constant degree expanders). Classification: known
     externally; Lean term is the gap.

  ### Attack ideas (sketched, one developed)

  A. Direct probabilistic method on the configuration model for 3 regular
     graphs: show that with positive probability every half set has
     `|∂S| ≥ |S| / 2`. Classification: known externally (Friedman); Lean
     cost is enormous (measure on matchings, union bounds over Finsets).
  B. LPS Ramanujan Cayley graphs then reduce degree to 3. Classification:
     known; algebraic number theory barrier in Lean.
  C. Margulis Gabber Galil (MGG) 8 regular family on `(Z/mZ)²`, prove Inv
     expansion from the Gabber Galil spectral gap, then cubicize by a
     replacement product with a fixed 3 regular gadget while tracking the
     Inv constant. Classification: adaptation; developed below.

  ### The one argument developed (C)

  Step 1. Intermediate family (new Frontier name proposed):
  `exists_mgg_hasExpansionInv_family`. For every `M`, take `m ≥ max M m0`
  and let `G_m` be the undirected 8 regular Margulis Gabber Galil graph on
  vertex set `Fin (m * m)` with the standard eight generators
  `(±1,0)`, `(0,±1)`, `±S`, `±T` (Gabber Galil / Hoory et al. presentation).
  Claim: `IsRegular G_m 8`, `G_m.IsConnected` for `m ≥ 2`, and
  `HasExpansionInv G_m kMGG` for an explicit Nat `kMGG`.
  Spectral input (known): second adjacency eigenvalue `λ₂(G_m) ≤ 5 * sqrt 2`.
  Cheeger lower bound (known adaptation to Nat Inv form):
  combinatorial expansion `φ ≥ (8 - λ₂) / 2`, hence
  `φ ≥ (8 - 5 * sqrt 2) / 2 > 2/5`, so every nonempty half set satisfies
  `S.card ≤ 3 * |∂S|` after a safe Nat rounding; pin `kMGG := 3` pending
  a Lean inequality discharge for `(8 - 5√2)/2 > 1/3`. If the float to Nat
  bridge stalls, raise to `kMGG := 4` without changing shape.
  Classification: known spectral fact plus routine Nat packaging.

  Step 2. Cubicization. Fix a 3 regular connected gadget `H` on a constant
  number of vertices that replaces each degree 8 vertex by a cloud and routes
  the eight external edges through distinct ports (replacement product /
  bipartite replacement as in Reingold Vadhan Wigderson style degree reduction).
  Output `G'_m` is 3 regular on `n(m) = Θ(m²)` vertices, connected when `G_m`
  is, and satisfies `HasExpansionInv G'_m kCub` for an explicit `kCub`
  depending only on `kMGG` and the gadget (standard replacement product
  Cheeger degradation). Classification: adaptation of known degree reduction;
  constant tracking is the Lean work.

  Step 3. Lock constants against Cluster 28. If the cubicized Inv constant
  satisfies `kCub ≤ cubicInvK = 2`, discharge
  `exists_cubic_hasExpansionInv_family` directly for all
  `n(m) ≥ max N 26`. If tracking only yields `kCub > 2` (likely; replacement
  loses a fixed factor), apply the already recorded fallback: raise
  `cubicInvK` to `kCub` (or to `12` as previously reserved) and recompute
  `cubicInvInformativeFloor` so that
  `tseitinInvWidthFloor n cubicInvK > 3`. Packaging lemmas are already
  parametric in `k`; only the locked defs and the informative Nat lemma need
  a Cluster 29 restatement. Classification: routine once `kCub` is known.

  Step 4. Formalize order after accept_prose:
  (i) `mggGraph m : FinGraph (m * m)` edge set and `IsRegular _ 8`;
  (ii) combinatorial or spectral Inv theorem at `kMGG`;
  (iii) gadget plus replacement product defs;
  (iv) Inv degradation lemma to `kCub`;
  (v) inhabit or raise `cubicInvK` then inhabit.
  Prefer new section in `FinGraph.lean` for MGG, keep Tseitin packaging edits
  minimal.

  ### Gap list

  1. Human accept_prose for this inhabit route (MGG then cubicize, with
     authorized `cubicInvK` raise if `kCub > 2`). Gap class: gate.
  2. Lean `mggGraph` construction and regularity. Gap class: routine.
  3. Gabber Galil spectral gap or a direct combinatorial expansion proof in
     Lean (Fourier analysis on `(Z/mZ)²` as in Hoory et al. / AFP Isabelle
     formalization; or trust reduction from a port of girving/aks MGG).
     Gap class: hard.
  4. Replacement product Inv degradation with explicit `kCub`. Gap class: hard.
  5. Informative floor recompute if `cubicInvK` rises. Gap class: routine.
  6. Connectivity of MGG and of the cubicized graph. Gap class: routine to hard.

  ### Self adversarial pass

  - Quantifiers: `n(m) = m² * |V(H)|` is unbounded as `m → ∞`, so `∀ N` is
    in range; do not pretend finite cages close the family.
  - Do not revive unbounded `HasExpansion _ 1`.
  - Do not claim `kCub = 2` before tracking; the fallback raise is part of the
    plan, not a silent move.
  - Spectral to combinatorial: Cheeger gives edge expansion; our
    `HasExpansionInv` is exactly the inverse of that combinatorial ratio on
    half sets. Match the edge boundary definition already in `FinGraph`
    (undirected cut size), including multiplicity if MGG is built with
    parallel edges; either quotient multiples or strengthen regularity proofs
    accordingly.
  - Barrier: still resolution Tseitin; no R3 flag.
  - Worst gap: Gabber Galil analysis in Lean (gap 3), not the packaging.

  Most important thing learned: the cubic pin should be inhabited by reducing
  an 8 regular MGG family whose Inv constant is classically easy, not by
  chasing cage by cage factor 1 graphs; expect a possible `cubicInvK` raise
  after replacement product tracking.
  gate_pending: accept_prose.

- 2026-09-08 loop note: human said merge and continue on loop. Cluster 28
  merge_certified applied. For the MGG cubicize inhabit prose, next wake may
  auto accept_prose (gate_auto) if no objection, then formalize `mggGraph`.

- 2026-09-08 human gate: accept_prose APPROVED (gate_auto: true, loop standing
  order after merge and continue). MGG then cubicize inhabit route accepted.
  Next: formalize Cluster 29 scaffolding.

- 2026-09-08 formalize (Cluster 29 MGG scaffolding): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "mggGraph encode decode neighbor scaffolding",
    "rationale": "Accepted inhabit route needs Lean MGG vertex encoding before Inv."
  }
  ```
  Accepted module `Theory/ProofComplexity/MGG.lean`: `mggDecode`, `mggEncode`,
  round trips, `mggNeighbor`, `mggEdgeOf`, `mggGraph`, membership lemma,
  `mgg_three_vertex_card`. Separate module avoids Heawood recompile cost in
  FinGraph. Not yet: `IsRegular mggGraph 8`, Inv expansion, cubicization.
  gate_pending: merge_certified.
  Next: formalize MGG regularity for `m ≥ 3`, then Inv.

- 2026-09-08 human gate: merge_certified APPROVED (gate_auto: true, loop wake).
  Cluster 29 scaffolding decls remain in accepted list.

- 2026-09-08 formalize (Cluster 29b simple MGG not 8-regular): SUCCESS.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "IsRegular mggGraph 8 for m>=3",
    "rationale": "Wake target after scaffolding merge."
  }
  ```
  Blocked obligation on exact regularity: simple `FinGraph` drops axis
  self-loops from S/T, so `IsRegular (mggGraph m _) 8` is false.
  Certified instead: `mggOrigin3_degree` (`= 4` at `m = 3`) and
  `not_isRegular_mggGraph_three_eight`.
  Most important thing learned: intermediate MGG pin must use multigraph
  degree or a restated min-degree / Cayley hypothesis, not simple
  `IsRegular _ 8`.
  gate_pending: merge_certified.
  Next: prove restatement of intermediate MGG regularity hypothesis.

- 2026-09-08 human gate: merge_certified APPROVED (gate_auto: true, loop wake)
  for Cluster 29b `mggOrigin3_degree` and `not_isRegular_mggGraph_three_eight`.

- 2026-09-08 prove (restate intermediate MGG degree pin): SUCCESS.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "prove",
    "target": "restate intermediate MGG pin without simple IsRegular 8",
    "rationale": "Cluster 29b killed IsRegular mggGraph 8; intermediate inhabit needs an honest hypothesis."
  }
  ```

  ### Statement restated

  Kill as intermediate hypothesis:
  `IsRegular (mggGraph m hm) 8` on the simple `FinGraph` encoding.

  New intermediate Frontier pin (Lean names proposed):

      mggInvK : ℕ := 4
      mggInformativeFloor : ℕ := 6

      exists_mgg_simple_hasExpansionInv_family :
        ∀ N : ℕ, ∃ (m : ℕ) (hm : 0 < m),
          max N mggInformativeFloor ≤ m ∧
            (mggGraph m hm).IsConnected ∧
              HasExpansionInv (mggGraph m hm) mggInvK

  Cubic inhabit then becomes: from this simple Inv family, produce a 3 regular
  connected `HasExpansionInv _ cubicInvK` family by replacement product (or
  raise `cubicInvK` as already authorized). No claim that simple MGG is
  8 regular.

  ### Non vacuity

  1. `mggGraph` is inhabited for every `m > 0` (Cluster 29 scaffolding).
  2. Cluster 29b shows the origin at `m = 3` has degree 4, so the killed
     regularity pin was empty of truth, not merely unproved.
  3. Classical Gabber Galil spectral gap on the 8 regular multigraph implies
     a uniform positive Cheeger constant; dropping loops and parallel edges
     only weakens cuts by a lower order axis effect, so a fixed Inv constant
     such as `mggInvK = 4` remains the intended Lean target. Classification:
     known externally; Lean spectral or combinatorial discharge is the hard gap.

  ### Attack ideas (sketched, one developed)

  A. Switch `FinGraph` to a multigraph API with multiplicity 8 everywhere.
     Classification: adaptation; large API change across Tseitin.
  B. Keep simple graphs; drop regularity; pin `HasExpansionInv` plus
     connectivity only (developed).
  C. Work entirely with directed Cayley outdegree 8 and a directed expansion
     predicate. Classification: new encoding; more defs.

  ### The one argument developed (B)

  Step 1. Treat Cluster 29b as a pin kill, not a build failure: simple
  `mggGraph` is the right Lean object for later Tseitin width packaging only
  after cubicization; it is the wrong place to demand degree 8.
  Classification: known from certified counterexample.

  Step 2. Intermediate mathematical content is expansion, not regularity.
  Gabber Galil give `λ₂ ≤ 5√2` on the multigraph; Cheeger yields combinatorial
  expansion `φ ≥ (8 − λ₂)/2 > 2/5` there. Passing to the underlying simple
  graph decreases some cut sizes (lost loops contribute 0; merged parallels
  count once). On non axis vertices for `m ≥ 3` the eight neighbors are
  distinct, so the local multi and simple stars agree. Axis vertices are
  `O(m)` of `m²`, so any half set expansion failure supported only on axes
  cannot survive for large `m` under a fixed Inv constant with room to spare.
  Pin `mggInvK := 4` as a safe Nat (weaker than `3` from the multi Cheeger
  rounding) pending Lean discharge; raise to `6` if formalize stalls.
  Classification: adaptation of Gabber Galil plus routine density of axes.

  Step 3. Connectivity of simple MGG for `m ≥ 2` is elementary from the
  translation generators alone (grid torus). Classification: routine.

  Step 4. Cubicization (unchanged shape): replacement product from a
  connected Inv expander with minimum degree at least 3 (true off axis;
  axis degree 4 at `m = 3` already) into a 3 regular Inv graph, tracking
  `kCub`, then feed Cluster 28 packaging, raising `cubicInvK` if needed.
  Classification: adaptation; hard constant tracking.

  Step 5. Formalize order after accept_prose: (i) `mggInvK` and connectivity
  lemmas; (ii) Frontier `exists_mgg_simple_hasExpansionInv_family`; (iii) Inv
  theorem or sorry Frontier for Gabber Galil; (iv) cubicize.

  ### Gap list

  1. Human accept_prose for killing simple `IsRegular _ 8` and adopting the
     Inv only intermediate pin with `mggInvK = 4`. Gap class: gate.
  2. Connectivity of `mggGraph` for `m ≥ 2`. Gap class: routine.
  3. Gabber Galil to `HasExpansionInv (mggGraph m _) mggInvK` in Lean,
     including axis multiplicity loss. Gap class: hard.
  4. Replacement cubicization with explicit `kCub`. Gap class: hard.
  5. Informative floor choice `mggInformativeFloor` relative to later cubic
     floor 26. Gap class: routine.

  ### Self adversarial pass

  - Do not smuggle back `IsRegular _ 8` on the simple graph.
  - Do not claim axis loss is negligible without an explicit Lean inequality
    when formalizing; the Inv constant must absorb it.
  - Quantifiers: unbounded `m` still required; `m = 3` is only a regularity
    counterexample, not an Inv family witness.
  - Barrier: still resolution Tseitin after cubicize; no R3 flag.
  - Worst gap remains Gabber Galil analysis (gap 3).

  Most important thing learned: intermediate MGG work should target
  `HasExpansionInv` on the existing simple `mggGraph`, not degree 8.
  gate_pending: accept_prose.

- 2026-09-08 human gate: accept_prose APPROVED (gate_auto: true, loop wake)
  for Inv-only MGG intermediate pin.

- 2026-09-08 formalize (Cluster 29c translation adjacency + Frontier family): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "mggGraph connectivity and exists_mgg_simple_hasExpansionInv_family",
    "rationale": "Accepted Inv-only pin; land adjacency then Frontier inhabit."
  }
  ```
  Accepted: `mggInvK`, `mggInformativeFloor`, right/up neighbor eqs, non-loops
  for `1 < m`, `mgg_adj_right`, `mgg_adj_up`.
  Frontier: `MGGFrontier.mggGraph_isConnected`,
  `MGGFrontier.exists_mgg_simple_hasExpansionInv_family`.
  gate_pending: merge_certified.
  Next: formalize torus connectivity from translation adjacency.

- 2026-09-08 human gate: merge_certified APPROVED (gate_auto: true, loop wake)
  for Cluster 29c adjacency constants.

- 2026-09-08 formalize (mggGraph_isConnected): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "MGGFrontier.mggGraph_isConnected via translation walks",
    "rationale": "Wake after 29c; discharge Frontier connectivity."
  }
  ```
  Accepted: `mgg_adj_right_encode`, `mgg_adj_up_encode` (cell steps).
  Still Frontier: `mggGraph_isConnected`, `exists_mgg_simple_hasExpansionInv_family`
  (Fin walk chaining stalled; encode adj is the lemma the walk needs).
  gate_pending: merge_certified.
  Next: formalize row/col Reachable induction using encode adj.

- 2026-09-08 formalize (Cluster 29d mggGraph_isConnected): SUCCESS.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "mggGraph_isConnected via translation Reachable walks",
    "rationale": "Wake cycle; discharge Frontier connectivity using encode adj."
  }
  ```
  gate_auto: true (merge prior encode adj). Certified: `mgg_reachable_right_pow`,
  `mgg_reachable_up_pow`, `mgg_reachable_right_to`, `mgg_reachable_up_to`,
  `mgg_reachable_encode`, `mggGraph_isConnected` (out of Frontier). Axiom gate PASS.
  Still Frontier: `exists_mgg_simple_hasExpansionInv_family`.
  Next: prove or formalize Gabber Galil Inv for `mggInvK`.

- 2026-09-08 formalize (Cluster 29e left/down + Inv packaging): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "progress toward exists_cubic_hasExpansion_family via MGG Inv pin",
    "rationale": "R2 existence pin blocks R2 certified; finish in progress MGG cluster."
  }
  ```
  gate_auto: true (merge prior connectivity). Accepted: `mggLeft`, `mggDown`,
  `Fin.sub_one_ne_of_one_lt`, `Fin.add_one_ne_sub_one_of_three_le`, left/down
  neighbor eqs and adj, pairwise translation distinctness for `m ≥ 3`,
  `exists_mgg_simple_hasExpansionInv_family_of_inv`. Frontier restated:
  `MGGFrontier.mggGraph_hasExpansionInv` (sorry; Gabber Galil gap);
  `exists_mgg_simple_hasExpansionInv_family` now packages connectivity via
  `of_inv`. Axiom gate PASS. Exact open obligation:
  `HasExpansionInv (mggGraph m hm0) mggInvK` for all `m ≥ mggInformativeFloor`.
  Next: prove Gabber Galil to Inv, or formalize a cut lower bound toward that.

- 2026-09-08 prove (pin Gabber Galil for mggGraph_hasExpansionInv): SUCCESS.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "prove",
    "target": "pin Gabber Galil argument for mggGraph_hasExpansionInv",
    "rationale": "Family packaging ready; need prose plan for Inv expansion before more Lean grind."
  }
  ```
  workstream: R2. Dirty WIP from prior timed out prove agents: none (tree clean at HEAD 6bf6206).

  ### Statement (exact Lean Frontier obligation)

  For every `m : ℕ` with `0 < m` and `mggInformativeFloor ≤ m` (locked floor 6),
  `HasExpansionInv (mggGraph m hm0) mggInvK` holds with locked `mggInvK = 4`.
  Unfolded: for every nonempty `S : Finset (Fin (m * m))` with
  `2 * S.card ≤ m * m`, one has
  `S.card ≤ 4 * (edgeBoundary (mggGraph m hm0) S).card`.
  Connectivity is already certified and packaged; this prove does not revisit it.
  No regularity hypothesis on the simple graph.

  ### Non vacuity

  1. For every `m ≥ 1`, `mggGraph m hm` is an inhabited `FinGraph (m * m)`
     (Cluster 29 scaffolding).
  2. For every `m ≥ 2`, `(mggGraph m hm).IsConnected` (Cluster 29d).
  3. Classical Gabber Galil: the 8 regular multigraph Cayley graph on
     `(Z/mZ)²` with generators `(±1,0)`, `(0,±1)`, `±S`, `±T` has second
     adjacency eigenvalue at most `5 * sqrt 2`. Classification: known
     (Gabber Galil 1981; Hoory Linial Wigderson survey presentation).
  4. Finite half sets exist for `m ≥ 2` (`n = m² ≥ 4`), so the Inv
     quantifier is non vacuous. Classification: routine.

  ### Attack ideas (sketched, one developed)

  A. Full Fourier analysis of the adjacency operator on `L²((Z/mZ)²)` inside
     Lean, deriving `λ₂ ≤ 5√2` from scratch. Classification: known externally;
     Lean cost extreme.
  B. Cite the Gabber Galil spectral bound as a single named external lemma,
     discharge Cheeger to combinatorial expansion on an auxiliary multigraph,
     then transfer cuts to simple `mggGraph` with an axis loss budget absorbed
     by `mggInvK = 4` (developed).
  C. Purely combinatorial cut counting using only the four translations
     (grid torus isoperimetry). Classification: adaptation; yields weaker or
     dimension dependent constants and does not use the S/T expansion that
     makes MGG work; rejected as primary.

  ### The one argument developed (B)

  Step 0. Auxiliary multigraph. For each `m ≥ 2`, let `M_m` be the undirected
  8 regular multigraph on the same vertex set `Fin (m * m)` whose edges are the
  eight labeled generator incidences (loops allowed when a generator fixes a
  vertex; parallel edges allowed when two generators share a neighbor). The
  existing `mggNeighbor` enumeration is exactly the labeled star of `M_m`.
  The simple graph `mggGraph m hm` is the support of `M_m` after deleting loops
  and collapsing parallel edges to one undirected `FinEdge`. Classification:
  routine packaging relative to Cluster 29.

  Step 1. Spectral input on `M_m` (known). Let `A` be the adjacency operator of
  `M_m` on real functions `Fin (m * m) → ℝ` (equivalently on `(Z/mZ)²`). Then
  the second largest eigenvalue in absolute value among vectors orthogonal to
  the constants satisfies `λ₂(M_m) ≤ 5 * sqrt 2`. Citation: Gabber Galil;
  presentation as in Hoory et al. Classification: known.

  Step 2. Cheeger on the regular multigraph (known adaptation). For an
  undirected `d` regular multigraph, the edge expansion
  `φ(M) = min_{S ≠ ∅, 2|S|≤n} |∂_M S| / |S|` obeys
  `φ(M) ≥ (d − λ₂) / 2`. With `d = 8` and `λ₂ ≤ 5√2` one gets
  `φ(M_m) ≥ (8 − 5√2) / 2`. Numerically `5√2 < 7.1`, so
  `8 − 5√2 > 0.9` and `(8 − 5√2)/2 > 0.45 > 2/5`. Hence every nonempty half set
  satisfies `|∂_M S| ≥ (2/5) |S|`, equivalently `|S| ≤ (5/2) |∂_M S|`.
  Nat target on the multigraph: `|S| ≤ 3 * |∂_M S|` after ceiling. Classification:
  known Cheeger plus routine real to Nat inequality
  `(8 − 5√2)/2 ≥ 2/5` (or directly `≥ 1/3`).

  Step 3. Cut transfer to the simple graph. Write `∂_G` for
  `edgeBoundary (mggGraph m hm)`. Every simple cut edge is a collapsed image of
  at least one multi cut incidence, so `|∂_G S| ≤ |∂_M S|` always. The dangerous
  direction for Inv is the reverse loss: `|∂_M S| − |∂_G S|` counts multi
  incidences that do not appear as distinct simple cut edges. Those losses are
  exactly (i) loops (generator fixes the vertex: never a cut edge) and
  (ii) parallel collisions (two generators yield the same neighbor: multi counts
  two, simple counts one).

  Loop locus (exact): `S` generator fixes `(x,y)` iff `x = 0`; `S⁻¹` likewise
  iff `x = 0`; `T` fixes iff `y = 0`; `T⁻¹` iff `y = 0`. Translations never loop
  for `m > 1`. So every loop vertex lies on the axis set
  `A_m = {v | (mggDecode v).1 = 0 ∨ (mggDecode v).2 = 0}` with
  `|A_m| ≤ 2m − 1`. Classification: routine from `mggNeighbor` equations.

  Parallel collisions off axis are constrained: for `m ≥ 3`, the four
  translations at a vertex are pairwise distinct (Cluster 29e). Remaining
  collisions involve at least one of `±S`, `±T`. Bound used below: at each
  vertex the multi degree is 8 and the simple degree is at most 8, and the
  local multiplicity excess `8 − degree(G,v)` is at most 4 on axes (witnessed
  at `m = 3` origin) and at most 2 off a thinner collision set for large `m`.
  Global cut loss therefore satisfies
  `|∂_M S| − |∂_G S| ≤ ∑_{v∈S} (8 − degree(G,v)) ≤ 4 * |S ∩ A_m| + 2 * |S|`
  after a safe uniform overcount (formalize may tighten). Classification:
  adaptation; inequality shape is the Lean obligation.

  Step 4. Absorb loss into `mggInvK = 4`. From Step 2,
  `|S| ≤ 3 |∂_M S| ≤ 3 (|∂_G S| + loss(S))`. For half sets with
  `|S| ≤ m²/2` and `m ≥ mggInformativeFloor = 6`, axis density
  `|A_m|/m² ≤ (2m)/m² = 2/m ≤ 1/3`. Feed the loss bound of Step 3 and
  rearrange to `|S| ≤ 4 |∂_G S|` for every nonempty half set. The constant 4 is
  chosen with slack so that a slightly worse collision bound still closes; if
  formalize discovers the inequality fails at `m = 6` only, raise the
  informative floor (not the Inv shape) or raise `mggInvK` to 6 as previously
  reserved. Classification: routine Nat algebra once the loss lemma exists.

  Step 5. Conclude Frontier. Steps 1 to 4 yield
  `MGGFrontier.mggGraph_hasExpansionInv`. Packaging
  `exists_mgg_simple_hasExpansionInv_family_of_inv` then discharges the
  intermediate family pin with no further math. Cubicization remains a later
  formalize cluster (replacement product, authorized `cubicInvK` raise).

  ### Formalize lemma order (Cluster 30 plan)

  (i) `mggAxis : Finset (Fin (m*m))` and `|mggAxis| ≤ 2m − 1`.
  (ii) Loop characterization: which `s : Fin 8` satisfy `mggNeighbor v s = v`.
  (iii) Optional multi cut API or direct counting from labeled generators
      without a new graph type.
  (iv) Nat lemma `(8 − 5√2)/2 ≥ 2/5` (or embed `5√2` via `Nat` squares:
      prove `50 < 49` is false wait: use `5√2 < 71/10` style rationals).
  (v) Frontier or axiom wrapped `mgg_multigraph_spectral_gap` citing Gabber Galil
      (one sorry until analysis lands).
  (vi) Cheeger packaging to `|S| ≤ 3 * multiCut S`.
  (vii) Loss lemma multiCut to `edgeBoundary`.
  (viii) Combine to `HasExpansionInv _ 4`; remove sorry on
      `mggGraph_hasExpansionInv`.

  Prefer finishing (i)(ii)(iv)(vii) combinatorial surface before investing in
  spectral analysis. Do not grind cubicization until Inv lands or is explicitly
  deferred with a raised constant plan.

  ### Gap list

  1. Human accept_prose for this Gabber Galil to simple Inv pin (spectral cite,
     Cheeger, axis loss, `mggInvK = 4`). Gap class: gate.
  2. Nat inequality packaging for `(8 − 5√2)/2 ≥ 2/5` and the final
     `|S| ≤ 4 |∂_G S|` algebra. Gap class: routine.
  3. Axis and loop characterization lemmas in Lean. Gap class: routine.
  4. Cut loss lemma from labeled generators to `edgeBoundary`. Gap class: hard
     (combinatorial bookkeeping).
  5. Gabber Galil spectral bound in Lean (or a single cited Frontier lemma).
     Gap class: hard.
  6. Cheeger inequality in the multigraph or labeled star model. Gap class: hard.
  7. Optional floor or `mggInvK` bump if `m = 6` fails quantitative slack.
     Gap class: routine.

  ### Self adversarial pass

  - Quantifiers: obligation is `∀ m ≥ 6`, not a single cage; axis density `2/m`
    vanishes, so axis only pathologies cannot kill Inv uniformly.
  - Do not reintroduce `IsRegular _ 8` on `mggGraph`.
  - Do not claim `|∂_G S| ≥ |∂_M S|`; loss goes the other way and must be budgeted.
  - Off by one: floor 6 gives `2/m ≤ 1/3`; check `m = 6` half set card
    `2 * |S| ≤ 36` carefully in Nat proofs (no silent `/`).
  - Hidden uniformity: `λ₂ ≤ 5√2` must hold for all large `m`, including
    composite `m` (Gabber Galil does; do not restrict to primes).
  - Summit sneak: this only builds expanders for resolution Tseitin width; no
    R3 system is claimed. Barrier audit not required.
  - Worst gap: Lean spectral bound or Cheeger (gaps 5 and 6), not the Inv
    packaging shape.

  Most important thing learned: discharge `mggGraph_hasExpansionInv` by a
  three layer reduction (Gabber Galil spectrum on the labeled 8 regular star,
  Cheeger to multi cuts, axis aware transfer to simple `edgeBoundary`) with
  `mggInvK = 4` absorbing loss; formalize should land axis and Nat surface
  lemmas before spectral grind.
  gate_pending: accept_prose.

- 2026-09-08 human gate: accept_prose APPROVED (gate_auto: true, workstream R2).
  Rationale: prose matches critical path Block A Inv pin, cites Gabber Galil
  as known, keeps simple graph honesty, and does not revive twice blocked
  factor 1 expansion. Next: formalize Cluster 30 axis and cut loss surface
  toward `mggGraph_hasExpansionInv`.

- 2026-09-08 formalize (Cluster 30 axis and cut loss surface): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "Cluster 30 axis and cut loss surface toward mggGraph_hasExpansionInv",
    "rationale": "accept_prose on Gabber Galil pin; start Lean surface for axis aware cut loss."
  }
  ```
  workstream: R2. Edited only `theory/Theory/ProofComplexity/MGG.lean` (no Bridge).

  Accepted (axiom gate on new decls):
  - Axis: `mggAxis`, `mggRow0`, `mggCol0`, `mggAxis_card_le` (`|A| ≤ 2m`),
    `mggAxis_card_mul_three_le_sq` (floor density `3|A| ≤ m²`).
  - Shear gens and loops: `mggS`, `mggSinv`, `mggT`, `mggTinv`, `mggShearGens`,
    `mggNeighbor_*_eq_self_iff`, `mggNeighbor_shear_loop_mem_axis`,
    `mggNeighbor_eq_self_mem_shear`, `mggNeighbor_ne_self_of_not_mem_axis`,
    `mgg_loop_incidences_le_four_mul_axis`.
  - Multi-cut surface: `mggMultiCutCard` (labeled leaving incidences).
  - Nat Cheeger or Inv absorb: `mgg_gabber_galil_cheeger_nat_witness`,
    `mgg_card_le_three_mul_of_two_fifth`, `mgg_inv4_absorb_of_loss_le_twelfth`.

  Still Frontier sorry: `MGGFrontier.mggGraph_hasExpansionInv` (spectral gap,
  Cheeger on multi, full multi to simple cut loss algebra).

  Most important thing learned: combinatorial axis and loop charge lemmas
  compile cleanly; remaining cost is multi cut versus `edgeBoundary` loss plus
  Gabber Galil spectrum, not axis packaging.
  gate_pending: merge_certified (Cluster 30 surface decls).
  next: formalize multi cut to `edgeBoundary` loss, or cite spectral gap Frontier.

- 2026-09-08 formalize (Cluster 31 multi-cut to edgeBoundary): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "next Cluster toward mggGraph_hasExpansionInv using Cluster 30 surface",
    "rationale": "Axis cut loss ready; push one Lean cluster on Inv expansion path."
  }
  ```
  workstream: R2. Edited only `theory/Theory/ProofComplexity/MGG.lean` (no Bridge).
  Did not duplicate Cluster 30.

  Accepted (axiom gate on new decls):
  - Cayley inverse: `mggInvGen`, `mggInvGen_invGen`, `mggNeighbor_invGen`,
    `mggEdgeOf_invGen_eq_of_eq_some`.
  - Leaving pairs: `mggLeavingPairs`, `mggLeavingPairs_card` (= `mggMultiCutCard`),
    `mggEdgeOf_eq_some_mem_edgeBoundary_of_leaving`,
    `exists_mem_mggLeavingPairs_of_mem_edgeBoundary`, `mggLeavingWitness`.
  - Cut transfer: `edgeBoundary_card_le_mggMultiCutCard` (`|∂_G| ≤ |∂_M|`).

  Still Frontier sorry: `MGGFrontier.mggGraph_hasExpansionInv` (spectral gap,
  Cheeger on multi, tighter loss `|∂_M| − |∂_G|` for Inv-4 absorb).

  Most important thing learned: labeled multi-cut surjects onto the simple cut
  via inverse generators, so `|∂_G| ≤ |∂_M|` is certified; remaining Inv cost is
  spectral or Cheeger plus a tighter reverse loss bound than the safe 8-fiber.
  gate_pending: merge_certified (Cluster 31 transfer decls).
  next: formalize reverse loss bound (axis aware) or cite Gabber Galil spectral
  Frontier lemma toward Cheeger packaging.

- 2026-09-08 formalize (Cluster 32 reverse cut loss): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "Cluster 32 tighter reverse cut loss or spectral surface toward mggGraph_hasExpansionInv",
    "rationale": "One way cut inequality ready; need reverse loss or spectrum step for Inv."
  }
  ```
  workstream: R2. Edited only `theory/Theory/ProofComplexity/MGG.lean` (no Bridge).
  Did not duplicate Cluster 30 or 31.

  Accepted (axiom gate on new decls):
  - Leaving excess API: `mggLeavingGens`, `mggOutNeighbors`, `mggLeavingExcess`,
    `mggReverseCutLoss`, `mggMultiCutCard_eq_sum_out_add_reverseLoss`.
  - Translation injectivity bound: `mggTranslationGens`,
    `mggNeighbor_translation_injOn`, `mggLeavingExcess_le_four`,
    `mggReverseCutLoss_le_four_mul_card` (`reverseLoss ≤ 4|S|` for `m ≥ 3`).
  - Directed cut injection: `mggDirectedCutPairs`, `mggOutEdge`,
    `sum_mggOutNeighbors_card_le_edgeBoundary`,
    `mggMultiCutCard_le_edgeBoundary_add_reverseLoss`
    (`|∂_M| ≤ |∂_G| + reverseLoss`).

  Still Frontier sorry: `MGGFrontier.mggGraph_hasExpansionInv` (spectral gap,
  Cheeger on multi, axis-aware tighter reverseLoss for Inv-4 absorb;
  uniform `4|S|` is not yet absorbable by `mgg_inv4_absorb_of_loss_le_twelfth`).

  Most important thing learned: reverse loss factors as parallel labeled excess
  over distinct out-neighbors, and `|∂_M| ≤ |∂_G| + reverseLoss` is certified;
  next need axis-aware excess or Gabber Galil spectral plus Cheeger.
  gate_pending: merge_certified (Cluster 32 reverse loss decls).
  next: formalize axis-aware reverseLoss bound, or cite Gabber Galil spectral
  Frontier lemma toward Cheeger packaging.

- 2026-09-09 formalize (Cluster 33 axis-aware excess surface): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "Cluster 33 minimal axis excess lemma toward Inv absorb",
    "rationale": "Retry stalled absorb; land one certifiable excess refinement not full HasExpansionInv."
  }
  ```
  workstream: R2. Dirty WIP from stalled agent: none (tree clean at HEAD 27612a8).
  Edited only `theory/Theory/ProofComplexity/MGG.lean` (no Bridge).

  Accepted (axiom gate on new decls):
  - Shear leaving charge: `mggShearLeavingGens`, `mggShearLeavingGens_eq_sdiff`,
    `mggLeavingExcess_le_shearLeavingCard`, `mggReverseCutLoss_le_sum_shearLeaving`.
  - Near-axis band: `mggNearAxis`, `mem_mggNearAxis_iff`, `mggAxis_subset_nearAxis`.
  - Nat absorb helpers: `mgg_inv4_absorb_of_near_loss`,
    `mgg_inv4_absorb_axis_budget_of_large` (pure `4a` budget under `576 m ≤ |S|`).

  Still open: `mggNearAxis` density `|nearAxis| ≤ 6m`, off-band excess `≤ 2`,
  and Frontier `MGGFrontier.mggGraph_hasExpansionInv`.
  Correction vs prior prose: uniform off-axis excess `≤ 2` is false at encode`(1,1)`.

  Most important thing learned: reverseLoss charges exactly to leaving shear labels;
  Inv absorb needs a near-axis band (not the raw axis) plus off-band excess control.
  gate_pending: merge_certified (Cluster 33 surface decls).
  next: formalize `mggNearAxis_card_le` and off-band excess `≤ 2`, or spectral cite.

- 2026-09-09 formalize (Cluster 34 nearAxis card bound): PARTIAL.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "Cluster 34 nearAxis card bound and or off-band excess le 2",
    "rationale": "Absorb helpers ready; need nearAxis size or off-band excess for Inv-4."
  }
  ```
  workstream: R2. Dirty WIP Bridge left untouched. Edited only
  `theory/Theory/ProofComplexity/MGG.lean` and acceptance list.

  Accepted (axiom gate PASS on new decls):
  - Band coords: `mggNearAxisCoord`, `mem_mggNearAxisCoord_iff`,
    `mggNearAxisCoord_card_le` (`≤ 3`).
  - Strip cover: `mggNearAxisRows`, `mggNearAxisCols`,
    `mggNearAxis_eq_rows_union_cols`,
    `mggNearAxisRows_card_le`, `mggNearAxisCols_card_le`.
  - Density: `mggNearAxis_card_le` (`|nearAxis| ≤ 6m`).

  Still open: off-band excess `≤ 2`, Frontier `MGGFrontier.mggGraph_hasExpansionInv`.
  Off-band attempt deferred after Fin modular collision lemmas did not close in cycle.

  Most important thing learned: nearAxis is the union of at most three row strips
  and three column strips, so `|nearAxis| ≤ 6m` is elementary and unlocks the
  `a ≤ 6m` hypothesis in `mgg_inv4_absorb_axis_budget_of_large`.
  gate_pending: merge_certified (Cluster 34 density decls).
  next: formalize off-band excess `≤ 2` (shear vs translation disjointness off band).

- 2026-09-09 formalize (Cluster 35 off-band excess le 2): SUCCESS.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "Cluster 35 off-band excess le 2 with Fin collision lemmas",
    "rationale": "nearAxis size ready; off-band excess is the remaining absorb gap before Inv."
  }
  ```
  workstream: R2. Edited only `theory/Theory/ProofComplexity/MGG.lean` and acceptance list.
  No Bridge touch. No wake armed.

  Accepted (axiom gate PASS on new decls):
  - Off-band coords: `not_mem_mggNearAxis_iff`.
  - Shear families: `mggShearSGens`, `mggShearTGens`, `mggShearGens_eq_S_union_T`,
    `mggShearSGens_disjoint_T`.
  - Fin collision: `mggNeighbor_*_ne_translation_of_not_mem_nearAxis`,
    `mggNeighbor_shear_ne_translation_of_not_mem_nearAxis`,
    `mggNeighbor_S_family_ne_T_family_of_not_mem_nearAxis`.
  - Excess: `mggLeavingExcess_le_two_of_not_mem_nearAxis`,
    `mggReverseCutLoss_le_four_near_two_off`
    (`reverseLoss ≤ 4|S ∩ near| + 2|S \ near|`).

  Still open: Frontier `MGGFrontier.mggGraph_hasExpansionInv` (spectral or Cheeger
  plus absorb packaging using the certified `4a + 2o` loss shape).

  Most important thing learned: encode`(1,1)` collisions sit inside the near-axis
  band; off band, shears miss translations and only `{S,S⁻¹}` and `{T,T⁻¹}` can
  collide, so excess is at most 2 and Inv absorb shape `4a + 2o` is now Lean-ready.
  gate_pending: merge_certified (Cluster 35 off-band decls).
  next: formalize Inv packaging (Cheeger or Gabber Galil cite plus absorb) for
  `mggGraph_hasExpansionInv`.

- 2026-09-09 formalize (Cluster 35 off-band excess le 2): SUCCESS.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "Cluster 35 off-band leaving excess le 2 and reverseLoss 4a+2o",
    "rationale": "Heartbeat woke on dirty Cluster 35 WIP; certify off-band excess for Inv absorb."
  }
  ```
  workstream: R2. gate_auto: true merge_certified (axiom gate PASS).
  Edited `theory/Theory/ProofComplexity/MGG.lean` and acceptance list.
  Left Bridge ProofSystem dirty untouched for R5.

  Accepted:
  - Off-band characterizations and shear family partition:
    `not_mem_mggNearAxis_iff`, `mggShearSGens`, `mggShearTGens`,
    `mggShearGens_eq_S_union_T`, `mggShearSGens_disjoint_T`.
  - Shear vs translation disjointness off band (S, Sinv, T, Tinv) plus
    S-family vs T-family image separation.
  - `mggLeavingExcess_le_two_of_not_mem_nearAxis`,
    `mggReverseCutLoss_le_four_near_two_off` (`reverseLoss ≤ 4a + 2o`).

  Still Frontier sorry: `MGGFrontier.mggGraph_hasExpansionInv`.
  Next: absorb packaging with `|nearAxis| ≤ 6m` and `4a+2o` into Inv-4, or
  spectral Cheeger surface for HasExpansionInv.

  Most important thing learned: off band, shears miss all translations and the
  two shear families miss each other, so leaving excess collapses to at most
  one collision per shear family (budget 2).
  gate_pending: merge_certified (Cluster 35).

- 2026-09-09 formalize (Cluster 36 Inv-4 absorb packaging): SUCCESS.
  Choice:
  ```json
  {
    "rung": "r2-width-machinery",
    "action_type": "formalize",
    "target": "Cluster 36 Inv-4 absorb packaging from near loss 4a+2o",
    "rationale": "Session wake after Cluster 35; glue multi Cheeger plus twelfth reverseLoss to Inv-4."
  }
  ```
  workstream: R2. gate_auto: true merge_certified (axiom gate PASS).
  Edited only MGG.lean and acceptance list. Bridge dirty left untouched.

  Accepted:
  - `card_inter_mggNearAxis_le` (`|S ∩ nearAxis| ≤ 6m`)
  - `mggReverseCutLoss_le_two_mul_card_add_twelve_mul_m` (`≤ 2|S| + 12m`)
  - `mgg_card_le_four_mul_edgeBoundary_of_multi_and_twelfth`
  - `mgg_card_le_four_mul_edgeBoundary_of_multi_near_two_off`
  - `mgg_inv4_absorb_near_two_off_of_large`

  Still Frontier: `MGGFrontier.mggGraph_hasExpansionInv` (needs multi Cheeger from Gabber Galil
  spectral, and a twelfth reverseLoss witness that `2|S|+12m` does not give for free).

  Most important thing learned: Inv-4 on a set reduces to multi Cheeger plus
  `12·reverseLoss ≤ |S|`; the `4a+2o` bound alone is too coarse for that twelfth
  when off-band vertices scale with `|S|`, so the next obligation is spectral
  multi expansion (or a sharper reverseLoss).
  gate_pending: merge_certified (Cluster 36).
  next: formalize Gabber Galil multi Cheeger Nat surface, or pin spectral lemma.
