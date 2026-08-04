# R2: Width Machinery and More Families

Status: prose_accepted
Lean home: theory/Theory/ProofComplexity/Width.lean and SizeWidth.lean (planned)

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
