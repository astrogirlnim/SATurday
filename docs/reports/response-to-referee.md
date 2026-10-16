# Response to the mathematical referee report (R4 statement fidelity dossier)

Date: 2026-10-15. Branch `r4/referee`, docs only. Nothing here is a certification claim. The report is treated as
data: each claim below was re-checked against the Lean sources in `theory/Theory/ProofComplexity/`, the plan files in
`docs/ladder/rungs/`, and the arXiv text of Pang (2610.00837, fetched 2026-10-15). Arithmetic was recomputed by script
from the Lean definitions (`PangParams.lean`, `ResLinDagSize.lean`). No Lean was built or changed. The revised
dossier is `docs/ladder/statement-fidelity-dossier.md`; section numbers 11 to 15 there are new.

Scope limit of this response: it checks the referee's statements and the dossier's. It does not re-verify the Lean
proofs, nor Braun's paper, nor the older papers (Part-Tzameret, Khaniki, AR, Green).

## Verdict table

| # | Objection | Verdict |
|---|-----------|---------|
| 1 | Tseitin satisfiability criterion wrong for disconnected graphs | Agree (dossier text wrong; Lean theorem not affected) |
| 2 | Quantifiers do not build the R4 family | Agree |
| 3 | Pang supersedes Braun; size-parameter reporting | Agree (with one refinement) |
| 4 | Pang already has the one-hot Tseitin application | Agree |
| 5 | System-strength comparisons need embeddings | Agree |
| 6 | C1 is not an intermediate toward AC0[p]-Frege | Agree (dossier already disclaimed R4, but wording was too soft) |
| 7 | Constants and thresholds | Agree; numbers confirmed |
| 8 | Nonvacuity / completeness | Agree |
| 9 | Choke points / dependency diagram | Agree |
| 10 | Nothing addresses the Frege bottleneck | Agree on the factual claim; partly agree that the program needs an explicit route statement (see below) |

No objection is disputed outright. Three places where the referee is slightly imprecise or where the dossier already
contained a partial answer are noted under 3, 5 and 10.

## Objection 1: Tseitin satisfiability

Verification. `tcnf` (`TseitinBool.lean`) has one block of `q` variables per edge, unique-value clauses, and one
clause per forbidden local labelling at each vertex. The net flow at `v` sums each edge value with `+` at its lesser
endpoint and `-` at its greater endpoint, so the net flows of one connected component sum to zero. Hence
satisfiable implies every component charge sum is zero mod `q`. The converse holds by spanning-tree propagation.
The referee's criterion is correct. The counterexample (two disjoint copies of `K_4`, `q = 2`, charge 1 on one vertex of
each copy) is correct: total `2 = 0`, component sums `1`, unsatisfiable. So the dossier sentence "Unsatisfiable iff
`∑ b ≠ 0`" and the follow-up "for `∑ b = 0` the formula is satisfiable" were false for general graphs.

What Lean says. The only Lean statement is `tcnf_unsat : ∑ v, b v ≠ 0 → ¬ Satisfiable (tcnf G q b)`. Its proof does
not use connectivity and is valid on any graph (nonzero total implies some component sum nonzero). I searched the
repository: there is no theorem stating or using the converse for `tcnf`. The error was in the dossier prose only. No Lean
theorem is affected.

Where connectivity is actually used. Not in `tcnf_unsat`. The graph family theorem
`exists_mggF2Cub_hasExpansionInv_family` returns `G.IsConnected`, and independently `HasExpansionInv` (every
nonempty `S` with `2|S| ≤ n` has `|S| ≤ K |∂S|`) forces connectivity, since a union of components with at most `n/2`
vertices would be a nonempty set with empty boundary. In `tseitin_bool_degree_Fp` the connectivity conjunct is
destructured and not used; the degree proof `tseitin_pc_degree` uses `HasExpansionInv`. A point the referee did not make
but which follows: the downstream theorems (`reslin_tseitin_size`, `reslin_tseitin_dag_size`, `tseitin_dag_exp`,
`c1_main`) state only `IsRegular G 3`; connectivity is not visible in their statements, so a reader cannot conclude from
the statements that "`b` hard iff `∑ b ≠ 0`".

Action taken: dossier Section 1.1 rewritten (componentwise criterion, counterexample, what Lean proves, where
connectivity is used). Planned: add an `IsConnected` conjunct to the family statements and prove the completeness
direction for connected graphs (work items 2 and 3).

## Objection 2: quantifiers

Verification. Confirmed for `reslin_tseitin_size`, `reslin_tseitin_dag_size`, `Pang.tseitin_dag_exp`, `C1.c1_main`
and `tseitin_bool_degree_Fp`: each is `∀ N, ∃ n ≥ N, ∃ G, ... ∀ b ...`. The bit-PHP theorems (`bphp_dag_exponential`:
`∀ ℓ ≥ 32`; `braunBitPHP`/`bphp_dag_superpolynomial`: `∀ K ∃ L ∀ ℓ ≥ L`) are uniformly indexed with an explicit
family. The GGW theorems (`ggw_tseitin_pc_degree`, `ggw_tseitin_reslin_size`) are explicitly indexed by `(m, k, σ)`.
Refinement: reading the proof of `exists_mggF2Cub_hasExpansionInv_family`, the witness is `n = 8m²` with
`m = max(6, N, 1968)`, so the existential theorems conceal an indexed family `m ↦ G_m` with ratio `((m+1)/m)² → 1` of
consecutive sizes; the content that is missing is a restatement, not new mathematics. The referee is right that this
is not in the statements, and padding (preserving unsatisfiability, size measure, lower bound in the target system) is
not formalized. For "`∀ b` includes satisfiable `b`": correct; hard instances are those with a nonzero component sum.
Explicit `b_n` (charge 1 at one vertex, 0 elsewhere; total `1 ≠ 0` in `Z_q`) is easy and computable, but no theorem
instantiates it.

Action taken: dossier Section 12 states, theorem by theorem, which shape it has. Planned: work items 1 and 3.

## Objection 3: Pang supersedes Braun; size parameters

Verification against the arXiv text. Pang Theorem 7.2(e): bit-PHP with `N < m = O(N)` pigeons and `N = 2^ℓ` holes
requires `exp(Ω(N))` in Res(PC_r/F_p). Section 7.1: for `p = 2`, `r = 1` this improves Braun's `exp(Ω(N/log² N))`,
and is tight up to the constant (tree-like `2^{O(N)}` refutation). Section 7.1 also says semantic weakening is
simulable by the syntactic rules with polynomial overhead. All three of the referee's citations are correct.
Refinement: the dossier already listed Pang's work as superseding Khaniki (Section 4.4 row 6) but did not say Pang
supersedes Braun; that omission is conceded.

Size parameters (computed from `bphpCNF`): `N+1` pigeons, variables `(N+1)ℓ`, clauses `C(N+1,2)·N = N²(N+1)/2`, width
`2ℓ`, literal occurrences `N²(N+1)ℓ`. So the referee's `Θ(N³)` clauses and `Θ(N³ log N)` literals are right. The bound is
exponential in `N`, hence `exp(L^{1/3-o(1)})` in the input length `L`, not `exp(Ω(L))`. For Tseitin on cubic graphs with
`n` vertices: `3nq/2` variables and `(3n/2)(1 + q(q-1)/2) + n(q³ - q²)` clauses (for `q = 2`: `3n` variables, `7n` clauses),
so `2^{Ω(n)}` is exponential in the formula size up to a log factor.

Action taken: dossier Section 2.3 note, Section 11 (novelty), Section 13 (size parameters).

## Objection 4: Pang's one-hot Tseitin application

Verification. Pang Theorem 1.1: `ln S ≥ (D/(32p²r))·(D/(16n))^{(p-1)r}` for `D ≥ max{32(p-1)²r, 8w}`, as the
dossier quoted. Theorem 7.2(b): `Tseitin_q(G,b)`, fixed prime `q ≠ p`, fixed-degree regular edge expanders, `exp(Ω(N))`. Pang's
encoding has `q|E|` variables, a block of `q` per edge, unique-value clauses and flow-conservation at each vertex: this
is the encoding of `tcnf`. So Section 6 of the dossier is a formalization of a published application, not an
independent discovery. The differences are as the referee says: composite `q` (with `p ∤ q`) which Lean allows (the degree
lemma is proved over a primitive `q`-th root of unity) and the stated sources fix a prime `q`; exact constants. Whether
the composite-`q` extension is a genuine extension of Pang needs one check I have not done: Pang's own proof of 7.2(b)
may go through verbatim for composite `q` given a degree lower bound, in which case the difference is only that Pang
stated the prime case. I do not claim more than what the Lean statement says.

Action taken: dossier Section 6.3 (verified statements), 6.4 row 9a, and the Section 11 table (what is and is not new).

## Objection 5: system embeddings

Verification. Correct and conceded. The labels "strengthens/weakens/neutral" in Sections 2.4, 3.4, 4.4, 5.4, 6.4, 7.4 are
informal comparisons, not Lean theorems. Specific facts I checked in the Lean definitions: `RLD`/`RLDag`
(`ResLinF*.lean`) have syntactic (superset) weakening, `comb` with scalars, constant deletion, no multiplication rule;
`Pang.Infer` has fused weakening in `comb`/`mul`/`falseConst` and a `mul` rule restricted to `(f·g).totalDegree ≤ 1`;
`PDag`/`DagRefutes` use semantic weakening; `Braun.PStep.binary` is a semantic binary rule. Each of these differs from
the corresponding standard calculus in at least one rule. The dossier already marks `pdag_to_affineDAG` and
Part-Tzameret's Theorem 45 variant as unverified; the referee is right that these are central. One partial qualification:
for fused weakening, Pang Section 7.1 (checked) states semantic weakening is polynomially simulable by syntactic
rules in this setting, so for `Pang.Refutation` the direction "Lean system is at least as strong as Pang's" is
immediate (adding rules only helps), and the genuine gap is the converse needed to claim the Lean bound for a
*standard* system, which is as the referee says an embedding statement. That embedding is not proved.

Action taken: none beyond text; planned: work item 4.

## Objection 6: C1

Verification. `C1.c1_main` concerns `RRefutation` with rules `sem1`, `sem2` defined by quantification over all Boolean
assignments (`SemOK`); it is not Cook-Reckhow. The rank in `R_ρ^p` is `finrank` of the span of a term's affine forms, not
a depth; the dossier (7.4 row 3, 10 item 3) already said "not evidence about AC0[p]-Frege", but the referee reports the phrase
"stronger intermediate system" and I did not locate every use; the referee is right that the wording could be read as progress toward
Frege. No bridge from AC0[p]-Frege proofs to `R_ρ^p` is proved or known. The bound has `ρ ≤ ε ln n` (logarithmic rank)
with `(κ+1)ε < 1`, `κ(3,2) ≈ 24.745`.

Action taken: new dossier Section 7.1a, which says plainly that it is a result about a bespoke semantic calculus,
not a Cook-Reckhow system, and gives no AC0[p]-Frege consequence without a bridge theorem.

## Objection 7: constants

Recomputed from `PangParams.lean`: `cA 2 = 6561`; `cLam 2 = 236196`; `cS 3 2 = 2(1 + 236196²) = 111,577,100,834`;
`cC 3 2 = 6561 · 32 · 111,577,100,834 = 23,425,835,474,299,968`. The referee's figures `6561`, `236196`,
`23,425,835,474,299,968 ≈ 2.34e16` are exactly right. `κ(3,2) = 2 ln 236196 = 24.745`; `ε < 1/25.745 = 0.03884`, right.
Additional thresholds computed (tree-like, dag-like, C1, Braun) are in dossier Section 14. A consequence the referee did
not note: for C1, `ρ ≥ 1` with `ρ ≤ ε ln n` already needs `n ≥ e^{1/ε} ≥ e^{25.7}`. Also, the family theorem's own floor
makes the guaranteed sizes `n = 8m²` with `m ≥ 17122` for `(p,q) = (3,2)` through `tseitin_bool_degree_Fp`, so the tree-like
exponent is positive on every size the theorem returns (`E ≈ 893,780` at the smallest). Positivity of the exponent is not
stated as a lemma in the theorem statements; that remains true and is conceded.

Action taken: dossier Section 14.

## Objection 8: nonvacuity and completeness

Verification. Correct. Only bit-PHP has an upper-bound theorem in the Lean system (`bphp_dagRefutable`). For `RLD`,
`RLDag`, `Pang.Refutation` and `RRefutation` on `tcnf` no theorem asserts that a refutation exists, so the lower-bound
theorems could in principle be vacuous (if the calculus were incomplete for these CNFs). Soundness (`rld_sound`,
`Refutation.unsat`) is not the issue. This was already listed in dossier Section 10 item 6; the referee is right that it is a
standing obligation. A constructive route is available (simulate a tree-like resolution refutation, or a truth-table
refutation, rule by rule; the size can be huge since only existence is needed).

Action taken: none in text beyond existing Section 10 item 6; planned: work item 2.

## Objection 9: choke points

Verification. Confirmed: `tseitin_bool_degree_Fp` is used by `ResLinTseitin`, `ResLinDagSize`, `PangTseitin`, `C1Tseitin`
and `TseitinSize`, so Sections 3, 4, 6, 7 share it and the MGG family. Section 5 does not (it uses `GGW` and
`green_immune`); Braun shares nothing with them. The referee's four audit items are reasonable; the diagram and audit order
are now in dossier Section 15. On the claim that the Boolean-edge Section 5 chain is "potentially especially
valuable" and that the immunity direction deserves scrutiny: agreed; the dossier already flags it (5.5(d)) and I did
not re-derive it.

## Objection 10: Frege bottleneck

Verification of the factual claim. Pang Section 8 (checked): the rank count is subadditive, inference preservation
extends to syntactic AC0[p]-Frege rules given error relations for each gate, but there is a quantitative bottleneck in
the tradeoff between approximation degree and rank shrinkage rate, and the missing ingredient is PC degree lower
bounds near or above `n/2` for polynomial-size `o(n)`-width CNFs, which are unknown. The referee's summary matches.
Partly agree on the recommendation: the dossier is a fidelity dossier and disclaims R4; I accept that `docs/ladder/`
should say which lemma would overcome the barrier (a PC degree lower bound of order `n/2` for a polynomial-size,
sub-linear-width CNF; or a different approximation scheme), and that the existing graph families (degree `Θ(n/1312)`)
and the logarithmic-rank C1 bound do not supply it. I do not assert any route works; that is research, not a Lean item.
Planned: a one-paragraph barrier statement in `docs/ladder/r4-completion-checklist.md` by the owner/chief; not
done here (outside this task's file scope).

## "Required revisions" list

| Revision | Verdict | Status |
|----------|---------|--------|
| Correct the Tseitin iff; connectedness or componentwise; prove both directions if used | Agree | Corrected in text (Section 1.1). Proving both directions in Lean is work item 2. No Lean theorem uses the converse. |
| Per headline theorem, a precise source theorem and two-way definition comparison | Agree | Partly present (Sections 2.3 to 7.4); Pang Thm 1.1, 7.2(b),(e), 7.1, 8 now verified against the arXiv text. Part-Tzameret/Khaniki/AR theorem numbers still unverified. |
| Size-controlled embeddings of standard systems into the Lean systems | Agree | Not done; work item 4. |
| Explicit unsatisfiable charge family and all-size/padded family | Agree | Work items 1 and 3; Section 12 states the gap. |
| Nonvacuity/completeness for nonstandard Tseitin calculi; relate graph size, variables, clauses, encoding length | Agree | Size relations done (Section 13); completeness is work item 2. |
| Isolate C1; standalone analysis; bridge lemma if intended toward AC0[p]-Frege | Agree | Section 7.1a. No bridge exists. A standalone proof-system analysis (e.g. completeness, relation to Res(lin F_p), whether `R_ρ^p` p-simulates anything standard) is not done. |
| Clean pinned reproduction; accepted axioms; resolve theorem numbering and unverified comparisons | Agree | The axiom list was produced from a cache, not a clean build (dossier Section 9 caveat); work item 5. |

## Prioritized Lean and mathematics work items

Size estimates are rough, in lines of Lean and in focused-session units (S ≈ 1 session or less, M ≈ a few sessions,
L ≈ weeks). "Feasible" means I see a route using existing lemmas.

1. Explicit hard charge family with computable `b_n` and indexed statements (S, feasible). State, for the MGG family,
   `∀ m ≥ m0(p,q), ∃ G on 8m² vertices, IsConnected ∧ IsRegular 3 ∧ (explicit b_m with ∑ b ≠ 0) ∧ lower bound`,
   where `b_m = Pi.single 0 1` (so `∑ b = 1 ≠ 0` in `ZMod q`, `q ≥ 2`). This is a restatement of
   `exists_mggF2Cub_hasExpansionInv_family` (the witness `n = 8m²` is already in the proof) plus `tcnf_unsat`. About
   150 to 300 lines; the cost is making the family a function (choose the graph by `mggF2CubGraph`, already a definition).
   Also add the `IsConnected` conjunct to the Tseitin theorems.
2. Completeness / nonvacuity for the Tseitin calculi (M, feasible). (a) Prove the componentwise satisfiability criterion
   for `tcnf` (both directions; about 200 to 400 lines: spanning tree / induction on edges removed, using `FinGraph`
   connectivity). (b) Show some refutation exists in each of `RLD`, `RLDag`, `Pang.Refutation`, `RRefutation` for
   `tcnf G q b` with `∑ b ≠ 0`: the cheapest route is to build a refutation from a complete decision-tree / truth-table
   refutation by induction on the variables; existence only, no size control (about 400 to 800 lines per system, shared
   skeleton). A concise simulation of resolution (width-3 CNF, so a resolution refutation exists by standard
   completeness) is the better statement, and it also feeds item 4; whether the repository already has a resolution completeness theorem to start from was not checked.
3. Padding to an all-size family (M, partly feasible). Needs a padding operation `Φ ↦ Φ'` on CNFs that preserves
   unsatisfiability, adds only polynomial size, and for which a refutation of `Φ'` yields a refutation of `Φ` in the same
   system with no size increase (restriction, e.g. setting the padding variables, preserves the tree-like, dag-like,
   Res(lin F_p), `R_ρ^p` systems since they are closed under restriction in the literature, but closure under
   restriction is NOT formalized and each Lean system needs it). Alternatively pad the graph by attaching a dummy
   subgraph and charge-zero vertices; for the expander-based theorems this destroys expansion, so the lower bound has
   to be re-derived or the padded instance reduced to the original by a restriction. Estimate 500 to 1500 lines; the
   bit-PHP case (padding pigeons/holes) is easier since sizes grow by factor 8 per `ℓ` and one can restrict.
4. Size-controlled embeddings of standard systems into the Lean systems rule by rule (M to L, the most valuable item,
   as the referee says). Targets: (a) standard Res(lin F_p) (Raz-Tzameret: weakening, resolution on linear forms with
   scalar combination, simplification) into `RLD`/`RLDag`; (b) Res(⊕) of Itsykson-Sokolov (syntactic weakening) into
   `Res.DagRefutes`, then `DagRefutes` into `PDag` (already in `bphp_dag_to_pdag`, check the size accounting); (c)
   `RLDag` into `Pang.Refutation` (rule-by-rule, including fused weakening and the restricted `mul`); (d)
   `Pang.Refutation` into `RRefutation`; (e) the `pdag_to_affineDAG` equivalence (which the dossier lists as
   unverified). Each embedding: a size-preserving map on `ℕ`-indexed derivations. Estimate 300 to 600 lines each for
   (a) to (d), (e) 300 to 1000 depending on the data/Prop gap. Feasible; (c) involves the `mul` rule and is the
   riskiest. Do (b) first (smallest and used by Braun).
5. Clean pinned reproduction (S, feasible, mostly operational). Fresh checkout at a recorded commit with a pinned
   `lean-toolchain`, `lake-manifest.json`, `lake build` from empty `.lake`, then `scripts/check_axioms.sh` and the ten
   `#print axioms`. No Lean change. Already needed for any outside review; the current axiom log came from a build cache.
6. Standalone analysis of `R_ρ^p` as a proof system (M, speculative). Completeness; relation to Res(lin F_p) at `ρ = 1`
   (does `R_1^p` p-simulate Res(lin F_p)?); a statement of the best-possible bridge lemma to AC0[p]-Frege and a note why
   iterated approximation (Pang Section 8) fails; none of this is a Lean-heavy item first, it is mathematics to write down.
7. Verify the remaining unverified source comparisons (S each, reading rather than Lean): Part-Tzameret Theorem 45
   Case 4 variant, Khaniki published statement, AR Theorem 4.4 constant, the composite-`q` question for Pang 7.2(b),
   Pang Lemma numbering for the layers in Section 6.5(e).
8. Statement hygiene (S): lemmas that the exponent is positive on the family (e.g. `E(8m²) ≥ 1` for `m ≥ m0`) so that
   the natural-number statements are non-degenerate by theorem rather than by prose.

Feasibility summary: items 1, 5, 7, 8 are small and feasible now; item 2 is medium and feasible; item 4(b) is feasible and
should precede the others in 4; items 3 and 4(c),(e) are the real work; item 6 and any Frege bridge are research and have
no size estimate.

## What changed in the dossier

Section 1.1 (criterion corrected, connectivity), header revision note, Section 2 (Pang supersedes Braun), Section 6.3
(Pang text verified) and 6.4 row 9a, new Section 7.1a (C1 plainly), and new Sections 11 (novelty), 12 (quantifier shapes),
13 (size parameters), 14 (constants and thresholds), 15 (dependency diagram). Statements of Lean theorems and their
`#print axioms` output are unchanged. Nothing is marked certified.

## Prover status (branch `r4/refrepair`)

Work item 1 (done). New file `TseitinExplicit.lean`: `tseitin_bool_degree_Fp_conn` and `reslin_tseitin_size_conn`,
`reslin_tseitin_dag_size_conn`, `Pang.tseitin_dag_exp_conn`, `C1.c1_main_conn` (the original statements with a
`G.IsConnected` conjunct; proofs are the original proofs, connectivity comes from
`exists_mggF2Cub_hasExpansionInv_family`, which already returned it), and `*_explicit` corollaries for
`tseitinCharge1 n q` (charge 1 at vertex 0): they also conclude `∑ b ≠ 0` and `¬ Satisfiable`. Originals untouched.
Still existential in `N` (the indexed family `m ↦ G_m` and padding are not done). GGW (`ggw_tseitin_reslin_size`) is
already indexed by `(m, k, σ)` for every `σ`; no `*_explicit` version was made because `OGraph` has no connectedness
notion and the CNF-level unsatisfiability of `ggwGraph` for nonzero total charge was not proved (only the polynomial
axioms, `OGraph.Ax_unsat`); connectedness of the walk multigraph does not follow from data in the Lean statements
(the spectral/expansion hypothesis `himm` is open there).

Work item 2 (done for one calculus). `TseitinSat.lean`: `tcnf_sat_iff`, on a connected graph with `0 < n`,
`Satisfiable (tcnf G q b) ↔ ∑ b = 0` (via `exists_flow`: the net flow map is linear and its image contains every
dipole). `PangComplete.lean`: `Pang.refutation_of_unsat`, every unsatisfiable CNF with variables in `V` has a
`Pang.Refutation` (resolution completeness simulated: `comb` on `1-x`, `x` giving `1=0`, then `falseConst`).
`TseitinNonvacuity.lean`: `tseitin_dag_exp_explicit_nonvacuous` (unsatisfiable, refutation exists, all have
`≥ 2^(n/C)` nodes). Existence only, no size control. Not done: the same for `RLD`, `RLDag` (RLF calculus) and
`RRefutation`; the route is the same (simulate `Derivation` rule by rule; `RLF.rld_dagRefutes`-style lemmas go the
other direction), about 150 lines each, not attempted.

Work item 5 is `docs/reports/reproduction.md`. The four new files are imported from `Theory.lean`; the axiom gate (`scripts/check_axioms.sh`) passed on this branch (2254 declarations checked, axioms within propext, Classical.choice, Quot.sound).

## Prover status (branch `r4/padding`): indexed families, padding, embeddings

Indexed form (done). New file `TseitinIndexed.lean`. `cubFam m : FinGraph (m*m*8)` is the explicit graph
`mggF2CubGraph` on `n = 8 m^2` vertices. For every `m >= tseitinFloor p q` (an explicit sum of the thresholds used
in the proofs, not optimized) Lean proves: `cubFam m` is 3-regular and connected; the Fp-degree bound
(`tseitin_bool_degree_Fp_idx`); the size bounds `reslin_tseitin_size_idx` (tree-like Res(lin F_p), `RLD`),
`reslin_tseitin_dag_size_idx` (`RLDag`), `Pang.tseitin_dag_exp_idx`, `C1.c1_tseitin_exp_idx`, all for every charge `b`;
`tseitin_idx_explicit_unsat` (charge 1 at vertex 0 has total `!= 0` and the CNF is unsatisfiable); and
`tseitin_dag_exp_idx_nonvacuous` (for that charge: unsatisfiable, a `Pang.Refutation` exists, every one has `>= 2^(8m^2/C)`
nodes). `C1.c1_main_idx` has `exists m0, forall m >= m0` (`m0` from `eventually_conditions`, existential but a threshold).
So the quantifier is now `forall m >= m0` over an explicit function `m |-> (cubFam m, tseitinCharge1)`, shape U, for
sizes `n = 8 m^2` only. `cubFam_size_gap`: consecutive sizes satisfy `n_{m+1} <= 2 n_m` (`m >= 3`).

Padding to every `n` (NOT done, and not claimed). What the indexed family gives: for any `n >= 8 m0^2`, take the
largest `m` with `8m^2 <= n`; the hard instance has `n' in (n/2, n]` vertices (ratio actually `->1`), so the bound
holds for a formula of size `n'`, not for a formula of size exactly `n`. A formula of size exactly `n` would need a
padding map `Phi |-> Phi'` with a lower-bound transfer; this needs, for each of `RLD`, `RLDag`, `Pang.Refutation`,
`RRefutation`, a lemma "refutation of `Phi'` gives refutation of `Phi` (restriction of padding variables) of no larger
size". Closure under restriction is not formalized for any of these Lean calculi, and for the expander-based bound
the alternative of adding dummy vertices destroys expansion (the degree lower bound is stated for `cubFam`). Estimate
unchanged (500 to 1500 lines); not attempted here.

Embeddings of standard Res(lin F_p) / Res(xor) (not started; plan). Order: (b) Res(xor) of Itsykson-Sokolov into
`Res.DagRefutes`, check size accounting against `bphp_dag_to_pdag`; (a) standard Res(lin F_p) (weakening, resolution on
linear forms, simplification) into `RLDag`: define the standard system as a `Finset`-line derivation with an explicit
`ℕ` size, prove each rule instance maps to one or a bounded number of `RLF` steps, and state
`size(RLDag derivation) <= c * size(standard derivation)`; then (c) `RLDag` into `Pang.Refutation` rule by rule
(riskiest: restricted `mul`), (d) `Pang.Refutation` into `RRefutation`. Each needs a formal definition of the standard
system that does not exist in the repository, which is the first deliverable.
