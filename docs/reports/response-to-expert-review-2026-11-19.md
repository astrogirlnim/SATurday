# Response to the expert review of 2026-11-19

Referee report: `docs/reports/expert-review-2026-11-19.md`. Reviewed document: `docs/ladder/expert-review-proposal.md` (revised in this change). The referee states that the Lean repository was not inspected, so every point below was checked against the Lean sources in `theory/Theory/ProofComplexity/` and the docs `statement-fidelity-dossier.md` ("dossier") and `response-to-referee.md`. Verdict key: agree, partly agree, disagree. No Lean code was changed; Lean follow-ups are collected in Section C.

## Headline finding (item 4, the referee's highest-risk point)

Acyclicity of derivations IS enforced, in every dag-like system, by construction. No circular justification can be accepted. Quoted definitions follow.

`RLF.RLDag` (`ResLinFDag.lean`), an inductive predicate on finite sets of lines, generated from the empty set, where every rule's premises must lie in the set built so far:

```lean
inductive RLDag (Ax : Set (Finset (LEq F))) : Finset (Finset (LEq F)) → Prop
  | empty : RLDag Ax ∅
  | ax {𝓛} (C : Finset (LEq F)) : RLDag Ax 𝓛 → C ∈ Ax → RLDag Ax (insert C 𝓛)
  | weak {𝓛} (L L' : Finset (LEq F)) : RLDag Ax 𝓛 → L ∈ 𝓛 → L ⊆ L' → RLDag Ax (insert L' 𝓛)
  | comb {𝓛} (A B : Finset (LEq F)) (e1 e2 : LEq F) (α β : F) :
      RLDag Ax 𝓛 → A ∈ 𝓛 → B ∈ 𝓛 → e1 ∈ A → e2 ∈ B →
      RLDag Ax (insert (A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2}) 𝓛)
  | simp {𝓛} (L : Finset (LEq F)) (c : F) : RLDag Ax 𝓛 → c ≠ 0 →
      insert ((0 : ℕ →₀ F), c) L ∈ 𝓛 → RLDag Ax (insert L 𝓛)
```

Why this is acyclic: `RLDag Ax 𝓛` can only hold if `𝓛` was obtained by a finite chain of `insert` steps from `∅`, and each step's premises (`L ∈ 𝓛`, `A ∈ 𝓛`, `B ∈ 𝓛`) are members of the earlier set. Order the elements of the final set by the step at which they were first inserted; every justification points strictly backwards. The referee's example A from B, B from C, C from A cannot be generated, because the first of A, B, C to be inserted would need a premise not yet present. A set that is merely closed under "every non-initial line is justified by other members" is NOT what `RLDag` says; it says reachable by sequential insertion. Soundness (`rldag_sound`) is proved by induction on this derivation, which would fail for a cyclic notion.

Size is `𝓛.card`, the number of distinct lines, which is at most the length of the insertion sequence (re-inserting an existing line is a no-op). So a lower bound on `𝓛.card` is, if anything, stronger than a bound on the sequence length.

`RL.Der` / `RL.DagRefutes` (`ResLinDag.lean`), the Res(xor) system, same pattern:

```lean
inductive Step (Ax : Set Clause) (P : Finset LClause) : LClause → Prop
  | ax {C : Clause} : C ∈ Ax → Step Ax P (ofClause C)
  | weak {L0 L : LClause} : L0 ∈ P → Imp L0 L → Step Ax P L
  | res {L1 L2 C D : LClause} {f : Finset ℕ} {a : ZMod 2} :
      L1 ∈ P → L2 ∈ P → Imp L1 (insert (f, a) C) → Imp L2 (insert (f, a + 1) D) →
      Step Ax P (C ∪ D)

inductive Der (Ax : Set Clause) : Finset LClause → Prop
  | empty : Der Ax ∅
  | add {P : Finset LClause} {L : LClause} : Der Ax P → Step Ax P L → Der Ax (insert L P)

def DagRefutes (Ax : Set Clause) (s : ℕ) : Prop :=
  ∃ P : Finset LClause, Der Ax P ∧ (∅ : LClause) ∈ P ∧ P.card ≤ s
```

`Pang.Refutation` (`PangDag.lean`), an explicit topologically ordered node array:

```lean
structure Refutation (Φ : CNF) (V : Finset ℕ) (p : ℕ) [Fact p.Prime] where
  S : ℕ
  line : ℕ → Line p
  prem : ℕ → List ℕ
  S_pos : 0 < S
  prem_lt : ∀ i < S, ∀ j ∈ prem i, j < i
  infer : ∀ i < S, Infer Φ V ((prem i).map line) (line i)
  wf : ∀ i < S, WF V (line i)
  last : line (S - 1) = ∅
```

`prem_lt` is the explicit well-foundedness: premises have strictly smaller index. `RRefutation` (`C1Rank.lean`) has the identical `prem_lt` field. `PDag` / `PStep` (`BraunDag.lean`) indexes lines by `Fin S` with `a < i`, `b < i` in every non-initial constructor (`weaken`, `resolve`, `binary`).

Residual points, none a circularity risk: (i) `Pang.Refutation.S` counts nodes with repetition allowed (a node may repeat a line), while `RLDag` counts distinct lines; this is a size-measure convention already recorded in the dossier (Section 6.4 row 6). (ii) `Der`/`RLDag` lines are set elements, so a "refutation" is the set, not a sequence; this is the standard dag convention. (iii) `PDag` does not itself require the empty clause; the theorems add `C f = ∅`. Verdict: the referee's concern was well placed as a thing to check, and the check passes.

## A. The 14 items

### 1. Tree-like vs dag-like Res(xor) "incomparable" (High). Agree.

The sentence in Section 5 of the proposal was wrong as written and has been replaced. For identical rules and size measure, a tree-like proof is a dag-like proof, so dag-like lower bounds imply tree-like lower bounds and not conversely. The Lean development already has the correct direction for Res(lin F): `RLF.rln_to_rldag` and `rln_refutes_to_rldag` (`EmbedTree.lean`) turn a tree-like derivation with n nodes into an `RLDag` derivation with at most n lines. One refinement the referee does not mention: that embedding is for node count. Section 2.3's tree-like theorem is stated for leaf count `s`, and leaves can be fewer than nodes (chains of weakenings and simplifications), so a dag line-count bound does not give the leaf-count bound. The revised proposal says this. None of the headline theorems is a tree-like Res(xor) theorem (the tree-like theorem is for Res(lin F_p)), so the old wording about Res(xor) was loose. Proposal Section 5 corrected.

### 2. Quantifiers do not give "all large n" (High). Agree.

The headline theorems have the shape `∀ N, ∃ n ≥ N, ∃ G, ...` (shape E in dossier Section 12). That is an infinite set of sizes, not an eventual bound. The dossier already says this (Section 12); the proposal blurred it ("Indexed all-size versions" was an overstatement, since the family covers sizes 8m² only). The indexed theorems in `TseitinIndexed.lean` are `∀ m ≥ tseitinFloor p q` on `cubFam m`; this is an explicit indexed family, not all n. `cubFam_size_gap` (consecutive sizes within a factor 2) is not a padding theorem, as the referee says. The revised proposal (Section 2.8) distinguishes three notions: infinite sequence of sizes (E), explicit indexed family (8m² vertices, bit PHP l ≥ 32), and eventual all-size bounds, which are not claimed. "Indexed all-size" wording removed. Follow-up: a padding theorem per proof system would be needed to reach the third notion (Section C).

### 3. Composite q versus Pang's prime q (High). Partly agree.

Agree on presentation: the proposal called the composite-q difference an "extension we want checked" inside the fidelity discussion and 2.6 described the result as a "formalization of a published application". The statements are for `q ≥ 2` with `¬ p ∣ q` (`tseitin_dag_exp`, `reslin_tseitin_size`, etc.). Pang's Theorem 7.2(b) is for prime q ≠ p; the dossier (Section 6.4 row 9a, Section 3.4 row 3) already notes this. The revised proposal makes prime q the fidelity target and moves composite q to a separate section (2.9) and a separate, optional question.

Disagree on one part: the referee says the extension "is not justified simply by observing that primitive q-th roots exist". The Lean statement is kernel-checked, so the composite-q theorem is a proved Lean theorem, not an unproved claim. The degree lemma `tseitin_bool_degree_Fp` (`TseitinPC` namespace; indexed version `tseitin_bool_degree_Fp_idx` visible in `TseitinIndexed.lean`) works over `CyclotomicField q (ZMod p)` for general q with `p ∤ q`, and the degree-bound, expansion and immunity steps are all inside the Lean proof for that q. The referee's four sub-conditions are therefore discharged by the proof for composite q in the formal sense; what is open is only whether the generalization is a known or natural mathematical statement (an expert-review question, not a correctness risk). Also, the prime-q statement is literally an instance of the composite-q one (take q prime), so the fidelity target is already covered. Follow-up (cheap): add explicit prime-q specializations `... (hq : q.Prime)` as named corollaries (Section C).

### 4. Dag representation, acyclicity (Potentially critical). Agree it had to be checked. Checked: enforced.

See the headline finding. Embeddings `RLDag` to/from `Pang.Refutation` and the standard calculi (`EmbedPang.lean`, `EmbedPangBack.lean`, `EmbedStd.lean`, `EmbedUsual.lean`) are theorems between these inductive or indexed structures, so they preserve acyclic structure by construction. The part still not independently audited is the match of the individual rules to the published calculi, which is the rule-level audit in item IV below.

### 5. Semantic weakening (Medium). Agree.

The referee's reasoning is right: only the forward embedding (standard syntactic system into ours, with size overhead) is needed to transfer a lower bound for our stronger system to the standard syntactic one. Lean has it: `stdXor_refutes_to_dag` (size s to s) and, for `Pang.Refutation`, whose rules fuse weakening into `comb`, `mul` and `falseConst` (so it is at least as strong as syntactic Res(lin F_p)). The converse (semantic to syntactic, Pang's Section 7.1) is needed only for polynomial equivalence, not for the lower bounds, and the proposal question 5 overrated its role. The revised wording separates "lower bound for the standard system" (needs the forward embedding, which is formalized) from "polynomial equivalence" (not formalized, not needed). Question 5 of the proposal was reworded accordingly.

### 6. Regularity is not expansion (Medium-High). Agree.

The displayed conclusion of `tseitin_dag_exp`, `reslin_tseitin_size`, `reslin_tseitin_dag_size` and `c1_main` is `IsRegular G 3`, with no expansion or connectivity predicate, and the proposal's prose said "cubic expanders". Expansion (`HasExpansionInv (cubFam m) mggF2CubK`) and connectivity are properties of the witness, proved in `cubFam_props`; the connectivity conjunct is dropped when the family is repackaged (the dossier says this in Section 1.1). A statement-only reader cannot see expansion, so the referee is right that the statements underdetermine the family. The revised proposal says so explicitly in 2.1. Mitigations that already exist: `tseitin_bool_degree_Fp_idx` and `tseitin_dag_exp_idx_nonvacuous` return `IsConnected`; the indexed family is a named explicit one. Follow-up: add `HasExpansionInv G K` and `G.IsConnected` conjuncts to the headline statements (Section C).

### 7. Part-Tzameret Theorem 45, Case 4 (Medium). Partly agree.

Agree that the proposal was unclear. We cannot verify the referee's reading of the arXiv text (f versus g); we did not re-read Case 4 for this response, and the claim stands as the referee's report. What the repository records (dossier Section 3.4 row 5, and `ResLinFPC.lean`, `RLF.rld_cnf_pcd`) is that Lean proves the width-to-degree transfer for its own `RLD`, with a variant (degree w+1 plus a side condition). The Lean theorem is about Lean's `RLD` as displayed; it is kernel-checked and its correctness does not depend on the paper's Case 4. The fidelity question that remains is whether `RLD` is the same system as the paper's Res(lin F) (rules, weakening), which does not need the paper's Case 4 proof to be correct. The revised proposal now says exactly this: our concern is not asserted to be more than the referee's typo, and no gap is claimed.

### 8. One-hot versus Boolean-edge encoding, and `tcnf` (Medium). Agree.

The proposal and dossier (Section 3.4 row 1, Section 10 item 1) already say the encodings differ and that the lower bound for one does not imply the other; the revised proposal repeats this at the head of 2.3 (the theorem is about the one-hot formula and is not a restatement of Corollary 46). On the `univ ×ˢ univ` point: this is a valid worry that the snippet does not settle, but the definitions do. `vC G q v α = (incE G v).image (fun e => ⟨xv e.1 (α e).val, false⟩)` mentions only edges incident to v, and `netAt` sums only edges with endpoint v (others contribute 0), so the clause depends on `α` only through its values on incident edges. The finite-set image deduplicates, giving one width-3 clause per forbidden local labelling. Lean proves: clause variables lie in `tVars` and width at most q+3 (`tcnf_clause_props`, `TseitinSize.lean`; q is the width of the at-least-one clause); satisfiability iff total charge zero on connected graphs (`tcnf_sat_iff`, `TseitinSat.lean`). Not proved: a clause-count formula or an explicit equivalence with a stated local-constraint CNF as a single theorem. Added to the proposal in 2.1.

### 9. Line count versus symbol count (Medium). Agree.

The proposal already says (Section 2.8 caveats) that a line-count bound yields a symbol bound and not conversely, and the dossier lists it (Section 3.4 row 6). The referee's remaining point, that this means the Lean statement is not a literal reproduction of the quantitative claim, is correct; the proposal now keeps the phrase "not a literal reproduction" in spirit via the existing caveat and asks the reviewer to assess size measures in question 1. Leaf versus node count for tree-like proofs is addressed in item 1; the leaf and node counts are related in `EmbedTree.lean` only as node count at least leaf count, with no upper bound on nodes in terms of leaves (unary weakening and simplification chains), and the Lean bound is on leaves. So the leaf/node relationship is documented but is not a clean factor-two statement.

### 10. Parameter regime (Medium). Agree.

All bounds are for fixed p and q with n the number of graph vertices. `Pang.cC p q` grows with both p and q. The revised proposal writes `2^{Ω_{p,q}(n)}`, states non-uniformity, and says n is vertices. The Lean theorems fix p, q before N, so the statements are consistent with this reading. The "explicit lemma that the exponent grows linearly after a threshold" is not in Lean as a separate lemma (the floors `tseitinFloor`, `cubFam_floor_le` serve as the thresholds in the indexed theorems). Follow-up listed in Section C.

### 11. `c1_main` out of the fidelity certification (Medium-High). Agree.

`C1.c1_main` concerns `RRefutation`, a calculus we defined (no published counterpart), with semantic rules. The proposal itself said it was the item we were least sure about. It is now excluded from the review request (2.7 and question 7 withdrawn), to be treated, if at all, by a separate mathematical review. The transfer from Pang's method to it is methodological, as the referee says; no formal bridge exists.

### 12. Vacuous cases (Medium-High). Partly agree.

Agree that the vacuity should be central. Partly disagree that it is not there: the combined statement the referee asks for already exists in Lean. `tseitin_dag_exp_idx_nonvacuous` (`TseitinIndexed.lean`) states, for every m at least the floor, on the explicit connected cubic instance with charge 1 at one vertex: regular, connected, total charge nonzero, `¬ Satisfiable`, `Nonempty (Pang.Refutation ...)`, and `∀ R, 2 ^ (8m²/cC) ≤ R.S`. Likewise `tseitin_dag_exp_explicit_nonvacuous` (`TseitinNonvacuity.lean`) and `tseitin_idx_explicit_unsat`. Gaps: the nonvacuity-with-existence theorem exists for `Pang.Refutation` only; for Res(lin F_p) tree-like and dag-like (`RLD`, `RLDag`) and for `RRefutation` existence of refutations is not formalized (dossier Section 10 item 6), though unsatisfiability is covered by `tcnf_charge1_unsat`. The proposal now presents the nonvacuous theorem in the first position in 2.8 as central evidence.

### 13. Reproduction (High for certification). Agree.

The commit hash is a placeholder because the owner pins it when sending; the cold-build caveat is already stated. The revised proposal adds a committed deliverable: with the pinned commit we supply a declaration-to-source mapping covering each theorem named in Section 2 and its entry in `scripts/accepted_declarations.txt` (spot check done for this response: `tseitin_dag_exp_idx_nonvacuous`, `tseitin_idx_explicit_unsat`, `bphp_dag_exponential`, `reslin_tseitin_dag_size`, `c1_main`, `stdLin_refutes_to_rldag`, `rldag_to_pang`, `ggw_tseitin_reslin_size`, `tseitin_dag_exp_explicit_nonvacuous`, `tcnf_sat_iff` are each listed; the full mapping is not yet produced) and the `check_axioms.sh` output. An independently reproduced build log does not exist and cannot be produced by us; that remains a stated limitation.

### 14. Bibliography (Low-Medium). Partly agree.

Agree to correct the Khaniki citation: the referee gives ACM TOCL 23(3), Article 16, July 2022, DOI 10.1145/3506702. We have not checked this metadata against the publisher and have not compared the journal version with ECCC TR20-034; the proposal now cites it as "reported" and says the comparison is not done. Agree that Pang is an unrefereed preprint; the proposal's phrase "published application" is replaced. The "original Green result and exact AR constants not verified" point is accepted and already listed in the proposal's source status (Green via Beck-Li; AR Theorem 4.4 constant unverified); nothing new is claimed about them.

## B. Section IV (what the referee would require before approval)

| Referee requirement | Response | Status |
|---|---|---|
| Critical: every dag-like calculus enforces acyclic, sound derivations | Verified, see headline finding; soundness theorems exist for all four | Done in this response; stated in proposal 2.1a |
| Critical: audit embeddings and exact rules against published counterparts | Embeddings are Lean theorems (table in proposal 2.8). Rule-by-rule comparison with each published calculus is the reviewer's task; not done by us | Open; remains the request to the expert, restructured as theorem-by-theorem |
| High: separate prime from composite modulus | Done in proposal (2.3, 2.6, 2.9, question 6) | Done for documents; prime corollaries are a Lean follow-up |
| High: explicit unsatisfiable size-indexed instances with lower bounds | Exist for `Pang.Refutation` (`tseitin_dag_exp_idx_nonvacuous`); not for `RLD`/`RLDag` with existence | Partly done; now central in proposal 2.8 |
| High: correct tree/dag comparison and all-size asymptotic claims | Done in proposal (Sections 5, 2.8) | Done |
| High: pinned repo and independent kernel/axiom audit | Cannot be done by us; mapping and axiom output promised | Open (owner) |
| Medium: relation between one-hot and Boolean-edge encodings | Documented as different; no transfer theorem | Open, mathematical |
| Medium: review bounded-rank calculus separately | Done: excluded from fidelity request | Done |

## C. Lean follow-ups (not done here)

1. Add `HasExpansionInv G mggF2CubK` and `G.IsConnected` to the conclusions of the headline Tseitin theorems (or add wrapper theorems), so statements display the family.
2. Add prime-q corollaries (`q.Prime`) of `tseitin_dag_exp`, `reslin_tseitin_size`, `reslin_tseitin_dag_size`, so the fidelity target is a named theorem.
3. Add nonvacuity-with-existence theorems for `RLD`/`RLDag` and `RRefutation` on the explicit charge-1 instance (existence of refutations; completeness is formalized for `Pang.Refutation` only).
4. Padding theorems to all n for each proof system, if an eventual all-size bound is wanted.
5. A small lemma that the exponents (with truncated subtraction and natural division) are at least `n / (c p q) - C0` for n above an explicit threshold, for each headline theorem.
6. A theorem-by-theorem mapping file: theorem name, file, accepted-declarations entry, published counterpart, embedding used.
7. Optional: a clause-count and local-encoding equivalence theorem for `tcnf`; a tree-like leaf-count versus dag-line-count relationship if the Section 2.3 bound is to be compared with dag-like ones.

## D. What changed in the proposal

`docs/ladder/expert-review-proposal.md`: revision note in the header; new Section 2.1a (acyclic derivation representation); 2.1 regularity-not-expansion caveat and clause-shape paragraph; 2.3 one-hot versus Boolean-edge formulas, fixed-p,q regime, composite q as extension, Case 4 stated precisely without claiming a gap; 2.4 Khaniki citation as reported; 2.6 wording "application already established in Pang's preprint" and prime-q as target; 2.7 `c1_main` excluded; 2.8 exact quantifier shapes, nonvacuous explicit theorem placed first, embedding direction note; new Section 2.9 (composite q kept separate); Section 3 questions 4, 6, 7 reworded and request restructured; Section 4 declaration-mapping promise; Section 5 incomparability sentence replaced.
