# Theorem-to-source map

Every headline declaration, with its Lean file and line (at the commit this file was generated, branch `r4/review-followups`), its line in `scripts/accepted_declarations.txt`, the published source, and the theorem number in that source where we know it. 'none' means no published counterpart or a Lean-specific fact. Theorem numbers marked 'not verified' were taken from the dossier and were not rechecked against the papers. Files are under `theory/Theory/`. Lines drift when files change; the declaration name is the stable key.

This is the declaration-to-source mapping promised in `docs/ladder/expert-review-proposal.md` Section 4 (referee requirement, response doc Section B). It does not replace the reviewer's own check of the Lean definitions.

| Declaration | File:line | accepted line | Source | Theorem or result | Note |
|---|---|---|---|---|---|
| `bphp_dag_exponential` | `ProofComplexity/BraunAssembly.lean:322` | 2576 | Braun, arXiv 2609.23015 | main bit-PHP theorem (exponential form; number not verified by us) | Res(xor) dag, line count; superseded asymptotically by Pang Thm 7.2(e) |
| `bphp_dag_superpolynomial` | `ProofComplexity/BraunAssembly.lean:315` | 2575 | Braun, arXiv 2609.23015 | main bit-PHP theorem (superpolynomial form) | same |
| `tcnf_unsat` | `ProofComplexity/TseitinBool.lean:178` | 2487 | none (folklore; Urquhart/Tseitin) | unsatisfiability when total charge is nonzero | one-hot encoding, Lean definition |
| `tcnf_sat_iff` | `ProofComplexity/TseitinSat.lean:136` | 2662 | none (folklore) | satisfiable iff total charge 0 on connected graphs | one-hot encoding |
| `tcnf_clause_props` | `ProofComplexity/TseitinSize.lean:120` | 2762 | none | clause shape: variables in tVars, width at most q+3 | Lean fact about our encoding |
| `tseitin_bool_degree_Fp` | `ProofComplexity/TseitinBool.lean:518` | 2490 | Part-Tzameret, arXiv 1806.09383; Alekhnovich-Razborov FOCS 2001 | degree lower bound for Tseitin mod q over F_p (AR Thm 4.4 / Cor 4.5 style); for the one-hot formula, ours | our one-hot variant; composite q allowed |
| `tseitin_bool_degree_Fp_idx` | `ProofComplexity/TseitinIndexed.lean:51` | 2671 | same | same, indexed family cubFam m | indexed |
| `reslin_tseitin_width` | `ProofComplexity/ResLinTseitin.lean:22` | 2580 | Part-Tzameret, arXiv 1806.09383 | Theorem 45 (width to degree) applied to Tseitin | width bound only |
| `reslin_tseitin_size` | `ProofComplexity/ResLinTseitin.lean:37` | 2591 | Part-Tzameret, arXiv 1806.09383; Pang arXiv 2610.00837 | Cor 46 (Boolean-edge formula; ours is one-hot); Pang Thm 7.2(b) covers one-hot | tree-like, leaf count |
| `reslin_tseitin_size_expander` | `ProofComplexity/ReviewFollowups.lean:52` | 2742 | same | same | new: adds IsConnected and HasExpansionInv |
| `reslin_tseitin_size_primeq` | `ProofComplexity/ReviewFollowups.lean:111` | 2746 | same | prime q, q != p (hypothesis of Pang Thm 7.2(b)) | new |
| `reslin_tseitin_size_idx` | `ProofComplexity/TseitinIndexed.lean:87` | 2672 | same | indexed form on cubFam m |  |
| `reslin_tseitin_size_idx_nonvacuous` | `ProofComplexity/ReviewNonvacuity.lean:212` | 2758 | same | explicit charge 1 instance: unsat, refutation exists, size bound | new |
| `reslin_tseitin_dag_size` | `ProofComplexity/ResLinDagSize.lean:174` | 2601 | Khaniki, ECCC TR20-034 | Theorem 3.1, Corollary 3.2 | dag-like, almost quadratic |
| `reslin_tseitin_dag_size_expander` | `ProofComplexity/ReviewFollowups.lean:65` | 2743 | same | same | new |
| `reslin_tseitin_dag_size_primeq` | `ProofComplexity/ReviewFollowups.lean:122` | 2747 | same | prime q, q != p | new |
| `reslin_tseitin_dag_size_idx` | `ProofComplexity/TseitinIndexed.lean:116` | 2673 | same | indexed |  |
| `reslin_tseitin_dag_size_idx_nonvacuous` | `ProofComplexity/ReviewNonvacuity.lean:229` | 2759 | same | explicit instance with existence | new |
| `tseitin_dag_exp` | `ProofComplexity/PangTseitin.lean:34` | 2761 | Pang, arXiv 2610.00837 | Theorem 1.1 and Theorem 7.2(b) | dag-like, exponential; Pang.Refutation, node count |
| `tseitin_dag_exp_expander` | `ProofComplexity/ReviewFollowups.lean:41` | 2741 | same | same | new |
| `tseitin_dag_exp_primeq` | `ProofComplexity/ReviewFollowups.lean:102` | 2745 | same | Theorem 7.2(b): q prime, q != p | new |
| `tseitin_dag_exp_idx` | `ProofComplexity/TseitinIndexed.lean:159` | 2674 | same | indexed |  |
| `tseitin_dag_exp_idx_nonvacuous` | `ProofComplexity/TseitinIndexed.lean:243` | 2678 | same | explicit instance with Pang.Refutation existence |  |
| `tseitin_dag_exp_explicit_nonvacuous` | `ProofComplexity/TseitinNonvacuity.lean:29` | 2665 | same | explicit instance, existence |  |
| `tseitin_idx_explicit_unsat` | `ProofComplexity/TseitinIndexed.lean:230` | 2677 | none | explicit charge 1 instance unsatisfiable |  |
| `pang_refutation_exists_charge1` | `ProofComplexity/TseitinNonvacuity.lean:20` | 2664 | none (resolution completeness) | existence of a Pang.Refutation |  |
| `green_immune` | `ProofComplexity/GreenImmunity.lean:509` | 2628 | Green, Computational Complexity 9 (2000), via Beck-Li arXiv 1304.0713 | immunity lemma | we followed Beck-Li, not Green |
| `ggw_tseitin_pc_degree` | `ProofComplexity/GreenTseitin.lean:191` | 2631 | Alekhnovich-Razborov, FOCS 2001 | Theorem 4.4 / Corollary 4.5 (constant not verified) | Boolean-edge Tseitin on walk multigraph |
| `ggw_tseitin_reslin_size` | `ProofComplexity/ResLinTseitinEdge.lean:66` | 2633 | Part-Tzameret, arXiv 1806.09383 | Corollary 46 (Ramanujan-type family; ours is the GGW walk multigraph) | tree-like |
| `stdLin_refutes_to_rldag` | `ProofComplexity/EmbedStd.lean:129` | 2682 | Part-Tzameret, arXiv 1806.09383 | definition of Res(lin F): embedding into RLDag | s to 2s |
| `rldag_refutes_to_stdLin` | `ProofComplexity/EmbedStd.lean:205` | 2684 | Part-Tzameret, arXiv 1806.09383 | embedding RLDag into Res(lin F) | n to n |
| `rldag_to_pang` | `ProofComplexity/EmbedPang.lean:294` | 2692 | Pang, arXiv 2610.00837 | definition of Res(lin F_p) (Section 7.1 conventions) | n to n+1 |
| `pang_to_rldag` | `ProofComplexity/EmbedPangBack.lean:258` | 2693 | Pang, arXiv 2610.00837 | same | S to 2S |
| `rln_to_rldag` | `ProofComplexity/EmbedTree.lean:76` | 2695 | none | tree-like into dag-like (node count) |  |
| `stdXor_refutes_to_dag` | `ProofComplexity/EmbedStd.lean:267` | 2686 | BCD, arXiv 2402.04364 | Res(xor) definition, semantic weakening convention | s to s |
| `dag_to_stdXor_refutes` | `ProofComplexity/EmbedStd.lean:319` | 2688 | BCD, arXiv 2402.04364 | same | s to 3s |
| `dagRefutes_to_rldag2` | `ProofComplexity/EmbedXorBack.lean:794` | 2785 | BCD, arXiv 2402.04364 (semantic Res(xor)); Part-Tzameret, arXiv 1806.09383 (syntactic Res(lin F_2)); Pang arXiv 2610.00837 Section 7.1 states the simulation | semantic weakening removed over F_2 | new; s lines, width W, at most N variables per equation, to at most xorBackCost W N * s lines, O(W^2 N) per line |
| `r_wsim` | `ProofComplexity/EmbedXorBack.lean:586` | 2786 | same | one semantic weakening M0 implies L over F_2 in RLDag | new; at most |L|(12N+5) + |M0|(|L|+1) + 1 lines |
| `PangR.pang_to_rref` | `ProofComplexity/EmbedPangR.lean:249` | 2782 | Pang, arXiv 2610.00837 (source system); R_rho^p is ours | Pang.Refutation into C1.RRefutation, rho >= 1 | new; S to S+3, V nonempty |
| `rld_refutation_of_unsat` | `ProofComplexity/ReviewNonvacuity.lean:92` | 2755 | none (resolution completeness) | existence of tree-like Res(lin F_p) refutation | new, existence only |
| `rldag_refutation_of_unsat` | `ProofComplexity/ReviewNonvacuity.lean:101` | 2756 | none | existence of dag-like refutation | new |
| `rref_of_unsat` | `ProofComplexity/ReviewNonvacuity.lean:193` | 2757 | none | existence of RRefutation for every rho >= 1 | new |
| `c1_main` | `ProofComplexity/C1Final.lean:20` | 2647 | none (our own calculus; Pang's method) | no counterpart | excluded from fidelity request |
| `c1_main_expander` | `ProofComplexity/ReviewFollowups.lean:84` | 2744 | none | no counterpart | new |
| `c1_main_idx` | `ProofComplexity/TseitinIndexed.lean:207` | 2676 | none | no counterpart |  |
| `c1_main_idx_nonvacuous` | `ProofComplexity/ReviewNonvacuity.lean:255` | 2760 | none | no counterpart | new |
| `pang_exponent_ge` | `ProofComplexity/ReviewFollowups.lean:154` | 2749 | none | explicit threshold lemma | new |
| `reslin_tree_exponent_ge` | `ProofComplexity/ReviewFollowups.lean:159` | 2750 | none | explicit threshold lemma | new |
| `tseitinW_ge` | `ProofComplexity/ReviewFollowups.lean:177` | 2751 | none | explicit threshold lemma | new |
| `exists_scale_index` | `ProofComplexity/ReviewPadding.lean` | see accepted list | none | arithmetic: every n has m with 8m^2 in (n/2, n] | new |
| `tseitin_dag_exp_all_scales` | `ProofComplexity/ReviewPadding.lean` | see accepted list | Pang, arXiv 2610.00837 | Theorem 7.2(b) at every scale within a factor 2 (not exact-n padding) | new |
