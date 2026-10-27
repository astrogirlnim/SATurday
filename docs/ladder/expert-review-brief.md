# Expert review brief: statement fidelity of the SATurday R4 results

Date 2026-10-27, repo state `main` at `de371c0` or later. This is the cover note for an outside proof-complexity expert.
Full detail is in `docs/ladder/statement-fidelity-dossier.md` (the "dossier", 17 sections). Nothing here is a certification claim.

## 1. What you are asked to check

Statement fidelity only. The Lean kernel checks the proofs; it cannot check that a Lean definition or theorem statement
means what the paper says. We ask: for each result below, does the Lean statement (the proof system, the formula family, the
quantifiers, the size measure) say what the cited source theorem says? You are not asked to read the Lean proofs, to
certify the project target R4, or to judge novelty.

## 2. The results, and where they live

All Lean files are in `theory/Theory/ProofComplexity/`. The dossier section gives the full Lean text, the plain
mathematics, the source, and a row-by-row list of differences.

| Result | Lean theorem (file) | Source theorem | Dossier |
|---|---|---|---|
| Dag-like Res(xor) needs exponential size for bit pigeonhole | `RL.Braun.braunBitPHP`, `bphp_dag_superpolynomial`, `bphp_dag_exponential` (`BraunAssembly.lean`) | Braun, arXiv 2609.23015 (unrefereed). Superseded asymptotically by Pang Thm 7.2(e) | Sec 2 |
| Tree-like Res(lin F_p) size for one-hot Tseitin mod q | `reslin_tseitin_size` (`ResLinTseitin.lean`) | Part and Tzameret, ITCS 2020 / Comput. Complex. 2021, arXiv 1806.09383 (Thms 44, 45, Cor 46) | Sec 3 |
| Dag-like Res(lin F_p) size, Tseitin | `reslin_tseitin_dag_size` (`ResLinDagSize.lean`) | Khaniki, ECCC TR20-034 (Thm 3.1, Cor 3.2) | Sec 4 |
| Alekhnovich-Razborov degree chain, Boolean-edge Tseitin on a walk multigraph | `TseitinEdge.ggw_tseitin_pc_degree` (`GreenTseitin.lean`), `ggw_tseitin_reslin_size` (`ResLinTseitinEdge.lean`), `Green.green_immune` (`GreenImmunity.lean`) | Alekhnovich-Razborov FOCS 2001 (Thm 4.4, Cor 4.5); Green 2000 via Beck-Li arXiv 1304.0713 | Sec 5 |
| Dag-like Res(lin F_p) exponential size, one-hot Tseitin | `Pang.tseitin_dag_exp` (`PangTseitin.lean`; system `PangDag.lean`, constants `PangParams.lean`) | Pang, arXiv 2610.00837 (unrefereed), Thm 1.1 and 7.2(b) | Sec 6 |
| Bounded-rank semantic calculus `R_rho^p` | `C1.c1_main` (`C1Final.lean`; system `C1Rank.lean`) | Pang's method at rank `eps log n`; bespoke, no direct source theorem | Sec 7 |

Shared inputs: one-hot Tseitin CNF `tcnf` and `tseitin_bool_degree_Fp` (`TseitinBool.lean`; polynomial calculus degree bound over
`ZMod p`, `p` not dividing `q`), the cubic expander family, and the unsatisfiability lemma `tcnf_unsat`. Sections 3, 4, 6, 7 all
depend on it (dependency diagram: dossier Sec 15).

Supporting statements added after the referee report: indexed all-size versions `*_idx` (`TseitinIndexed.lean`, e.g.
`tseitin_dag_exp_idx`, `c1_main_idx`, `tseitin_idx_explicit_unsat`); connected and explicit-charge versions (`TseitinExplicit.lean`,
`*_conn`, `*_explicit`); embeddings between the Lean systems and the standard published calculi (`Embed*.lean`, table in
dossier Sec 16, e.g. `stdLin_refutes_to_rldag`, `stdXor_refutes_to_dag`, `dag_to_stdXor_refutes`, `pang_to_rldag`).

## 3. Caveats and open leftovers, stated plainly

- NOT claimed: any lower bound for AC0[p]-Frege, at any depth, including depth 2. That is the open project target
  (`AC0pFregeFrontier.r4_target` is an intentional `sorry`). The results above are for weaker or different systems. The
  barrier audit (`docs/ladder/rungs/r4-phase31-barrier-audit.md`) finds no candidate route to the target.
- Tree-like versus dag-like: Sec 3 is tree-like only; Sec 4, 6 are dag-like; the dossier does not claim the tree-like and
  dag-like results transfer to each other. Dag-like Res(xor) vs tree-like Res(xor) are incomparable in the literature.
- `C1.c1_main` is about a bespoke semantic calculus with logarithmic rank and a huge constant (`kappa(3,2)` about 24.7;
  guaranteed instance sizes above about `10^16` in the Pang constants). It is not Cook-Reckhow and is not evidence about
  AC0[p]-Frege; no bridge theorem exists (dossier 7.1a).
- Semantic weakening is not removed: the Lean dag-like Res(xor) system has semantic weakening. We have embeddings both ways with
  the standard system that also has semantic weakening (factor 1 and 3), and from syntactic into semantic, but the converse
  (semantic to syntactic, polynomial overhead) is open in Lean. Pang Sec 7.1 states it; the proof is not formalized
  (dossier Sec 17 item 1, scoping attempt: no uniform local rewriting).
- Not done: `Pang.Refutation` into `C1.RRefutation`; `pdag_to_affineDAG`; completeness (existence of refutations) for the Tseitin
  calculi; closure under restriction and padding; a standalone analysis of `R_rho^p`.
- Unverified source details: theorem numbers in Part-Tzameret, the published version of Khaniki, the constant in AR Thm 4.4, Green's
  original (we followed Beck-Li), Itsykson-Sokolov's text (BCD used instead), composite-`q` extension of Pang 7.2(b).
- Quantifiers: older Tseitin theorems have shape "for all N there exists n at least N"; indexed all-size versions exist for the
  MGG family. Natural-number truncation appears in exponents; positivity needs large `n`.
- Sources: Braun and Pang are unrefereed preprints; Braun declares substantial AI assistance. The Lean development is also
  AI-assisted. Lean removes the need to trust proofs, not statements. An earlier outside referee report is answered in
  `docs/reports/response-to-referee.md` (all ten objections accepted; fixes are in the dossier).
- Remote CI has never run (nothing was pushed before 2026-10-27); local gate passes.

## 4. Reproduce

    git clone git@github.com:astrogirlnim/SATurday.git && cd SATurday && git checkout <hash given in the hand-over email>
    cd theory && lake build            # toolchain leanprover/lean4:v4.30.0-rc1 (theory/lean-toolchain), Mathlib pinned by lake-manifest.json; do not lake update
    cd .. && bash scripts/check_axioms.sh

The script builds, rejects `sorry` outside Frontier-marked files, and runs `#print axioms` on every declaration in
`scripts/accepted_declarations.txt`; allowed axioms are exactly `propext`, `Classical.choice`, `Quot.sound`. A cold build
(Mathlib from scratch) takes hours on a slow disk; recipe and caveats are in `docs/reports/reproduction.md`. The access to the repo
must be granted to the expert (the URL is an SSH remote).

## 5. Questions for the expert

1. Does each Lean proof system (`RLD`/`RLDag`, `Pang.Refutation`, `RL.DagRefutes`/`PDag`, `C1.RRefutation`) match the standard
   calculus it is named for, given the embedding table in dossier Sec 16? Is the "lines" size measure acceptable where the
   papers count symbols?
2. Is the one-hot Tseitin encoding `tcnf` (blocks of `q` variables per edge, unique-value and local-flow clauses) the encoding the
   sources use, and is the cubic-expander family with a nonzero-charge vertex the intended hard family?
3. Is the Part-Tzameret Theorem 45 Case 4 variant (flagged as a possible gap in the paper) used correctly?
4. Do the quantifier shapes (existential versus indexed families, truncated subtraction) faithfully express "exponential size for
   all large n"?
5. Is semantic weakening in the dag-like Res(xor) and Pang systems a harmless convention, or does the missing converse
   simulation change what the Braun and Pang statements mean?
6. Does Pang's Thm 7.2(b) extend to composite `q` as the Lean statement assumes?
7. Is `C1.c1_main` worth keeping as a stated result at all, or should it be dropped from the fidelity claim?
8. Anything in the statements that a specialist would call vacuous or misleading.

## 6. What the owner must do

1. Pick a reviewer in proof complexity (algebraic proof systems, Res(lin) or Res(xor); the authors of the cited papers are the
   obvious candidates, or a colleague who can read Lean statements). The owner chooses and contacts; no agent sends it.
2. Hand over: this brief; `docs/ladder/statement-fidelity-dossier.md`; `docs/reports/response-to-referee.md` and the referee report
   `.docx`; `docs/ladder/rungs/r4-phase31-barrier-audit.md`; the commit hash to check out; read access to the GitHub repo
   (or a tarball); and the instructions of Section 4. Say plainly that R4 itself is open and that only statement fidelity is asked.
3. Push the final main to origin first if the reviewer will clone it (needs the owner's confirmation) and, ideally, observe CI
   (checklist 3.2 stays unticked until a green remote run).
4. What unblocks card 3.4 (human gate, R4 certified): R4 itself is not proved, so 3.4 cannot honestly close. What this review can
   unblock is checklist item 3.3 ("Independent expert review of statement fidelity"): a written answer from the expert that the statements in
   Section 2 are faithful, or a list of corrections. Record it in `docs/ladder/r4-completion-checklist.md`, then tick 3.3.
   Card 3.4 stays open until a proof of the pin exists and the owner decides.
