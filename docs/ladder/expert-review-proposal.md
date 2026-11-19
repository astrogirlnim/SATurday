# Do the Lean statements say what the papers say? A request for expert review of a formalization of Res(lin) and Res(xor) lower bounds

Date: 2026-11-18, revised after an outside referee report of 2026-11-19 (see `docs/reports/response-to-expert-review-2026-11-19.md`). Repository state: `main` at `bdcc7c1` or later (the exact hash to check out will be given in the covering message). Nothing in this document is a certification claim.

## Abstract

We have formalized, in Lean 4 with Mathlib, a group of lower bounds for algebraic and parity-based proof systems: dag-like Res(xor) on bit pigeonhole (Braun, arXiv 2609.23015), tree-like and dag-like Res(lin F_p) on one-hot Tseitin formulas mod q (Part and Tzameret; Khaniki; Pang, arXiv 2610.00837), the Alekhnovich-Razborov degree chain for Boolean-edge Tseitin, and one bespoke bounded-rank semantic calculus. The Lean kernel checks the proofs. It cannot check that a Lean definition or theorem statement means what the paper says, and that is the main remaining risk. We ask an expert in proof complexity to read the statements (not the proofs) and tell us where a statement is unfaithful, vacuous, or misleading. We do not claim any lower bound for AC0[p]-Frege at any depth. That is the open problem that motivated the project, and it is not solved here.

## 1. Background and the project target

The project (called SATurday) formalizes proof-complexity lower bounds in Lean 4 as a ladder of increasingly hard targets. Earlier rungs covered known results: resolution, Razborov-Smolensky, Hastad's switching lemma with the bounded-depth Frege bound for pigeonhole, polynomial calculus degree bounds for Tseitin formulas over F_p, and Count_q bounds for bounded-depth Frege with Count_p axioms.

The fourth rung, called R4, asks for a super-polynomial lower bound for a proof system with no known one. The default first subtarget is AC0[p]-Frege: for every prime p, a polynomial-size family of unsatisfiable CNFs such that for every fixed depth d and every c, all large n, every depth-d AC0[p]-Frege refutation of the n-th formula has size greater than n^c. In Lean this is the statement `AC0pFregeFrontier.r4_target`, which is an intentional `sorry` (quarantined in a Frontier namespace). We do not have a proof, and a barrier audit we wrote (`docs/ladder/rungs/r4-phase31-barrier-audit.md`) finds no candidate route to it among the techniques we examined.

The intermediate rungs of R4 are Res(xor), Res(lin F_p), depth-2 AC0[p]-Frege, and constant-depth AC0[p]-Frege. The work described below sits on the first two of these, using recent preprints and older published results. The Lean development is AI-assisted. The kernel check removes the need to trust proofs, but not statements.

## 2. What is formalized

All Lean files are in `theory/Theory/ProofComplexity/`. Conventions: a CNF is a finite set of clauses, a clause a finite set of literals `{var : ℕ, pos : Bool}`. "Size" in the Lean statements counts lines (or nodes, or leaves, as stated), not symbols. The full detail, with the plain mathematics and a row-by-row list of differences from each source, is in the statement fidelity dossier (`docs/ladder/statement-fidelity-dossier.md`, 17 sections), which we can send with this document.

### 2.1 Shared input: one-hot Tseitin mod q on a cubic family

Variables `x_{e,j}` mean "edge e carries value j in Z_q". The formula `tcnf G q b` has, for each edge, an at-least-one clause and pairwise at-most-one clauses, and for each vertex v and each local labelling of its three incident edges whose net flow differs from the charge `b v`, one forbidden-labelling clause of width 3. Net flow at v is the sum of values on edges where v is the smaller endpoint minus the sum where v is the larger endpoint.

```lean
def tcnf (b : Fin n → ZMod q) : CNF :=
  (univ.image (aloC G q)) ∪
    ((univ ×ˢ (range q ×ˢ range q)).filter (fun x : G × ℕ × ℕ => x.2.1 ≠ x.2.2)).image
      (fun x => amoC G x.1 x.2.1 x.2.2) ∪
    ((univ ×ˢ univ).filter (fun x : Fin n × (G → ZMod q) => netAt G q x.1 x.2 ≠ b x.1)).image
      (fun x => vC G q x.1 x.2)

theorem tcnf_unsat {b} (hb : ∑ v, b v ≠ 0) : ¬ Satisfiable (tcnf G q b)
```

Satisfiability of `tcnf G q b` is equivalent to every connected component having charge sum zero in Z_q. Lean proves only the direction "some component sum nonzero implies unsatisfiable" (in the weaker form with total sum nonzero), which is the direction every lower bound needs. On a connected graph, total charge nonzero is exactly unsatisfiability. The graph family is a cubicized Margulis/Gabber-Galil torus graph: for every N there is a connected cubic graph on n ≥ N vertices with vertex expansion constant `K`. The proof shows that n = 8m² for suitable m. Important for reading the displayed theorems below: their conclusions say only `IsRegular G 3` (the headline theorems do not even state connectivity). Regularity is not expansion; expansion (`HasExpansionInv`) and connectivity are properties of the specific witness, available as `cubFam_props` and used inside the proofs, but not part of the displayed conclusion. A reader must not take "IsRegular G 3" as certifying an expander. The indexed theorem `tseitin_bool_degree_Fp_idx` also exposes connectivity.

Clause shape: `vC` mentions only the three edges incident to `v`, and `netAt` depends only on those edges, so the quantification over full labellings `G → ZMod q` in `tcnf` produces, after the finite-set image deduplicates, one width-3 clause per forbidden local labelling. Lean proves the clause properties (`tcnf_clause_props`: variables inside `tVars`, width at most q+3) and the satisfiability criterion on connected graphs (`tcnf_sat_iff`: satisfiable iff total charge is 0). It does not prove a clause-count formula, and we do not claim one.

The key algebraic input is `tseitin_bool_degree_Fp`: for primes p not dividing q, on this family, no polynomial calculus refutation over `ZMod p` of `tcnf G q b` has degree `((n-2)/1312 - q(q+3))/(q-1)` (natural-number arithmetic). Sections 2.3, 2.4, 2.6 below all depend on it.

### 2.1a How dag-like derivations are represented (acyclicity)

Every dag-like system here is built so that a line can only be justified by lines that were already present, so a cyclic justification such as A from B, B from C, C from A cannot be accepted. In three different ways:

- `RLF.RLDag Ax 𝓛` and `RL.Der Ax P` are inductive predicates on finite sets of lines, generated from the empty set by adding one line at a time, where each rule's premises must lie in the set built so far (`RLDag.comb`: `RLDag Ax 𝓛 → A ∈ 𝓛 → B ∈ 𝓛 → ... → RLDag Ax (insert (...) 𝓛)`; `Der.add`: `Der Ax P → Step Ax P L → Der Ax (insert L P)`). Every member of the final set has a first insertion, whose premises were inserted strictly earlier, which is a topological order. Size is the number of distinct lines, which is at most the length of the insertion sequence.
- `PDag` (Braun's affine DAG) indexes lines by `Fin S` and every justification uses indices `a < i`, `b < i`.
- `Pang.Refutation` and `RRefutation` carry a node list with `prem_lt : ∀ i < S, ∀ j ∈ prem i, j < i`.

Soundness of each (`rldag_sound`, `Der`'s soundness, `Pang.Refutation.unsat`, `RRefutation.unsat`) is proved by induction over this structure.

### 2.2 Dag-like Res(xor) on bit pigeonhole (Braun)

Source: Braun, arXiv 2609.23015 (unrefereed; the abstract states substantial AI assistance). Pang's Theorem 7.2(e) gives an asymptotically better bit-PHP bound, so this result is no longer the strongest known; we have formalized Braun's statement, not Pang's.

Bit PHP has 2^l + 1 pigeons, each an l-bit string, and clauses forbidding two pigeons from having the same string. Lines of the proof system are disjunctions of F_2-affine equations. The Lean statements:

```lean
def BraunBitPHP : Prop :=
  ∀ K : ℝ, 0 < K → ∃ L : ℕ, ∀ l ≥ L, ∀ {S : ℕ} (C : Fin S → PClause (BitVar (2 ^ l + 1) l)),
    PDag (usualInitials (2 ^ l + 1) l) C → ∀ f : Fin S, C f = ∅ → ((2 ^ l : ℕ) : ℝ) ^ K < (S : ℝ)

theorem bphp_dag_superpolynomial (K : ℝ) (hK : 0 < K) :
    ∃ L : ℕ, ∀ l ≥ L, ∀ s : ℕ, DagRefutes (↑(bphpCNF l (2 ^ l + 1)) : Set Clause) s →
      ((2 ^ l : ℕ) : ℝ) ^ K < (s : ℝ)

theorem bphp_dag_exponential (l : ℕ) (hl : 32 ≤ l) (s : ℕ)
    (hs : DagRefutes (↑(bphpCNF l (2 ^ l + 1)) : Set Clause) s) :
    Real.exp (((2 ^ l : ℕ) : ℝ) / (32768 * (l : ℝ) ^ 2)) < (s : ℝ)
```

With n = 2^l the exponential bound reads 2^{Ω(n / log² n)} lines. The bound is proved for a larger affine DAG calculus `PDag` (steps: initial, weakening by semantic entailment, resolution on an affine form and its complement, and a binary semantic step) and transferred to `DagRefutes`, the system as defined in Lean. This is a bound on the number of lines, for the formula `bphpCNF` with an explicit index set (shape: for all l ≥ 32).

### 2.3 Tree-like Res(lin F_p) on one-hot Tseitin (Part and Tzameret)

Source: Part and Tzameret, ITCS 2020 and Computational Complexity 2021, arXiv 1806.09383 (Theorems 44, 45, Corollary 46). Their formula uses one Boolean variable per edge; ours is the one-hot encoding with q variables per edge. These are different formulas. We prove nothing that transfers a lower bound between the two encodings, so our theorem is about the one-hot formula only and is not a restatement of their Corollary 46 instance.

```lean
theorem reslin_tseitin_size (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ ∀ b : Fin n → ZMod q, ∀ w s : ℕ,
      RLF.RLD (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' tcnf G q b) ∪ RLF.boolAx)
        w ∅ s →
      2 ^ ((((n - 2) / 1312 - q * (q + 3)) / (q - 1) - (q + 3) - p) / (p - 1)) ≤ 2 * s
```

Here `RLD` is tree-like Res(lin F_p) with Boolean axioms and the CNF as leaves, lines of width w, and s leaves. For large n the exponent is at least n / (1312 (q-1)(p-1)) minus a constant, so s = 2^{Ω_{p,q}(n)} for fixed p and q, with n the number of graph vertices (not the number of Boolean variables or the input length). The statement does not itself assert that the exponent is positive. The Lean statement allows any q ≥ 2 with p not dividing q, while the cited sources state prime q. The prime-q case is a special case of the Lean theorem (instantiate q) and is the fidelity target; the composite-q generality is a separate extension, discussed in Section 2.9. The proof uses the degree bound of Section 2.1 and the size-to-width and width-to-degree transfers. For Theorem 45, Case 4: what we know is that our repository notes flag this case and that the Lean transfer (`RLF.rld_cnf_pcd`) uses a variant (degree w+1, with a side condition). We have not verified whether our concern is the same as a typographical slip in the paper's text (a premise written with g but its arithmetization with f) or a different defect; we do not claim a mathematical gap in the paper.

### 2.4 Dag-like Res(lin F_p), almost quadratic (Khaniki)

Source: Khaniki, ECCC TR20-034 (Theorem 3.1, Corollary 3.2); the journal version is reported to be ACM Trans. Comput. Logic 23(3), Article 16 (2022), DOI 10.1145/3506702 (metadata supplied by a referee, not yet checked by us). We have not compared the journal version with the ECCC statement.

```lean
theorem reslin_tseitin_dag_size (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ q + 5 ≤ tseitinW p q n ∧
      ∀ b : Fin n → ZMod q, ∀ 𝓛 : Finset (Finset (RLF.LEq (ZMod p))),
        RLF.RLDag (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' tcnf G q b) ∪
          RLF.boolAx) 𝓛 → (∅ : Finset (RLF.LEq (ZMod p))) ∈ 𝓛 →
        ((tseitinW p q n - (q + 3)) * (tseitinW p q n - (q + 3)) <
          72 * (q + 3) * 𝓛.card * (Nat.log 2 (3 * 𝓛.card) + 1)) ∧
        (tseitinW p q n - (q + 3)) * (tseitinW p q n - (q + 3)) /
          (72 * (q + 3) * (Nat.log 2 (3 * ((tseitinW p q n - (q + 3)) *
            (tseitinW p q n - (q + 3)))) + 1)) ≤ 𝓛.card
```

where `tseitinW p q n = (((n - 2) / 1312 - q (q + 3)) / (q - 1)) / (p - 1)`. In words: a dag-like refutation with L distinct lines satisfies (W - (q+3))² < 72 (q+3) L (log₂(3L) + 1) with W of order n, hence L = Ω(n² / log n). The second conjunct is a division form giving an explicit lower bound on L. This is superseded by the exponential bound of Section 2.6.

### 2.5 The Alekhnovich-Razborov chain for Boolean-edge Tseitin

Sources: Alekhnovich and Razborov, FOCS 2001 (Theorem 4.4, Corollary 4.5); Green, Computational Complexity 2000, followed via Beck and Li, arXiv 1304.0713 (we did not read Green's original). The formula is the Tseitin formula on a walk multigraph `GGW m k` (left vertices the torus, right vertices the torus, one edge per length-k walk in the 8-step Gabber-Galil system), with Boolean edge variables.

```lean
theorem green_immune {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) (hq : (q : F) ≠ 0) (A : Finset ℕ)
    (s : ZMod q) {g : ML F} (hg : g ≠ 0) (hv : ∀ a ∈ ZA q A s, ev a g = 0) :
    (A.card + 1) / q ≤ deg g

theorem ggw_tseitin_pc_degree {F : Type} [Field F] {q : ℕ} (hq2 : 2 ≤ q) (hqF : (q : F) ≠ 0)
    {m : ℕ} (hm : 16 * q ≤ m) {k : ℕ} (hk : k0 q ≤ k) (σ : MggTorus m ⊕ MggTorus m → ZMod q)
    {d : ℕ} (hd : (d : ℝ) ≤ (m : ℝ) * m * (8 : ℝ) ^ k / (256 * (q : ℝ) ^ 2)) :
    ¬ PCD ((ggwGraph m (by omega) k).Ax F q σ) d 1

theorem ggw_tseitin_reslin_size (p : ℕ) [Fact p.Prime] {q : ℕ} (hq2 : 2 ≤ q) (hpq : ¬ p ∣ q)
    {m : ℕ} (hm : 16 * q ≤ m) {k : ℕ} (hk : k0 q ≤ k) (σ : MggTorus m ⊕ MggTorus m → ZMod q)
    {w s : ℕ}
    (h : RLF.RLD (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) ''
      ((ggwGraph m (by omega) k).cnf q σ)) ∪ RLF.boolAx) w ∅ s) :
    2 ^ ((m * m * 8 ^ k / (256 * q ^ 2) - 8 ^ k - p) / (p - 1)) ≤ 2 * s
```

The first says that a nonzero multilinear polynomial vanishing on the "A-sum equals s mod q" slice has degree at least (|A| + 1)/q (Green's immunity bound, here with the slightly stronger constant floor((d+1)/q) in place of AR's floor(d/(4(q-1)))). The second and third are the degree and tree-like size consequences. The statements are for all charge vectors σ, including satisfiable ones, where they hold vacuously.

### 2.6 Dag-like Res(lin F_p), exponential, one-hot Tseitin (Pang)

Source: Pang, arXiv 2610.00837 (unrefereed; Theorem 1.1 and Theorem 7.2(b)). This is the strongest dag-like result here and Pang's preprint already contains the Tseitin application, so what we have is a formalization of an application already established in Pang's (unrefereed) preprint, not a new theorem. The Lean theorem is stated for q ≥ 2 with p not dividing q; Pang's Theorem 7.2(b) assumes q prime and different from p. The prime-q instance is the fidelity target; composite q is an extension (Section 2.9).

```lean
theorem tseitin_dag_exp (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ ∀ b : Fin n → ZMod q,
      ∀ R : Pang.Refutation (tcnf G q b) (tVars G q) p, 2 ^ (n / cC p q) ≤ R.S
```

The system `Pang.Refutation` has lines that are finite sets of polynomials of degree at most 1 over `ZMod p` in the CNF's own variables (no extension variables), the rules init, zero, boolean, weakening, false-constant removal, linear combination, and multiplication keeping degree at most 1, and size is the number of nodes (nodes may repeat a line). The constant `cC p q = cA q * 8 (p-1)² * cS p q` with `cA q = 2624 q + 1313`, `cLam q = 18 q cA q`, `cS p q = 2 (1 + cLam q ^ (p-1))`. It is huge: about 2.34 × 10^16 for (p, q) = (3, 2), so the bound is meaningful only for very large n. Asymptotically it is 2^{Ω_{p,q}(n)} for fixed p, q; it is not uniform in p and q (the constant grows with both, so for moduli growing with n the displayed bound can be trivial).

### 2.7 A bounded-rank semantic calculus

This result has no published source: it concerns a calculus we defined, so there is no published definition to be faithful to. It is therefore excluded from the statement-fidelity request (it would need a separate mathematical review of the calculus and of the transfer from Pang's method) and is listed here only so that the whole development is visible.

```lean
theorem c1_main (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (ε : ℝ) (hε : 0 < ε) (hεκ : (kappa p q + 1) * ε < 1) (M : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), M ≤ n ∧ IsRegular G 3 ∧ ∀ b : Fin n → ZMod q,
      ∀ ρ : ℕ, 1 ≤ ρ → (ρ : ℝ) ≤ ε * Real.log n →
      ∀ R : RRefutation (tcnf G q b) (tVars G q) ρ p,
        Real.exp ((n : ℝ) ^ (1 - (kappa p q + 1) * ε)) ≤ R.S
```

with `kappa p q = (p - 1) log (cLam q)`. In `RRefutation`, a line is a disjunction of terms, a term is a conjunction of affine equations over F_p whose span (of affine forms, constants included) has dimension at most ρ. The rules are initial clause, the tautology x_i = 0 or x_i = 1, weakening, and two semantic rules: from one term (or two terms in two premise lines) infer any term of rank at most ρ implied on the Boolean cube, or the empty clause if the premises are unsatisfiable there. Size is the node count.

Plainly: this is Pang's method run at rank ε log n. The semantic rules are checked by quantifying over all Boolean assignments, so this is not a Cook-Reckhow proof system. Its rank parameter is a dimension, not a depth. κ is about 24.7 for (3, 2), so ε must be below about 1/25.7. We prove no bridge from depth-d AC0[p]-Frege proofs into this calculus, and we do not know whether one exists. The theorem is evidence about nothing at the R4 level.

### 2.8 Supporting statements

- Quantifier shapes, stated exactly. The displayed headline theorems in 2.3, 2.4, 2.6, 2.7 have shape (E): for every N there exist n ≥ N and a graph G on n vertices such that the bound holds. This gives arbitrarily large hard instances (an infinite set of sizes). It is not the shape (U) "there is n0 such that for every n ≥ n0 there is a hard G_n", and we do not claim it. The indexed theorems (`TseitinIndexed.lean`) have an intermediate shape: for every m at least an explicit floor, on the explicit family `cubFam m` on 8m² vertices, with explicit charge, so the sizes are an explicit sequence, not all sizes. Padding to every n is not formalized, and a padding argument would need a reduction preserving the lower bound in each proof system; consecutive sizes differing by a factor at most 2 is not such an argument. Bit PHP (2.2) is indexed by l ≥ 32 (sizes growing by a factor about 8 per step).
- Non-vacuous explicit instances (central, not peripheral): `tseitin_dag_exp_idx_nonvacuous` states, for every m ≥ the floor, on the explicit connected cubic instance with charge 1 at one vertex, together: the CNF is unsatisfiable, a `Pang.Refutation` exists, and every `Pang.Refutation` has at least 2^(8m²/C) nodes. The other explicit variants are `tseitin_dag_exp_explicit_nonvacuous`, `tseitin_idx_explicit_unsat`, `c1_main_idx`. The unquantified-charge theorems of 2.3 to 2.7 include satisfiable charges, for which they hold vacuously.
- Connected and explicit-charge variants (`TseitinExplicit.lean`).
- Embeddings between our systems and the standard published calculi (`Embed*.lean`), summarized in this table (sizes are line or node counts):

The `RLDag`/`Pang.Refutation` embeddings are the load-bearing ones for comparing systems; they should be read together with 2.1a. Direction matters: a lower bound for a system P transfers to a system Q only along an embedding of Q-proofs into P-proofs with a size bound. Tree-like `RLD` into dag-like `RLDag` is also formalized (`rln_to_rldag`, `EmbedTree.lean`, node count to line count, not leaf count).

| Statement | Lean name | Size change |
|---|---|---|
| Part-Tzameret Res(lin F) into our `RLDag` | `stdLin_refutes_to_rldag` | s to 2s |
| `RLDag` into Part-Tzameret Res(lin F) | `rldag_refutes_to_stdLin` | n to n |
| Standard Res(xor) (BCD, arXiv 2402.04364, syntactic or semantic weakening) into `RL.DagRefutes` | `stdXor_refutes_to_dag` | s to s |
| `RL.DagRefutes` into standard Res(xor) with semantic weakening | `dag_to_stdXor_refutes` | s to 3s |
| `RLDag` into `Pang.Refutation` | `rldag_to_pang` | n to n+1 |
| `Pang.Refutation` into `RLDag` | `pang_to_rldag` | S to 2S |

Caveats on the table: the encoding of a positive literal x = 1 differs between systems (a separate theorem pair handles the usual encoding at a cost additive in clause widths), and Part and Tzameret measure total symbol size while we count lines, so a lower bound on lines yields one on symbols and not conversely.

### 2.9 Composite q, kept separate

All Tseitin statements above are for q ≥ 2 with p not dividing q. For the sources, q is prime. We present the prime-q case as the thing to compare with the literature (it is an instance of the Lean statements) and the composite-q case as a different claim: a generalization that the Lean kernel has checked, but that no source states. Its Lean proof goes through `tseitin_bool_degree_Fp`, which works over a cyclotomic extension containing a primitive q-th root of unity. We do not claim the generalization is mathematically known, and have not had it reviewed by an expert.


Follow-up status (branch `r4/review-followups`, 2026-11-19). Done in Lean since this proposal was revised: expansion and connectivity conjuncts as new theorems `tseitin_dag_exp_expander`, `reslin_tseitin_size_expander`, `reslin_tseitin_dag_size_expander` (and `c1_main_expander`); prime-q corollaries `tseitin_dag_exp_primeq`, `reslin_tseitin_size_primeq`, `reslin_tseitin_dag_size_primeq`; non-vacuity with refutation existence for `RLD`, `RLDag`, `RRefutation` (`rld_refutation_of_unsat`, `rldag_refutation_of_unsat`, `rref_of_unsat`, and the combined indexed statements `reslin_tseitin_size_idx_nonvacuous`, `reslin_tseitin_dag_size_idx_nonvacuous`, `c1_main_idx_nonvacuous`); explicit exponent thresholds (`pang_exponent_ge`, `reslin_tree_exponent_ge`, `tseitinW_ge`); the declaration-to-source table `docs/ladder/theorem-source-map.md`; and every-scale hard instances within a factor 2 (`tseitin_dag_exp_all_scales`). Not done: padding to exactly n vertices (see the response document, Section E), and the clause-count equivalence for `tcnf`. The statements displayed in Sections 2.3, 2.4, 2.6 are unchanged; the new theorems are the ones to cite for the expander family and for prime q.

## 3. What we ask the reviewer to check

We ask about statement fidelity only. You are not asked to read Lean proofs, to certify the project target, or to judge novelty. `c1_main` (Section 2.7) is out of scope. Please assess results one at a time (theorem name, Lean definition, published counterpart, established equivalence or one-way embedding), not as a whole. Concretely:

1. Proof systems. Does each Lean system (`RLD` and `RLDag`, `Pang.Refutation`, `RL.DagRefutes` and `PDag`, `RRefutation`) match the standard calculus it is named after, given the embedding table above? Is a line count an acceptable size measure where the papers count symbols?
2. Formula and family. Is the one-hot Tseitin encoding `tcnf` (blocks of q variables per edge, unique-value and local-flow clauses) the encoding the sources use, or a defensible variant? Is a cubic expander family with a nonzero-charge vertex the intended hard family?
3. Part-Tzameret Theorem 45, Case 4. The paper's argument has a step that may be a gap. Is our variant of it used correctly?
4. Quantifiers. Older theorems have the shape "for all N there is n at least N". The honest classification is in 2.8: (E) infinitely many hard sizes, indexed explicit family on 8m² vertices, and not eventual all-size bounds. Do these shapes, including truncated natural-number subtraction and division in exponents, express what a reader would take from the claim in the paper, and is the 8m²-indexed family enough for how you would cite the result?
5. Semantic weakening. Our dag-like Res(xor) system has semantic weakening. We have embeddings both ways with the standard system that also has it (factors 1 and 3), and from the syntactic standard system into ours, but the converse (semantic weakening to syntactic, polynomial overhead) is not formalized. Pang's Section 7.1 states it; the proof is not in Lean, and a scoping attempt found no uniform local rewriting. Our understanding is that only the forward embedding (standard syntactic system into ours, formalized with no size loss for Res(xor)) is needed to transfer a lower bound to the standard syntactic system, and the missing converse affects only polynomial equivalence of the two systems, not the lower bounds. Is that right, and is the forward embedding the correct one (initial clauses, rules, size overhead)?
6. Composite q (a separate extension, not part of the fidelity target). The Lean statements are for q ≥ 2 with p not dividing q, proved via a degree lemma over a primitive q-th root of unity (a kernel-checked proof, so the generalization is established as a Lean theorem). The sources, including Pang's Theorem 7.2(b), state prime q. The fidelity question is only about the prime-q instance. As a separate, optional request: is the composite-q statement a faithful and natural generalization, and does anything in the sources' argument (expansion and immunity hypotheses, the extension-field step) that we have not isolated depend on q being prime?
7. (Withdrawn.) The bounded-rank result `c1_main` has no published counterpart and is excluded from the fidelity request; see 2.7.
8. Vacuity and misleading statements. Is there anything a specialist would call vacuous or misleading? We already know of these: statements quantify over all charge vectors b and so include satisfiable instances (vacuously true there); connectivity and expansion of the graph are properties of the witness and do not appear in the displayed old theorems (the new `*_expander` theorems state them); exponents need large n to be positive.

## 4. Trust base and reproduction

The Lean kernel checks every proof. The development uses exactly the three standard axioms `propext`, `Classical.choice`, `Quot.sound`. The script `scripts/check_axioms.sh` builds the project, rejects any `sorry` in a file not marked as Frontier, and runs `#print axioms` on every declaration in `scripts/accepted_declarations.txt`. Eleven Frontier-quarantined `sorry`s exist (at last recorded run, in `AC0pFrege`, `CuttingPlanes`, `MGG/SpectralFrontier`, `MGG/Factor2Inv4`, `Tseitin`, `CSExpansion`); none of them is in the accepted declarations list, and none is used by the results above.

The accepted-declarations list is `scripts/accepted_declarations.txt`; we will supply, with the pinned commit, a table mapping each theorem named in Section 2 to its file and to its line in that list, and the `check_axioms.sh` output. A cold, independently reproduced build is a limitation of the evidence (see below); the reviewer's audit would be the first independent one.

```
git clone <repo> SATurday && cd SATurday && git checkout <pinned hash>
cd theory && lake build        # Lean toolchain leanprover/lean4:v4.30.0-rc1; Mathlib pinned by lake-manifest.json; do not run lake update
cd .. && bash scripts/check_axioms.sh
```

Caveats, stated exactly. A cold build (Mathlib from scratch) has not been run on our machine; all gate runs used a warm cache, and a cold build is expected to take hours on a slow disk (recipe in `docs/reports/reproduction.md`). Remote continuous integration has never run, because nothing had been pushed before 2026-10-27; the local gate passes. Repository access must be granted to the reviewer (or a tarball supplied).

Source status. Braun and Pang are unrefereed preprints from September 2026; Braun states substantial AI assistance. Part-Tzameret, Alekhnovich-Razborov, and Green are refereed. Details we could not verify: theorem numbers in Part-Tzameret, the published version of Khaniki (see 2.4 for the reported citation), the constant in AR Theorem 4.4, Green's original text (we followed Beck-Li), and Itsykson-Sokolov's text (we used BCD, which states the semantic-weakening convention). An earlier outside referee report on the dossier raised ten objections; all were accepted and the fixes are in the dossier (`docs/reports/response-to-referee.md`). They included a wrong satisfiability criterion for disconnected graphs, the missing indexed family, Pang's priority over Braun, and the need for embeddings.

## 5. Open problems and what is not claimed

- No lower bound for AC0[p]-Frege is proved or claimed, at any depth, including depth 2. The R4 target is an intentional `sorry`. The results above are for weaker or different systems.
- Depth-2 AC0[p]-Frege and constant-depth AC0[p]-Frege remain open (rungs 2.3 and 2.4 of our plan). Pang names the obstruction for the Frege route in his Section 8: a quantitative tradeoff between approximation degree and rank shrinkage under iteration over depth, with the missing ingredient being polynomial calculus degree lower bounds near or above n/2 for polynomial-size, o(n)-width CNFs. Our bounded-rank theorem does not supply this, since its rank bound is logarithmic.
- Tree-like and dag-like results are different statements: Section 2.3 is tree-like (leaf count), Sections 2.2, 2.4, 2.6 are dag-like. With identical rules and size measure every tree-like proof is a dag-like proof, so a dag-like lower bound implies the tree-like one and not conversely; this is formalized for Res(lin F) as `rln_to_rldag`, for node count. A dag-like line-count bound does not give the leaf-count bound of 2.3 (leaves can be fewer than nodes), so 2.3 is not a corollary of 2.4 or 2.6 as stated.
- Semantic weakening has not been removed (question 5).
- Not formalized: translation of `Pang.Refutation` into the bounded-rank calculus; translation `pdag_to_affineDAG`; size-controlled completeness for the Tseitin calculi (existence of refutations is now formalized, without size control); closure under restriction and padding to every size; a standalone analysis of the bounded-rank calculus.
- No single Lean theorem has the R4 shape (an explicit polynomial-size family, every depth, every exponent) for a standard system.
- Novelty. Every result here has a published antecedent except the bounded-rank calculus, which is a corollary of Pang's method for a calculus we defined. Mathematically, the Tseitin results are formalizations, with composite q and explicit constants as the only differences. We make no novelty claim.

## 6. Next steps and contact

Placeholder: contact name and address, and the commit hash and repository access instructions, to be filled in by the project owner when sending. We would be grateful for either a written statement that the statements in Section 2 are faithful, or a list of corrections. A correction list would be recorded in the repository (`docs/ladder/r4-completion-checklist.md`, item 3.3, independent expert review of statement fidelity), and any changed statement would be re-proved or re-stated before any claim is made.

## References

- Braun, arXiv 2609.23015 (2026), dag-like Res(xor) and bit pigeonhole. Unrefereed.
- Pang, arXiv 2610.00837 (2026), dag-like Res(lin F_p) lower bounds. Unrefereed.
- Part and Tzameret, Resolution with counting: dag-like lower bounds and different moduli, ITCS 2020 and Computational Complexity 2021, arXiv 1806.09383.
- Khaniki, ECCC TR20-034 (revised 2021); published version not checked.
- Alekhnovich and Razborov, Lower bounds for polynomial calculus: non-binomial case, FOCS 2001 and Proc. Steklov Inst. Math. 242 (2003).
- Green, Computational Complexity 9 (2000); Beck and Li, arXiv 1304.0713.
- BCD, arXiv 2402.04364 (authors as cited in the dossier), Res(xor) with the semantic weakening convention.
- Efremenko, Garlik, Itsykson (2024) and Itsykson and Sokolov, cited in the dossier for Res(xor); texts not all retrieved.
