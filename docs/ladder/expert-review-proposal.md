# Do the Lean statements say what the papers say? A request for expert review of a formalization of Res(lin) and Res(xor) lower bounds

Date: 2026-11-18. Repository state: `main` at `bdcc7c1` or later (the exact hash to check out will be given in the covering message). Nothing in this document is a certification claim.

## Abstract

We have formalized, in Lean 4 with Mathlib, a group of lower bounds for algebraic and parity-based proof systems: dag-like Res(xor) on bit pigeonhole (Braun, arXiv 2609.23015), tree-like and dag-like Res(lin F_p) on one-hot Tseitin formulas mod q (Part and Tzameret; Khaniki; Pang, arXiv 2610.00837), the Alekhnovich-Razborov degree chain for Boolean-edge Tseitin, and one bespoke bounded-rank semantic calculus. The Lean kernel checks the proofs. It cannot check that a Lean definition or theorem statement means what the paper says, and that is the main remaining risk. We ask an expert in proof complexity to read the statements (not the proofs) and tell us where a statement is unfaithful, vacuous, or misleading. We do not claim any lower bound for AC0[p]-Frege at any depth. That is the open problem that motivated the project, and it is not solved here.

## 1. Background and the project target

The project (called SATurday) formalizes proof-complexity lower bounds in Lean 4 as a ladder of increasingly hard targets. Earlier rungs covered known results: resolution, Razborov-Smolensky, Hastad's switching lemma with the bounded-depth Frege bound for pigeonhole, polynomial calculus degree bounds for Tseitin formulas over F_p, and Count_q bounds for bounded-depth Frege with Count_p axioms.

The fourth rung, called R4, asks for a super-polynomial lower bound for a proof system with no known one. The default first subtarget is AC0[p]-Frege: for every prime p, a polynomial-size family of unsatisfiable CNFs such that for every fixed depth d and every c, all large n, every depth-d AC0[p]-Frege refutation of the n-th formula has size greater than n^c. In Lean this is the statement `AC0pFregeFrontier.r4_target`, which is an intentional `sorry` (quarantined in a Frontier namespace). We do not have a proof, and a barrier audit we wrote (`docs/ladder/rungs/r4-phase31-barrier-audit.md`) finds no candidate route to it among the techniques we examined.

The intermediate rungs of R4 are Res(xor), Res(lin F_p), depth-2 AC0[p]-Frege, and constant-depth AC0[p]-Frege. The work described below sits on the first two of these, using recent preprints and older published results. The Lean development is AI-assisted. The kernel check removes the need to trust proofs, but not statements.

## 2. What is formalized

All Lean files are in `theory/Theory/ProofComplexity/`. Conventions: a CNF is a finite set of clauses, a clause a finite set of literals `{var : ℕ, pos : Bool}`. "Size" in the Lean statements counts lines (or nodes, or leaves, as stated), not symbols. The full detail, with the plain mathematics and a row-by-row list of differences from each source, is in the statement fidelity dossier (`docs/ladder/statement-fidelity-dossier.md`, 17 sections), which we can send with this document.

### 2.1 Shared input: one-hot Tseitin mod q on cubic expanders

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

Satisfiability of `tcnf G q b` is equivalent to every connected component having charge sum zero in Z_q. Lean proves only the direction "some component sum nonzero implies unsatisfiable" (in the weaker form with total sum nonzero), which is the direction every lower bound needs. On a connected graph, total charge nonzero is exactly unsatisfiability. The graph family is a cubicized Margulis/Gabber-Galil torus graph: for every N there is a connected cubic graph on n ≥ N vertices with vertex expansion constant `K`. The proof shows that n = 8m² for suitable m.

The key algebraic input is `tseitin_bool_degree_Fp`: for primes p not dividing q, on this family, no polynomial calculus refutation over `ZMod p` of `tcnf G q b` has degree `((n-2)/1312 - q(q+3))/(q-1)` (natural-number arithmetic). Sections 2.3, 2.4, 2.6 below all depend on it.

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

Source: Part and Tzameret, ITCS 2020 and Computational Complexity 2021, arXiv 1806.09383 (Theorems 44, 45, Corollary 46). Their formula uses Boolean edge variables; ours is the one-hot encoding.

```lean
theorem reslin_tseitin_size (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ ∀ b : Fin n → ZMod q, ∀ w s : ℕ,
      RLF.RLD (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' tcnf G q b) ∪ RLF.boolAx)
        w ∅ s →
      2 ^ ((((n - 2) / 1312 - q * (q + 3)) / (q - 1) - (q + 3) - p) / (p - 1)) ≤ 2 * s
```

Here `RLD` is tree-like Res(lin F_p) with Boolean axioms and the CNF as leaves, lines of width w, and s leaves. For large n the exponent is at least n / (1312 (q-1)(p-1)) minus a constant, so s = 2^{Ω(n)}. The statement does not itself assert that the exponent is positive. q need not be prime in the Lean statement (the cited sources state prime q); this is an extension we want checked (question 6). The proof uses the degree bound of Section 2.1 and the size-to-width and width-to-degree transfers. One step (Case 4 of Theorem 45) is flagged as a possible gap in the paper itself.

### 2.4 Dag-like Res(lin F_p), almost quadratic (Khaniki)

Source: Khaniki, ECCC TR20-034 (Theorem 3.1, Corollary 3.2). The published version has not been checked.

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

Source: Pang, arXiv 2610.00837 (unrefereed; Theorem 1.1 and Theorem 7.2(b)). This is the strongest dag-like result here and it already contains the Tseitin application, so what we have is a formalization of a published application, not a new theorem.

```lean
theorem tseitin_dag_exp (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ ∀ b : Fin n → ZMod q,
      ∀ R : Pang.Refutation (tcnf G q b) (tVars G q) p, 2 ^ (n / cC p q) ≤ R.S
```

The system `Pang.Refutation` has lines that are finite sets of polynomials of degree at most 1 over `ZMod p` in the CNF's own variables (no extension variables), the rules init, zero, boolean, weakening, false-constant removal, linear combination, and multiplication keeping degree at most 1, and size is the number of nodes (nodes may repeat a line). The constant `cC p q = cA q * 8 (p-1)² * cS p q` with `cA q = 2624 q + 1313`, `cLam q = 18 q cA q`, `cS p q = 2 (1 + cLam q ^ (p-1))`. It is huge: about 2.34 × 10^16 for (p, q) = (3, 2), so the bound is meaningful only for very large n. Asymptotically it is 2^{Ω(n)} for fixed p, q.

### 2.7 A bounded-rank semantic calculus

This result has no direct published source and is the one we are least sure should be kept in the fidelity claim.

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

- Indexed all-size versions of the Tseitin theorems (`TseitinIndexed.lean`): for all m at least a floor, on the explicit family on 8m² vertices, with an explicit charge (1 at one vertex, 0 elsewhere) and a proof that the instance is unsatisfiable. Examples: `tseitin_dag_exp_idx`, `c1_main_idx`, `tseitin_idx_explicit_unsat`. Padding to every n is not formalized; consecutive sizes differ by a factor at most 2.
- Connected and explicit-charge variants (`TseitinExplicit.lean`).
- Embeddings between our systems and the standard published calculi (`Embed*.lean`), summarized in this table (sizes are line or node counts):

| Statement | Lean name | Size change |
|---|---|---|
| Part-Tzameret Res(lin F) into our `RLDag` | `stdLin_refutes_to_rldag` | s to 2s |
| `RLDag` into Part-Tzameret Res(lin F) | `rldag_refutes_to_stdLin` | n to n |
| Standard Res(xor) (BCD, arXiv 2402.04364, syntactic or semantic weakening) into `RL.DagRefutes` | `stdXor_refutes_to_dag` | s to s |
| `RL.DagRefutes` into standard Res(xor) with semantic weakening | `dag_to_stdXor_refutes` | s to 3s |
| `RLDag` into `Pang.Refutation` | `rldag_to_pang` | n to n+1 |
| `Pang.Refutation` into `RLDag` | `pang_to_rldag` | S to 2S |

Caveats on the table: the encoding of a positive literal x = 1 differs between systems (a separate theorem pair handles the usual encoding at a cost additive in clause widths), and Part and Tzameret measure total symbol size while we count lines, so a lower bound on lines yields one on symbols and not conversely.

## 3. What we ask the reviewer to check

We ask about statement fidelity only. You are not asked to read Lean proofs, to certify the project target, or to judge novelty. Concretely:

1. Proof systems. Does each Lean system (`RLD` and `RLDag`, `Pang.Refutation`, `RL.DagRefutes` and `PDag`, `RRefutation`) match the standard calculus it is named after, given the embedding table above? Is a line count an acceptable size measure where the papers count symbols?
2. Formula and family. Is the one-hot Tseitin encoding `tcnf` (blocks of q variables per edge, unique-value and local-flow clauses) the encoding the sources use, or a defensible variant? Is a cubic expander family with a nonzero-charge vertex the intended hard family?
3. Part-Tzameret Theorem 45, Case 4. The paper's argument has a step that may be a gap. Is our variant of it used correctly?
4. Quantifiers. Older theorems have the shape "for all N there is n at least N". Indexed all-size versions exist for one family. Do these shapes, including truncated natural-number subtraction and division in exponents, faithfully express "exponential size for all large n"?
5. Semantic weakening. Our dag-like Res(xor) system has semantic weakening. We have embeddings both ways with the standard system that also has it (factors 1 and 3), and from the syntactic standard system into ours, but the converse (semantic weakening to syntactic, polynomial overhead) is not formalized. Pang's Section 7.1 states it; the proof is not in Lean, and a scoping attempt found no uniform local rewriting. Is this a harmless convention, or does the missing converse change what the Braun and Pang statements mean?
6. Composite q. The Lean statements allow composite q with p not dividing q, because the degree lemma is proved over a primitive q-th root of unity. The sources state prime q. Does Pang's Theorem 7.2(b) extend this way?
7. The bounded-rank result. Is `c1_main` worth keeping as a stated result, or should it be dropped from the fidelity claim?
8. Vacuity and misleading statements. Is there anything a specialist would call vacuous or misleading? We already know of these: statements quantify over all charge vectors b and so include satisfiable instances (vacuously true there); connectivity of the graph is a property of the witness and does not appear in the displayed theorem; exponents need large n to be positive.

## 4. Trust base and reproduction

The Lean kernel checks every proof. The development uses exactly the three standard axioms `propext`, `Classical.choice`, `Quot.sound`. The script `scripts/check_axioms.sh` builds the project, rejects any `sorry` in a file not marked as Frontier, and runs `#print axioms` on every declaration in `scripts/accepted_declarations.txt`. Eleven Frontier-quarantined `sorry`s exist (at last recorded run, in `AC0pFrege`, `CuttingPlanes`, `MGG/SpectralFrontier`, `MGG/Factor2Inv4`, `Tseitin`, `CSExpansion`); none of them is in the accepted declarations list, and none is used by the results above.

```
git clone <repo> SATurday && cd SATurday && git checkout <pinned hash>
cd theory && lake build        # Lean toolchain leanprover/lean4:v4.30.0-rc1; Mathlib pinned by lake-manifest.json; do not run lake update
cd .. && bash scripts/check_axioms.sh
```

Caveats, stated exactly. A cold build (Mathlib from scratch) has not been run on our machine; all gate runs used a warm cache, and a cold build is expected to take hours on a slow disk (recipe in `docs/reports/reproduction.md`). Remote continuous integration has never run, because nothing had been pushed before 2026-10-27; the local gate passes. Repository access must be granted to the reviewer (or a tarball supplied).

Source status. Braun and Pang are unrefereed preprints from September 2026; Braun states substantial AI assistance. Part-Tzameret, Alekhnovich-Razborov, and Green are refereed. Details we could not verify: theorem numbers in Part-Tzameret, the published version of Khaniki, the constant in AR Theorem 4.4, Green's original text (we followed Beck-Li), and Itsykson-Sokolov's text (we used BCD, which states the semantic-weakening convention). An earlier outside referee report on the dossier raised ten objections; all were accepted and the fixes are in the dossier (`docs/reports/response-to-referee.md`). They included a wrong satisfiability criterion for disconnected graphs, the missing indexed family, Pang's priority over Braun, and the need for embeddings.

## 5. Open problems and what is not claimed

- No lower bound for AC0[p]-Frege is proved or claimed, at any depth, including depth 2. The R4 target is an intentional `sorry`. The results above are for weaker or different systems.
- Depth-2 AC0[p]-Frege and constant-depth AC0[p]-Frege remain open (rungs 2.3 and 2.4 of our plan). Pang names the obstruction for the Frege route in his Section 8: a quantitative tradeoff between approximation degree and rank shrinkage under iteration over depth, with the missing ingredient being polynomial calculus degree lower bounds near or above n/2 for polynomial-size, o(n)-width CNFs. Our bounded-rank theorem does not supply this, since its rank bound is logarithmic.
- Tree-like and dag-like results are separate: Section 2.3 is tree-like only, Sections 2.2, 2.4, 2.6 are dag-like, and we do not claim either transfers to the other. Tree-like and dag-like Res(xor) are incomparable in the literature.
- Semantic weakening has not been removed (question 5).
- Not formalized: translation of `Pang.Refutation` into the bounded-rank calculus; translation `pdag_to_affineDAG`; completeness (existence of refutations) for the Tseitin calculi; closure under restriction and padding to every size; a standalone analysis of the bounded-rank calculus.
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
