# Expert review of 2026-11-19 (referee report)

Source: pasted by the owner on 2026-11-19. Reformatted only (chat indent and escapes removed); the text is otherwise verbatim, including residual citation-widget lines. Response: response-to-expert-review-2026-11-19.md.

## Referee Report: Critical Evaluation of the SATurday Formalization Review

Major revisions recommended

**Overall assessment:** The proposal demonstrates a reasonably sophisticated understanding of proof complexity and, importantly, distinguishes formal verification of proofs from verification of their intended meaning. That distinction is essential.

However, I would not yet endorse the claim that the Lean statements faithfully formalize the cited mathematical results.

My concerns fall into three categories:

1. **Definite errors or misleading mathematical statements** that can be identified from the document itself.
2. **Substantive gaps in the fidelity argument**, particularly around proof-system definitions, theorem quantifiers, and extensions beyond the literature.
3. **Claims that cannot be independently established** without inspecting the actual Lean definitions, proof dependencies, and the cited fidelity dossier.

Some issues are straightforward corrections. Others could materially affect what has actually been established.

My assessment is based on the complete uploaded proposal and a comparison with the cited papers, especially Part–Tzameret, Khaniki, and Pang. I have not inspected or compiled the Lean repository.

## **I. Definite errors and substantive mathematical objections**

### **1. The claim that tree-like and dag-like Res(xor) are incomparable is wrong**

Severity: High · Section 5

The document states:

> Tree-like and dag-like Res(xor) are incomparable in the literature.

This is mathematically incorrect under the usual meaning of these proof systems.

Every tree-like proof is also a dag-like proof. A tree is a special case of a directed acyclic graph.

Consequently, for a fixed formula $F$, with identical inference rules and size measures,

$$S_{\mathrm{dag}}(F)\leq S_{\mathrm{tree}}(F).$$

It follows that:

- A lower bound for dag-like Res(xor) automatically applies to tree-like Res(xor).
- A lower bound for tree-like Res(xor) does not automatically apply to dag-like Res(xor).

The document also says that the two kinds of lower bounds do not transfer to each other. That is misleading because transfer does hold in one direction.

**Required correction:** Replace the incomparability statement with the precise simulation relationship. If the author intends to compare different variants of Res(xor), they must specify those variants and explain why the ordinary containment does not apply.

The distinction is foundational, not terminological.

expert-review-proposal.md



### **2. The quantifiers do not establish the advertised lower bounds for every sufficiently large input size**

Severity: High · Sections 2.3–2.6 and 3.4

Several theorem statements have the form

$$\forall N\ \exists n\geq N\ \exists G_n\  \forall \pi\quad S(\pi)\geq 2^{cn}.$$

This establishes **arbitrarily large hard instances**, or an infinite sequence of hard sizes.

It does not establish

$$\exists N_0\ \forall n\geq N_0\ \exists G_n\  \forall\pi\quad S(\pi)\geq 2^{cn}.$$

Those are different mathematical claims.

The document partially acknowledges this, stating that indexed versions exist on $n=8m^2$ vertices, but padding to every size is not formalized.

Having consecutive indexed sizes differ by a factor of at most two does not establish the missing theorem. That would require an appropriate reduction or padding construction that preserves the lower bound.

One could potentially obtain the desired family by adding unconstrained variables or other padding, but the required relationship between the original and padded proof systems would have to be established.

**Required correction:** Distinguish explicitly between infinite-subsequence bounds, indexed-family bounds, and eventual all-size bounds.

Do not describe the first as the third.

### **3. The composite-modulus result is not merely a faithful restatement of Pang**

Severity: High · Sections 2.3 and 2.6

The proposal says:

> The Lean statements allow composite q with p not dividing q, because the degree lemma is proved over a primitive q-th root of unity.

Pang's Theorem 7.2(b), however, explicitly assumes that $q$ is prime and $q\neq p$. His application is to Tseitin formulas modulo that prime.

[image](https://www.google.com/s2/favicons?domain=https://arxiv.org&sz=32)

arXiv



The Lean statement instead permits

$$q\geq 2,\qquad p\nmid q,$$

including composite $q$.

This extension might be true. Indeed, the underlying algebra suggests a potentially valid generalization. But it is not justified simply by observing that primitive $q$-th roots of unity exist in a suitable extension field.

One must also establish that:

- The polynomial-calculus degree lower bound works for the relevant $\mathbb Z/q\mathbb Z$ charge constraints.
- The expansion and immunity arguments remain valid.
- The extension-field argument preserves the required degree lower bound over $\mathbb F_p$.
- Every relevant source-dependent lemma survives the change of modulus.

A faithful formalization of an existing theorem and a formal proof of a generalization are different intellectual contributions.

**Required correction:** Present the prime-$q$ theorem as the fidelity target, and the composite-$q$ extension as a separate result requiring independent mathematical review.

### **4. The dag-like proof representation needs particularly careful inspection**

Severity: Potentially critical · Sections 2.4 and 2.8

The dag-like theorem is formulated in terms of

```
RLF.RLDag initialClauses 𝓛
```

where `𝓛` is a finite set of clauses and its cardinality is the proof size.

This raises an important question.

**How does the definition establish that the set of clauses constitutes an acyclic derivation?**

A legitimate dag-like proof must have a topological ordering in which each derived line follows its premises.

For example, suppose a proposed collection contains clauses $A,B,C$, with the following justifications:

$$A\leftarrow B,\qquad B\leftarrow C,\qquad C\leftarrow A.$$

Merely requiring every noninitial clause to be justified by other members of the set would admit this circular collection. It would not constitute a proof.

A correct implementation might establish derivability inductively, preserve an underlying derivation sequence, or require a well-founded dependency relation.

The displayed theorem does not tell us which of these is done.

This is not evidence that the Lean implementation actually contains a circularity bug. It is an important unverified property of the definition.

**Required check:** Inspect the definition of `RLDag` and establish explicitly that every accepted refutation corresponds to a genuine, acyclic proof derivation.

The same scrutiny should be applied to the stated embeddings between `RLDag`, `Pang.Refutation`, and the standard calculi.

An incorrect representation of derivations would be far more serious than a discrepancy in constants.

### **5. The semantic weakening concern is partly misplaced**

Severity: Medium · Sections 2.2 and 3.5

The document worries that it has not established a polynomial-overhead simulation from semantic weakening to syntactic weakening.

That is a legitimate question about equivalence between proof systems, but its importance to the stated lower bounds needs to be distinguished.

Suppose $P$ is the standard syntactic system and $Q$ is a stronger semantic system.

If every $P$-proof of size $s$ can be transformed into a $Q$-proof of size at most $Cs$, then

$$S_Q(F)\geq L \quad\Longrightarrow\quad S_P(F)\geq L/C.$$

There is no need to simulate $Q$ back into $P$ to establish this lower bound for $P$.

Thus the missing converse does **not by itself invalidate** the claimed lower bound for standard syntactic Res(xor).

What matters is whether the forward embedding is correct, including the initial clauses, inference rules, and size overhead.

The dossier should distinguish between proving a lower bound for the standard system and proving polynomial equivalence of the two systems.

### **6. Regularity is not an expansion hypothesis**

Severity: Medium–High · Sections 2.1–2.6

The principal Tseitin theorems assert existence of graphs satisfying

```
N ≤ n ∧ IsRegular G 3
```

However, the surrounding mathematics repeatedly describes the instances as Tseitin formulas on cubic expanders.

A cubic graph need not be an expander. A disjoint union of small cubic graphs is an immediate example of how regularity alone is insufficient.

The distinction matters because the polynomial-calculus degree lower bounds are driven by expansion properties.

There is no contradiction here if the particular graph constructed in the proof is indeed an expander. The existence theorem could be correct even though its conclusion omits useful properties of the witness.

But that means the displayed formal statement does not itself establish the advertised graph-family properties.

A more informative theorem would include a suitable expansion predicate, connectivity, and the explicit graph construction in the witness conditions.

This would strengthen the statement-fidelity case and make it much harder to certify an unintended family accidentally.

### **7. Part–Tzameret Theorem 45 contains an identifiable typo, but the alleged deeper gap remains unsubstantiated**

Severity: Medium · Section 2.3 and question 3

I checked Case 4 of Theorem 45 in the arXiv manuscript. The passage contains an apparent copy-and-paste error.

The second premise is written as

$$C'\vee E\vee(g=0),$$

but the subsequent arithmetization incorrectly refers to $f$ instead of $g$.

It should use

$$a(C')a(E)g,$$

not $a(C')a(E)f$.

This is a genuine textual error in the paper.

[image](https://www.google.com/s2/favicons?domain=https://arxiv.org&sz=32)

arXiv



However, it is not sufficient evidence of a substantive mathematical gap. The intended derivation from the corrected premises appears coherent: multiply by the missing clause factors and take the appropriate linear combination.

The proposal says a variant of this case is used in Lean, but does not give its exact lemma or explain which part of the argument was modified.

**Required correction:** Identify precisely whether the concern is this typographical mistake or a separate mathematical defect. If the latter, provide the explicit failed inference and the Lean theorem that replaces it.

A reviewer should not have to reconstruct the alleged gap from a vague reference to Case 4.

### **8. The formula encoding is faithful to Pang, but not directly to all the cited predecessors**

Severity: Medium · Sections 2.1, 2.3, and 2.5

The one-hot formula described in the proposal closely matches Pang's definition: each edge has $q$ Boolean variables, exactly one edge value is selected, and local clauses enforce the flow equation.

That is a positive finding.

[image](https://www.google.com/s2/favicons?domain=https://arxiv.org&sz=32)

arXiv



Part–Tzameret, however, uses a different encoding with one Boolean variable per edge.

[image](https://www.google.com/s2/favicons?domain=https://arxiv.org&sz=32)

arXiv



These formulas are not identical. Their relationship requires an encoding reduction or an independent lower-bound proof.

For a fixed $q$, the discrepancy need not be problematic. But a faithful formalization should distinguish the original formula from the modified formula and state the relevant transfer explicitly.

There is also a subtlety in the supplied `tcnf` definition:

```
univ ×ˢ univ
```

ranges over full edge labellings in `G → ZMod q`, rather than just local assignments at a vertex.

This can be perfectly legitimate if `vC` only depends on the three incident edges and duplicate resulting clauses are eliminated. But that is not established by the snippet.

I would want a theorem showing that `tcnf` is semantically equivalent to the advertised local-constraint encoding, ideally with the exact clause width and formula-size bounds.

### **9. The use of line count versus symbol count is directionally valid, but not an equivalence**

Severity: Medium · Sections 2.3 and 2.8

Part–Tzameret explicitly defines proof size using the representation size of all the clauses, including variable occurrences and coefficients.

[image](https://www.google.com/s2/favicons?domain=https://arxiv.org&sz=32)

arXiv



The Lean statements instead count leaves, distinct lines, or proof nodes.

A lower bound of $L$ on the number of lines generally yields a lower bound of order $L$ on the total encoded size.

The converse need not hold.

A small number of extremely large clauses can have substantial total symbol size. Therefore, the two measures should not be described as equivalent without a translation argument.

This does not invalidate a line-count lower bound. It can actually be a stronger result. But it means that the formal statement is not a literal reproduction of the source's quantitative claim.

For the tree-like statements, the document should also explain the relationship between leaf count and node count, taking into account unary and binary inference rules.

### **10. The asymptotic claims require a clearer parameter regime**

Severity: Medium · Sections 2.3–2.7

The document writes several bounds in the form

$$2^{\Omega(n)}$$

or

$$\Omega(n^2/\log n).$$

These are reasonable descriptions when $p$ and $q$ are fixed constants and $n$ grows.

They are not uniform bounds over arbitrary varying moduli.

For example, in the Pang formalization, the denominator $c_C(p,q)$ depends heavily on both $p$ and $q$. Allowing these parameters to grow with $n$ could make the displayed lower bound trivial.

The statement should consistently say

$$2^{\Omega_{p,q}(n)}$$

for fixed $p,q$, and clarify that $n$ denotes graph vertices, not the number of Boolean variables or the encoded input length.

Similarly, the numerous natural-number divisions and truncated subtractions deserve a small explicit lemma showing that the exponent grows linearly after a specified threshold.

The document recognizes these issues, but an expert-review request should demonstrate the asymptotic implication rather than ask the reader to infer it.

## **II. Problems with the evidence and presentation**

### **11. The bounded-rank calculus should not be included in a statement-fidelity certification**

Severity: Medium–High · Section 2.7

The bounded-rank result is interesting, but it is an original, bespoke semantic calculus rather than a formalization of an identified published proof system.

That distinction is fundamental.

A reviewer assessing whether Lean definitions match published definitions cannot certify the fidelity of a calculus that has no published counterpart.

Moreover, its semantic inference rules are validated by quantification over Boolean assignments, which the document correctly recognizes as placing it outside the usual Cook–Reckhow framework.

Such a calculus may still have mathematically meaningful lower bounds. But determining that requires a different review focused on the calculus's semantics and the proof of its lower bound.

The claim that it follows from Pang's method should also be supported by a precise transfer theorem or independent explanation, not merely by methodological resemblance.

**Recommendation:** Remove `c1_main` from the statement-fidelity certification and commission a separate mathematical review.

### **12. The vacuous cases are more than a presentational inconvenience**

Severity: Medium–High · Sections 2.5, 2.6, and 3.8

Several theorems quantify over every charge vector, including vectors that yield satisfiable formulas.

For these vectors the assertion

$$\forall R\in\operatorname{Refutations}(F),\quad S(R)\geq L$$

is true simply because there are no sound refutations of $F$.

The document acknowledges this, and the separately described explicit-charge theorems appear intended to resolve the problem.

But the reviewer should be shown at least one theorem that combines the relevant properties:

$$\operatorname{Unsat}(F_n) \quad\land\quad \forall R,\ S(R)\geq L(n).$$

Otherwise, someone examining the main theorem statements cannot immediately distinguish substantive hardness claims from empty implications.

I am not suggesting the results are actually vacuous. The explicit-charge variants, if correctly implemented, would provide the necessary nonvacuity witnesses.

They should simply be central to the evidence, not relegated to supporting statements.

### **13. The reproduction claim is not yet independently verifiable**

Severity: High for certification · Section 4

The document correctly explains the difference between a kernel-checked Lean proof and a faithful mathematical formalization.

However, its reproducibility instructions remain incomplete.

The repository is not provided, and the exact commit hash is still a placeholder. There is no independent build log, toolchain checksum, or reviewer-accessible verification artifact included with the request.

The stated use of `#print axioms` is sensible, but a reviewer must verify that the accepted-declarations list covers every theorem claimed in Section 2.

I would require an exact commit, a complete declaration-to-source mapping, and reproducible axiom-check output before attesting to the claims.

A warm-cache build is not inherently suspicious; the lack of an independently reproduced build is a limitation on the available evidence, not evidence of incorrect mathematics.

### **14. The bibliographic audit is incomplete, and one omission is easily corrected**

Severity: Low–Medium · Sections 2.4 and 4

The proposal states that the published version of Khaniki has not been checked.

The published article is readily identifiable:

**Erfan Khaniki,** *On Proof Complexity of Resolution over Polynomial Calculus*, ACM Transactions on Computational Logic, volume 23, issue 3, Article 16, July 2022. DOI: [10.1145/3506702](https://doi.org/10.1145/3506702?utm_source=chatgpt.com).

[image](https://www.google.com/s2/favicons?domain=https://paperity.org&sz=32)

Paperity



The publication metadata should be corrected, and the published version should be checked for any differences in the relevant statement or proof.

Likewise, the original Green result and the exact Alekhnovich–Razborov constants should be verified before describing their statements as faithful formalizations.

Finally, Pang's application is contained in an unrefereed arXiv preprint, not a refereed publication. The phrase "published application" should be replaced by "application already established in Pang's preprint."

## **III. What appears mathematically sound**

There are several positive features I would preserve.

**The Tseitin encoding described is consistent with Pang's construction.** The one-hot variables, unique-value clauses, and local conservation constraints agree at the mathematical level, although the Lean implementations still need inspection.

**The broad lower-bound landscape is presented accurately.** Pang does give exponential lower bounds for dag-like resolution over constant-degree polynomials, including the relevant Tseitin application. Braun's bit-pigeonhole result is also reported with the correct quantitative form.

[image](https://www.google.com/s2/favicons?domain=https://arxiv.org&sz=32)

arXiv+1



**The project does not claim a solution of the AC⁰[p]-Frege problem.** That restraint is appropriate. Pang's conditional Frege theorem requires substantially stronger polynomial-calculus degree information than the document has established.

[image](https://www.google.com/s2/favicons?domain=https://arxiv.org&sz=32)

arXiv



**The distinction between formal correctness and mathematical fidelity is exactly the right one.** A formalized false interpretation of a paper can be proved perfectly correctly in Lean.

Those strengths make this a credible starting point for an expert audit rather than evidence that the project is fundamentally unsound.

## **IV. What I would require before approval**

| Priority | Required action                                                                             |
| -------- | ------------------------------------------------------------------------------------------- |
| Critical | Verify that every dag-like calculus enforces acyclic, sound derivations.                    |
| Critical | Audit the embeddings and the exact proof-system rules against their published counterparts. |
| High     | Separate prime-modulus formalizations from composite-modulus generalizations.               |
| High     | Provide explicit, unsatisfiable, size-indexed instances together with their lower bounds.   |
| High     | Correct the tree-like/dag-like comparison and the all-size asymptotic claims.               |
| High     | Supply a pinned repository and reproduce the kernel/axiom audit independently.              |
| Medium   | Establish the precise relation between the one-hot and Boolean-edge Tseitin encodings.      |
| Medium   | Review the bounded-rank calculus separately from the fidelity exercise.                     |

## **Final referee recommendation**

**Recommendation: Major revision before certification of statement fidelity.**

I do not see enough evidence in the proposal to conclude that its central Lean theorems are incorrect. Several of the advertised results are consistent with the mathematics in the cited papers.

Nevertheless, the proposal makes a few unequivocally incorrect statements, conflates formalizations with mathematical generalizations, and has not supplied enough information to establish that its proof-system definitions represent the intended calculi.

The highest-risk issue is the representation of dag-like derivations. The highest-confidence errors are the false incomparability claim and the quantifier mismatch between infinite-subsequence and all-sufficiently-large-size lower bounds.

I would also emphasize that **reviewing the prose and reviewing the actual Lean formalization are materially different activities**. The former can identify some mathematical errors and unsupported claims. It cannot conclusively establish correctness of the definitions.

If I were evaluating this as an academic research submission, I would require the exact Lean source, the statement-fidelity dossier, and the proof-system embedding lemmas for a second-stage technical audit.

The goal should not be a general letter saying that the statements look faithful. It should be a theorem-by-theorem assessment identifying the precise formal definition, the published mathematical counterpart, and the established equivalence or one-way simulation.

That would provide significantly more meaningful scientific assurance than a broad endorsement of the current document.
