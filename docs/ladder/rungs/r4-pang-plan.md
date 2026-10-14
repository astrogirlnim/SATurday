# R4 scouting: formalizing Pang's degree-size theorem for dag-like Res(lin F_p)

Status: scouting only, nothing built, no Lean written. Date 2026-10-13. Branch r4/scout-pang.

Source: S. Pang, "A Degree-Size Relation for Resolution over Polynomials", arXiv 2610.00837 v1
(30 Sep 2026). Read in full from the arXiv TeX source (deg--size.tex, 993 lines; all sections,
all proofs, applications and conclusions). Line numbers below refer to that file.
Everything marked UNVERIFIED was not machine checked; "checked by hand" means I re-derived the step
on paper while reading, not that it is formalized.

## 1. Statement (r = 1 is what we need)

p prime, F a CNF of width w on n Boolean variables, Q(F) = Bool + clause falsity polynomials
(`clausePoly`), C_D = {f : Q(F) |-_D f} (PC degree D, Boolean axioms included). Theorem 1.1 (l.103):
if 1 not in C_D, D >= max{32 (p-1)^2 r, 8 w}, then every S-node dag-like Res(PC_r/F_p) refutation
has ln S >= D/(32 p^2 r) * (D/(16 n))^((p-1) r). r = 1 is Res(lin F_p). The rules are: syntactic
weakening, contraction, deletion of false constants, linear combination
(A v f=0, B v g=0 |- A v B v alpha f + beta g = 0), multiplication by a polynomial (only
scalars when r = 1), axioms (0=0) and Boolean axioms. Size = number of DAG nodes.
The proof does not introduce extension variables, and the system has syntactic (not semantic)
weakening; the footnote at l.837 says semantic weakening is simulable with polynomial overhead
"cf. IS14" (UNVERIFIED, and irrelevant if we define the syntactic system).

## 2. Proof layers (what the paper actually does)

Notation: d = (p-1) r, g_h = ML(1 - h^(p-1)) the 0/1 indicator of h = 0 (deg <= d), line
L = OR_i (h_i = 0), P_L = prod_{j<=t} (1 - q_j^(p-1)) with q_j in F_p-span{g_{L,i}}, Delta = t(p-1)d.

- L0 Facts (l.221-242). Multiplication absorption: f in C_D, deg f + deg g <= D => fg in C_D.
  Boolean reduction: Bool |-_{deg f} f - ML(f) (so a polynomial of degree m vanishing on the cube is
  in C_D once D >= m). Frobenius: Bool |-_{pd} g^p - g for deg g <= d. Checked by hand.
- L1 Base change (Lemma 2.3, l.244): for E/F_p a field extension, E (x) (C_D cap V_k) = C_D^E cap
  E[x]_{<=k}, and absorption holds over E. Checked by hand (intersection commutes with flat base change).
- L2 Rank specialization (Lemma 3.1, l.268, "pencil"): M(lambda) = sum lambda_i M_i, lambda
  algebraically independent; E_{a in F_p^s} rank M(a) >= (1 - 1/p) rank_{F_p(lambda)} M(lambda).
  Proof: multivariate multiplicity Schwartz-Zippel (DKSS Lemma 8, sum_a mult(H,a) <= deg(H) p^(s-1),
  re-proved in the paper by induction on s) plus rank(M(a)) >= R - mult(det minor, a) via row
  operations. Checked by hand, including the induction; I believe it correct. The cited DKSS
  statement itself is UNVERIFIED against the original (the in-paper proof is self-contained).
- L3 Frobenius kernel descent (Lemmas 3.2-3.3 and Cor 3.4, l.303-409): if ker_E M(lambda) is inside
  ker_E M(lambda^p) then ker_E M(lambda) is defined over F_p, hence rank_E M(lambda) = rank_{F_p} of the
  stacked map, and some F_p-point c has rank sum c_i M_i >= (1-1/p) rank (stacked). The condition holds
  for f -> [f g_i h_j] on V_k when b + k + p a <= D, using q^p = sum lambda_i^p g_i^p and
  g_i^p - g_i in C_D. Proof of the descent: reduced row echelon basis T, T^[p] has same pivots, uniqueness
  of RREF gives T^[p] = T. Checked by hand; Remark 3.5 (l.368) shows the Frobenius hypothesis is needed.
- L4 Normalized rank is monotone (Lemma 4.1 "hilbert", l.443): c_P(k)/N_n(k) is nonincreasing for
  0 <= k <= K, where c_P(k) is the rank of f -> ([P g_i f])_i on V_k and N_n(k) = sum_{j<=k} C(n,j).
  Proof: leading monomials in a graded order of the kernel Z_P(K); the complement is a down-closed
  family of multilinear monomials; double counting (j+1) b_{j+1} <= (n-j) b_j. Checked by hand.
  (This is one of the two "dimension bookkeeping" lemmas flagged by the earlier audits.)
- L5 Approximation gain (Lemma 4.2 "onestep", l.457): for K >= d, a + K + p d <= D there is
  q in span_{F_p}{g_i} with c_{P(1-q^(p-1))}(K) <= c_P(K) - (1-1/p) c_P(K-d). Uses L3 on the stacked map
  (whose kernel is Z_P(K-d); the inclusion "<=" multiplies by g_i^(p-2) and uses g_i^p - g_i), then
  Z_{P'}(K) contains q V_{K-d} + Z_P(K). Checked by hand. (The second flagged lemma.)
- L6 Common multiplier (Theorem 4.3, l.504): with eta = (1-1/p) N_n(K-d)/N_n(K) and h_K =
  dim V_K/C_{<=K}, rank for every line is <= h_K (1-eta)^t after t rounds (L4 + L5); if S (1-eta)^t < 1 a
  multilinear f in V_K, f notin C_D, exists with f g_{nu,i} P_nu in C_D for all lines nu and all i.
  Dimension count over the S lines. Checked by hand.
- L7 Simulation in PC (Proposition 5.1, l.579): with f from L6, f P_L in C_D for every line L, in
  topological order, provided K + max{2 Delta + 2d, Delta + w} <= D. Cases: initial clause (telescoping
  1 = Q_J + sum prod_{j<i}(1-l_j) l_i), Boolean axiom, (0=0), weakening/contraction/false-constant
  (via 1 - P_L = sum U_{L,i} g_{L,i}, deg U <= Delta - d), "useful claim" (1-g_h) f P_L in C_D (l.623),
  linear combination (4-term telescoping in g_{h1}, g_{h2}, g_{h3}), multiplication. Empty line has P = 1,
  so f in C_D, contradiction. Checked by hand, all displayed degrees recomputed.
- L8 Parameters (Section 6, l.674): K = floor(D/4), t = floor(D/(8(p-1)d)); N_n(K) <= 2 C(n,K) for
  K <= n/3; N(K-d)/N(K) >= (1/2)(D/16n)^d; eta t >= D/(32 p d)(D/16n)^d >= D/(32 p^2 r)(...)^d.
  Checked by hand (the paper's bound has slack: 32 p d = 32 p (p-1) r <= 32 p^2 r). It uses D <= n,
  proved by "degree n always refutes" (l.677-680); for us D <= n is an explicit numeric hypothesis
  and that lemma is NOT needed.

Net: no error found on a second full read. The mathematical content is elementary linear algebra
over F_p, F_p(lambda) and a multiplicity bound; no deep external theorem is imported.

## 3. Mapping onto the repo

Reusable as is:
- `clausePoly`, `cnfAx`, `litPoly` (PolyCalc.lean): `litPoly l = if l.pos then 1 - X v else X v`,
  `clausePoly C = prod litPoly`. Matches Pang's Q_{x_i} = 1 - x_i, Q_{not x_i} = x_i, Q_J = prod. Read, not
  built: the match is by inspection of the definitions (UNVERIFIED by Lean).
- `PCD` (PolyCalc.lean): axioms charged their own degree, `bool` rule needs 2 <= d, multiplication
  by a variable needs degree <= d. Same as Pang's C_D (l.81). `pcd_mono`, `pcd₀_mul` (absorption on the
  PCD0 side) exist; `pcd₀_sum`, `pcd₀_smul`, `pcd₀_add` give the linear structure.
- `tseitin_bool_degree_Fp` (TseitinBool.lean): certified, one-hot Tseitin mod q, cubic expanders,
  p prime, p not dividing q: `tcnf G q b` has no PCD refutation of degree D0 = ((n-2)/1312 - q(q+3))/(q-1)
  over ZMod p, where n is the number of VERTICES.
- `tcnf_clause_props` (width <= q+3 as used in `reslin_tseitin_size`; true width max(q,3)).
- `RLF.LEq`, `RLF.cmb`, `RLF.boolCl`, `RLF.boolAx`, `RLF.rld_sound` (ResLinF.lean): the line
  language and soundness of Res(lin F). The dag rule set is a copy of `RLF.RLD` with sharing instead of
  trees; `ResLinSize` style counting (distinct lines) must be defined anew.
- BraunPC.lean (Derives, degreeSpace, pcSpace, nsSpace, `Derives.mul_polynomial`, `Derives.substitute`,
  `substitution_degree`): general field K, arbitrary variable type. Useful for C_D as a Submodule, for
  absorption, and for restricting variables (see below). It is NOT the same inductive as `PCD`, so a
  small bridge lemma (PCD d <-> Derives (cnfAx + booleanBase) d for d >= 2) is needed.

Does NOT carry over:
- ResLin.lean, ResLinDag.lean, ResLinGame.lean, ResLinBPHP.lean: F_2 only (ZMod 2, parity), and
  ResLinDag uses SEMANTIC weakening (`Imp`), which is exactly the variant footnoted at l.837. Pang's
  theorem is for syntactic weakening, so do not reuse `RL.DagRefutes`; define a fresh dag type over F_p.
- Braun's F_2 machinery. 34 of the Braun*.lean files mention ZMod 2 (BraunDag, BraunCommonKernel,
  BraunRestriction, BraunENS*, BraunCube*, BraunMatching*, BraunAug*, BraunRow*, BraunClause*...). Pang's
  proof uses only the IDEA of a common multiplier from Braun; his own text (l.180) says the dimension
  analysis replaces the "common-kernel argument with explicit affine restrictions". So: Braun's affine
  restriction kernel, ENS low-rank, chessboard and matching-moment layers are not on Pang's path, and
  there is no F_p extension of them to do. The only Braun pieces worth touching are BraunPC (already
  field-generic) and BraunPCBoolean's `sqPart` multilinearization (ZMod 2 only: 38 occurrences of
  `ZMod 2`; the proofs `sqPart_eval`, `sqPart_eq_zero_of_eval_zero` should generalize to ZMod p but this
  is a rewrite, not a re-use; UNVERIFIED how much of it is 2-specific beyond the type).
- Tree-like stack (`RLF.RLD`, `rld_size_width`, `reslin_tseitin_size`): sound and finished, gives the
  weaker tree-like bound only; no part of its proof (size-width induction) is used by Pang.

New work required (nothing exists):
- A dag-like Res(lin F_p) type with syntactic rules, variable set bookkeeping (see risk 3 below).
- Multilinearization ML over F_p with degree control and "vanishes on the cube => in C_D".
- All of L1-L8 above.

## 4. Does Braun's F_2 machinery extend to F_p?

Not needed and not the right question: Pang's proof is a different architecture. The one place
characteristic enters is L2/L3 (Frobenius, factor 1 - 1/p), which is built from scratch. For p = 2
Pang's proof specializes (he states the Res(xor) corollary at l.133), but it still does not reuse
Braun's kernel lemmas. The F_2 Braun modules stay useful only for the Braun bit-PHP target, not here.

## 5. Size estimate (Lean lines, honest ranges; r = 1, CNF inputs only)

| Layer | Content | Lines |
|---|---|---|
| A | dag type over F_p (syntactic), soundness, size = distinct lines, restrict to Var(F) | 300-500 |
| B | PC algebra: C_D as submodule, absorption, ML, cube-vanishing, Frobenius, PCD bridge | 600-900 |
| C | base change, RREF/Frobenius descent, generic descent over F_p(lambda) | 1000-1700 |
| D | multiplicity SZ (DKSS), determinant multiplicity vs rank, pencil lemma | 600-1100 |
| E | normalized-rank monotonicity (L4) | 400-800 |
| F | onestep + common multiplier (L5, L6) | 500-800 |
| G | simulation (L7, r = 1: weakening, combination, axioms) | 500-800 |
| H | parameter arithmetic (binomials, floors, ln/exp) | 300-500 |
| I | Tseitin assembly (width, Var(F) vs variable count, degree input) | 300-500 |
| Total | | 4500-7600 (central guess 6000) |

For comparison the earlier scouting put the Alekhnovich-Razborov port at 4000-7000 with an open
external obstruction (large-degree expanders, not in repo), and Khaniki's weaker route at 1300-2000.
Pang is the same order of cost as the AR port but has no missing external input; all hypotheses
needed are already certified in the repo.

## 6. Feasibility call

Feasible, expensive: a many-session project, roughly the cost of a second Braun-scale port, with
elementary mathematics and fully certified input (`tseitin_bool_degree_Fp`). It is higher cost than
Khaniki (about 3-4x) but gives exp(Omega(n)) instead of n^(2-o(1)), and the dag type and degree input
are shared with Khaniki either way. Recommended risk burn-down order (each gate is a standalone
statement, testable before any proof-complexity context): D (pencil lemma on bare matrices), C
(Frobenius descent on bare linear maps), E (monotone normalized rank on bare subspaces of multilinear
polynomials), then A, B, F, G, H, I.

## 7. Riskiest single step

Layer C/D, the combination "Frobenius kernel descent over E = F_p(lambda_1..lambda_s) + rank
specialization" (Lemmas 3.1-3.3, Cor 3.4), consumed by Lemma 4.2. It needs a transcendental
extension, base change of the subspace C_D (only valid because absorption is stated degree-wise),
RREF uniqueness under the Frobenius entry map, and a multivariate multiplicity bound with an
unusual determinant-vs-rank estimate, none of which has a ready Mathlib counterpart. A weaker
fallback (a deterministic c with only rank >= 1) does not suffice: a quick counting argument gives
only that, and the linear fraction (1 - 1/p) is exactly what yields eta. The earlier audits'
two flagged bookkeeping lemmas (L4 and L5) are lower risk: both re-check by hand with the degree
conditions a + K + d <= D and a + K + p d <= D, and L4 is a purely combinatorial statement.

Secondary risks (not the single riskiest):
1. L4 needs leading monomials of a subspace in a graded order; can be restated for down-closed
   families through an abstract linear-algebra lemma to avoid Groebner machinery (UNVERIFIED that
   this restatement is clean).
2. Weakening footnote (l.837): irrelevant to a syntactic system; but if the target were stated for
   `RL.DagRefutes` (semantic weakening), an extra simulation lemma would be needed, with cost UNVERIFIED.
3. Variable-set bookkeeping: our PCD and lines live over `MvPolynomial N F` with sparse variables
   (`xv e j = Nat.pair ..`), while Pang's n is the number of variables of F and the lines use only those.
   Need: restriction of a refutation to Var(F) by substituting outside variables with 0 (needs the
   axiom (0=0), which Pang has), and that PCD non-refutability over N-indexed variables transfers to
   the finite variable set. `BraunPC.Derives.substitute` is the likely tool. Moderate, not exotic.
4. The paper is two weeks old and AI-assisted (its own AI Disclosure, l.54-61). Second full read
   found no error, but no one has machine checked it; formalization is itself the check.

## 8. Final theorem for Tseitin mod q (what we would obtain)

Using `tseitin_bool_degree_Fp` as input (one-hot encoding, cubic MGG expanders, p prime, p not
dividing q, q >= 2), with n the number of vertices, n_v = (number of Boolean variables of `tcnf G q b`)
= q * |E| = 3 q n / 2, width w <= max(q,3) (certified bound q+3 used in repo), and
D0 = ((n-2)/1312 - q(q+3))/(q-1):

For every N there is a cubic graph on n >= N vertices such that for every charge b, every dag-like
Res(lin F_p) refutation of `tcnf G q b` with S lines satisfies
  ln S >= (D / (32 p^2)) * (D / (16 n_v))^(p-1)    for any D <= D0 with D >= max{32 (p-1)^2, 8 w}.
Taking D = D0 and n large this is S >= exp(c(p,q) n) with, roughly (UNVERIFIED arithmetic, ignoring
floors), D0 ~ n/(1312 (q-1)), D0/(16 n_v) ~ 1/(31488 q (q-1)), hence
  c(p,q) ~ 1 / (32 p^2 * 1312 (q-1)) * (1/(31488 q (q-1)))^(p-1), a tiny but positive constant
(for q = 3, p = 2 about 1.6e-11 per vertex; the bound is only meaningful for astronomically large n).

What the hypotheses require:
- Constant width: w = max(q,3) (<= q+3) is a constant, so D >= 8w is just n >= n0(q); satisfied by
  choosing N large. If q grew with n the bound would degrade; we fix q.
- Formula size n: this is n_v = Theta(n) (3qn/2), not the vertex count. The factor (D/(16 n_v))^(p-1)
  is a constant exactly because D0 = Theta(n_v); if D0 were o(n_v) the bound would be sub-exponential.
  Also needs D <= n_v (here D0 ~ n/(1312(q-1)) << n_v, true), used only for K <= n_v/3.
- D >= 32 (p-1)^2 (r = 1): again n >= n0(p,q).
- Same field: the PC lower bound must be over ZMod p of the SAME p as in Res(lin F_p); p not dividing
  q is already the hypothesis of the certified bound (and necessary: Res(lin F_q) refutes it in
  poly size, Pang l.846, Corollary on different moduli).
- The encoding must be exactly Bool + `clausePoly` of the CNF (no extra axioms): matches `cnfAx`.
- Everything is for the one-hot formula `tcnf`, not the paper's Boolean-edge mod-p Tseitin (Pang's
  Theorem at l.784, item (b), uses the A-R degree bound for his encoding; the owner's earlier decision to port A-R
  for the paper-exact formula is NOT needed for the dag-like bound in this form, since we apply the
  degree-size relation to `tcnf` directly, but the statement is then about `tcnf`).

Not covered: r >= 2, polynomial-clause axioms (Remark at l.118), Res(k), proof search, the upper bound for
different moduli, any non-Tseitin family.

## 9. Overlap with Khaniki and Phase 2.2

Pang's theorem implies Khaniki's n^(2-o(1)) dag bound for these formulas (stronger conclusion, same
hypothesis). Shared work with Khaniki: dag type K1 and the certified degree input. Do K1 once, in the
syntactic form of Layer A. This document does not assign work; it only records dependencies.

## 10. Prover status (2026-10-14, branch r4/prover-pang)

Paper source re-fetched (arXiv e-print 2610.00837, deg--size.tex, 992 lines) and Section 3 re-read
against Section 2 above: no mismatch with the layer list. Refinements actually used:

- Layer D and C were formalized in the abstract matrix form, with `F_p = ZMod p`, and are DONE
  (no sorry, axioms propext/Classical.choice/Quot.sound only, checked by `#print axioms`):
  - `Theory/ProofComplexity/PangMult.lean` (244 lines): Taylor shift, `mult a f`, and
    `Pang.sum_mult_le : (sum_a mult a H) * q <= totalDegree H * q^n` for nonzero H over a finite field
    (DKSS multiplicity bound, induction through `finSuccEquiv`, univariate step by `taylor`/`rootMultiplicity`).
  - `PangPencil.lean` (262 lines): `OrdGe`, `sq_deficit` (det(A + L) vanishes to order >= R - rank A, via
    Mathlib's transvection/diagonal Gauss decomposition), `deficit_le_mult`, and
    `Pang.pencil_sum : R * q^(s+1) <= q * sum_a rank(sum a_i M_i) + R * q^s` for any nonzero R x R minor of the
    generic pencil (this is Lemma 3.1 in minor form).
  - `PangDescent.lean` (about 380 lines): `exists_minor` (rank R gives a nonzero R x R minor),
    `frob_descent` (Frobenius-stable subspace of E^n contains dim W F_p-independent F_p-rational vectors; pivot
    argument, replaces the RREF-uniqueness proof), `pencil_descent_rank`
    (kernel inclusion ker M(lambda) in ker M(lambda^p) gives rank_{F_p}(stack M_i) <= rank_E M(lambda)), and
    `Pang.pang_rank_retention` (E = FractionRing (MvPolynomial (Fin s) (ZMod p))): there is c in F_p^s with
    rank_{F_p}(stack) * (p-1) <= p * rank(sum c_i M_i). This is Lemma 3.2 plus Lemma 3.1 assembled (Corollary 3.4
    minus its hypothesis check).
- Only the direction rank_{F_p}(stack) <= rank_E M(lambda) of eq. (rank-nullity) is needed downstream and proved.
- NOT yet done: the verification of the Frobenius hypothesis for the multiplication maps on V_k / C_D
  (Corollary 3.4 proper, needs the PC-side facts of Layer B: absorption, g^p - g in C_D, base change; the
  base-change lemma 2.3 is not needed in this matrix form if the hypothesis is stated over E by clearing
  denominators, to be settled when Layer B exists), and Layers A, B, E-I.
- Verdict on the riskiest step: feasible and done in about 900 Lean lines, well under the 1600-2800 estimate for C+D.
  The risk that remains in this cluster is only the hypothesis check of Corollary 3.4 (Layer B interface).
- Tooling note: the external drive makes `import Mathlib` take ~35 min per cold lean process. Iterating with a local
  olean mirror of the needed import closure on the internal disk (LEAN_PATH) gives ~10 s checks.
