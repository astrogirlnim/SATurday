# R4 Phase 2.3, round 2: candidate theorem C1 (rank-bounded linear terms)

Status: research notes, docs only. No Lean, no builds. Date 2026-10-14, branch r4/prover-c1.
Follows r4-phase23-program.md (round 1, Section 4 candidate C1) and r4-phase23-analysis.md.

Labels: PROVED-BY-HAND (derived on paper this session, not machine checked), CITED (a theorem
of the literature or of this repo, used as a black box), COMPUTED (a script run this session),
CONJECTURE. "Pang Thm 1.1" is the degree-size theorem of the Pang paper (arXiv 2610.00837 v1,
TeX deg--size.tex, `thm:quantitative`, read in full again this session, including the
definition of Res(PC_r/F_p), the syntactic rules, Remark poly-clause, the Res(k) Fact, and
the Tseitin application).

## 0. Verdict

1. C1 holds, in a slightly corrected form (Section 1.4), and it is a direct corollary of
   Pang Thm 1.1. PROVED-BY-HAND modulo two black boxes (Pang Thm 1.1; the certified linear
   PC degree for Tseitin mod q, `tseitin_bool_degree_Fp`).
2. Corrections to round 1 (Section 6): the translation target needs degree 3(p-1)rho, not
   2(p-1)rho, for the fully general term rule (the separate rules fit in 2(p-1)rho); the
   polynomial 1 - prod(1 - l^(p-1)) in round 1 is the falsity polynomial of the term, not
   its exact indicator; the proof-size overhead is O(N) lines per rule, not O(1) (harmless).
3. What is new versus Pang: only the system. Pang proves the same shape of bound for
   Res(k) (conjunctions of k literals, any p) and for Res(PC_r/F_p) and Res(lin_{F_p});
   C1 is the intermediate system "disjunctions of conjunctions of rho F_p-linear equations",
   which contains Res(lin_{F_p}) (rho = 1) and Res(rho) (a rho-term is a rank-rho
   conjunction), and is contained in Res(PC_{3(p-1)rho}/F_p). Novelty: low. I found no
   reference that names this system (CITED-UNCHECKED, a literature search was not done).
4. Kill test (Section 4): no short refutation found, and none can exist below Pang's bound
   (the simulation is exact). Controls behave as they should (q = p is easy, so the
   hypothesis q != p is exactly where the proof uses its input).
5. Next target (Section 5): the barrier at rank rho = Theta(log n) is the (D/16n)^((p-1)r)
   factor of Pang Thm 1.1. It is the same barrier as Res(k) for k = omega(log n), which
   Pang does not break either. The concrete next target is a rank lemma for multiplication
   by indicators of affine subspaces whose loss is exp(-O(rho/ polylog)) instead of
   exp(-Theta(rho)).

## 1. Task 1: the precise statement

### 1.1 The proof system R_rho^p

Fix a prime p and an integer rho >= 1. Variables x_1..x_N range over {0,1}; all arithmetic
in forms is in F_p, and a point of the cube is read as a point of F_p^N.

- An affine form is l = a_1 x_1 + ... + a_N x_N + a_0 with a_i in F_p. The equation (l = 0).
- A term T is a finite nonempty set of equations. Its rank is
  rk(T) = dim_{F_p} span{l : (l=0) in T} in the space of affine forms (including the
  constant forms). T is rho-bounded if rk(T) <= rho. The term is true at a in {0,1}^N if
  every l in T vanishes at a. A literal x_i = 1 or x_i = 0 is a term of rank 1.
- A line is a finite set of rho-bounded terms (read as their disjunction); the empty line is
  the empty clause.
- Rules. Write T1 |= T3 for semantic consequence on the cube {0,1}^N (this is checkable but
  need not be efficient; a stronger rule only strengthens the theorem).
  - (Ax) The clauses of the input CNF F, with each literal as a rank-1 term; and the tautology
    clauses {x_i = 0}, {x_i = 1}.
  - (Wk) Weakening: from L infer L union L' (any rho-bounded terms L').
  - (Sem) Semantic term inference, which contains cut, simplification, and AND-introduction:
    from L1 union {T1} and L2 union {T2} infer L1 union L2 union {T3}, whenever
    T1 and T2 together semantically imply T3 on the cube, T3 rho-bounded. T3 may be absent
    ("falsum"), and T2 may be absent ("top"). Special cases: cut on a term T is
    T1 = T and the negation clause; resolution on a variable is T1 = (x=1), T2 = (x=0),
    T3 absent; simplification (AND-elimination, replacing a term by a weaker one,
    including any linear consequence) is T2 absent; AND-introduction is T3 = T1 union T2
    (rank <= rho required).
  Contraction is implicit (lines are sets).
- A refutation of F is a DAG of lines ending in the empty line. The size S is the number of
  lines (nodes). (This is Pang's convention, he counts lines, not symbols.)

The system depends on p (an F_p-linear equation is not an F_q-linear equation). It is
sound (each rule is semantically valid) and its refutations are of F unsatisfiable.

### 1.2 Statement C1

Theorem C1. Let p != q be primes. Put kappa = kappa(p,q) = 3(p-1)^2 ln(62976 q (q-1)).
For every epsilon > 0 there are N_0 and a family of cubic graphs G (the certified expanders
of `tseitin_bool_degree_Fp`) with N >= N_0 Boolean variables (N = 3 q m / 2 for m
vertices) such that for every charge b with sum_v b(v) != 0 mod q, and every
1 <= rho <= epsilon ln m, every R_rho^p refutation of the one-hot Tseitin_q(G,b) formula has
size
  S >= exp( N^(1 - (kappa+1) epsilon) ) >= exp( m^(1 - (kappa+1) epsilon) ).

For epsilon < 1/(kappa+1) this is exp(N^(Omega(1))); for fixed rho the proof gives
exp(Omega(N)) with constant depending on (p,q,rho). Table of kappa (COMPUTED, c1chk.py):
(p,q) = (3,2): 140.9; (2,3): 38.5; (5,2): 563.7; (2,5): 42.1. The "O(epsilon)" of the
informal C1 is therefore (kappa+1) epsilon with a large explicit constant, and the bound is
asymptotic only (for p = 3, rho = 1 the constants (delta/16)^(3 (p-1)^2) are astronomically
small, so there is no concrete N at which the bound is nontrivial that I would want to quote).

### 1.3 Is it already a corollary of Pang?

Yes. Pang Thm 1.1 applies to Res(PC_r/F_p) for every constant-ish r (r may depend on n,
the theorem is explicit), and its Tseitin application (Theorem on applications, item (b))
and Corollary moduli apply to Res(lin_{F_p}) (r = 1) and, through Fact resk and
Corollary resk, to Res(k) with k up to epsilon log n, giving exp(N / 2^{O(k)}).
C1 is the same chain with the rank-rho linear conjunctions in place of k-literal
conjunctions. Everything new is the simulation lemma of Section 2; the parameter chain is
Pang's own.

Exactly what is new versus what is known:
- Versus Res(lin_{F_p}) (r = 1): C1 allows conjunctions of up to rho linear equations in a
  term. A rank-rho term is not obviously a disjunction of linear equations. I
  proved only the containment Res(lin_{F_p}) in R_rho^p, not a separation. CONJECTURE that
  the containment is strict at rho >= 2 (not needed for C1).
- Versus Res(k) for k = rho: R_rho^p contains Res(rho) (literal conjunctions are rank-rho
  terms), and also contains any F_p-parity of unboundedly many variables in rank 1. For
  p = 2 this includes parities of many variables inside a term, unlike Res(k).
  The lower bound shape exp(N^(1-O(epsilon))) matches Pang's Res(k) bound
  exp(N / 2^{O(k)}) at k = epsilon log N.
- Versus Res(PC_r/F_p): R_rho^p is a syntactic fragment (SIMULATED, Section 2), so C1 is
  weaker than the bound for the whole of Res(PC_{3(p-1)rho}/F_p).

### 1.4 Corrected form of the round 1 statement

Round 1 wrote the lower bound as exp(n^(1-O(epsilon))) with "n" the number of vertices and
rank epsilon log n. This holds, with the translation (m vertices, N = 3qm/2 variables,
ln N = ln m + O(1)); the only place where the base of the logarithm matters is kappa (a
change of base multiplies epsilon by a constant).

## 2. Task 2: the simulation lemma

### 2.1 Translation of terms and lines

Let d = (p-1) rho. For a term T choose a maximal linearly independent subset B_T of its
forms (by a fixed rule); |B_T| = rk(T) <= rho. Define
  chi_T = prod_{l in B_T} (1 - l^(p-1))   (a polynomial of degree <= d).

Claim 1 (PROVED-BY-HAND; COMPUTED on 43200 random (T, point) pairs, p in {2,3,5}, N in {4,5},
zero mismatches). For every point a in F_p^N, chi_T(a) = 1 if a satisfies every equation of
T, else 0. Proof. By Fermat, 1 - l(a)^(p-1) is 1 if l(a) = 0 and 0 otherwise. So chi_T(a) = 1
iff every form of B_T vanishes at a. Every form of T lies in span(B_T), a linear combination
of forms vanishing at a also vanishes at a, so "all of B_T vanish" iff "all of T vanish"
(forms in span(B_T): l = sum c_j l_j holds as a polynomial identity including constants, so
l(a) = sum c_j l_j(a)). QED. Remark: if span(T) contains a nonzero constant (an inconsistent
term) then no point satisfies all of B_T and chi_T is 0 on all of F_p^N. No special case is
needed. For literal terms I take chi = x_i, resp. 1 - x_i, which also has the two
properties (degree 1 <= d, 0/1-valued indicator on the cube); the derivations below use only
these two properties of chi, not the product form.

Translation. A line L = {T_1,..,T_s} becomes the clause
  tr(L) = (chi_{T_1} - 1 = 0) or ... or (chi_{T_s} - 1 = 0)
of Res(PC_r/F_p) with r = 3 d = 3(p-1) rho. Soundness of the translation: for a in the
cube, tr(L) holds at a iff some chi_{T_j}(a) = 1 iff L holds at a. The empty line goes to the
empty clause. Initial clauses of F: a clause l_1 or .. or l_s of F becomes
(chi_{l_1} - 1 = 0) or ...; Pang's input form is (Q_{l_j} = 0) with Q the falsity
polynomial, Q = 1 - x for the literal x and Q = x for the literal not-x. These
differ by the scalar -1: for the literal x, chi = x and chi - 1 = x - 1 = -Q; for the
literal not-x, chi = 1 - x and chi - 1 = -x = -Q. So tr(l_j) = -Q_{l_j} in both cases: one
scaling (linear-combination) step per literal, no degree increase. The tautology clauses {x_i = 0},
{x_i = 1} become (x_i = 0) or (x_i - 1 = 0), the default axiom of Res(PC_r).

### 2.2 Two auxiliary facts

Fact BR (Boolean reduction, PROVED-BY-HAND). Let P be a polynomial in F_p[x_1..x_N] with
deg P <= r that vanishes on the cube. Then P = sum_i u_i (x_i^2 - x_i) with deg u_i <=
deg P - 2. Proof. Divide P by the monic (in x_1) polynomial x_1^2 - x_1: P = u_1 (x_1^2 - x_1)
+ P_1 with x_1-degree of P_1 at most 1 and total degree of P_1 and u_1 + 2 at most deg P.
Iterate with x_2 on P_1 (dividing by a polynomial in x_2 does not raise the x_1-degree),
etc. The final remainder is multilinear, and vanishes on the cube, hence is the zero polynomial
(a multilinear polynomial is determined by its values on the cube). QED.

Fact U (unit equation, PROVED-BY-HAND). If P vanishes on the cube and deg P <= r then the
unit clause (P = 0) has a Res(PC_r/F_p) derivation of at most 3N + N + N = 5N lines, using
only the default axioms. Proof. For each i: from (x_i = 0) or (x_i - 1 = 0) multiply the
first disjunct by (x_i - 1) to get (x_i(x_i - 1) = 0) or (x_i - 1 = 0), then multiply the
second disjunct by x_i to get (x_i^2 - x_i = 0) or (x_i^2 - x_i = 0), contract. (Pang's
multiplication rule acts on a chosen disjunct; each displayed polynomial has degree 2 <= r;
r >= 3 here.) Multiply by u_i from Fact BR (displayed degree <= deg P <= r); then add the N
products with N - 1 linear-combination steps. The result is (P = 0). The N lines
(x_i^2 - x_i = 0) can be shared across the whole refutation, so each application of Fact U
costs at most 2N new lines. QED.

### 2.3 The rule (Sem), every case

Let a = chi_{T_1}, b = chi_{T_2}, c = chi_{T_3}, each of degree <= d and 0/1-valued on the
cube. Hypothesis of the rule: T_1 and T_2 together imply T_3 on the cube, i.e.
P = a b (1 - c) vanishes on the cube. deg P <= 3d = r.
Premises tr(L1 + T1) = A or (a - 1 = 0) and tr(L2 + T2) = B or (b - 1 = 0).
1. Multiply the first premise's disjunct (a - 1 = 0) by b: A or (ab - b = 0).
   (displayed degrees: d, d, 2d, all <= r.)
2. Linear combination with the second premise (coefficients 1, 1):
   A or B or ((ab - b) + (b - 1) = ab - 1 = 0).
3. (T_3 present.) Multiply the disjunct by (1 - c): A or B or ((ab - 1)(1 - c) = 0).
   Displayed degree <= 3d = r. Unit equation (P = 0) by Fact U, where
   P = ab(1 - c). Linear combination (1, -1): (ab - 1)(1 - c) - ab(1 - c) = -(1 - c) = c - 1.
   Result A or B or (c - 1 = 0) = tr(L1 + L2 + T3). Done.
3'. (T_3 absent, falsum.) Then P = ab vanishes on the cube; displayed degree 2d. From step 2:
   A or B or (ab - 1 = 0); unit equation (ab = 0) by Fact U; linear combination (1, -1)
   gives A or B or (-1 = 0), a false constant equation; Pang's deletion rule leaves A or B.
   (Degrees at most 2d.)
Cases with T_2 absent (top, i.e. b = 1): skip steps 1, 2: premise is A or (a - 1 = 0),
then step 3 with b = 1 (displayed degree <= 2d); with T_3 absent the premise gives
A or (a - 1 = 0) and a = ab vanishes: unit (a = 0), combine to get (-1 = 0), delete.
Special cases checked individually:
- Cut on a term T (L1 + T and L2 + not-T, where not-T = {l-c' : l in T, c' != 0} as rank-1
  terms): reduces to p-1 times |T| applications of (Sem) with T3 absent, one for each
  disjunct (each (l - c' = 0) is inconsistent with T), as in the standard derivation: from
  A + T, B' + t_1 + .. + t_m derive A + B' + t_2 + .. + t_m, and repeat with the original
  premise A + T, contracting A. Degree 2d each.
- Resolution on a variable: (x=1), (x=0), T3 absent. Degree 2.
- AND-introduction T3 = T1 and T2 (rank <= rho): step 3 with 1 - c, deg 3d, or directly:
  premises A or (a-1=0), B or (b-1=0); multiply the first by b, combine with the second:
  A or B or (ab - 1 = 0) (degree 2d); and (c - ab = 0) is a unit equation (Fact U, c and ab
  agree on the cube) so combine: A or B or (c - 1 = 0). Degree 2d here (the direct
  derivation never forms (1-c) times anything), so ANDs and cuts alone fit in 2d.
- Simplification / weakening of a term T1 to T3 with T1 |= T3: (Sem) with T2 absent, degree
  3d; the direct derivation costs 2d: multiply A or (a-1=0) by c: A or (ac - c = 0),
  unit equation (ac - a = 0) (a(1-c) vanishes on the cube, degree 2d), combine to get
  A or (a - c = 0), combine with A or (a - 1 = 0) to get A or (c - 1 = 0). Degree 2d.
So: cut, resolution, AND-introduction and linear simplification each fit in degree 2d =
2(p-1) rho, and the single unified semantic rule (Sem) fits in 3d. The program's 2(p-1)rho
holds for the named rules; the unified rule needs 3(p-1)rho.
(Wk) Weakening: Pang's syntactic weakening, adding any clauses at once. Contraction: lines
are sets; Pang's contraction rule.

### 2.4 Size accounting

The simulation of one (Sem) step uses at most 3 + 2N new lines (steps 1, 2, the
multiplication, the combination, the unit equation); weakening and axioms use O(1). So
  S' <= 3N + (2N + 5) S + 2 |F|,
where S' is the size of the Res(PC_r/F_p) refutation and S is the size of the R_rho^p
refutation. It ends with the empty line since tr(empty line) is the empty clause.

Lemma 1 (PROVED-BY-HAND). A refutation of F in R_rho^p with S lines gives a refutation of F in
Res(PC_{3(p-1)rho}/F_p) with at most 3N + (2N+5) S + 2|F| lines. Soundness of each step was
checked above using only (i) 0/1-valuedness of chi on the cube, (ii) deg chi <= d,
(iii) Fact U.

Check of the claim in the task, "a conjunction of linear equations as one polynomial
equation of degree (p-1)*rank": confirmed with the correction of Section 6 (the polynomial
is the falsity polynomial 1 - chi, equation 1 - chi = 0 iff the term is true). A disjunction
becomes a clause of Res(PC_r), the equations of its terms. No union bound or approximation
is needed, which is what makes this class special compared with arbitrary depth-2 AND/OR.

## 3. Task 3: deriving C1

### 3.1 Inputs

(I1) Pang Thm 1.1, with p, r, and F a CNF in N variables of width w: if Q(F) does not have a
degree-D PC refutation over F_p (with Boolean axioms) and D >= max{32 (p-1)^2 r, 8 w}, then
every S-node Res(PC_r/F_p) refutation satisfies ln S >= (D / (32 p^2 r)) (D / (16 N))^((p-1) r).
(CITED, the statement of eq:main, read in the TeX.)

(I2) `tseitin_bool_degree_Fp` (TseitinBool.lean, certified in this repo, CITED): for primes
p not dividing q and every N_0 there is a cubic graph on m >= N_0 vertices such that for every
charge b the one-hot Tseitin_q CNF has no PC refutation over F_p of degree
D_0 = ((m - 2)/1312 - q (q+3)) / (q - 1) (natural-number division). The polynomial system is
`cnfAx (tcnf G q b)` (clause falsity polynomials, with Boolean axioms in `PCD`), the same Q(F)
as Pang. N = |E| q = 3 q m / 2. Clause width of tcnf: at-least-one clauses have width q,
at-most-one width 2, vertex clauses width 3, so w = max(q,3). Lean statement is for all b;
unsatisfiability needs sum b != 0 (round 1 convention), and when sum b = 0 the formula is
satisfiable and has no refutation.

### 3.2 The numeric chain, line by line

1. Ratio. D_0 >= m/(1312 (q-1)) - q(q+3)/(q-1) - 1, so D_0/N tends to
   (1/(1312(q-1))) / (3q/2) = 2/(3936 q (q-1)) = 1/(1968 q (q-1)) =: delta_0.
   (3 * 1312 / 2 = 1968.) For m large, D_0 >= (delta_0 / 2) N =: delta N, where
   delta = 1/(3936 q (q-1)).
2. Take D = D_0. Hypotheses of (I1): D >= 32 (p-1)^2 r with r = 3 (p-1) rho: need
   D >= 96 (p-1)^3 rho. Since rho <= epsilon ln m this holds for large m because D is linear
   in N. Also D >= 8 max(q,3), true for large N.
3. Exponent in (I1): (p-1) r = 3 (p-1)^2 rho <= 3 (p-1)^2 epsilon ln N. Hence
   (D/(16N))^((p-1)r) >= (delta/16)^(3(p-1)^2 epsilon ln N) = N^(-kappa epsilon),
   with kappa = 3 (p-1)^2 ln(16/delta) = 3 (p-1)^2 ln(16 * 3936 q (q-1)) = 3 (p-1)^2 ln(62976 q (q-1)).
   (16 * 3936 = 62976.) Numerics: p=3, q=2: 3*4*ln(125952) = 12 * 11.743 = 140.9. ✓.
4. Prefactor: D/(32 p^2 r) = D/(96 p^2 (p-1) rho) >= delta N / (96 p^2 (p-1) epsilon ln N).
5. So ln S' >= c_1 N^(1 - kappa epsilon) / (epsilon ln N), c_1 = delta/(96 p^2 (p-1)).
6. Lemma 1: S >= (S' - 3N - 2|F|) / (2N + 5), so ln S >= ln(S' - O(N)) - ln(2N+5)
   >= c_1 N^(1-kappa epsilon)/(epsilon ln N) - O(ln N), for large N (S' is huge, so the
   subtraction is harmless).
7. For N large depending on epsilon, N^(epsilon) >= (2/c_1) epsilon^{-1}... precisely
   c_1/(epsilon ln N) * N^(1 - kappa epsilon) - O(ln N) >= N^(1 - (kappa+1) epsilon)
   once N^epsilon >= 2 epsilon ln N / c_1. This gives Theorem C1.
Monotonicity: the bound improves as rho decreases, so the worst case rho = epsilon ln m
suffices (and rho <= epsilon ln m <= epsilon ln N).
No error found in the chain. Points where an error is easy to make and which I rechecked:
the exponent is (p-1) r = 3(p-1)^2 rho (not 3(p-1) rho); the condition D >= 32 (p-1)^2 r
involves r not rho; D/N uses N = 3qm/2 (variables), not m; q enters twice (in N and in the
D formula) and the net is 1968 q (q-1), the ratio shrinks like 1/q^2.
Small base-of-log remark: if "log" is log2, replace epsilon by epsilon/ln 2 in kappa.

## 4. Task 4: kill test

Goal: find a refutation of Tseitin_q in R_rho^p, rho = O(log n), that is shorter than
exp(N^(1-(kappa+1)epsilon)).

(K1) Control, q = p. Gaussian elimination over F_p: the vertex clauses give flow equations,
all lines are single F_p-linear equations (rank 1), the sum of all vertex equations is
the contradiction. Pang Corollary moduli gives size O(N) in Res(lin_{F_p}), which is
R_1^p. So the bound is false for q = p, consistently: the certified PC degree over F_p of
Tseitin_p is not linear (the degree lower bound requires p not dividing q, the
hypothesis of (I2)). The proof of C1 fails exactly there. PROVED-BY-HAND consistent.

(K2) q != p, Gaussian elimination over F_q. The F_q-linear equation sum_{e in boundary U} y_e = s(U)
with y_e = sum_a a X_{e,a} is not an F_p-affine form over the cube: on one edge a form can
express any subset of the q values, but a vertex or cut constraint is an F_q-linear function
of the edge values, and a map Z_q -> F_p additive (to make the sum collapse into one form)
is trivial because p does not divide q. So the F_q lines have no rank-1 translation. A
cut-line is (as a function) "parity-like", needs exp(Omega(|boundary|)) disjuncts of
rank-O(rho) terms to be expressed as a clause (heuristic). COMPUTED toy check
(mono.py, p = 3, q = 2, the number-of-terms obstruction for a boundary of size m): the largest
number of cube points covered by a single rank-rho F_3 term lying entirely inside the
odd-parity set of m Boolean variables: m=4: 6 of 8 (rho=1,2,3); m=5: 0 at rho=1, 6 of 16 at
rho=2 and 3 (rho = 3 is a sampled lower bound). The coverage fraction falls with m
(0.75, 0.375), but m is far too small to read a rate, so I do not claim more than
"consistent". The honest quantitative content for this item is Pang's theorem itself.
Any such elimination also would have to beat the PC degree: the exact PC degree of Tseitin
mod 2 over odd p is about boundary/2 with ratio at most 1/4 (round 1, theorem LB/UB in
program Section 2), linear, which is what (I2) provides for q = 2 and the chain uses.

(K3) Brute force. Any CNF on N variables has a size 2^(O(N)) refutation in R_1^p (Pang Fact
brute-force, size O(2^t t)). C1 is not contradicted by it: exp(N^(1 - (kappa+1) epsilon)) <<
exp(O(N)). So there is a gap between the best upper bound I know (2^(O(N))) and C1. For
rank rho the true size may be 2^(Theta(N/ polylog)) (CONJECTURE, no argument).

(K4) Width/degree upper bounds. Tseitin has resolution width Theta(N) on expanders, so
Res(k) refutations for k = O(log N) cost exp(N / 2^{O(k)}) at best (CITED: Pang
Corollary resk, matching the exponent form 1 - O(epsilon) here). Not contradicted.

(K5) Other known upper bounds: AC0[q]-Frege (constant depth, mod q gates, polynomial size
for Tseitin_q) is not an R_rho^p refutation because its lines contain MOD_q gates; R_rho^p
has MOD_p only. Part--Tzameret tree-like incomparability (CITED via Pang) and Pang Cor
moduli (Tseitin_q has size O(N) in Res(lin_{F_q})) are consistent with C1 in the sense that
Res(lin_{F_q}) is not contained in R_rho^p for q != p.

(K6) The simulation itself (soundness of Lemma 1): the cases were checked by hand in
Section 2.3, and Claim 1 numerically. I could not find a rule whose simulation exceeds
degree 3d, so no kill by "rule needs a higher degree". Another potential kill, "Pang's
theorem not allowing the needed r": Thm 1.1 requires D >= 32 (p-1)^2 r, i.e. r = O(N), and
the bound is nontrivial only while (delta/16)^((p-1) r) is not smaller than 1/N, i.e. r up to
about ln N / (3 (p-1)^2 ln(16/delta)); this is the epsilon log N regime of C1. Not a kill.

Result: no kill. The only fragile points are the constants (kappa is large, so the theorem
is non-vacuous only for tiny epsilon and large N) and the fact that the lower bound is
inherited from Pang, so an attack on C1 would also be an attack on Pang Thm 1.1 (or on the
Lean-certified degree bound).

## 5. Task 5: what remains toward genuine depth 2

C1 covers: depth-2 formulas OR(AND(MOD_p equations)) with joint rank in each AND at most
epsilon log n, and nothing else. Left open, each labeled as a concrete target.

(T1) Rank beyond log n. This is the main barrier. The loss (D/16N)^((p-1) r) in Pang Thm 1.1 comes from
N_n(K-d)/N_n(K) >= (K/2n)^d (the dimension drop when multiplying by a degree-d polynomial).
With d = 3(p-1) rho and rho = omega(log N) the bound is below 1 and the theorem is vacuous.
For terms that are conjunctions of literals this is the Res(k) barrier at k = omega(log n),
which Pang's corollary also stops at epsilon log n (CITED). So the target is not specific to
linear terms. Concrete form, CONJECTURE C1-plus: for T an affine subspace of codimension rho, the rank
of multiplication by chi_T on V_K / C_D drops by a factor at most p^(-O(rho)) (instead of
(K/n)^((p-1) rho)), or at least by a factor exp(-rho^(1-c)). First test: subcubes
(x_1 = .. = x_rho = 0), that is Res(k) at k = (log n)^2. For K <= n/3 the density of a
codimension-rho subcube among the multilinear monomials of degree K is (K/n)^rho, not
2^(-rho), and I see no counting argument that avoids this loss. If the loss is real for
subcubes, C1-plus is false for this method. I rate the method succeeding at about 10 percent
(CONJECTURE).

(T2) Cut on depth-2 formulas. C1 allows cut only on terms (inside lines). A cut formula that
is itself a DNF of terms is not a rule of R_rho^p. A DNF of m terms is a line, but cutting
on it needs the rank-bounded negation (a conjunction of m negated terms), which is
a CNF, not a term. This is the first unwritten item B5(iii) of the analysis document;
not attempted here.

(T3) MOD_p connectives over terms (the real missing piece for AC0[p]-Frege of depth 2).
Round 1 item E6 / analysis B5(iv): the gate "sum of terms = c mod p" has no low-degree
equation; C1 leaves it entirely. Concretely: a degree-size theorem for Res(PC_r) extended by
one MOD_p connective over lines. Not touched here.

(T4) A family with more favorable ratio than C1's. The constant kappa in C1 is tiny-epsilon-only because
delta = D/N is about 1/4000 for certified cubic expanders (round 1: no family has ratio above
1/4 for parity Tseitin). Improving the PC degree constant (e.g. ratio 0.05 instead of 1/3936)
would improve kappa by ln(80) only, since kappa = 3(p-1)^2 ln(16/delta): kappa is logarithmic
in 1/delta. So this is not where the leverage is.

Recommended next concrete target (statement only, no owner task): T1, via a rank lemma for
multiplication by affine-subspace indicators, tested first on subcubes of codimension
(log n)^2 against the known Res(k) landscape.

## 6. Corrections and checks of round 1 (program Section 4, C1; Section 3, E5)

- Round 1 E5/C1 called 1 - prod(1 - l_j^(p-1)) "the exact indicator of the affine subspace".
  It is 1 minus the indicator, i.e. the falsity polynomial of the term, 0/1-valued, equal to 1
  exactly when the term is false. The equation (1 - chi_T = 0) says "T is true" and has
  degree (p-1) rho; the rest of C1's derivation (term cut by the linear combination rule) is
  unaffected because I re-derived it with chi_T and (chi_T - 1 = 0).
- Round 1 stated r = 2(p-1) rho. Correct for the named rules (cut, AND-introduction,
  simplification), shown in Section 2.3. The unified semantic rule needs 3(p-1) rho; I use
  that r throughout, which affects only the constant kappa (factor 3/2).
- Round 1 said "polynomial overhead". It is O(N) lines per rule, from Fact U. Harmless
  because ln S absorbs ln N.
- Round 1 odds: "the statement is true and a corollary of Pang, about 65 percent; novelty
  low-to-moderate." Updated: the statement is true (modulo the two black boxes) and a
  corollary, novelty low (the system is new in name, not in method).

## 7. Session log (append-only)

- 2026-10-14 prover (round 2): read round 1 documents and Pang's TeX (Theorem quantitative,
  Res(PC_r) rules, Fact resk, Tseitin application, Corollary moduli). Wrote the system,
  the simulation Lemma 1 with Facts BR and U, the parameter chain (kappa table), kill
  test (controls, one toy computation: chi indicator check 43200 pairs, odd-term coverage
  at m = 4, 5). Scripts: scratchpad c1chk.py, mono.py (not committed). No Lean, no builds.
  Nothing pushed.
