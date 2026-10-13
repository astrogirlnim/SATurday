# R4 scout note: Green's weak-degree theorem and AR Theorem 4.4

Status: docs only, scout. Date 2026-10-13. No Lean, no builds.

## 0. What I found (honest summary)

- Green's paper itself (F. Green, "A complex-number Fourier technique for lower bounds on the Mod-m degree",
  Computational Complexity 9 (2000) 16-38, doi 10.1007/PL00001599; STACS 1995 preliminary version) is NOT
  available in full text. Springer is paywalled, Unpaywall reports oa_status closed with no repository copy,
  Clark University Commons (commons.clarku.edu/faculty_computer_sciences/64) is a metadata/abstract record whose
  only full-text link is the DOI, and there is no ECCC report (ECCC TR98-036 is Grolmusz-Tardos, an unrelated paper;
  I downloaded it by mistake and deleted it). So Green's Thm 3.4 text, his lemmas, and his proof are UNVERIFIED by me.
- What I did get in full: Beck and Li, "Represent MOD function by low degree polynomial with unbounded one-sided
  error", arXiv:1304.0713 (2013), downloaded to the session scratchpad
  (.../scratchpad/green/bl.pdf, bl.txt). It states Green's bound, reuses Green's composite-to-prime reduction, and
  gives complete ELEMENTARY proofs of a bound at least as strong as Green's, with no Fourier or cyclotomic input.
  Everything marked "BL" below is read from that text. Everything marked "reconstructed" is my own derivation.
- Abstract of Green (from the Clark record): if a nonconstant integer polynomial is 0 mod m whenever Mod_q is 0 on
  n Boolean inputs, gcd(q,m)=1, then degree is Omega(n); method: inputs as complex q-th roots of unity, Fourier
  transform, algebraic-integer arguments.

## 1. Statement of Green Thm 3.4 (as far as it can be known)

Not read. Second-hand: BL abstract says Green's bound is floor(n/(2(q-1))) (the BL introduction writes
floor(n/(2(q+1))), which is inconsistent with their abstract and with AR; AR cites floor(d1/(2(p-1))), so q-1 is
the best-supported value). Form: for coprime q, m and n Boolean variables, the weak mod-m degree of Mod_q
(a nonzero g in Z[x_1..x_n] with Mod_q(x)=0 => g(x) = 0 mod m) is at least floor(n/(2(q-1))). Green's convention
for Mod_q appears to be "Mod_q(x)=0 iff q | sum x_i" (consistent with the abstract and with AR's use);
UNVERIFIED. Green's Lemma "weak mod-m degree = min over primes p | m of weak mod-p degree" is reproved in BL
Lemma 2.1 (elementary, CRT plus a divisibility-by-p argument), not needed for AR (AR only needs a field F with
char != q, so m is replaced by a field).

## 2. The convention trap (important for formalization)

For a field F and Boolean set Z, "f is l-immune" in AR (per r4-phase22-plan.md): no nonzero g of degree <= l
vanishes on the Boolean roots of f. AR's predicate for Thm 4.4 has roots Z = {alpha : sum_j eps_j alpha_j = sigma
mod p}. So the relevant ideal is polynomials vanishing ON the congruence class {sum = sigma}. In BL notation
chi_q = 1 iff q | |x|; BL's ideal <h> = functions vanishing where h = 0. Therefore:

- The AR/Green object is the ideal <not chi_q> (vanish on {|x| = 0 mod q}), BL Section 5, immunity exactly
  floor((n+q-1)/q) for sigma = 0 (BL Thm 5.2, over F_p with p coprime to q).
- BL's Section 3 result (n/2, Razborov-Smolensky omega trick) concerns <chi_q>, polynomials vanishing OFF the class.
  That is the wrong direction for AR. Do not use it. (An earlier plan line "d/(2q)" is also superseded; see
  r4-expander-plan.md.)

## 3. Recommended route: replace Green by BL Section 4-5 (elementary, no cyclotomics)

Claim (reconstructed from BL, extended by me to shift sigma and signs): over any field F with char F not dividing q
(including char 0), for Z_n,q,s = {x in {0,1}^n : |x| = s mod q}, every nonzero function g in F[x]/(x_i^2 = x_i)
vanishing on Z has degree >= l + floor((n-2l+1)/q) minimized over 0 <= l <= n/2 (and >= n-l+1 otherwise), hence
>= floor((n+2-q)/q)-ish, in particular >= floor(n/(4(q-1))) once n >= 4(q-1).

Proof outline (BL, verified there for sigma = 0, F = F_p; extension to general F and sigma is my reconstruction):

1. Symmetric ideal. Z is S_n-invariant. BL Lemma 4.1: among minimum-degree nonzero g in the ideal there is one of
   the form g = g' * prod_{i<=l}(x_{2i-1} - x_{2i}) with g' symmetric in x_{2l+1..n}. Proof: if g is not symmetric,
   pick a transposition pi=(i,j) with pi(g) != g; g - pi(g) = (x_i - x_j) h with h = g1 - g2 where g = g0 + g1 x_i
   + g2 x_j + g3 x_i x_j (g_k free of x_i,x_j); degree does not increase, g-pi(g) is still in the ideal (ideal is
   pi-invariant); repeat on h. Works over any F (no averaging, which fails in char p).
2. Restriction. g vanishes on Z iff g' vanishes on weights w in [0, m], m = n-2l, with w + l = sigma mod q
   (the product is nonzero exactly when each pair differs, contributing l ones). So g' is a nonzero symmetric
   function, g' = sum_{k<=e} c_k e_k (elementary symmetric), vanishing on W_l = {w in [0,m] : w = sigma-l mod q}.
3. Rank lemma, BL Lemma 5.1: for any a >= 0, d > 0, q a unit in F, the vectors psi_d(a + i q) = (C(a+iq, 0..d-1)),
   i = 0..d-1, are a basis of F^d. Proof: det = prod_{i<j}(a_j - a_i) / prod_{k=1}^{d-1} k! = q^{d(d-1)/2}
   (binomial rows -> falling factorial polynomials in a_i by column ops, -> Vandermonde). Nonzero iff char does not
   divide q. (BL state it for F_p, p prime to q; the formula is characteristic-free over Z so it holds over any F
   where q is a unit. Subtle: the closed form divides by k!, so state it in Z or Q and then reduce mod char, or
   prove as an identity det(binom matrix) = q^{d(d-1)/2} in Z. Note the BL display has an obvious typo
   "(a0 - d - 2)" for "(a0 - d + 2)".)
4. Counting. g' nonzero with e <= m forces c != 0 and psi_{e+1}(w) . c = 0 for all w in W_l. If |W_l| >= e+1, Lemma
   5.1 (the points of W_l form an arithmetic progression of step q) gives c = 0, contradiction. So e+1 > |W_l|,
   deg g = e + l >= l + |W_l|. If e > m then deg g > m + l = n - l >= n/2. |W_l| >= floor((m+1)/q) = floor((n-2l+1)/q).
   Minimizing: l + floor((n-2l+1)/q) >= (n-q+2)/q + l(1-2/q) >= (n-q+2)/q for q >= 2.
5. Signs and shift (AR Thm 4.4 has eps_j in {+-1}). Substituting x_j -> 1-x_j for the eps_j = -1 variables is an
   invertible affine change that preserves polynomial degree and maps Z onto {sum_{+} x - sum_{-} x' ... }, i.e.
   {sum of all new variables = sigma + #neg mod q}. So WLOG all signs +1 with sigma replaced by sigma + #neg. Then
   steps 1-4 with a general shift apply. This replaces AR's route (Cor 2.6, Lemma 2.7, halving to d1 >= d/2), and
   yields a bound about d/q rather than d/(4(q-1)); the AR bound is weaker, so it follows.
6. Comparison with AR's claim floor(d/(4(q-1))): (n-q+2)/q - 1 >= n/(4(q-1)) holds for n >= roughly 4(q-1)(q-2)/(3q-4);
   for n >= 4(q-1) the AR value is >= 1 and my bound dominates (checked by hand for the inequality chain, but the
   exact floor arithmetic is unchecked; re-derive before formalizing). For n < 4(q-1) AR's value is 0 and the claim
   is "0-immune", meaning Z is nonempty. THAT CAN FAIL for tiny d (e.g. d < q-1 and sigma out of reach). Gap in AR's
   statement as written: it needs a side condition (Z nonempty), harmless in D1 where d = 8^k is large. Flag it.

## 4. What Green's own Fourier proof would use (reconstructed, thin)

From the abstract only: represent x in {0,1}^n as omega^{x_i} with omega a primitive q-th root of unity in C,
expand the polynomial g (integer coefficients, g = 0 mod m on Mod_q's zeros) in the character basis of (Z/q)^n
restricted to the cube, and use that Fourier coefficients are algebraic integers in Z[omega] whose divisibility
by m/norm properties (norm from Q(omega) to Q, cyclotomic polynomial Phi_q irreducible over Q, Phi_q(1) value,
omega^i - 1 associates when q prime) force many coefficients nonzero mod a prime above m. I do not know the exact
lemmas, so I do not outline further. Mathlib status for such an argument: IsPrimitiveRoot, Polynomial.cyclotomic,
cyclotomic irreducibility over Q (Polynomial.cyclotomic.irreducible_rat), IsCyclotomicExtension, existence of
primitive roots in a splitting field when char does not divide q (IsCyclotomicExtension.exists / splitting field of
X^q-1, separable), Algebra.norm and Algebra.trace for cyclotomic extensions (e.g. IsPrimitiveRoot.norm_eq_one,
norm_sub_one_of_prime_ne_two) all exist, but Green's result over a general field F still needs a
characteristic-p / residue-field passage that Mathlib does not package. This route is NOT recommended: it is
unverified and heavier than Section 3. The omega trick (BL Sec 3) needs only a primitive q-th root in an
extension, but proves the wrong direction (section 2).

## 5. Mathlib inventory for the recommended route

- Vandermonde: Matrix.det_vandermonde (exists). Binomial/falling factorial: Nat.choose, descPochhammer,
  Polynomial.ascPochhammer (exist). Need to prove the column-operation step from the binomial matrix to the
  Vandermonde (not in Mathlib; maybe via polynomial basis change: C(x,k) = descPochhammer k / k! is a monic-up-to-unit
  triangular basis of polys of degree < d, then evaluation matrix at d points is invertible when the points are
  distinct and the basis change is invertible; needs k! units in F or work over Q then clear denominators; this is
  the delicate point in char p: k! can vanish for k >= p, so do the determinant identity over Z/Q and reduce).
  Cleaner alternative: prove independence of binomial rows directly via the integer identity det = q^{d(d-1)/2}.
- Multilinear/Boolean-function ring: either work with functions {0,1}^n -> F and a custom degree (needs a bridge to
  MvPolynomial degree: every polynomial reduces to a multilinear one of no larger total degree; check whether the
  repo already has a reduction lemma for PC), or MvPolynomial with ideal (X_i^2 - X_i). Permutation action:
  MvPolynomial.rename, expected to exist.
- Division/char: needs (q : F) != 0 from CharP / char F not dividing q; standard.

## 6. Size and risk

- Estimate: 800 to 1300 lines of Lean total, roughly: symmetrization Lemma 4.1 (300-500), binomial/Vandermonde
  rank lemma (200-350), counting and floors, sign flip and shift reduction (250-400), bridge to the repo's
  immunity definition (100-200). Consistent with the 800-1500 in r4-expander-plan.md, and no cyclotomic or Galois
  theory needed.
- Riskiest step: Lemma 4.1 (iterated transposition symmetrization on multilinear polynomials: termination/degree
  bookkeeping, the (x_i - x_j) factorization, and relabeling to get the pairs (1,2),(3,4),...), closely followed by
  the Lemma 5.1 determinant identity in arbitrary characteristic (k! may vanish in F). If either stalls, fall back
  is to cite no theorem: both are needed; there is no cheaper route known to me for the vanish-on-class direction.
- Residual unverified items: Green's exact Thm 3.4 text and the q-1 versus q+1 discrepancy; BL's claim for general
  fields and shift sigma (they treat F_p and sigma = 0; my extension is reconstructed); the floor arithmetic in
  section 3 step 6; the exact AR definition of "l-immune" (strict vs non-strict) against the AR PDF.
