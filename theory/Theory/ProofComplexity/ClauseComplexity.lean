import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.Basic
import Theory.ProofComplexity.CriticalAssignments
import Theory.ProofComplexity.Resolution

/-!
# Clause Complexity Measure for PHP (R1, Beame-Pitassi Lemma 2)

Defines the falsifying set of critical assignments and the complexity measure
μ from the 2026-08-03 prove cycle (docs/ladder/rungs/r1-php-haken.md):

  Fals(C) = { π ∈ Crit(n) | the critical assignment of π falsifies C }
  μ(C)    = |Fals(C)|

Certified claims in this module:

1. Axiom values: μ(hole) = 0, μ(pigeonClause i) = n!, μ(∅) = (n+1)!.
2. Subadditivity: Fals(resolvent C D x) ⊆ Fals(C) ∪ Fals(D), hence
   μ(resolvent) ≤ μ(C) + μ(D).
3. Leaf sum: for any derivation from phpCNF n, μ(conclusion) ≤ sum of μ over
   hyp leaves ≤ Derivation.size * n!, so any refutation has size ≥ n+1.

Honest scope: Claim 3 is only a linear lower bound. The exponential R1 target
needs lemmas 3 and 4 (width of medium complexity clauses).

Also certified (lemma 3 support G1/G2): literal unsatisfaction under critical
assignments, and the width 1 counterexample μ({p_ij}) = (n+1)! − n!.

Also certified (G5, BP96 Lemma 1 measure): L(C) = left-out pigeons of Fals(C),
pigeonComplexity = |L|, values on axioms and empty, subadditivity, and
existence of an intermediate-complexity clause in every refutation (n ≥ 1).

LOG: R1 clause complexity module (BP96 lemma 2, lemma 3 support, G5)
-/

namespace SATurday.ProofComplexity

-- clauseSat is an existential over a Finset; Classical gives Decidable for filters.
open Classical

/-- Critical permutations: all placements of n+1 pigeons with one left out. -/
abbrev Crit (n : ℕ) := Equiv.Perm (Fin (n + 1))

/-- A critical permutation falsifies clause `C` when its critical assignment
does not satisfy `C`. -/
def falsifies (n : ℕ) (C : Clause) (pi : Crit n) : Prop :=
  ¬ clauseSat (criticalAssignment n pi) C

/-- The finite set of critical permutations that falsify `C`. -/
noncomputable def Fals (n : ℕ) (C : Clause) : Finset (Crit n) :=
  Finset.univ.filter fun pi => falsifies n C pi

/-- Complexity μ(C) = |Fals(C)|. -/
noncomputable def complexity (n : ℕ) (C : Clause) : ℕ := (Fals n C).card

/-! ## Claim 1: values on axioms and the empty clause -/

/-- Every critical assignment falsifies the empty clause. -/
theorem falsifies_empty (n : ℕ) (pi : Crit n) : falsifies n ∅ pi := by
  intro h
  obtain ⟨l, hl, _⟩ := h
  exact Finset.notMem_empty l hl

/-- μ(∅) = (n+1)!. -/
theorem complexity_empty (n : ℕ) : complexity n ∅ = (n + 1).factorial := by
  have hfilter : Fals n ∅ = Finset.univ := by
    ext pi
    simp [Fals, falsifies_empty]
  simp only [complexity, hfilter, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-- No critical assignment falsifies a hole clause. -/
theorem not_falsifies_holeClause {n : ℕ} (pi : Crit n) {C : Clause}
    (hC : C ∈ holeClauses n) : ¬ falsifies n C pi := by
  intro hf
  exact hf (criticalAssignment_sat_holeClause pi hC)

/-- μ(H) = 0 for every hole clause H. -/
theorem complexity_holeClause {n : ℕ} {C : Clause} (hC : C ∈ holeClauses n) :
    complexity n C = 0 := by
  simp only [complexity, Fals, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro pi _
  exact not_falsifies_holeClause pi hC

/-- Falsifying a pigeon clause means that pigeon is the left-out one
(`pi i = Fin.last n`). -/
theorem falsifies_pigeonClause_iff {n : ℕ} (i : Fin (n + 1)) (pi : Crit n) :
    falsifies n (pigeonClause n i) pi ↔ pi i = Fin.last n := by
  simp only [falsifies, criticalAssignment_sat_pigeonClause_iff]
  constructor
  · intro h
    by_contra hne
    exact h hne
  · intro h hsat
    exact hsat h

/-- Fiber card of evaluation at a fixed domain point: all fibers of
`π ↦ π i` have size `n!`, since they partition `(n+1)!` equally. -/
theorem card_perm_fiber (n : ℕ) (i y : Fin (n + 1)) :
    Fintype.card { pi : Crit n // pi i = y } = n.factorial := by
  -- Sigma of fibers ≃ all permutations.
  let e : (Σ z : Fin (n + 1), { pi : Crit n // pi i = z }) ≃ Crit n :=
    ⟨fun ⟨_, ⟨pi, _⟩⟩ => pi,
     fun pi => ⟨pi i, ⟨pi, rfl⟩⟩,
     fun ⟨z, ⟨pi, h⟩⟩ => by
       refine Sigma.ext h ?_
       subst h
       rfl,
     fun _ => rfl⟩
  have hsigma :
      Fintype.card (Σ z : Fin (n + 1), { pi : Crit n // pi i = z }) =
      (n + 1).factorial := by
    rw [Fintype.card_congr e, Fintype.card_perm, Fintype.card_fin]
  -- Fibers are equal via postcomposition with a swap.
  have hconst : ∀ y₁ y₂ : Fin (n + 1),
      Fintype.card { pi : Crit n // pi i = y₁ } =
      Fintype.card { pi : Crit n // pi i = y₂ } := by
    intro y₁ y₂
    let τ : Crit n := Equiv.swap y₁ y₂
    refine Fintype.card_congr
      ⟨fun ⟨pi, hpi⟩ => ⟨pi.trans τ, ?_⟩,
       fun ⟨pi, hpi⟩ => ⟨pi.trans τ, ?_⟩,
       fun ⟨pi, _⟩ => ?_,
       fun ⟨pi, _⟩ => ?_⟩
    · simp [τ, hpi, Equiv.trans_apply, Equiv.swap_apply_left]
    · simp [τ, hpi, Equiv.trans_apply, Equiv.swap_apply_right]
    · ext x; simp [τ, Equiv.trans_apply, Equiv.swap_apply_self]
    · ext x; simp [τ, Equiv.trans_apply, Equiv.swap_apply_self]
  -- Sum of equal fibers: card(fiber y) * (n+1) = (n+1)!.
  have hfiber :
      Fintype.card { pi : Crit n // pi i = y } * (n + 1) = (n + 1).factorial := by
    have hsum' :
        ∑ z : Fin (n + 1), Fintype.card { pi : Crit n // pi i = z } =
        (n + 1).factorial := by
      rw [← Fintype.card_sigma]
      exact hsigma
    have hsum'' :
        ∑ z : Fin (n + 1), Fintype.card { pi : Crit n // pi i = y } =
        (n + 1).factorial := by
      rw [← hsum']
      exact Finset.sum_congr rfl fun z _ => (hconst z y).symm
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.mul_comm] using hsum''
  have hfact : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
  have : Fintype.card { pi : Crit n // pi i = y } * (n + 1) =
      n.factorial * (n + 1) := by
    rw [hfiber, hfact, Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos n) this

/-- μ(pigeonClause i) = n!. -/
theorem complexity_pigeonClause (n : ℕ) (i : Fin (n + 1)) :
    complexity n (pigeonClause n i) = n.factorial := by
  simp only [complexity, Fals]
  have hfilter :
      Finset.univ.filter (fun pi : Crit n => falsifies n (pigeonClause n i) pi) =
      Finset.univ.filter (fun pi : Crit n => pi i = Fin.last n) := by
    refine Finset.filter_congr ?_
    intro pi _
    exact falsifies_pigeonClause_iff i pi
  rw [hfilter, ← Fintype.card_coe]
  refine (Fintype.card_congr ?e).trans (card_perm_fiber n i (Fin.last n))
  exact ⟨fun ⟨pi, h⟩ => ⟨pi, (Finset.mem_filter.mp h).2⟩,
    fun ⟨pi, h⟩ => ⟨pi, Finset.mem_filter.mpr ⟨Finset.mem_univ pi, h⟩⟩,
    fun _ => rfl, fun _ => rfl⟩

/-! ## Claim 2: subadditivity under erase then union resolvent -/

/-- If a critical assignment satisfies both parents, it satisfies the resolvent.
Same case split as `derivation_entails` (R0). -/
theorem criticalAssignment_sat_resolvent {n : ℕ} (pi : Crit n)
    {C D : Clause} {x : ℕ}
    (hC : clauseSat (criticalAssignment n pi) C)
    (hD : clauseSat (criticalAssignment n pi) D) :
    clauseSat (criticalAssignment n pi) (resolvent C D x) := by
  set α := criticalAssignment n pi
  by_cases hax : α x = true
  · obtain ⟨l, hl, hla⟩ := hD
    have hlne : l ≠ ⟨x, false⟩ := by
      rintro rfl
      simp only [litSat] at hla
      rw [hax] at hla
      exact Bool.noConfusion hla
    exact ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hlne, hl⟩), hla⟩
  · have hax' : α x = false := by
      cases h : α x
      · rfl
      · exact absurd h hax
    obtain ⟨l, hl, hla⟩ := hC
    have hlne : l ≠ ⟨x, true⟩ := by
      rintro rfl
      simp only [litSat] at hla
      rw [hax'] at hla
      exact Bool.noConfusion hla
    exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hlne, hl⟩), hla⟩

/-- Subadditivity of Fals under resolution. -/
theorem Fals_resolvent_subset {n : ℕ} (C D : Clause) (x : ℕ) :
    Fals n (resolvent C D x) ⊆ Fals n C ∪ Fals n D := by
  intro pi hpi
  simp only [Fals, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and] at hpi ⊢
  -- hpi : falsifies resolvent; show falsifies C ∨ falsifies D
  by_contra h
  -- h : ¬ (falsifies C ∨ falsifies D) i.e. satisfies both
  have hCs : clauseSat (criticalAssignment n pi) C := by
    unfold falsifies at h
    tauto
  have hDs : clauseSat (criticalAssignment n pi) D := by
    unfold falsifies at h
    tauto
  exact hpi (criticalAssignment_sat_resolvent pi hCs hDs)

/-- Subadditivity of μ under resolution. -/
theorem complexity_resolvent_le {n : ℕ} (C D : Clause) (x : ℕ) :
    complexity n (resolvent C D x) ≤ complexity n C + complexity n D := by
  simp only [complexity]
  calc (Fals n (resolvent C D x)).card
      ≤ (Fals n C ∪ Fals n D).card := Finset.card_le_card (Fals_resolvent_subset C D x)
    _ ≤ (Fals n C).card + (Fals n D).card := Finset.card_union_le _ _

/-! ## Claim 3: leaf sum and the linear size lower bound -/

/-- Sum of μ over hypothesis leaves of a derivation from `phpCNF n`. -/
noncomputable def Derivation.complexitySum (n : ℕ) :
    {C : Clause} → Derivation (phpCNF n) C → ℕ
  | _, .hyp C _ => complexity n C
  | _, .res _ dC dD _ _ => dC.complexitySum n + dD.complexitySum n

/-- Complexity of the conclusion is at most the leaf complexity sum. -/
theorem complexity_le_complexitySum {n : ℕ} {C : Clause}
    (d : Derivation (phpCNF n) C) :
    complexity n C ≤ d.complexitySum n := by
  induction d with
  | hyp C hC =>
    simp [Derivation.complexitySum]
  | res x dC dD hx hnx ihC ihD =>
    simp only [Derivation.complexitySum]
    calc complexity n (resolvent _ _ x)
        ≤ complexity n _ + complexity n _ := complexity_resolvent_le _ _ x
      _ ≤ dC.complexitySum n + dD.complexitySum n := by omega

/-- Every hypothesis leaf from PHP has complexity at most n!. -/
theorem complexity_php_hyp_le {n : ℕ} {C : Clause} (hC : C ∈ phpCNF n) :
    complexity n C ≤ n.factorial := by
  rcases Finset.mem_union.mp hC with hp | hh
  · simp only [pigeonClauses, Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    exact (complexity_pigeonClause n i).le
  · rw [complexity_holeClause hh]
    exact Nat.zero_le _

/-- The leaf complexity sum is at most size times n!. -/
theorem Derivation.complexitySum_le_size_mul {n : ℕ} {C : Clause}
    (d : Derivation (phpCNF n) C) :
    d.complexitySum n ≤ d.size * n.factorial := by
  induction d with
  | hyp C hC =>
    simp only [Derivation.complexitySum, Derivation.size, one_mul]
    exact complexity_php_hyp_le hC
  | res x dC dD hx hnx ihC ihD =>
    simp only [Derivation.complexitySum, Derivation.size]
    calc dC.complexitySum n + dD.complexitySum n
        ≤ dC.size * n.factorial + dD.size * n.factorial := by omega
      _ = (dC.size + dD.size) * n.factorial := by ring
      _ ≤ (dC.size + dD.size + 1) * n.factorial := by
            exact Nat.mul_le_mul_right _ (Nat.le_succ _)

/-- Linear size lower bound: every resolution refutation of PHP(n+1, n) has
size at least n+1. (Honest: not the exponential R1 target.) -/
theorem php_resolution_size_linear (n : ℕ)
    (d : Derivation (phpCNF n) (∅ : Clause)) :
    n + 1 ≤ d.size := by
  have hμ := complexity_empty n
  have hle := complexity_le_complexitySum d
  have hsum := d.complexitySum_le_size_mul
  -- (n+1)! ≤ size * n!
  have h : (n + 1).factorial ≤ d.size * n.factorial := by
    calc (n + 1).factorial = complexity n ∅ := hμ.symm
      _ ≤ d.complexitySum n := hle
      _ ≤ d.size * n.factorial := hsum
  -- divide by n! using factorial_succ: (n+1)! = (n+1) * n!
  have hfact : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
  rw [hfact] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.factorial_pos n)

/-! ## Literal characterization (lemma 3 support, G1/G2 from 2026-08-03 prove)

Certified so that the naive "large μ implies wide" claim cannot return silently:
a single positive grid literal already has μ = (n+1)! − n!.
-/

/-- Positive grid literal is false under the critical assignment iff the
permutation does not place pigeon `i` in hole `j`. -/
theorem litUnsat_pos_iff {n : ℕ} (pi : Crit n) (i : Fin (n + 1)) (j : Fin n) :
    ¬ litSat (criticalAssignment n pi) ⟨pvar n i j, true⟩ ↔
      pi i ≠ Fin.castSucc j := by
  simp only [litSat, criticalAssignment_pvar]

/-- Negative grid literal is false under the critical assignment iff the
permutation places pigeon `i` in hole `j`. -/
theorem litUnsat_neg_iff {n : ℕ} (pi : Crit n) (i : Fin (n + 1)) (j : Fin n) :
    ¬ litSat (criticalAssignment n pi) ⟨pvar n i j, false⟩ ↔
      pi i = Fin.castSucc j := by
  -- litSat of negative means assignment is false; criticalAssignment is true
  -- exactly on placements, so unsat of negative means placed.
  constructor
  · intro h
    by_contra hne
    have : criticalAssignment n pi (pvar n i j) = false := by
      cases hval : criticalAssignment n pi (pvar n i j)
      · rfl
      · exact absurd ((criticalAssignment_pvar pi i j).mp hval) hne
    exact h this
  · intro hplace hsat
    have htrue : criticalAssignment n pi (pvar n i j) = true :=
      (criticalAssignment_pvar pi i j).mpr hplace
    exact Bool.noConfusion (hsat.symm.trans htrue)

/-- A critical permutation falsifies `C` iff every literal of `C` is unsatisfied. -/
theorem falsifies_iff_forall_lit {n : ℕ} (C : Clause) (pi : Crit n) :
    falsifies n C pi ↔ ∀ l ∈ C, ¬ litSat (criticalAssignment n pi) l := by
  simp only [falsifies, clauseSat, not_exists, not_and]

/-- Width 1 counterexample: one positive grid literal has
μ = (n+1)! − n!. Kills naive "large μ implies wide". -/
theorem complexity_singleton_pos (n : ℕ) (i : Fin (n + 1)) (j : Fin n) :
    complexity n ({⟨pvar n i j, true⟩} : Clause) =
      (n + 1).factorial - n.factorial := by
  simp only [complexity, Fals]
  -- Fals = {σ | σ i ≠ castSucc j}
  have hfilter :
      Finset.univ.filter (fun σ : Crit n =>
          falsifies n ({⟨pvar n i j, true⟩} : Clause) σ) =
      Finset.univ.filter (fun σ : Crit n => σ i ≠ Fin.castSucc j) := by
    refine Finset.filter_congr ?_
    intro σ _
    simp only [falsifies_iff_forall_lit, Finset.mem_singleton, forall_eq,
      litUnsat_pos_iff]
  rw [hfilter]
  -- card(filter ≠ y) = card univ − card(filter = y)
  set Sy : Finset (Crit n) :=
    Finset.univ.filter (fun σ : Crit n => σ i = Fin.castSucc j)
  set Sne : Finset (Crit n) :=
    Finset.univ.filter (fun σ : Crit n => σ i ≠ Fin.castSucc j)
  have hdisj : Disjoint Sy Sne := by
    rw [Finset.disjoint_left]
    intro σ hSy hSne
    exact (Finset.mem_filter.mp hSne).2 (Finset.mem_filter.mp hSy).2
  have hunion : Sy ∪ Sne = Finset.univ := by
    ext σ
    constructor
    · intro _; exact Finset.mem_univ σ
    · intro _
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Sy, Sne]
      exact Classical.em (σ i = Fin.castSucc j)
  have heqCard : Sy.card = Fintype.card { σ : Crit n // σ i = Fin.castSucc j } := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr
      ⟨fun ⟨σ, h⟩ => ⟨σ, (Finset.mem_filter.mp h).2⟩,
       fun ⟨σ, h⟩ => ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ σ, h⟩⟩,
       fun _ => rfl, fun _ => rfl⟩
  have hsum := (Finset.card_union_of_disjoint hdisj).symm
  -- (Sy ∪ Sne).card = Sy.card + Sne.card, and union = univ
  rw [hunion, Finset.card_univ] at hsum
  have hcard : Sne.card = Fintype.card (Crit n) -
      Fintype.card { σ : Crit n // σ i = Fin.castSucc j } := by
    omega
  simpa [Sne, Fintype.card_perm, Fintype.card_fin, card_perm_fiber] using hcard

/-! ## BP96 Lemma 1 complexity (G5): left-out pigeon measure

Locked 2026-08-03 prove cycle (docs/ladder/rungs/r1-php-haken.md):

  L(C) = { i | ∃ π, π leaves out i and falsifies C }
  pigeonComplexity(C) = |L(C)|

This is the Beame-Pitassi measure (minimum number of pigeon axioms that imply
C on critical assignments). Distinct from μ = |Fals|; μ stays for the linear
size bound only.
-/

/-- The pigeon left out by a critical permutation: the unique `i` with
`pi i = Fin.last n`. -/
def Crit.leftOut {n : ℕ} (pi : Crit n) : Fin (n + 1) :=
  pi.symm (Fin.last n)

/-- Specification: `leftOut` is mapped to the last (hole-out) value. -/
theorem Crit.leftOut_eq {n : ℕ} (pi : Crit n) :
    pi pi.leftOut = Fin.last n :=
  pi.apply_symm_apply _

/-- Left-out characterization: `pi i = last` iff `i = leftOut pi`. -/
theorem Crit.leftOut_iff {n : ℕ} (pi : Crit n) (i : Fin (n + 1)) :
    pi i = Fin.last n ↔ i = pi.leftOut := by
  constructor
  · intro h
    have hsym := congrArg pi.symm h
    simpa [Crit.leftOut, Equiv.symm_apply_apply] using hsym
  · intro h
    rw [h, Crit.leftOut_eq]

/-- L(C): pigeons that appear as left-out for some falsifying critical perm. -/
noncomputable def L (n : ℕ) (C : Clause) : Finset (Fin (n + 1)) :=
  (Fals n C).image Crit.leftOut

/-- Membership in L via existence of a falsifying critical perm leaving out `i`. -/
theorem mem_L_iff {n : ℕ} (C : Clause) (i : Fin (n + 1)) :
    i ∈ L n C ↔ ∃ pi : Crit n, pi i = Fin.last n ∧ falsifies n C pi := by
  simp only [L, Finset.mem_image, Fals, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨pi, hf, rfl⟩
    exact ⟨pi, Crit.leftOut_eq pi, hf⟩
  · rintro ⟨pi, hlast, hf⟩
    refine ⟨pi, hf, ((Crit.leftOut_iff pi i).mp hlast).symm⟩

/-- BP96 complexity: number of left-out pigeons that can falsify `C`. -/
noncomputable def pigeonComplexity (n : ℕ) (C : Clause) : ℕ := (L n C).card

/-- Every pigeon is left out by some critical perm, so L(∅) = univ. -/
theorem L_empty (n : ℕ) : L n (∅ : Clause) = Finset.univ := by
  ext i
  constructor
  · intro _; exact Finset.mem_univ i
  · intro _
    refine (mem_L_iff (∅ : Clause) i).mpr ?_
    exact ⟨Equiv.swap i (Fin.last n), by simp [Equiv.swap_apply_left],
      falsifies_empty n _⟩

/-- pigeonComplexity(∅) = n+1. -/
theorem pigeonComplexity_empty (n : ℕ) :
    pigeonComplexity n (∅ : Clause) = n + 1 := by
  simp only [pigeonComplexity, L_empty, Finset.card_univ, Fintype.card_fin]

/-- L(pigeonClause i) = {i}. -/
theorem L_pigeonClause (n : ℕ) (i : Fin (n + 1)) :
    L n (pigeonClause n i) = {i} := by
  ext k
  simp only [mem_L_iff, Finset.mem_singleton, falsifies_pigeonClause_iff]
  constructor
  · rintro ⟨pi, hkLast, hiLast⟩
    -- hkLast : pi k = last, hiLast : pi i = last ⇒ k = i
    exact (pi.injective (hiLast.trans hkLast.symm)).symm
  · intro hk
    rw [hk]
    refine ⟨Equiv.swap i (Fin.last n), ?_, ?_⟩
    · simp [Equiv.swap_apply_left]
    · simp [Equiv.swap_apply_left]

/-- pigeonComplexity(pigeonClause i) = 1. -/
theorem pigeonComplexity_pigeonClause (n : ℕ) (i : Fin (n + 1)) :
    pigeonComplexity n (pigeonClause n i) = 1 := by
  simp [pigeonComplexity, L_pigeonClause]

/-- L(hole) = ∅. -/
theorem L_holeClause {n : ℕ} {C : Clause} (hC : C ∈ holeClauses n) :
    L n C = ∅ := by
  ext i
  simp only [mem_L_iff, Finset.notMem_empty, iff_false]
  rintro ⟨pi, _, hf⟩
  exact not_falsifies_holeClause pi hC hf

/-- pigeonComplexity(hole) = 0. -/
theorem pigeonComplexity_holeClause {n : ℕ} {C : Clause} (hC : C ∈ holeClauses n) :
    pigeonComplexity n C = 0 := by
  simp [pigeonComplexity, L_holeClause hC]

/-- Subadditivity of L under resolution. -/
theorem L_resolvent_subset {n : ℕ} (C D : Clause) (x : ℕ) :
    L n (resolvent C D x) ⊆ L n C ∪ L n D := by
  intro i hi
  obtain ⟨pi, hlast, hf⟩ := (mem_L_iff (resolvent C D x) i).mp hi
  have hFals : pi ∈ Fals n (resolvent C D x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ pi, hf⟩
  have hCD : pi ∈ Fals n C ∪ Fals n D := Fals_resolvent_subset (n := n) C D x hFals
  simp only [Finset.mem_union, Fals, Finset.mem_filter, Finset.mem_univ, true_and] at hCD
  simp only [Finset.mem_union]
  rcases hCD with hfC | hfD
  · left; exact (mem_L_iff C i).mpr ⟨pi, hlast, hfC⟩
  · right; exact (mem_L_iff D i).mpr ⟨pi, hlast, hfD⟩

/-- Subadditivity of pigeonComplexity under resolution. -/
theorem pigeonComplexity_resolvent_le {n : ℕ} (C D : Clause) (x : ℕ) :
    pigeonComplexity n (resolvent C D x) ≤
      pigeonComplexity n C + pigeonComplexity n D := by
  simp only [pigeonComplexity]
  calc (L n (resolvent C D x)).card
      ≤ (L n C ∪ L n D).card := Finset.card_le_card (L_resolvent_subset C D x)
    _ ≤ (L n C).card + (L n D).card := Finset.card_union_le _ _

/-- PHP hypotheses have pigeonComplexity at most 1. -/
theorem pigeonComplexity_php_hyp_le {n : ℕ} {C : Clause} (hC : C ∈ phpCNF n) :
    pigeonComplexity n C ≤ 1 := by
  rcases Finset.mem_union.mp hC with hp | hh
  · simp only [pigeonClauses, Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    exact (pigeonComplexity_pigeonClause n i).le
  · rw [pigeonComplexity_holeClause hh]
    exact Nat.zero_le _

/-- If a derived clause has pigeonComplexity above 2(n+1)/3 and n ≥ 1, some
(possibly earlier) clause in the same derivation lies in the intermediate band
((n+1)/3, 2(n+1)/3]. -/
theorem exists_intermediate_of_high_pigeonComplexity {n : ℕ} (hn : 1 ≤ n)
    {C : Clause} (d : Derivation (phpCNF n) C)
    (hhigh : 2 * (n + 1) / 3 < pigeonComplexity n C) :
    ∃ C' : Clause, (n + 1) / 3 < pigeonComplexity n C' ∧
      pigeonComplexity n C' ≤ 2 * (n + 1) / 3 ∧
      Nonempty (Derivation (phpCNF n) C') := by
  cases d with
  | hyp C hC =>
    have hle := pigeonComplexity_php_hyp_le hC
    omega
  | res x dC dD hx hnx =>
    set k := n + 1
    -- Use term-level conclusions so omega sees one resolvent expression.
    change 2 * k / 3 <
      pigeonComplexity n (resolvent dC.conclusion dD.conclusion x) at hhigh
    have hle : pigeonComplexity n (resolvent dC.conclusion dD.conclusion x) ≤
        pigeonComplexity n dC.conclusion + pigeonComplexity n dD.conclusion :=
      pigeonComplexity_resolvent_le dC.conclusion dD.conclusion x
    by_cases hCh : 2 * k / 3 < pigeonComplexity n dC.conclusion
    · exact exists_intermediate_of_high_pigeonComplexity hn dC hCh
    · by_cases hDh : 2 * k / 3 < pigeonComplexity n dD.conclusion
      · exact exists_intermediate_of_high_pigeonComplexity hn dD hDh
      · have hCh' : pigeonComplexity n dC.conclusion ≤ 2 * k / 3 := Nat.not_lt.mp hCh
        have hDh' : pigeonComplexity n dD.conclusion ≤ 2 * k / 3 := Nat.not_lt.mp hDh
        by_cases hCmid : k / 3 < pigeonComplexity n dC.conclusion
        · exact ⟨dC.conclusion, hCmid, hCh', ⟨dC⟩⟩
        · by_cases hDmid : k / 3 < pigeonComplexity n dD.conclusion
          · exact ⟨dD.conclusion, hDmid, hDh', ⟨dD⟩⟩
          · have hCmid' : pigeonComplexity n dC.conclusion ≤ k / 3 := Nat.not_lt.mp hCmid
            have hDmid' : pigeonComplexity n dD.conclusion ≤ k / 3 := Nat.not_lt.mp hDmid
            omega

/-- Every resolution refutation of PHP(n+1, n) for n ≥ 1 contains a clause of
intermediate BP96 complexity. -/
theorem exists_intermediate_pigeonComplexity {n : ℕ} (hn : 1 ≤ n)
    (d : Derivation (phpCNF n) (∅ : Clause)) :
    ∃ C : Clause, (n + 1) / 3 < pigeonComplexity n C ∧
      pigeonComplexity n C ≤ 2 * (n + 1) / 3 ∧
      Nonempty (Derivation (phpCNF n) C) := by
  have hhigh : 2 * (n + 1) / 3 < pigeonComplexity n (∅ : Clause) := by
    rw [pigeonComplexity_empty]
    omega
  exact exists_intermediate_of_high_pigeonComplexity hn d hhigh

end SATurday.ProofComplexity
