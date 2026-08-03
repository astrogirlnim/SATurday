import Mathlib.Logic.Equiv.Defs
import Theory.ProofComplexity.PHP

/-!
# Critical Assignments for the Pigeonhole Family (R1, Beame-Pitassi Lemma 1)

Groundwork for the R1 target (Haken's lower bound, route: Beame and Pitassi
1996 bottleneck counting; see docs/ladder/rungs/r1-php-haken.md).

A critical assignment places n of the n+1 pigeons bijectively into the n holes
and leaves exactly one pigeon out. We encode the placement data as a
permutation `pi` of `Fin (n + 1)`: pigeon `i` sits in hole `j` exactly when
`pi i = Fin.castSucc j` (the values below `Fin.last n` are the holes), and the
left-out pigeon is the one mapped to `Fin.last n`, namely `pi.symm (Fin.last n)`.

Certified results in this module (no sorries, standard axioms only):

1. `pvar_inj`: the variable encoding pigeon i, hole j is injective.
2. `criticalAssignment_pvar`: the assignment sets variable (i, j) true exactly
   when the permutation places pigeon i in hole j.
3. `criticalAssignment_sat_holeClause`: every hole clause is satisfied
   (injectivity of the permutation means no two pigeons share a hole).
4. `criticalAssignment_sat_pigeonClause_iff`: pigeon i's clause is satisfied
   exactly when pigeon i is placed (not mapped to the last element).
5. `criticalAssignment_falsifies_leftOut` and `criticalAssignment_sat_iff`:
   a critical assignment falsifies exactly one clause of PHP(n+1, n), the
   pigeon clause of the left-out pigeon. This is the launching fact of the
   Beame-Pitassi counting argument.
6. `criticalAssignment_sat_php_erase`: the BP96 shape, satisfaction of the
   whole family minus the left-out pigeon clause.

LOG: R1 critical assignments module (BP96 lemma 1)
-/

namespace SATurday.ProofComplexity

/-- The critical assignment attached to a permutation `pi` of the pigeons:
variable (i, j) is true exactly when `pi` places pigeon `i` in hole `j`.
Defined on all of `ℕ` (variables outside the PHP grid are false), with the
grid lookup done by a decidable finite search. -/
def criticalAssignment (n : ℕ) (pi : Equiv.Perm (Fin (n + 1))) : Assignment :=
  fun v =>
    decide (∃ i : Fin (n + 1), ∃ j : Fin n, v = pvar n i j ∧ pi i = Fin.castSucc j)

/-- The pigeon-hole variable encoding is injective: `i * n + j` with `j < n`
determines both coordinates (division and remainder by `n`). -/
theorem pvar_inj {n : ℕ} {i i' : Fin (n + 1)} {j j' : Fin n}
    (h : pvar n i j = pvar n i' j') : i = i' ∧ j = j' := by
  have hn : 0 < n := j.pos
  -- The remainder recovers the hole and the quotient recovers the pigeon.
  have hmod : ∀ (a : Fin (n + 1)) (b : Fin n), pvar n a b % n = b.val := by
    intro a b
    show (a.val * n + b.val) % n = b.val
    exact Nat.mul_add_mod_of_lt b.isLt
  have hdiv : ∀ (a : Fin (n + 1)) (b : Fin n), pvar n a b / n = a.val := by
    intro a b
    show (a.val * n + b.val) / n = a.val
    calc (a.val * n + b.val) / n
        = a.val + b.val / n := by rw [Nat.mul_comm]; exact Nat.mul_add_div hn a.val b.val
      _ = a.val := by rw [Nat.div_eq_of_lt b.isLt, Nat.add_zero]
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩
  · have := congrArg (· / n) h
    simpa [hdiv] using this
  · have := congrArg (· % n) h
    simpa [hmod] using this

/-- Specification of the critical assignment on grid variables: variable (i, j)
is true exactly when the permutation places pigeon i in hole j. -/
theorem criticalAssignment_pvar {n : ℕ} (pi : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) (j : Fin n) :
    criticalAssignment n pi (pvar n i j) = true ↔ pi i = Fin.castSucc j := by
  simp only [criticalAssignment, decide_eq_true_eq]
  constructor
  · rintro ⟨i', j', heq, hpi⟩
    obtain ⟨hi, hj⟩ := pvar_inj heq
    rw [hi, hj]
    exact hpi
  · intro h
    exact ⟨i, j, rfl, h⟩

/-- Every hole clause is satisfied by a critical assignment: two distinct
pigeons cannot both be placed in the same hole because the permutation is
injective, so one of the two negative literals is true. -/
theorem criticalAssignment_sat_holeClause {n : ℕ} (pi : Equiv.Perm (Fin (n + 1)))
    {C : Clause} (hC : C ∈ holeClauses n) :
    clauseSat (criticalAssignment n pi) C := by
  simp only [holeClauses, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and] at hC
  obtain ⟨j, i, i', hlt, rfl⟩ := hC
  by_cases h1 : pi i = Fin.castSucc j
  · -- Pigeon i occupies hole j, so pigeon i' does not; its negative literal wins.
    have h2 : pi i' ≠ Fin.castSucc j := fun h2 =>
      absurd (pi.injective (h1.trans h2.symm)) (ne_of_lt hlt)
    refine ⟨⟨pvar n i' j, false⟩,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
    show criticalAssignment n pi (pvar n i' j) = false
    cases hval : criticalAssignment n pi (pvar n i' j)
    · rfl
    · exact absurd ((criticalAssignment_pvar pi i' j).mp hval) h2
  · -- Pigeon i does not occupy hole j; its negative literal wins.
    refine ⟨⟨pvar n i j, false⟩, Finset.mem_insert_self _ _, ?_⟩
    show criticalAssignment n pi (pvar n i j) = false
    cases hval : criticalAssignment n pi (pvar n i j)
    · rfl
    · exact absurd ((criticalAssignment_pvar pi i j).mp hval) h1

/-- Pigeon i's clause is satisfied exactly when pigeon i is placed in a real
hole, that is, when the permutation does not map it to the last element. -/
theorem criticalAssignment_sat_pigeonClause_iff {n : ℕ} (pi : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) :
    clauseSat (criticalAssignment n pi) (pigeonClause n i) ↔ pi i ≠ Fin.last n := by
  constructor
  · rintro ⟨l, hl, hla⟩ hlast
    simp only [pigeonClause, Finset.mem_image, Finset.mem_univ, true_and] at hl
    obtain ⟨j, rfl⟩ := hl
    have hval : criticalAssignment n pi (pvar n i j) = true := hla
    have hpi : pi i = Fin.castSucc j := (criticalAssignment_pvar pi i j).mp hval
    rw [hlast] at hpi
    exact absurd hpi.symm (ne_of_lt (Fin.castSucc_lt_last j))
  · intro hne
    -- Not mapped to last means the image value is a genuine hole index.
    have hlt : (pi i).val < n := by
      have hle : (pi i).val ≤ n := Nat.lt_succ_iff.mp (pi i).isLt
      rcases Nat.lt_or_eq_of_le hle with h | h
      · exact h
      · exact absurd (Fin.ext h) hne
    refine ⟨⟨pvar n i ⟨(pi i).val, hlt⟩, true⟩,
      Finset.mem_image.mpr ⟨⟨(pi i).val, hlt⟩, Finset.mem_univ _, rfl⟩, ?_⟩
    show criticalAssignment n pi (pvar n i ⟨(pi i).val, hlt⟩) = true
    refine (criticalAssignment_pvar pi i _).mpr ?_
    apply Fin.ext
    simp

/-- The left-out pigeon (the one mapped to the last element) has its pigeon
clause falsified: it sits in no hole. -/
theorem criticalAssignment_falsifies_leftOut {n : ℕ} (pi : Equiv.Perm (Fin (n + 1))) :
    ¬ clauseSat (criticalAssignment n pi) (pigeonClause n (pi.symm (Fin.last n))) := by
  intro hsat
  exact (criticalAssignment_sat_pigeonClause_iff pi _).mp hsat (pi.apply_symm_apply _)

/-- The launching fact of the Beame-Pitassi argument: a critical assignment
satisfies a clause of PHP(n+1, n) exactly when that clause is not the pigeon
clause of the left-out pigeon. In particular it falsifies exactly one clause. -/
theorem criticalAssignment_sat_iff {n : ℕ} (pi : Equiv.Perm (Fin (n + 1)))
    {C : Clause} (hC : C ∈ phpCNF n) :
    clauseSat (criticalAssignment n pi) C ↔
      C ≠ pigeonClause n (pi.symm (Fin.last n)) := by
  constructor
  · intro hsat heq
    subst heq
    exact criticalAssignment_falsifies_leftOut pi hsat
  · intro hne
    rcases Finset.mem_union.mp hC with hp | hh
    · simp only [pigeonClauses, Finset.mem_image, Finset.mem_univ, true_and] at hp
      obtain ⟨i, rfl⟩ := hp
      refine (criticalAssignment_sat_pigeonClause_iff pi i).mpr ?_
      intro hlast
      apply hne
      have hi : i = pi.symm (Fin.last n) := by
        rw [← hlast, Equiv.symm_apply_apply]
      rw [hi]
    · exact criticalAssignment_sat_holeClause pi hh

/-- BP96 shape: a critical assignment satisfies the whole pigeonhole family
with the left-out pigeon's clause removed. -/
theorem criticalAssignment_sat_php_erase {n : ℕ} (pi : Equiv.Perm (Fin (n + 1))) :
    cnfSat (criticalAssignment n pi)
      ((phpCNF n).erase (pigeonClause n (pi.symm (Fin.last n)))) := by
  intro C hC
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hC
  exact (criticalAssignment_sat_iff pi hmem).mpr hne

end SATurday.ProofComplexity
