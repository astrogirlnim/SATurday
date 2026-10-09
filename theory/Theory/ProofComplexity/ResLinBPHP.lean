import Theory.ProofComplexity.ResLinDag

/-!
# Rank of linear clauses and the bit pigeonhole principle (Ladder Rung R4, Phase 2 foundations)

* `rk L`: the rank of a linear clause, the dimension of the `F₂` span of its linear forms
  (Efremenko–Garlik–Itsykson, ECCC TR23-187, section 1.3 and 2: `rk(¬C)`).
* `bphpCNF l m`: the binary (bit) pigeonhole principle with `m` pigeons and `2^l` holes. Pigeon `i`
  is the `l` bits `x_{i,0..l-1}` (variable `i*l+j`); for `i<k` and every `α ∈ {0,1}^l` the clause
  "pigeon `i` is not at `α`, or pigeon `k` is not at `α`" (`2l` literals). It is unsatisfiable
  once `m > 2^l` (`bphpCNF_unsat`).

LOG: R4 ResLinBPHP module (rank measure, bit PHP CNF)
-/

namespace SATurday.ProofComplexity

namespace RL

noncomputable section

open Classical
open Finset

/-- The coefficient vector of a linear form `∑_{w∈S} x_w` over `F₂`. -/
def ind (S : Finset ℕ) : ℕ → ZMod 2 := fun w => if w ∈ S then 1 else 0

/-- Rank of a linear clause: dimension of the span of the forms occurring in it. -/
def rk (L : LClause) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (((L.image fun e => ind e.1) : Finset (ℕ → ZMod 2)) : Set (ℕ → ZMod 2)))

theorem rk_le_card (L : LClause) : rk L ≤ L.card := by
  unfold rk
  exact (finrank_span_finset_le_card _).trans card_image_le

theorem rk_empty : rk ∅ = 0 := by
  have := rk_le_card ∅
  simpa using this

theorem rk_mono {L L' : LClause} (h : L ⊆ L') : rk L ≤ rk L' := by
  unfold rk
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  exact_mod_cast image_subset_image h

/-- The bit pigeonhole CNF: `m` pigeons, each an `l` bit string, pairwise distinct. -/
def bphpCNF (l m : ℕ) : CNF :=
  ((univ : Finset (Fin m × Fin m × (Fin l → Bool))).filter fun t => t.1 < t.2.1).image fun t =>
    (univ : Finset (Fin l)).image (fun j => (⟨t.1.val * l + j.val, !(t.2.2 j)⟩ : Literal)) ∪
    (univ : Finset (Fin l)).image (fun j => (⟨t.2.1.val * l + j.val, !(t.2.2 j)⟩ : Literal))

/-- Pigeonhole: with more than `2^l` pigeons the bit pigeonhole CNF is unsatisfiable. -/
theorem bphpCNF_unsat (l m : ℕ) (h : 2 ^ l < m) : ¬ Satisfiable (bphpCNF l m) := by
  rintro ⟨a, ha⟩
  let s : Fin m → (Fin l → Bool) := fun i j => a (i.val * l + j.val)
  have hc : Fintype.card (Fin l → Bool) < Fintype.card (Fin m) := by simpa using h
  obtain ⟨i, k, hik, hs⟩ := Fintype.exists_ne_map_eq_of_card_lt s hc
  -- orient so that the first pigeon has the smaller index
  have key : ∀ i k : Fin m, i < k → s i = s k → False := by
    intro i k hlt heq
    let C : Clause :=
      (univ : Finset (Fin l)).image (fun j => (⟨i.val * l + j.val, !(s i j)⟩ : Literal)) ∪
      (univ : Finset (Fin l)).image (fun j => (⟨k.val * l + j.val, !(s i j)⟩ : Literal))
    have hmem : C ∈ bphpCNF l m := by
      unfold bphpCNF
      exact mem_image.2 ⟨(i, k, s i), by simp [hlt], rfl⟩
    obtain ⟨lit, hl, hsat⟩ := ha C hmem
    simp only [C, mem_union, mem_image, mem_univ, true_and] at hl
    unfold litSat at hsat
    rcases hl with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have : s i j = a (i.val * l + j.val) := rfl
      simp only at hsat
      rw [← this] at hsat
      cases hb : s i j <;> simp [hb] at hsat
    · have : s k j = a (k.val * l + j.val) := rfl
      simp only at hsat
      have h2 : s i j = s k j := congrFun heq j
      rw [← this, ← h2] at hsat
      cases hb : s i j <;> simp [hb] at hsat
  rcases lt_or_gt_of_ne hik with hlt | hlt
  · exact key i k hlt hs
  · exact key k i hlt hs.symm

/-- Non vacuity for the dag-like lower bound target: the bit pigeonhole CNF with more than `2^l`
pigeons has a dag-like `Res(⊕)` refutation (of some finite size). -/
theorem bphp_dagRefutable (l m : ℕ) (h : 2 ^ l < m) :
    ∃ s, DagRefutes (↑(bphpCNF l m) : Set Clause) s :=
  dagRefutes_of_unsat (bphpCNF_unsat l m h)

end

end RL

end SATurday.ProofComplexity
