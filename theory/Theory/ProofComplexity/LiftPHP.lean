import Theory.ProofComplexity.LiftDup
import Theory.ProofComplexity.PHPKEval

/-!
# Res(⊕) rank bound for `PHP_n ∘ MAJ₃` (assembly of the lifting warm-up)

The base Duplicator family for `PHP_n`: block sets `C` of size at most `W + 1` together with a
total assignment whose true variables inside `C` form a partial matching. A pigeon clause is
kept alive by sending the pigeon to a hole outside the (at most `W + 1`) holes touched by `C`;
a hole clause by setting one of its variables false. Lifting through `MAJ₃` (`maj3_lifting_rank`)
gives: every dag-like Res(⊕) refutation of `PHP_n ∘ MAJ₃` has a line of rank at least `n - 1`.

LOG: R4 LiftPHP module (PHP base Duplicator and the lifted rank bound)
-/

namespace SATurday.ProofComplexity

namespace RL

noncomputable section

open Classical
open Finset

/-- The matching family for `PHP_n` with width parameter `W`. -/
def phpG (n W : ℕ) (C : Finset ℕ) (β : ℕ → Bool) : Prop :=
  C.card ≤ W + 1 ∧ ∀ v ∈ C, ∀ v' ∈ C, β v = true → β v' = true →
    v = v' ∨ (v / n ≠ v' / n ∧ v % n ≠ v' % n)

theorem phpBase (n W : ℕ) (hW : W + 2 ≤ n) : BaseDup (phpCNF n) W (phpG n W) where
  congr := by
    rintro C β β' hag ⟨hc, hm⟩
    refine ⟨hc, fun v hv v' hv' h1 h2 => hm v hv v' hv' ?_ ?_⟩
    · rw [hag v hv]; exact h1
    · rw [hag v' hv']; exact h2
  mono := by
    rintro C C' β hsub ⟨hc, hm⟩
    exact ⟨(card_le_card hsub).trans hc, fun v hv v' hv' => hm v (hsub hv) v' (hsub hv')⟩
  empty := ⟨fun _ => false, by simp [phpG]⟩
  ext := by
    rintro C β ⟨hc, hm⟩ hcard v
    by_cases hv : v ∈ C
    · refine ⟨β, fun _ _ => rfl, ?_⟩
      rw [Finset.insert_eq_of_mem hv]; exact ⟨hc, hm⟩
    · refine ⟨Function.update β v false, fun w hw => ?_, ?_, ?_⟩
      · have : w ≠ v := fun h => hv (h ▸ hw)
        simp [Function.update_of_ne this]
      · exact (card_insert_le _ _).trans (by omega)
      · intro x hx x' hx' h1 h2
        have hxv : x ≠ v := by
          rintro rfl; simp at h1
        have hxv' : x' ≠ v := by
          rintro rfl; simp at h2
        rw [Function.update_of_ne hxv] at h1
        rw [Function.update_of_ne hxv'] at h2
        exact hm x ((mem_insert.1 hx).resolve_left hxv) x' ((mem_insert.1 hx').resolve_left hxv') h1 h2
  sat := by
    rintro C β ⟨hc, hm⟩ D hD
    have hn : 0 < n := by omega
    rcases mem_phpCNF hD with ⟨i, rfl⟩ | ⟨i, i', j, hii, rfl⟩
    · -- pigeon clause
      by_cases hA : ∃ v ∈ C, β v = true ∧ v / n = i.val
      · obtain ⟨v, hvC, hvt, hvi⟩ := hA
        refine ⟨β, fun _ _ => rfl, ⟨pvar n i ⟨v % n, Nat.mod_lt _ hn⟩, true⟩, ?_, ?_⟩
        · exact mem_image.2 ⟨⟨v % n, Nat.mod_lt _ hn⟩, mem_univ _, rfl⟩
        · have : pvar n i ⟨v % n, Nat.mod_lt _ hn⟩ = v := by
            unfold pvar; simp only; rw [← hvi]; exact Nat.div_add_mod' v n
          show β _ = true
          rw [this]; exact hvt
      · have hcard : (C.image (· % n)).card < n := by
          have := card_image_le (s := C) (f := (· % n))
          omega
        have : ∃ j : Fin n, j.val ∉ C.image (· % n) := by
          by_contra hall
          push Not at hall
          have hsub : range n ⊆ C.image (· % n) := fun j hj =>
            hall ⟨j, mem_range.1 hj⟩
          have := card_le_card hsub
          rw [card_range] at this; omega
        obtain ⟨j, hj⟩ := this
        refine ⟨Function.update β (pvar n i j) true, fun w hw => ?_, ⟨pvar n i j, true⟩, ?_, ?_⟩
        · have : w ≠ pvar n i j := by
            rintro rfl
            apply hj
            exact mem_image.2 ⟨_, hw, pvar_mod n⟩
          simp [Function.update_of_ne this]
        · exact mem_image.2 ⟨j, mem_univ _, rfl⟩
        · show Function.update β (pvar n i j) true (pvar n i j) = true
          simp
    · -- hole clause
      have hdiv : pvar n i j / n ≠ pvar n i' j / n := by
        rw [pvar_div, pvar_div]; exact fun h => absurd (Fin.ext h) (ne_of_lt hii)
      have hmod : pvar n i j % n = pvar n i' j % n := by rw [pvar_mod, pvar_mod]
      have hne : pvar n i j ≠ pvar n i' j := fun h => hdiv (by rw [h])
      by_cases hp : pvar n i j ∈ C
      · by_cases hb : β (pvar n i j) = false
        · refine ⟨β, fun _ _ => rfl, ⟨pvar n i j, false⟩, by simp, hb⟩
        · have hbt : β (pvar n i j) = true := by simpa using hb
          by_cases hp' : pvar n i' j ∈ C
          · have hb' : β (pvar n i' j) = false := by
              by_contra h'
              have h't : β (pvar n i' j) = true := by simpa using h'
              rcases hm _ hp _ hp' hbt h't with h | ⟨-, h⟩
              · exact hne h
              · exact h hmod
            exact ⟨β, fun _ _ => rfl, ⟨pvar n i' j, false⟩, by simp, hb'⟩
          · refine ⟨Function.update β (pvar n i' j) false, fun w hw => ?_,
              ⟨pvar n i' j, false⟩, by simp, ?_⟩
            · have : w ≠ pvar n i' j := fun h => hp' (h ▸ hw)
              simp [Function.update_of_ne this]
            · show Function.update β (pvar n i' j) false (pvar n i' j) = false
              simp
      · refine ⟨Function.update β (pvar n i j) false, fun w hw => ?_,
          ⟨pvar n i j, false⟩, by simp, ?_⟩
        · have : w ≠ pvar n i j := fun h => hp (h ▸ hw)
          simp [Function.update_of_ne this]
        · show Function.update β (pvar n i j) false (pvar n i j) = false
          simp

/-- **Res(⊕) rank bound for `PHP_n ∘ MAJ₃`**: every dag-like Res(⊕) refutation of
`PHP_n ∘ MAJ₃` contains a line of rank at least `n - 1`. -/
theorem php_maj3_rank (n : ℕ) (hn : 2 ≤ n) {P : Finset LClause} (hD : Der (liftedPHP n) P)
    (h0 : (∅ : LClause) ∈ P) : ∃ L ∈ P, n - 2 < rk L :=
  maj3_lifting_rank (W := n - 2) (phpBase n (n - 2) (by omega)) hD h0

end

end RL

end SATurday.ProofComplexity
