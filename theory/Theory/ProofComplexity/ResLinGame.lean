import Theory.ProofComplexity.ResLinBPHP

/-!
# Duplicator strategies for Res(⊕) pebble games (Ladder Rung R4, Phase 2)

Following Alekseev–Itsykson (ECCC TR24-128, Lemma 3.3, after Atserias–Dalmau): a Duplicator
winning family `H` of linear systems for the `(W+1)`-pebble Res(⊕) game on a CNF rules out every
dag-like Res(⊕) refutation all of whose lines have rank at most `W`. Linear systems are
`LClause`s read as conjunctions of equations; the system `neg L` is the negation of the clause `L`.

LOG: R4 ResLinGame module (Duplicator strategies exclude bounded rank refutations)
-/

namespace SATurday.ProofComplexity

namespace RL

noncomputable section

open Classical
open Finset

/-- Solutions of a linear system. -/
def satS (Φ : LClause) (x : ℕ → ZMod 2) : Prop := ∀ e ∈ Φ, lf e.1 x = e.2

/-- The system equivalent to the negation of the clause `L`. -/
def neg (L : LClause) : LClause := L.image fun e => (e.1, e.2 + 1)

theorem z2_ne_iff : ∀ v b : ZMod 2, v ≠ b ↔ v = b + 1 := by decide

theorem lsatL_iff_not_satS_neg (x : ℕ → ZMod 2) (L : LClause) : lsatL x L ↔ ¬ satS (neg L) x := by
  unfold lsatL satS neg
  constructor
  · rintro ⟨e, he, hv⟩ hs
    have := hs (e.1, e.2 + 1) (mem_image.2 ⟨e, he, rfl⟩)
    exact (z2_ne_iff _ _).2 this hv
  · intro h
    by_contra hc
    apply h
    intro e' he'
    obtain ⟨e, he, rfl⟩ := mem_image.1 he'
    exact (z2_ne_iff _ _).1 fun hv => hc ⟨e, he, hv⟩

theorem rk_neg (L : LClause) : rk L = rk (neg L) := by
  unfold rk neg
  rw [image_image]
  rfl

/-- A Duplicator winning strategy in the `(W+1)`-pebble Res(⊕) game on the CNF `Ax`
(Alekseev–Itsykson section 3). -/
structure Duplicator (Ax : Set Clause) (W : ℕ) (H : Set LClause) : Prop where
  empty : (∅ : LClause) ∈ H
  sat : ∀ F ∈ H, ∀ C ∈ Ax, ∃ x, satS F x ∧ ¬ cfalse x C
  rank : ∀ F ∈ H, rk F ≤ W + 1
  imp : ∀ F ∈ H, ∀ G : LClause, (∀ x, satS F x → satS G x) → G ∈ H
  ext : ∀ F ∈ H, rk F ≤ W → ∀ f : Finset ℕ, ∃ a : ZMod 2, insert (f, a) F ∈ H

theorem z2_not_succ : ∀ a b : ZMod 2, b ≠ a + 1 → b = a + 1 + 1 := by decide

theorem key_res {x : ℕ → ZMod 2} {C E L1 : LClause} {f : Finset ℕ} {a : ZMod 2}
    (i1 : Imp L1 (insert (f, a) C)) (hf : lf f x = a + 1) (hCE : C ⊆ E) (hE : satS (neg E) x) :
    satS (neg L1) x := by
  have : ¬ lsatL x L1 := by
    intro h
    obtain ⟨e, he, hv⟩ := i1 x h
    rcases mem_insert.1 he with rfl | he
    · have hv' : lf f x = a := hv
      rw [hf] at hv'; exact z2_succ_ne a hv'
    · exact (lsatL_iff_not_satS_neg x E).1 ⟨e, hCE he, hv⟩ hE
  by_contra hn
  exact this ((lsatL_iff_not_satS_neg x _).2 hn)

theorem der_no_neg {Ax : Set Clause} {W : ℕ} {H : Set LClause} (hH : Duplicator Ax W H)
    {P : Finset LClause} (hD : Der Ax P) (hr : ∀ L ∈ P, rk L ≤ W) : ∀ L ∈ P, neg L ∉ H := by
  induction hD with
  | empty => simp
  | @add P L hD hs ih =>
    have ihP := ih (fun L' hL' => hr L' (mem_insert_of_mem hL'))
    intro L' hL'
    rcases mem_insert.1 hL' with rfl | hL'
    · intro hmem
      cases hs with
      | ax hC =>
        obtain ⟨x, hx, hnc⟩ := hH.sat _ hmem _ hC
        exact ((lsatL_iff_not_satS_neg x _).1 ((lsatL_ofClause x _).2 hnc)) hx
      | @weak L0 _ h0 hi =>
        refine ihP L0 h0 (hH.imp _ hmem _ fun x hx => ?_)
        by_contra hn
        exact (lsatL_iff_not_satS_neg x _).1 (hi x ((lsatL_iff_not_satS_neg x _).2 hn)) hx
      | @res L1 L2 C D f a h1 h2 i1 i2 =>
        have hrk : rk (neg (C ∪ D)) ≤ W := by
          rw [← rk_neg]; exact hr _ (mem_insert_self _ _)
        obtain ⟨b, hb⟩ := hH.ext _ hmem hrk f
        have hsat : ∀ x, satS (insert (f, b) (neg (C ∪ D))) x →
            lf f x = b ∧ satS (neg (C ∪ D)) x := fun x hx =>
          ⟨hx _ (mem_insert_self _ _), fun e he => hx _ (mem_insert_of_mem he)⟩
        by_cases hba : b = a + 1
        · refine ihP L1 h1 (hH.imp _ hb _ fun x hx => ?_)
          obtain ⟨hf, hE⟩ := hsat x hx
          exact key_res i1 (hba ▸ hf) subset_union_left hE
        · have hb' : b = a + 1 + 1 := z2_not_succ a b hba
          refine ihP L2 h2 (hH.imp _ hb _ fun x hx => ?_)
          obtain ⟨hf, hE⟩ := hsat x hx
          exact key_res i2 (hb' ▸ hf) subset_union_right hE
    · exact ihP L' hL'

/-- **Duplicator strategies exclude bounded rank refutations** (Alekseev–Itsykson, Lemma 3.3):
no dag-like Res(⊕) refutation of the CNF `Ax` has all lines of rank at most `W`. -/
theorem duplicator_no_refutation {Ax : Set Clause} {W : ℕ} {H : Set LClause}
    (hH : Duplicator Ax W H) {P : Finset LClause} (hD : Der Ax P) (hr : ∀ L ∈ P, rk L ≤ W) :
    (∅ : LClause) ∉ P := by
  intro h0
  apply der_no_neg hH hD hr ∅ h0
  have : neg (∅ : LClause) = ∅ := by simp [neg]
  rw [this]; exact hH.empty

end

end RL

end SATurday.ProofComplexity
