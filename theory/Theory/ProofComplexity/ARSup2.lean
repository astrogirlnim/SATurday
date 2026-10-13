import Theory.ProofComplexity.ARSup

/-!
# Alekhnovich-Razborov Lemma 3.11 (Ladder Rung R4, AR-A, layer 7)

LOG: R4 AR-A Lemma 3.11
-/

namespace SATurday.ProofComplexity.PCL

open Finset

noncomputable section
open Classical

variable {F : Type} [Field F] {ι : Type} [Fintype ι] {J : ι → Finset ℕ} {ℓ : ℕ}

theorem bdry_insert_sub (t : Finset ℕ) {I : Finset ι} {i : ι} (hi : i ∉ I) :
    bdry J (insert i I) \ t ⊆ (bdry J I \ t) ∪ (J i \ (t ∪ I.biUnion J)) := by
  intro j hj
  rw [Finset.mem_sdiff] at hj
  obtain ⟨hjb, hjt⟩ := hj
  unfold bdry at hjb
  rw [Finset.mem_filter] at hjb
  obtain ⟨_, hcard⟩ := hjb
  by_cases hji : j ∈ J i
  · refine Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hji, ?_⟩)
    intro hmem
    rcases Finset.mem_union.1 hmem with h | h
    · exact hjt h
    · obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.1 h
      have hsub : ({i, k} : Finset ι) ⊆ (insert i I).filter (fun m => j ∈ J m) := by
        intro m hm
        rcases Finset.mem_insert.1 hm with rfl | hm
        · exact Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, hji⟩
        · rw [Finset.mem_singleton] at hm
          subst hm
          exact Finset.mem_filter.2 ⟨Finset.mem_insert_of_mem hk, hjk⟩
      have hne : i ≠ k := fun h => hi (h ▸ hk)
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hne, hcard] at this
      omega
  · refine Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨?_, hjt⟩)
    rw [Finset.filter_insert, if_neg hji] at hcard
    unfold bdry
    rw [Finset.mem_filter]
    refine ⟨?_, hcard⟩
    obtain ⟨k, hk⟩ := Finset.card_pos.1 (by omega : 0 < (I.filter (fun m => j ∈ J m)).card)
    rw [Finset.mem_filter] at hk
    exact Finset.mem_biUnion.2 ⟨k, hk.1, hk.2⟩

theorem der_bdry {s : ℝ} (hwt : ∀ i, ((J i).card : ℝ) ≤ s) {t : Finset ℕ} {I : Finset ι}
    (h : Der J ℓ t I) :
    (((bdry J I \ t).card : ℝ) ≤ I.card * (s - ℓ / 4)) ∧
      (I.Nonempty → ((bdry J I \ t).card : ℝ) < I.card * (s - ℓ / 4)) := by
  induction h with
  | nil => simp [bdry]
  | @cons I i hI hi hc ih =>
    have hsub := Finset.card_le_card (bdry_insert_sub (J := J) t hi)
    have hu := Finset.card_union_le (bdry J I \ t) (J i \ (t ∪ I.biUnion J))
    have hsplit := Finset.card_sdiff_add_card_inter (J i) (t ∪ I.biUnion J)
    have hw := hwt i
    have hc' : (ℓ : ℝ) < 4 * ((J i ∩ (t ∪ I.biUnion J)).card : ℝ) := by exact_mod_cast hc
    have hsplit' : (((J i \ (t ∪ I.biUnion J)).card : ℝ) + ((J i ∩ (t ∪ I.biUnion J)).card : ℝ))
        = ((J i).card : ℝ) := by exact_mod_cast hsplit
    have h1 : (((bdry J (insert i I) \ t).card : ℕ) : ℝ) ≤
        (((bdry J I \ t).card : ℕ) : ℝ) + (((J i \ (t ∪ I.biUnion J)).card : ℕ) : ℝ) := by
      exact_mod_cast hsub.trans hu
    have hcard : ((insert i I).card : ℝ) = (I.card : ℝ) + 1 := by
      rw [Finset.card_insert_of_notMem hi]; push_cast; ring
    have hstrict : (((bdry J (insert i I) \ t).card : ℕ) : ℝ) < ((insert i I).card : ℝ) * (s - ℓ / 4) := by
      rw [hcard]
      have := ih.1
      nlinarith
    exact ⟨hstrict.le, fun _ => hstrict⟩

/-- **Lemma 3.11**: the support of a term of degree at most `r (ℓ/4 - (s-c))` has fewer than `r` rows. -/
theorem Sup_card_of_der {Z : ι → Set (Set ℕ)} {r : ℕ} {s c : ℝ} (G : Good F J Z ℓ r s c)
    {t : Finset ℕ} (ht : (t.card : ℝ) ≤ Dbd ℓ r s c) {I : Finset ι} (hI : Der J ℓ t I) :
    I.card < r := by
  by_contra hcon
  push Not at hcon
  obtain ⟨I', hI', hcard⟩ := hI.card_exists r hcon
  have hne : I'.Nonempty := Finset.card_pos.1 (by have := G.hr; omega)
  have h1 := G.exp I' (by omega)
  have h2 := (der_bdry G.wt hI').2 hne
  have h3 := Finset.card_le_card_sdiff_add_card (s := bdry J I') (t := t)
  have h3' : (((bdry J I').card : ℕ) : ℝ) ≤ (((bdry J I' \ t).card : ℕ) : ℝ) + (t.card : ℝ) := by
    exact_mod_cast h3
  rw [hcard] at h1 h2
  unfold Dbd at ht
  nlinarith

theorem Sup_card {Z : ι → Set (Set ℕ)} {r : ℕ} {s c : ℝ} (G : Good F J Z ℓ r s c)
    {t : Finset ℕ} (ht : (t.card : ℝ) ≤ Dbd ℓ r s c) : (Sup J ℓ t).card < r :=
  Sup_card_of_der G ht (Sup_der t)

end

end SATurday.ProofComplexity.PCL
