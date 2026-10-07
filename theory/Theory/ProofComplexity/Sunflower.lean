import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# The sunflower lemma (Erdős–Rado) (Ladder Rung R3)

A family of more than `sfBound p ℓ` sets, each of size at most `ℓ`, contains a sunflower
with `p` petals: `p` distinct sets whose pairwise intersections are all equal to one core.

`sfBound p ℓ` satisfies `sfBound p ℓ ≤ (p * ℓ + 1) ^ ℓ`, which is all the clique lower
bound needs.

LOG: R3 Sunflower module (Erdős–Rado)
-/

namespace SATurday.ProofComplexity

open Finset

/-- Size threshold for the sunflower lemma. -/
def sfBound (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | ℓ + 1 => p * (ℓ + 1) * sfBound p ℓ + 1

theorem sfBound_le (p : ℕ) : ∀ ℓ, sfBound p ℓ ≤ (p * ℓ + 1) ^ ℓ := by
  intro ℓ
  induction ℓ with
  | zero => simp [sfBound]
  | succ ℓ ih =>
      simp only [sfBound]
      have h1 : (p * ℓ + 1) ^ ℓ ≤ (p * (ℓ + 1) + 1) ^ ℓ :=
        Nat.pow_le_pow_left (by nlinarith) ℓ
      have h2 : sfBound p ℓ ≤ (p * (ℓ + 1) + 1) ^ ℓ := ih.trans h1
      have h3 : 1 ≤ (p * (ℓ + 1) + 1) ^ ℓ := Nat.one_le_pow _ _ (by omega)
      calc p * (ℓ + 1) * sfBound p ℓ + 1
          ≤ p * (ℓ + 1) * (p * (ℓ + 1) + 1) ^ ℓ + (p * (ℓ + 1) + 1) ^ ℓ := by
            have := Nat.mul_le_mul_left (p * (ℓ + 1)) h2; omega
        _ = (p * (ℓ + 1) + 1) ^ (ℓ + 1) := by ring

/-- A sunflower: pairwise intersections of distinct members all equal `Z`. -/
def IsSunflower {α : Type*} [DecidableEq α] (S : Finset (Finset α)) (Z : Finset α) : Prop :=
  ∀ X ∈ S, ∀ Y ∈ S, X ≠ Y → X ∩ Y = Z

/-- Pairwise disjoint families. -/
def PWDisj {α : Type*} (D : Finset (Finset α)) : Prop :=
  ∀ X ∈ D, ∀ Y ∈ D, X ≠ Y → Disjoint X Y

theorem exists_sunflower {α : Type*} [DecidableEq α] [Nonempty α] (p : ℕ) :
    ∀ (ℓ : ℕ) (F : Finset (Finset α)), (∀ X ∈ F, X.card ≤ ℓ) → sfBound p ℓ < F.card →
      ∃ S ⊆ F, S.card = p ∧ ∃ Z, IsSunflower S Z := by
  intro ℓ
  induction ℓ with
  | zero =>
      intro F hF hcard
      exfalso
      have : F ⊆ {∅} := by
        intro X hX
        rw [Finset.mem_singleton, ← Finset.card_eq_zero]
        exact Nat.le_zero.1 (hF X hX)
      have := Finset.card_le_card this
      simp [sfBound] at hcard
      simp at this
      omega
  | succ ℓ ih =>
      intro F hF hcard
      classical
      -- a largest pairwise disjoint subfamily
      have hne : (F.powerset.filter PWDisj).Nonempty :=
        ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, by intro X hX; simp at hX⟩⟩
      obtain ⟨D, hD, hDmax⟩ := Finset.exists_max_image _ Finset.card hne
      rw [Finset.mem_filter, Finset.mem_powerset] at hD
      obtain ⟨hDF, hDpw⟩ := hD
      by_cases hp : p ≤ D.card
      · obtain ⟨S, hSD, hS⟩ := Finset.exists_subset_card_eq hp
        refine ⟨S, hSD.trans hDF, hS, ∅, fun X hX Y hY hXY => ?_⟩
        exact Finset.disjoint_iff_inter_eq_empty.1 (hDpw X (hSD hX) Y (hSD hY) hXY)
      · push_neg at hp
        set U := D.biUnion id with hU
        have hUcard : U.card ≤ p * (ℓ + 1) := by
          calc U.card ≤ ∑ X ∈ D, (id X).card := Finset.card_biUnion_le
            _ ≤ ∑ _X ∈ D, (ℓ + 1) := Finset.sum_le_sum fun X hX => hF X (hDF hX)
            _ = D.card * (ℓ + 1) := by simp
            _ ≤ p * (ℓ + 1) := Nat.mul_le_mul_right _ hp.le
        set F' := F.filter fun X => X.Nonempty with hF'
        have hF'card : F.card ≤ F'.card + 1 := by
          have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
            (s := F) (fun X : Finset α => X.Nonempty)
          have hsmall : (F.filter fun X => ¬ X.Nonempty).card ≤ 1 := by
            apply Finset.card_le_one.2
            intro X hX Y hY
            simp only [Finset.mem_filter, Finset.not_nonempty_iff_eq_empty] at hX hY
            rw [hX.2, hY.2]
          have hF'eq : F'.card = (F.filter fun X : Finset α => X.Nonempty).card := rfl
          omega
        -- every nonempty member meets `U`
        have hmeet : ∀ X ∈ F', (X ∩ U).Nonempty := by
          intro X hX
          rw [Finset.mem_filter] at hX
          obtain ⟨hXF, hXne⟩ := hX
          by_cases hXD : X ∈ D
          · obtain ⟨x, hx⟩ := hXne
            exact ⟨x, Finset.mem_inter.2 ⟨hx, Finset.mem_biUnion.2 ⟨X, hXD, hx⟩⟩⟩
          · by_contra hdis
            rw [Finset.not_nonempty_iff_eq_empty] at hdis
            have hpw : PWDisj (insert X D) := by
              intro A hA B hB hAB
              rw [Finset.mem_insert] at hA hB
              rcases hA with rfl | hA <;> rcases hB with rfl | hB
              · exact absurd rfl hAB
              · rw [Finset.disjoint_left]
                intro x hxA hxB
                have : x ∈ A ∩ U := Finset.mem_inter.2 ⟨hxA, Finset.mem_biUnion.2 ⟨B, hB, hxB⟩⟩
                rw [hdis] at this; simp at this
              · rw [Finset.disjoint_left]
                intro x hxA hxB
                have : x ∈ B ∩ U := Finset.mem_inter.2 ⟨hxB, Finset.mem_biUnion.2 ⟨A, hA, hxA⟩⟩
                rw [hdis] at this; simp at this
              · exact hDpw A hA B hB hAB
            have := hDmax (insert X D) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2
              (Finset.insert_subset hXF hDF), hpw⟩)
            rw [Finset.card_insert_of_notMem hXD] at this
            omega
        -- pigeonhole on a chosen common element
        let pick : Finset α → α := fun X =>
          if h : (X ∩ U).Nonempty then h.choose else Classical.arbitrary α
        have hpick : ∀ X ∈ F', pick X ∈ X ∩ U := by
          intro X hX
          simp only [pick, dif_pos (hmeet X hX)]
          exact (hmeet X hX).choose_spec
        have hlt : U.card * sfBound p ℓ < F'.card := by
          have h1 : U.card * sfBound p ℓ ≤ p * (ℓ + 1) * sfBound p ℓ :=
            Nat.mul_le_mul_right _ hUcard
          simp only [sfBound] at hcard
          omega
        obtain ⟨u, _, hfib⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
          (f := pick) (fun X hX => (Finset.mem_inter.1 (hpick X hX)).2) hlt
        set G := F'.filter fun X => pick X = u with hG
        have huG : ∀ X ∈ G, u ∈ X := by
          intro X hX
          rw [Finset.mem_filter] at hX
          have := hpick X hX.1
          rw [hX.2] at this
          exact (Finset.mem_inter.1 this).1
        have hinj : Set.InjOn (fun X : Finset α => X.erase u) (G : Set (Finset α)) := by
          intro X hX Y hY hXY
          simp only at hXY
          rw [← Finset.insert_erase (huG X hX), ← Finset.insert_erase (huG Y hY), hXY]
        set Fu := G.image fun X : Finset α => X.erase u with hFu
        have hFucard : Fu.card = G.card := Finset.card_image_of_injOn hinj
        have hFusize : ∀ Y ∈ Fu, Y.card ≤ ℓ := by
          intro Y hY
          obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 hY
          have hXF : X ∈ F := (Finset.mem_filter.1 (Finset.mem_filter.1 hX).1).1
          rw [Finset.card_erase_of_mem (huG X hX)]
          have := hF X hXF
          omega
        obtain ⟨S', hS'F, hS'card, Z', hZ'⟩ := ih Fu hFusize (by omega)
        have huS' : ∀ Y ∈ S', u ∉ Y := by
          intro Y hY
          obtain ⟨X, _, rfl⟩ := Finset.mem_image.1 (hS'F hY)
          exact Finset.notMem_erase u X
        refine ⟨S'.image (insert u), ?_, ?_, insert u Z', ?_⟩
        · intro X hX
          obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 hX
          obtain ⟨X0, hX0, rfl⟩ := Finset.mem_image.1 (hS'F hY)
          rw [Finset.insert_erase (huG X0 hX0)]
          exact (Finset.mem_filter.1 (Finset.mem_filter.1 hX0).1).1
        · rw [Finset.card_image_of_injOn, hS'card]
          intro Y hY Y' hY' h
          rw [← Finset.erase_insert (huS' Y hY), ← Finset.erase_insert (huS' Y' hY'), h]
        · intro X hX Y hY hXY
          obtain ⟨X1, hX1, rfl⟩ := Finset.mem_image.1 hX
          obtain ⟨Y1, hY1, rfl⟩ := Finset.mem_image.1 hY
          have hne : X1 ≠ Y1 := fun h => hXY (by rw [h])
          rw [← Finset.insert_inter_distrib, hZ' X1 hX1 Y1 hY1 hne]

end SATurday.ProofComplexity
