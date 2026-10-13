import Theory.ProofComplexity.PCLocalThm

/-!
# Alekhnovich-Razborov: support of a term, Lemmas 3.11 and 3.12 (Ladder Rung R4, AR-A, layer 6)

Rows `i : ι` carry column sets `J i` and root sets `Z i` of Boolean points (local to `J i`, `ℓ`-immune).
`bdry J I` is the set of columns with exactly one one in the rows `I`.  `Der t I` is a derivation of the row
set `I` one row at a time, a row `i` being added when more than `ℓ/4` of its columns lie in
`t ∪ ⋃_{I} J` (Definition 3.10 of AR, with a strict inequality); `Sup t` is the largest derivable set.
`Sup_card` is Lemma 3.11, `rdc_Sup_eq` is Lemma 3.12.

LOG: R4 AR-A Sup lemmas
-/

namespace SATurday.ProofComplexity.PCL

open Finset

noncomputable section
open Classical

variable {F : Type} [Field F] {ι : Type} [Fintype ι]

/-- Columns with exactly one `1` in the rows `I`. -/
def bdry (J : ι → Finset ℕ) (I : Finset ι) : Finset ℕ :=
  (I.biUnion J).filter fun j => (I.filter fun i => j ∈ J i).card = 1

/-- Roots common to all rows of `I`. -/
def ZI (Z : ι → Set (Set ℕ)) (I : Finset ι) : Set (Set ℕ) := {a | ∀ i ∈ I, a ∈ Z i}

/-- Hypotheses of AR Theorem 3.8 (semantic form). -/
structure Good (F : Type) [Field F] {ι : Type} (J : ι → Finset ℕ) (Z : ι → Set (Set ℕ))
    (ℓ r : ℕ) (s c : ℝ) : Prop where
  loc : ∀ i (a b : Set ℕ), (∀ x ∈ J i, (x ∈ a ↔ x ∈ b)) → a ∈ Z i → b ∈ Z i
  imm : ∀ i (g : ML F), g ≠ 0 → (∀ a ∈ Z i, ev a g = 0) → ℓ ≤ deg g
  wt : ∀ i, ((J i).card : ℝ) ≤ s
  exp : ∀ I : Finset ι, I.card ≤ r → c * (I.card : ℝ) ≤ ((bdry J I).card : ℝ)
  hr : 1 ≤ r
  hl : 1 ≤ ℓ
  hsc : 4 * (s - c) < ℓ

/-- The degree bound `r (ℓ/4 - (s - c))`. -/
def Dbd (ℓ r : ℕ) (s c : ℝ) : ℝ := r * ((ℓ : ℝ) / 4 - (s - c))

variable (J : ι → Finset ℕ) (ℓ : ℕ)

/-- Derivations of row sets (Definition 3.10). -/
inductive Der (t : Finset ℕ) : Finset ι → Prop
  | nil : Der t ∅
  | cons {I : Finset ι} (i : ι) : Der t I → i ∉ I →
      ℓ < 4 * (J i ∩ (t ∪ I.biUnion J)).card → Der t (insert i I)

variable {J ℓ}

theorem Der.mono {t t' : Finset ℕ} (h : t ⊆ t') {I : Finset ι} (hI : Der J ℓ t I) : Der J ℓ t' I := by
  induction hI with
  | nil => exact Der.nil
  | cons i _ hi hc ih =>
    refine Der.cons i ih hi (lt_of_lt_of_le hc ?_)
    exact Nat.mul_le_mul_left _ (Finset.card_le_card
      (Finset.inter_subset_inter_left (Finset.union_subset_union_left h)))

theorem Der.card_exists {t : Finset ℕ} {I : Finset ι} (hI : Der J ℓ t I) :
    ∀ k, k ≤ I.card → ∃ I', Der J ℓ t I' ∧ I'.card = k := by
  induction hI with
  | nil => intro k hk; exact ⟨∅, Der.nil, by simp at hk ⊢; omega⟩
  | @cons I i hI hi hc ih =>
    intro k hk
    rw [Finset.card_insert_of_notMem hi] at hk
    rcases Nat.lt_or_ge k (I.card + 1) with h | h
    · exact ih k (by omega)
    · refine ⟨insert i I, Der.cons i hI hi hc, ?_⟩
      rw [Finset.card_insert_of_notMem hi]; omega

theorem exists_maxDer (t : Finset ℕ) : ∃ I, Der J ℓ t I ∧ ∀ I', Der J ℓ t I' → I'.card ≤ I.card := by
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (Der J ℓ t)) Finset.card
    ⟨∅, by simp [Der.nil]⟩
  exact ⟨I, (Finset.mem_filter.1 hI).2, fun I' h' => hmax I' (by simpa using h')⟩

variable (J ℓ) in
/-- The support of the term `t`: the largest derivable set of rows. -/
def Sup (t : Finset ℕ) : Finset ι := Classical.choose (exists_maxDer (J := J) (ℓ := ℓ) t)

theorem Sup_der (t : Finset ℕ) : Der J ℓ t (Sup J ℓ t) :=
  (Classical.choose_spec (exists_maxDer (J := J) (ℓ := ℓ) t)).1

theorem Sup_max (t : Finset ℕ) {I : Finset ι} (h : Der J ℓ t I) : I.card ≤ (Sup J ℓ t).card :=
  (Classical.choose_spec (exists_maxDer (J := J) (ℓ := ℓ) t)).2 I h

theorem Sup_closed (t : Finset ℕ) (i : ι)
    (h : ℓ < 4 * (J i ∩ (t ∪ (Sup J ℓ t).biUnion J)).card) : i ∈ Sup J ℓ t := by
  by_contra hi
  have := Sup_max t (Der.cons i (Sup_der t) hi h)
  rw [Finset.card_insert_of_notMem hi] at this
  omega

/-- Everything derivable from a term contained in `t' ∪ ⋃_{Sup t'} J` lies in `Sup t'`. -/
theorem Der_sub_Sup {t t' : Finset ℕ} (h : t ⊆ t' ∪ (Sup J ℓ t').biUnion J) {I : Finset ι}
    (hI : Der J ℓ t I) : I ⊆ Sup J ℓ t' := by
  induction hI with
  | nil => simp
  | cons i _ hi hc ih =>
    intro k hk
    rcases Finset.mem_insert.1 hk with rfl | hk
    · refine Sup_closed t' k (lt_of_lt_of_le hc ?_)
      refine Nat.mul_le_mul_left _ (Finset.card_le_card (Finset.inter_subset_inter_left ?_))
      exact Finset.union_subset h ((Finset.biUnion_subset_biUnion_of_subset_left J ih).trans Finset.subset_union_right)
    · exact ih hk

theorem Sup_sub_of {t t' : Finset ℕ} (h : t ⊆ t' ∪ (Sup J ℓ t').biUnion J) :
    Sup J ℓ t ⊆ Sup J ℓ t' := Der_sub_Sup h (Sup_der t)

theorem Sup_mono {t t' : Finset ℕ} (h : t ⊆ t') : Sup J ℓ t ⊆ Sup J ℓ t' :=
  Sup_sub_of (h.trans Finset.subset_union_left)

theorem Der_empty {I : Finset ι} (h : Der J ℓ (∅ : Finset ℕ) I) : I = ∅ := by
  induction h with
  | nil => rfl
  | cons i _ hi hc ih =>
    subst ih
    simp at hc

theorem Sup_empty : Sup J ℓ (∅ : Finset ℕ) = ∅ := Der_empty (Sup_der ∅)

end

end SATurday.ProofComplexity.PCL
