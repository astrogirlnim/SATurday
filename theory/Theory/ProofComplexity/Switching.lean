import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# Håstad's switching lemma (Ladder Rung R4, 1B.1 and 1B.2)

Restrictions `ρ : Fin n → Option Bool` (`none` is a free variable), DNFs as lists of terms
(finite sets of literals `(i, b)`, true when `x_i = b`), and the depth of the canonical
decision tree of `F|ρ`: take the first term not falsified by `ρ`; if it is satisfied the
depth is `0`, otherwise query its free variables `S` and continue on every answer.

LOG: R4 Switching module (restrictions, canonical decision trees)
-/

namespace SATurday.ProofComplexity

open Finset

noncomputable section

open Classical

variable {n : ℕ}

/-- A restriction: `none` is a free (starred) variable. -/
abbrev Rst (n : ℕ) := Fin n → Option Bool

/-- A term: a set of literals `(i, b)`, the literal being true when `x_i = b`. -/
abbrev Term (n : ℕ) := Finset (Fin n × Bool)

/-- A DNF: an ordered list of terms. -/
abbrev DNF (n : ℕ) := List (Term n)

/-- Number of free variables. -/
def numStars (ρ : Rst n) : ℕ := (Finset.univ.filter fun i => ρ i = none).card

/-- `ρ` falsifies a literal of `T`. -/
def Falsified (ρ : Rst n) (T : Term n) : Prop := ∃ l ∈ T, ρ l.1 = some (!l.2)

/-- `ρ` satisfies every literal of `T`. -/
def Satisfied (ρ : Rst n) (T : Term n) : Prop := ∀ l ∈ T, ρ l.1 = some l.2

/-- Free variables of `T` under `ρ`. -/
def freeVars (ρ : Rst n) (T : Term n) : Finset (Fin n) :=
  (T.filter fun l => ρ l.1 = none).image Prod.fst

/-- First term not falsified by `ρ`. -/
def firstLive (ρ : Rst n) (F : DNF n) : Option (Term n) := F.find? fun T => ¬ Falsified ρ T

/-- Set the variables of `S` to the values of `α`. -/
def setOn (ρ : Rst n) (S : Finset (Fin n)) (α : Fin n → Bool) : Rst n :=
  fun i => if i ∈ S then some (α i) else ρ i

theorem freeVars_nonempty {ρ : Rst n} {T : Term n} (h1 : ¬ Falsified ρ T)
    (h2 : ¬ Satisfied ρ T) : (freeVars ρ T).Nonempty := by
  unfold Satisfied at h2
  push_neg at h2
  obtain ⟨⟨i, c⟩, hl, hne⟩ := h2
  have : ρ i = none := by
    cases h : ρ i with
    | none => rfl
    | some b =>
        exfalso
        by_cases hb : b = c
        · exact hne (by rw [h, hb])
        · exact h1 ⟨(i, c), hl, by rw [h]; cases b <;> cases c <;> simp_all⟩
  exact ⟨i, Finset.mem_image.2 ⟨(i, c), Finset.mem_filter.2 ⟨hl, this⟩, rfl⟩⟩

theorem freeVars_none {ρ : Rst n} {T : Term n} {i : Fin n} (h : i ∈ freeVars ρ T) :
    ρ i = none := by
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 h
  exact (Finset.mem_filter.1 hl).2

theorem numStars_setOn_lt {ρ : Rst n} {S : Finset (Fin n)} (hS : S.Nonempty)
    (hfree : ∀ i ∈ S, ρ i = none) (α : Fin n → Bool) :
    numStars (setOn ρ S α) < numStars ρ := by
  unfold numStars setOn
  apply Finset.card_lt_card
  refine ⟨fun i hi => ?_, fun h => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_cases h : i ∈ S <;> simp_all
  · obtain ⟨i, hi⟩ := hS
    have := h (Finset.mem_filter.2 ⟨Finset.mem_univ _, hfree i hi⟩)
    simp [hi] at this

/-- Depth of the canonical decision tree of `F|ρ`. -/
def cdtDepth (F : DNF n) : Rst n → ℕ
  | ρ => match h : firstLive ρ F with
    | none => 0
    | some T =>
        if hs : Satisfied ρ T then 0
        else (freeVars ρ T).card +
          Finset.univ.sup fun α : Fin n → Bool => cdtDepth F (setOn ρ (freeVars ρ T) α)
termination_by ρ => numStars ρ
decreasing_by
  have hT : ¬ Falsified ρ T := by
    have := List.find?_some h
    simpa using this
  exact numStars_setOn_lt (freeVars_nonempty hT hs) (fun i hi => freeVars_none hi) α

/-! ## Widths, consistency and basic restriction algebra -/

/-- Width of a DNF (maximum term size), as a bound. -/
def WidthLe (F : DNF n) (w : ℕ) : Prop := ∀ T ∈ F, T.card ≤ w

/-- A term without complementary literals. -/
def Consistent (T : Term n) : Prop := ∀ i, ¬ ((i, true) ∈ T ∧ (i, false) ∈ T)

/-- `ρ'` extends `ρ`. -/
def Ext (ρ ρ' : Rst n) : Prop := ∀ i b, ρ i = some b → ρ' i = some b

/-- Free the variables of `S`. -/
def unsetOn (ρ : Rst n) (S : Finset (Fin n)) : Rst n := fun i => if i ∈ S then none else ρ i

/-- The free set of a restriction. -/
def freeSet (ρ : Rst n) : Finset (Fin n) := Finset.univ.filter fun i => ρ i = none

theorem numStars_eq (ρ : Rst n) : numStars ρ = (freeSet ρ).card := rfl

theorem freeSet_setOn (ρ : Rst n) (S : Finset (Fin n)) (α : Fin n → Bool) :
    freeSet (setOn ρ S α) = freeSet ρ \ S := by
  ext i; by_cases h : i ∈ S <;> simp [freeSet, setOn, h]

theorem numStars_setOn_sub {ρ : Rst n} {S : Finset (Fin n)} (hS : ∀ i ∈ S, ρ i = none)
    (α : Fin n → Bool) : numStars (setOn ρ S α) = numStars ρ - S.card := by
  rw [numStars_eq, numStars_eq, freeSet_setOn, Finset.card_sdiff_of_subset]
  intro i hi; simp [freeSet, hS i hi]

theorem numStars_setOn_fixed {ρ : Rst n} {S : Finset (Fin n)} (hS : ∀ i ∈ S, ρ i ≠ none)
    (α : Fin n → Bool) : numStars (setOn ρ S α) = numStars ρ := by
  rw [numStars_eq, numStars_eq, freeSet_setOn, Finset.sdiff_eq_self_of_disjoint]
  rw [Finset.disjoint_left]
  intro i hi hiS; exact hS i hiS (by simpa [freeSet] using hi)

theorem setOn_setOn (ρ : Rst n) (S : Finset (Fin n)) (α β : Fin n → Bool) :
    setOn (setOn ρ S α) S β = setOn ρ S β := by
  funext i; by_cases h : i ∈ S <;> simp [setOn, h]

theorem setOn_self {ρ : Rst n} {S : Finset (Fin n)} {α : Fin n → Bool}
    (h : ∀ i ∈ S, ρ i = some (α i)) : setOn ρ S α = ρ := by
  funext i; by_cases hi : i ∈ S <;> simp [setOn, hi, h]

theorem unsetOn_setOn {ρ : Rst n} {S : Finset (Fin n)} (hS : ∀ i ∈ S, ρ i = none)
    (α : Fin n → Bool) : unsetOn (setOn ρ S α) S = ρ := by
  funext i; by_cases hi : i ∈ S <;> simp [setOn, unsetOn, hi, hS]

theorem ext_refl (ρ : Rst n) : Ext ρ ρ := fun _ _ h => h

theorem ext_setOn {ρ : Rst n} {S : Finset (Fin n)} (hS : ∀ i ∈ S, ρ i = none)
    (α : Fin n → Bool) : Ext ρ (setOn ρ S α) := by
  intro i b h
  have : i ∉ S := fun hi => by simp [hS i hi] at h
  simp [setOn, this, h]

/-- If `T` is the first live term under `ρ`, it stays first under any extension that
does not falsify it. -/
theorem firstLive_ext {ρ ρ' : Rst n} {F : DNF n} {T : Term n}
    (h : firstLive ρ F = some T) (hext : Ext ρ ρ') (hT : ¬ Falsified ρ' T) :
    firstLive ρ' F = some T := by
  unfold firstLive at h ⊢
  rw [List.find?_eq_some_iff_append] at h ⊢
  obtain ⟨_, as, bs, hF, has⟩ := h
  refine ⟨by simpa using hT, as, bs, hF, fun a ha => ?_⟩
  have := has a ha
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_not] at this ⊢
  obtain ⟨l, hl, hv⟩ := this
  exact ⟨l, hl, hext _ _ hv⟩

theorem firstLive_live {ρ : Rst n} {F : DNF n} {T : Term n} (h : firstLive ρ F = some T) :
    ¬ Falsified ρ T := by
  have := List.find?_some h
  simpa using this

theorem firstLive_mem {ρ : Rst n} {F : DNF n} {T : Term n} (h : firstLive ρ F = some T) :
    T ∈ F := List.mem_of_find?_eq_some h

/-! ## Unfolding the canonical decision tree -/

theorem cdtDepth_none {F : DNF n} {ρ : Rst n} (h : firstLive ρ F = none) :
    cdtDepth F ρ = 0 := by
  rw [cdtDepth]; split <;> simp_all

theorem cdtDepth_some {F : DNF n} {ρ : Rst n} {T : Term n} (h : firstLive ρ F = some T) :
    cdtDepth F ρ = if Satisfied ρ T then 0 else (freeVars ρ T).card +
      Finset.univ.sup fun α : Fin n → Bool => cdtDepth F (setOn ρ (freeVars ρ T) α) := by
  rw [cdtDepth]; split
  · simp_all
  · rename_i T' h'
    rw [h] at h'; cases h'
    by_cases hs : Satisfied ρ T <;> simp [hs]

/-! ## The code: positions inside a term -/

/-- Position of a literal in a fixed enumeration of the term. -/
def pos (T : Term n) (l : Fin n × Bool) : ℕ := T.toList.idxOf l

theorem pos_lt {T : Term n} {l : Fin n × Bool} (h : l ∈ T) : pos T l < T.card := by
  unfold pos; rw [← Finset.length_toList]
  exact List.idxOf_lt_length_of_mem (Finset.mem_toList.2 h)

theorem pos_inj {T : Term n} {l l' : Fin n × Bool} (h : l ∈ T) (h' : l' ∈ T)
    (he : pos T l = pos T l') : l = l' := by
  unfold pos at he
  exact (List.idxOf_inj (Finset.mem_toList.2 h)).1 he

/-- Variables of `T` at the positions `β`. -/
def sel (T : Term n) (β : Finset ℕ) : Finset (Fin n) :=
  (T.filter fun l => pos T l ∈ β).image Prod.fst

/-- Answers read from the positions `γ`. -/
def ansOf (T : Term n) (γ : Finset ℕ) : Fin n → Bool :=
  fun i => decide (∃ l ∈ T, l.1 = i ∧ pos T l ∈ γ)

/-- The positions of the literals of `T` on the variables `S`. -/
def posSet (T : Term n) (S : Finset (Fin n)) : Finset ℕ :=
  (T.filter fun l => l.1 ∈ S).image (pos T)

/-- The positions of the literals of `T` on the variables of `S` answered `true`. -/
def ansSet (T : Term n) (S : Finset (Fin n)) (α : Fin n → Bool) : Finset ℕ :=
  (T.filter fun l => l.1 ∈ S ∧ α l.1 = true).image (pos T)

theorem sel_posSet {T : Term n} {S : Finset (Fin n)} (hS : S ⊆ T.image Prod.fst) :
    sel T (posSet T S) = S := by
  ext i
  simp only [sel, posSet, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨l, ⟨hl, l', ⟨hl', hS'⟩, he⟩, rfl⟩
    rwa [← pos_inj hl' hl he]
  · intro hi
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 (hS hi)
    exact ⟨l, ⟨hl, l, ⟨hl, hi⟩, rfl⟩, rfl⟩

theorem ansOf_ansSet {T : Term n} {S : Finset (Fin n)} (hS : S ⊆ T.image Prod.fst)
    (α : Fin n → Bool) : ∀ i ∈ S, ansOf T (ansSet T S α) i = α i := by
  intro i hi
  unfold ansOf ansSet
  cases hα : α i
  · simp only [decide_eq_false_iff_not, Finset.mem_image, Finset.mem_filter]
    rintro ⟨l, hl, rfl, l', ⟨hl', _, ht⟩, he⟩
    rw [pos_inj hl' hl he] at ht
    rw [ht] at hα; cases hα
  · simp only [decide_eq_true_eq, Finset.mem_image, Finset.mem_filter]
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 (hS hi)
    exact ⟨l, hl, rfl, l, ⟨hl, hi, hα⟩, rfl⟩

theorem posSet_card {T : Term n} {S : Finset (Fin n)} (hS : S ⊆ T.image Prod.fst)
    (hc : Consistent T) : (posSet T S).card = S.card := by
  unfold posSet
  rw [Finset.card_image_of_injOn (fun l hl l' hl' he => pos_inj
    (Finset.mem_filter.1 hl).1 (Finset.mem_filter.1 hl').1 he)]
  symm
  apply Finset.card_bij (fun i hi => (i, decide ((i, true) ∈ T)))
  · intro i hi
    simp only [Finset.mem_filter]
    refine ⟨?_, hi⟩
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 (hS hi)
    by_cases ht : (l.1, true) ∈ T
    · simpa [ht] using ht
    · have : l.2 = false := by
        cases h2 : l.2
        · rfl
        · exact absurd (by rw [← h2]; exact hl) ht
      simp only [ht, decide_false]
      rw [← this]; exact hl
  · intro i _ j _ h; simpa using congrArg Prod.fst h
  · rintro ⟨i, b⟩ hl
    simp only [Finset.mem_filter] at hl
    refine ⟨i, hl.2, ?_⟩
    cases b
    · have : (i, true) ∉ T := fun ht => hc i ⟨ht, hl.1⟩
      simp [this]
    · simp [hl.1]

theorem posSet_sub {T : Term n} {S : Finset (Fin n)} {w : ℕ} (hw : T.card ≤ w) :
    posSet T S ⊆ Finset.range w := by
  intro k hk
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hk
  exact Finset.mem_range.2 (lt_of_lt_of_le (pos_lt (Finset.mem_filter.1 hl).1) hw)

theorem ansSet_sub (T : Term n) (S : Finset (Fin n)) (α : Fin n → Bool) :
    ansSet T S α ⊆ posSet T S := by
  intro k hk
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hk
  simp only [Finset.mem_filter] at hl
  exact Finset.mem_image.2 ⟨l, Finset.mem_filter.2 ⟨hl.1, hl.2.1⟩, rfl⟩

theorem freeVars_sub (ρ : Rst n) (T : Term n) : freeVars ρ T ⊆ T.image Prod.fst :=
  Finset.image_subset_image (Finset.filter_subset _ _)

/-- The assignment satisfying a consistent term on its variables. -/
def satOf (T : Term n) : Fin n → Bool := fun i => decide ((i, true) ∈ T)

theorem satOf_lit {T : Term n} (hc : Consistent T) {l : Fin n × Bool} (hl : l ∈ T) :
    satOf T l.1 = l.2 := by
  obtain ⟨i, b⟩ := l
  cases b
  · have : (i, true) ∉ T := fun ht => hc i ⟨ht, hl⟩
    simp [satOf, this]
  · simp [satOf, hl]

/-- Setting free variables of a live term to its satisfying values keeps it live. -/
theorem live_setOn_sat {ρ : Rst n} {T : Term n} (hc : Consistent T) (hT : ¬ Falsified ρ T)
    (S : Finset (Fin n)) : ¬ Falsified (setOn ρ S (satOf T)) T := by
  rintro ⟨l, hl, hv⟩
  unfold setOn at hv
  split_ifs at hv with h
  · rw [satOf_lit hc hl] at hv
    cases h2 : l.2 <;> simp [h2] at hv
  · exact hT ⟨l, hl, hv⟩

/-- Liveness of `T` only depends on the variables of `T`; on them, the extension agrees
with `ρ` (where `ρ` is fixed) or with `satOf T`. -/
theorem live_of_agree {ρ ρ' : Rst n} {T : Term n} (hc : Consistent T) (hT : ¬ Falsified ρ T)
    (h : ∀ l ∈ T, ρ' l.1 = ρ l.1 ∨ ρ' l.1 = some (satOf T l.1) ∨ ρ' l.1 = none) :
    ¬ Falsified ρ' T := by
  rintro ⟨l, hl, hv⟩
  rcases h l hl with h1 | h1 | h1
  · exact hT ⟨l, hl, h1 ▸ hv⟩
  · rw [h1, satOf_lit hc hl] at hv
    cases h2 : l.2 <;> simp [h2] at hv
  · rw [h1] at hv; cases hv

/-! ## Decoding and the code space -/

/-- Decoding: from the final restriction and the code, recover the original restriction. -/
def dec (F : DNF n) : Rst n → List (Finset ℕ × Finset ℕ) → Rst n
  | ρ, [] => ρ
  | ρ, (β, γ) :: c => match firstLive ρ F with
    | none => ρ
    | some T => unsetOn (dec F (setOn ρ (sel T β) (ansOf T γ)) c) (sel T β)

/-- Codes for depth `s`: blocks of nonempty position sets of total size `s`, each with a
subset of answered positions. -/
def codes (w : ℕ) : ℕ → Finset (List (Finset ℕ × Finset ℕ))
  | 0 => {[]}
  | s + 1 => (Finset.range (s + 1)).biUnion fun m =>
      ((Finset.range w).powersetCard (m + 1)).biUnion fun β =>
        β.powerset.biUnion fun γ => (codes w (s - m)).image (List.cons (β, γ))
termination_by s => s
decreasing_by omega

theorem geom_two (k : ℕ) : ∑ j ∈ Finset.range k, 2 ^ j + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem codes_card (w s : ℕ) : (codes w s).card ≤ (4 * w) ^ s := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  cases s with
  | zero => simp [codes]
  | succ s =>
    rw [codes]
    calc _ ≤ ∑ m ∈ Finset.range (s + 1), (2 * w) ^ (m + 1) * (4 * w) ^ (s - m) := by
          refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun m hm => ?_)
          refine (Finset.card_biUnion_le).trans ?_
          calc _ ≤ ∑ β ∈ (Finset.range w).powersetCard (m + 1), 2 ^ (m + 1) * (4 * w) ^ (s - m) := by
                refine Finset.sum_le_sum fun β hβ => ?_
                refine (Finset.card_biUnion_le).trans ?_
                rw [(Finset.mem_powersetCard.1 hβ).2.symm, ← Finset.card_powerset]
                rw [← smul_eq_mul, ← Finset.sum_const]
                refine Finset.sum_le_sum fun γ _ => (Finset.card_image_le).trans ?_
                exact ih _ (by omega)
            _ = w.choose (m + 1) * (2 ^ (m + 1) * (4 * w) ^ (s - m)) := by
                rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_range, smul_eq_mul]
            _ ≤ w ^ (m + 1) * (2 ^ (m + 1) * (4 * w) ^ (s - m)) :=
                Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)
            _ = _ := by rw [mul_pow]; ring
      _ = ∑ m ∈ Finset.range (s + 1), (2 * w) ^ (s + 1) * 2 ^ (s - m) := by
          refine Finset.sum_congr rfl fun m hm => ?_
          have hm := Finset.mem_range.1 hm
          obtain ⟨k, rfl⟩ : ∃ k, s = m + k := ⟨s - m, by omega⟩
          have h4 : (4 * w) ^ k = 2 ^ k * (2 * w) ^ k := by rw [← mul_pow]; ring_nf
          rw [show m + k - m = k by omega, h4]; ring
      _ = (2 * w) ^ (s + 1) * ∑ j ∈ Finset.range (s + 1), 2 ^ j := by
          rw [← Finset.mul_sum, ← Finset.sum_range_reflect]
          refine congrArg _ (Finset.sum_congr rfl fun j hj => ?_)
          have := Finset.mem_range.1 hj
          congr 1; omega
      _ ≤ (2 * w) ^ (s + 1) * 2 ^ (s + 1) := by
          have := geom_two (s + 1); exact Nat.mul_le_mul_left _ (by omega)
      _ = (4 * w) ^ (s + 1) := by rw [← mul_pow]; ring_nf

/-! ## The encoding lemma -/

theorem encode (F : DNF n) (w : ℕ) (hw : WidthLe F w) (hc : ∀ T ∈ F, Consistent T) :
    ∀ s (ρ : Rst n), s ≤ cdtDepth F ρ → ∃ ρ' c, c ∈ codes w s ∧
      numStars ρ' = numStars ρ - s ∧ Ext ρ ρ' ∧ dec F ρ' c = ρ := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro ρ hs
  cases s with
  | zero => exact ⟨ρ, [], by simp [codes], by simp, ext_refl ρ, rfl⟩
  | succ s =>
  cases hF : firstLive ρ F with
  | none => rw [cdtDepth_none hF] at hs; omega
  | some T =>
  rw [cdtDepth_some hF] at hs
  by_cases hsat : Satisfied ρ T
  · rw [if_pos hsat] at hs; omega
  rw [if_neg hsat] at hs
  have hTF := firstLive_mem hF
  have hcT := hc T hTF
  have hwT := hw T hTF
  have hlive := firstLive_live hF
  obtain ⟨S, hSdef⟩ : ∃ S, S = freeVars ρ T := ⟨_, rfl⟩
  rw [← hSdef] at hs
  have hSfree : ∀ i ∈ S, ρ i = none := fun i hi => freeVars_none (hSdef ▸ hi)
  have hSsub : S ⊆ T.image Prod.fst := hSdef ▸ freeVars_sub ρ T
  by_cases hA : s + 1 ≤ S.card
  · -- the path is cut inside this block
    obtain ⟨S', hS'S, hS'c⟩ := Finset.exists_subset_card_eq hA
    have hS'free : ∀ i ∈ S', ρ i = none := fun i hi => hSfree i (hS'S hi)
    have hS'sub : S' ⊆ T.image Prod.fst := hS'S.trans hSsub
    refine ⟨setOn ρ S' (satOf T), [(posSet T S', ∅)], ?_, ?_, ext_setOn hS'free _, ?_⟩
    · rw [codes]
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
        Finset.mem_powerset, Finset.mem_image]
      refine ⟨s, by omega, posSet T S', ⟨posSet_sub hwT, by rw [posSet_card hS'sub hcT, hS'c]⟩,
        ∅, Finset.empty_subset _, [], ?_, rfl⟩
      rw [Nat.sub_self]; simp [codes]
    · rw [numStars_setOn_sub hS'free, hS'c]
    · have hfl : firstLive (setOn ρ S' (satOf T)) F = some T :=
        firstLive_ext hF (ext_setOn hS'free _) (live_setOn_sat hcT hlive S')
      simp only [dec, hfl, sel_posSet hS'sub, setOn_setOn]
      exact unsetOn_setOn hS'free _
  · -- the whole block is queried; continue along a deep branch
    push Not at hA
    have hne : S.Nonempty := hSdef ▸ freeVars_nonempty hlive hsat
    obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 :=
      ⟨S.card - 1, by have := hne.card_pos; omega⟩
    have hle : s - m ≤ Finset.univ.sup fun α : Fin n → Bool =>
        cdtDepth F (setOn ρ S α) := by
      have h3 := Nat.sub_le_iff_le_add'.2 hs
      exact le_trans (show s - m ≤ s + 1 - S.card by omega) h3
    obtain ⟨α, hα⟩ : ∃ α, s - m ≤ cdtDepth F (setOn ρ S α) := by
      rcases Nat.eq_zero_or_pos (s - m) with h0 | h0
      · exact ⟨fun _ => false, by omega⟩
      · obtain ⟨α, -, hα⟩ := (Finset.le_sup_iff h0).1 hle
        exact ⟨α, hα⟩
    obtain ⟨ρ₁', c₁, hc₁, hn₁, he₁, hd₁⟩ :=
      ih (s - m) (by omega) (setOn ρ S α) hα
    refine ⟨setOn ρ₁' S (satOf T), (posSet T S, ansSet T S α) :: c₁, ?_, ?_, ?_, ?_⟩
    · rw [codes]
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
        Finset.mem_powerset, Finset.mem_image]
      exact ⟨m, by omega, posSet T S, ⟨posSet_sub hwT, by rw [posSet_card hSsub hcT, hm]⟩,
        ansSet T S α, ansSet_sub T S α, c₁, hc₁, rfl⟩
    · have hfix : ∀ i ∈ S, ρ₁' i ≠ none := fun i hi => by
        rw [he₁ i (α i) (by simp [setOn, hi])]; simp
      rw [numStars_setOn_fixed hfix, hn₁, numStars_setOn_sub hSfree]
      omega
    · intro i b h
      have hi : i ∉ S := fun hi => by simp [hSfree i hi] at h
      simp only [setOn, hi, if_false]
      exact he₁ i b (by simp [setOn, hi, h])
    · have hext : Ext ρ (setOn ρ₁' S (satOf T)) := by
        intro i b h
        have hi : i ∉ S := fun hi => by simp [hSfree i hi] at h
        simp only [setOn, hi, if_false]
        exact he₁ i b (by simp [setOn, hi, h])
      have hlive' : ¬ Falsified (setOn ρ₁' S (satOf T)) T := by
        refine live_of_agree hcT hlive fun l hl => ?_
        by_cases hlS : l.1 ∈ S
        · right; left; simp [setOn, hlS]
        · left
          cases hρ : ρ l.1 with
          | none =>
              have hm' : l.1 ∈ freeVars ρ T :=
                Finset.mem_image.2 ⟨l, Finset.mem_filter.2 ⟨hl, hρ⟩, rfl⟩
              exact absurd (hSdef ▸ hm') hlS
          | some b => exact (hext _ _ hρ)
      have hfl := firstLive_ext hF hext hlive'
      have hback : setOn ρ₁' S (ansOf T (ansSet T S α)) = ρ₁' := by
        apply setOn_self
        intro i hi
        rw [ansOf_ansSet hSsub α i hi]
        exact he₁ i (α i) (by simp [setOn, hi])
      simp only [dec, hfl, sel_posSet hSsub, setOn_setOn, hback, hd₁]
      exact unsetOn_setOn hSfree α

/-! ## Håstad's switching lemma (counting form) -/

/-- Restrictions with exactly `ℓ` free variables. -/
def restr (n ℓ : ℕ) : Finset (Rst n) := Finset.univ.filter fun ρ => numStars ρ = ℓ

/-- **Switching lemma** (Håstad; Razborov's encoding proof). For a DNF of width at most `w`
with consistent terms, the restrictions with `ℓ` stars whose canonical decision tree has
depth at least `s` number at most `|R^{ℓ-s}| (4w)^s`. -/
theorem switching_lemma (F : DNF n) (w : ℕ) (hw : WidthLe F w)
    (hc : ∀ T ∈ F, Consistent T) (ℓ s : ℕ) :
    ((restr n ℓ).filter fun ρ => s ≤ cdtDepth F ρ).card ≤
      (restr n (ℓ - s)).card * (4 * w) ^ s := by
  calc _ ≤ ((restr n (ℓ - s) ×ˢ codes w s).image fun p => dec F p.1 p.2).card := by
        apply Finset.card_le_card
        intro ρ hρ
        simp only [restr, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
        obtain ⟨ρ', c, hc', hn, -, hd⟩ := encode F w hw hc s ρ hρ.2
        refine Finset.mem_image.2 ⟨(ρ', c), Finset.mem_product.2 ⟨?_, hc'⟩, hd⟩
        simp [restr, hn, hρ.1]
    _ ≤ (restr n (ℓ - s) ×ˢ codes w s).card := Finset.card_image_le
    _ ≤ _ := by rw [Finset.card_product]; exact Nat.mul_le_mul_left _ (codes_card w s)

end

end SATurday.ProofComplexity
