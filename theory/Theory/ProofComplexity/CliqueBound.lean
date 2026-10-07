import Theory.ProofComplexity.MonotoneClique
import Theory.ProofComplexity.CuttingPlanesInterp

/-!
# Clique lower bound for monotone Boolean circuits: the approximation argument (R3)

Monotone Boolean circuits are straight line programs (`MGate` lists) whose gates are
edge inputs, the constants `0` and `1`, `min` (AND) and `max` (OR). Each gate gets an
approximator (`apx`): edge inputs are exact, OR is union then plucking, AND is pairwise
union of small sets then plucking.

`pos_claim`: on a positive test a gate of value `1` is accepted by its approximator
unless the test lies in an AND error set (`NewPos`). `neg_claim`: on a negative test an
accepting approximator means value `1` unless the test lies in a plucking error set
(`NewNeg`).

LOG: R3 CliqueBound module (approximation argument)
-/

namespace SATurday.ProofComplexity

open Finset

noncomputable section

open Classical

/-- Gates of a monotone Boolean circuit. -/
def BoolGate (g : MGate) : Prop :=
  (∃ v, g = .inp v) ∨ g = .cst 0 ∨ g = .cst 1 ∨ (∃ i j, g = .op min i j) ∨
    (∃ i j, g = .op max i j)

/-- A monotone Boolean circuit. -/
def MCBool (C : List MGate) : Prop := ∀ g ∈ C, BoolGate g

variable {n : ℕ}

/-- Pairwise unions of small sets. -/
def andF (ℓ : ℕ) (A B : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  ((A ×ˢ B).image fun XY => XY.1 ∪ XY.2).filter fun W => W.card ≤ ℓ

/-- Approximator of an input variable: the edge as a two element clique. -/
def inApx (n : ℕ) (v : ℕ) : Finset (Finset (Fin n)) :=
  if h : ∃ uw : Fin n × Fin n, uw.1 ≠ uw.2 ∧ eVar n uw.1 uw.2 = v then
    {{h.choose.1, h.choose.2}} else ∅

/-- Approximator before plucking for a binary gate. -/
def preApx (ℓ : ℕ) (f : ℝ → ℝ → ℝ) (A B : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  if f = max then normF (A ∪ B) else if f = min then normF (andF ℓ A B) else ∅

variable (n) (ℓ p : ℕ) (gt : ℕ → MGate)

/-- The approximator of gate `m`. -/
def apx : ℕ → Finset (Finset (Fin n))
  | m => match gt m with
    | .inp v => inApx n v
    | .cst c => if c = 1 then {∅} else ∅
    | .op f i j => pluck p ℓ (preApx ℓ f (if h : i < m then apx i else ∅)
        (if h : j < m then apx j else ∅))
decreasing_by all_goals exact h

/-- Earlier approximator, `∅` when the index is not earlier. -/
def rdA (m i : ℕ) : Finset (Finset (Fin n)) := if i < m then apx n ℓ p gt i else ∅

theorem apx_eq (m : ℕ) : apx n ℓ p gt m = match gt m with
    | .inp v => inApx n v
    | .cst c => if c = 1 then {∅} else ∅
    | .op f i j => pluck p ℓ (preApx ℓ f (rdA n ℓ p gt m i) (rdA n ℓ p gt m j)) := by
  rw [apx]
  cases gt m <;> simp [rdA]

/-- AND error set of gate `m` on positive tests. -/
def NewPos (k m : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard k).filter fun K => ∃ i j, gt m = .op min i j ∧
    ∃ X ∈ rdA n ℓ p gt m i, ∃ Y ∈ rdA n ℓ p gt m j, X ∪ Y ⊆ K ∧ ℓ < (X ∪ Y).card

/-- Plucking error set of gate `m` on negative tests. -/
def NewNeg (Kc m : ℕ) : Finset (Fin n → Fin Kc) :=
  Finset.univ.filter fun c => ∃ f i j, gt m = .op f i j ∧
    Acc (negG c) (apx n ℓ p gt m) ∧
      ¬ Acc (negG c) (preApx ℓ f (rdA n ℓ p gt m i) (rdA n ℓ p gt m j))

/-! ## Gate values -/

theorem read_val (a : Assignment) (m i : ℕ) :
    (mcVals a ((List.range m).map gt)).getD i 0 = if i < m then gateValue a gt i else 0 := by
  split_ifs with h
  · exact read_earlier a gt h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
    · rfl
    · rw [mcVals_length]; simp; omega

theorem gateValue_eq (a : Assignment) (m : ℕ) :
    gateValue a gt m = (gt m).val a (mcVals a ((List.range m).map gt)) := rfl

/-- Gate values are `0` or `1`. -/
theorem val01 (hB : ∀ m, BoolGate (gt m)) (a : Assignment) :
    ∀ m, gateValue a gt m = 0 ∨ gateValue a gt m = 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  have rd : ∀ i, (mcVals a ((List.range m).map gt)).getD i 0 = 0 ∨
      (mcVals a ((List.range m).map gt)).getD i 0 = 1 := by
    intro i
    rw [read_val]
    split_ifs with h
    · exact ih i h
    · left; rfl
  rw [gateValue_eq]
  rcases hB m with ⟨v, hv⟩ | hv | hv | ⟨i, j, hv⟩ | ⟨i, j, hv⟩ <;> rw [hv] <;>
    simp only [MGate.val]
  · split_ifs <;> simp
  · left; trivial
  · right; trivial
  · rcases rd i with h1 | h1 <;> rcases rd j with h2 | h2 <;> rw [h1, h2] <;> norm_num
  · rcases rd i with h1 | h1 <;> rcases rd j with h2 | h2 <;> rw [h1, h2] <;> norm_num

theorem min_ne_max : (min : ℝ → ℝ → ℝ) ≠ max := by
  intro h
  have := congrFun (congrFun h 0) 1
  norm_num at this

theorem preApx_max (A B : Finset (Finset (Fin n))) : preApx ℓ max A B = normF (A ∪ B) := by
  unfold preApx; rw [if_pos rfl]

theorem preApx_min (A B : Finset (Finset (Fin n))) : preApx ℓ min A B = normF (andF ℓ A B) := by
  unfold preApx; rw [if_neg min_ne_max, if_pos rfl]

theorem rdA_of_lt {m i : ℕ} (h : i < m) : rdA n ℓ p gt m i = apx n ℓ p gt i := by
  unfold rdA; rw [if_pos h]

theorem not_acc_rdA {G : Gr n} {m i : ℕ} (h : Acc G (rdA n ℓ p gt m i)) : i < m := by
  unfold rdA at h
  split_ifs at h with hi
  · exact hi
  · obtain ⟨X, hX, _⟩ := h; simp at hX

theorem read_eq_one {a : Assignment} {m i : ℕ}
    (h : (mcVals a ((List.range m).map gt)).getD i 0 = 1) : i < m ∧ gateValue a gt i = 1 := by
  rw [read_val] at h
  split_ifs at h with hi
  · exact ⟨hi, h⟩
  · norm_num at h

/-- The input approximator of an edge variable is the edge. -/
theorem inApx_edge {v : ℕ} (hv : v ∈ edgeVars n) :
    ∃ u w : Fin n, u ≠ w ∧ eVar n u w = v ∧ inApx n v = {{u, w}} := by
  have hex : ∃ uw : Fin n × Fin n, uw.1 ≠ uw.2 ∧ eVar n uw.1 uw.2 = v := by
    unfold edgeVars at hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨t, (Finset.mem_filter.1 ht).2, rfl⟩
  refine ⟨hex.choose.1, hex.choose.2, hex.choose_spec.1, hex.choose_spec.2, ?_⟩
  unfold inApx; rw [dif_pos hex]

theorem isCl_pair {G : Gr n} {u w : Fin n} (h1 : G u w) (h2 : G w u) : IsCl G {u, w} := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · exact h1
  · exact h2
  · exact absurd rfl hxy

theorem isCl_posG_of_subset {K X : Finset (Fin n)} (h : X ⊆ K) : IsCl (posG K) X :=
  fun _ hu _ hv _ => ⟨h hu, h hv⟩

theorem apx_small (hℓ : 2 ≤ ℓ) : ∀ m, SmallF ℓ (apx n ℓ p gt m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  have hrd : ∀ i, SmallF ℓ (rdA n ℓ p gt m i) := by
    intro i; unfold rdA; split_ifs with h
    · exact ih i h
    · intro X hX; simp at hX
  rw [apx_eq]
  cases gt m with
  | inp v =>
      dsimp only
      unfold inApx
      split_ifs with h
      · intro X hX
        rw [Finset.mem_singleton] at hX; subst hX
        rw [Finset.card_pair h.choose_spec.1]
        exact ⟨hℓ, by norm_num⟩
      · intro X hX; simp at hX
  | cst c =>
      dsimp only
      split_ifs
      · intro X hX; rw [Finset.mem_singleton] at hX; subst hX; simp
      · intro X hX; simp at hX
  | op f i j =>
      apply pluck_small
      unfold preApx
      split_ifs
      · apply smallF_normF
        intro X hX
        rcases Finset.mem_union.1 hX with h | h
        · exact (hrd i X h).1
        · exact (hrd j X h).1
      · apply smallF_normF
        intro X hX
        exact (Finset.mem_filter.1 hX).2
      · intro X hX; simp at hX

variable {n ℓ p gt}

/-- Positive tests: value `1` is caught by the approximator or by an AND error. -/
theorem pos_claim {k : ℕ} (hℓ : 2 ≤ ℓ) (hB : ∀ m, BoolGate (gt m))
    (hI : ∀ m v, gt m = .inp v → v ∈ edgeVars n) {K : Finset (Fin n)} (hK : K.card = k)
    (a : Assignment) (ha : ∀ u w : Fin n, u ≠ w → (a (eVar n u w) = true ↔ u ∈ K ∧ w ∈ K)) :
    ∀ m, gateValue a gt m = 1 →
      Acc (posG K) (apx n ℓ p gt m) ∨ ∃ m' ≤ m, K ∈ NewPos n ℓ p gt k m' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hv
  have h01 := val01 gt hB a
  have rd : ∀ t, (mcVals a ((List.range m).map gt)).getD t 0 = 0 ∨
      (mcVals a ((List.range m).map gt)).getD t 0 = 1 := by
    intro t; rw [read_val]; split_ifs
    · exact h01 t
    · left; rfl
  rw [gateValue_eq] at hv
  rcases hB m with ⟨v, hg⟩ | hg | hg | ⟨i, j, hg⟩ | ⟨i, j, hg⟩
  · rw [hg] at hv
    simp only [MGate.val] at hv
    have hav : a v = true := by
      by_contra h; rw [if_neg h] at hv; norm_num at hv
    obtain ⟨u, w, huw, rfl, hin⟩ := inApx_edge n (hI m v hg)
    left
    rw [apx_eq, hg]
    simp only [hin]
    have := (ha u w huw).1 hav
    exact ⟨{u, w}, Finset.mem_singleton_self _, isCl_pair n ⟨this.1, this.2⟩ ⟨this.2, this.1⟩⟩
  · rw [hg] at hv; simp [MGate.val] at hv
  · left
    rw [apx_eq, hg]
    simp only [if_true]
    exact ⟨∅, Finset.mem_singleton_self _, isCl_of_card_le_one (by simp)⟩
  · -- AND
    rw [hg] at hv
    simp only [MGate.val] at hv
    have hi1 : (mcVals a ((List.range m).map gt)).getD i 0 = 1 := by
      rcases rd i with h | h
      · rw [h] at hv
        rcases rd j with h' | h' <;> rw [h'] at hv <;> norm_num at hv
      · exact h
    have hj1 : (mcVals a ((List.range m).map gt)).getD j 0 = 1 := by
      rw [hi1] at hv
      rcases rd j with h | h
      · rw [h] at hv; norm_num at hv
      · exact h
    obtain ⟨hi, gi⟩ := read_eq_one gt hi1
    obtain ⟨hj, gj⟩ := read_eq_one gt hj1
    rcases ih i hi gi with ai | ⟨m', hm', hK'⟩
    swap; · exact Or.inr ⟨m', by omega, hK'⟩
    rcases ih j hj gj with aj | ⟨m', hm', hK'⟩
    swap; · exact Or.inr ⟨m', by omega, hK'⟩
    obtain ⟨X, hX, hXc⟩ := ai
    obtain ⟨Y, hY, hYc⟩ := aj
    have hsX := apx_small n ℓ p gt hℓ i X hX
    have hsY := apx_small n ℓ p gt hℓ j Y hY
    have hXK : X ⊆ K := (isCl_posG hsX.2).1 hXc
    have hYK : Y ⊆ K := (isCl_posG hsY.2).1 hYc
    by_cases hsz : (X ∪ Y).card ≤ ℓ
    · left
      rw [apx_eq, hg]
      simp only
      apply pluck_acc
      rw [preApx_min, acc_normF]
      refine ⟨X ∪ Y, ?_, isCl_posG_of_subset n (Finset.union_subset hXK hYK)⟩
      rw [rdA_of_lt n ℓ p gt hi, rdA_of_lt n ℓ p gt hj]
      exact Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(X, Y), Finset.mem_product.2 ⟨hX, hY⟩, rfl⟩,
        hsz⟩
    · right
      refine ⟨m, le_rfl, ?_⟩
      unfold NewPos
      refine Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hK⟩, i, j, hg,
        X, ?_, Y, ?_, Finset.union_subset hXK hYK, by omega⟩
      · rw [rdA_of_lt n ℓ p gt hi]; exact hX
      · rw [rdA_of_lt n ℓ p gt hj]; exact hY
  · -- OR
    rw [hg] at hv
    simp only [MGate.val] at hv
    have hor : (mcVals a ((List.range m).map gt)).getD i 0 = 1 ∨
        (mcVals a ((List.range m).map gt)).getD j 0 = 1 := by
      rcases rd i with h | h
      · rw [h] at hv
        rcases rd j with h' | h'
        · rw [h'] at hv; norm_num at hv
        · exact Or.inr h'
      · exact Or.inl h
    have key : ∀ t, (mcVals a ((List.range m).map gt)).getD t 0 = 1 →
        Acc (posG K) (rdA n ℓ p gt m t) ∨ ∃ m' ≤ m, K ∈ NewPos n ℓ p gt k m' := by
      intro t ht
      obtain ⟨htm, gt1⟩ := read_eq_one gt ht
      rw [rdA_of_lt n ℓ p gt htm]
      rcases ih t htm gt1 with h | ⟨m', hm', hK'⟩
      · exact Or.inl h
      · exact Or.inr ⟨m', by omega, hK'⟩
    have hacc : Acc (posG K) (rdA n ℓ p gt m i) ∨ Acc (posG K) (rdA n ℓ p gt m j) ∨
        ∃ m' ≤ m, K ∈ NewPos n ℓ p gt k m' := by
      rcases hor with h | h
      · rcases key i h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr h')
      · rcases key j h with h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')
    rcases hacc with h | h | h
    · left
      rw [apx_eq, hg]
      simp only
      apply pluck_acc
      rw [preApx_max, acc_normF]
      obtain ⟨X, hX, hc⟩ := h
      exact ⟨X, Finset.mem_union_left _ hX, hc⟩
    · left
      rw [apx_eq, hg]
      simp only
      apply pluck_acc
      rw [preApx_max, acc_normF]
      obtain ⟨X, hX, hc⟩ := h
      exact ⟨X, Finset.mem_union_right _ hX, hc⟩
    · exact Or.inr h

/-- Negative tests: an accepting approximator means value `1` or a plucking error. -/
theorem neg_claim {Kc : ℕ} (hB : ∀ m, BoolGate (gt m))
    (hI : ∀ m v, gt m = .inp v → v ∈ edgeVars n) (c : Fin n → Fin Kc)
    (a : Assignment) (ha : ∀ u w : Fin n, u ≠ w → (a (eVar n u w) = true ↔ c u ≠ c w)) :
    ∀ m, Acc (negG c) (apx n ℓ p gt m) →
      gateValue a gt m = 1 ∨ ∃ m' ≤ m, c ∈ NewNeg n ℓ p gt Kc m' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hacc
  have h01 := val01 gt hB a
  have rd : ∀ t, (mcVals a ((List.range m).map gt)).getD t 0 = 0 ∨
      (mcVals a ((List.range m).map gt)).getD t 0 = 1 := by
    intro t; rw [read_val]; split_ifs
    · exact h01 t
    · left; rfl
  -- reading an accepted earlier approximator
  have key : ∀ t, Acc (negG c) (rdA n ℓ p gt m t) →
      (mcVals a ((List.range m).map gt)).getD t 0 = 1 ∨ ∃ m' ≤ m, c ∈ NewNeg n ℓ p gt Kc m' := by
    intro t ht
    have htm := not_acc_rdA n ℓ p gt ht
    rw [rdA_of_lt n ℓ p gt htm] at ht
    rw [read_val, if_pos htm]
    rcases ih t htm ht with h | ⟨m', hm', hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨m', by omega, hc⟩
  rw [gateValue_eq]
  rcases hB m with ⟨v, hg⟩ | hg | hg | ⟨i, j, hg⟩ | ⟨i, j, hg⟩
  · obtain ⟨u, w, huw, rfl, hin⟩ := inApx_edge n (hI m _ hg)
    rw [apx_eq, hg] at hacc
    simp only [hin] at hacc
    obtain ⟨X, hX, hXc⟩ := hacc
    rw [Finset.mem_singleton] at hX; subst hX
    have hcw : c u ≠ c w := hXc u (by simp) w (by simp) huw
    left
    rw [hg]; simp only [MGate.val]
    rw [if_pos ((ha u w huw).2 hcw)]
  · rw [apx_eq, hg] at hacc
    simp only at hacc
    rw [if_neg (by norm_num)] at hacc
    obtain ⟨X, hX, _⟩ := hacc; simp at hX
  · left; rw [hg]; rfl
  · -- AND
    rw [apx_eq, hg] at hacc
    simp only at hacc
    by_cases hpre : Acc (negG c) (preApx ℓ min (rdA n ℓ p gt m i) (rdA n ℓ p gt m j))
    · rw [preApx_min, acc_normF] at hpre
      obtain ⟨W, hW, hWc⟩ := hpre
      obtain ⟨hWi, _⟩ := Finset.mem_filter.1 hW
      obtain ⟨⟨X, Y⟩, hXY, rfl⟩ := Finset.mem_image.1 hWi
      obtain ⟨hX, hY⟩ := Finset.mem_product.1 hXY
      rcases key i ⟨X, hX, hWc.mono Finset.subset_union_left⟩ with h1 | h1
      · rcases key j ⟨Y, hY, hWc.mono Finset.subset_union_right⟩ with h2 | h2
        · left; rw [hg]; simp only [MGate.val]; rw [h1, h2]; norm_num
        · exact Or.inr h2
      · exact Or.inr h1
    · right
      refine ⟨m, le_rfl, Finset.mem_filter.2 ⟨Finset.mem_univ _, min, i, j, hg, ?_, hpre⟩⟩
      rw [apx_eq, hg]; exact hacc
  · -- OR
    rw [apx_eq, hg] at hacc
    simp only at hacc
    by_cases hpre : Acc (negG c) (preApx ℓ max (rdA n ℓ p gt m i) (rdA n ℓ p gt m j))
    · rw [preApx_max, acc_normF] at hpre
      obtain ⟨X, hX, hXc⟩ := hpre
      rcases Finset.mem_union.1 hX with hX | hX
      · rcases key i ⟨X, hX, hXc⟩ with h1 | h1
        · left; rw [hg]; simp only [MGate.val]; rw [h1]
          rcases rd j with h2 | h2 <;> rw [h2] <;> norm_num
        · exact Or.inr h1
      · rcases key j ⟨X, hX, hXc⟩ with h1 | h1
        · left; rw [hg]; simp only [MGate.val]; rw [h1]
          rcases rd i with h2 | h2 <;> rw [h2] <;> norm_num
        · exact Or.inr h1
    · right
      refine ⟨m, le_rfl, Finset.mem_filter.2 ⟨Finset.mem_univ _, max, i, j, hg, ?_, hpre⟩⟩
      rw [apx_eq, hg]; exact hacc

end

end SATurday.ProofComplexity
