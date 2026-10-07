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

/-! ## Sizes of approximators and error sets -/

variable (n ℓ p gt)

theorem apx_card (hp : 2 ≤ p) (hℓ : 2 ≤ ℓ) (hn : Nonempty (Fin n)) :
    ∀ m, (apx n ℓ p gt m).card ≤ sfBound p ℓ := by
  intro m
  have h1 : 1 ≤ sfBound p ℓ := by
    cases ℓ with
    | zero => simp [sfBound]
    | succ ℓ => simp [sfBound]
  rw [apx_eq]
  cases gt m with
  | inp v =>
      dsimp only
      unfold inApx
      split_ifs <;> simp [h1]
  | cst c =>
      dsimp only
      split_ifs <;> simp [h1]
  | op f i j =>
      dsimp only
      refine pluck_card hp hn _ ?_
      intro X hX
      unfold preApx at hX
      split_ifs at hX
      · obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 hX
        refine (Finset.card_le_card (normSet_subset Y)).trans ?_
        rcases Finset.mem_union.1 hY with h | h
        · unfold rdA at h; split_ifs at h
          · exact (apx_small n ℓ p gt hℓ i Y h).1
          · simp at h
        · unfold rdA at h; split_ifs at h
          · exact (apx_small n ℓ p gt hℓ j Y h).1
          · simp at h
      · obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 hX
        exact (Finset.card_le_card (normSet_subset Y)).trans (Finset.mem_filter.1 hY).2
      · simp at hX

theorem rdA_card (hp : 2 ≤ p) (hℓ : 2 ≤ ℓ) (hn : Nonempty (Fin n)) (m i : ℕ) :
    (rdA n ℓ p gt m i).card ≤ sfBound p ℓ := by
  unfold rdA; split_ifs
  · exact apx_card n ℓ p gt hp hℓ hn i
  · simp

/-- `k` sets containing a fixed set. -/
theorem card_supsets_le (k : ℕ) (W : Finset (Fin n)) :
    ((Finset.univ.powersetCard k).filter fun K : Finset (Fin n) => W ⊆ K).card ≤
      (n - W.card).choose (k - W.card) := by
  have hmap : ∀ K ∈ (Finset.univ.powersetCard k).filter (fun K : Finset (Fin n) => W ⊆ K),
      K \ W ∈ (Finset.univ \ W).powersetCard (k - W.card) := by
    intro K hK
    obtain ⟨hK1, hWK⟩ := Finset.mem_filter.1 hK
    rw [Finset.mem_powersetCard] at hK1 ⊢
    refine ⟨Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl W), ?_⟩
    rw [Finset.card_sdiff_of_subset hWK, hK1.2]
  have hinj : Set.InjOn (fun K : Finset (Fin n) => K \ W)
      (((Finset.univ.powersetCard k).filter fun K : Finset (Fin n) => W ⊆ K) :
        Set (Finset (Fin n))) := by
    intro K1 h1 K2 h2 h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at h1 h2
    rw [← Finset.sdiff_union_of_subset h1.2, ← Finset.sdiff_union_of_subset h2.2]
    simp only at h; rw [h]
  calc _ ≤ ((Finset.univ \ W).powersetCard (k - W.card)).card :=
        Finset.card_le_card_of_injOn _ hmap hinj
    _ = (n - W.card).choose (k - W.card) := by
        rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_univ, Fintype.card_fin]

theorem choose_sub_mono {N K : ℕ} (hKN : K ≤ N) :
    ∀ t w, t ≤ w → (N - w).choose (K - w) ≤ (N - t).choose (K - t) := by
  intro t w htw
  induction w, htw using Nat.le_induction with
  | base => exact le_rfl
  | succ w hw ih =>
      refine le_trans ?_ ih
      by_cases hwK : w < K
      · have e1 : N - w = (N - (w + 1)) + 1 := by omega
        have e2 : K - w = (K - (w + 1)) + 1 := by omega
        rw [e1, e2, Nat.choose_succ_succ]
        omega
      · have h1 : K - (w + 1) = 0 := by omega
        have h2 : K - w = 0 := by omega
        rw [h1, h2, Nat.choose_zero_right, Nat.choose_zero_right]

theorem newPos_card (hp : 2 ≤ p) (hℓ : 2 ≤ ℓ) (hn : Nonempty (Fin n)) {k : ℕ}
    (hk : ℓ + 1 ≤ k) (hkn : k ≤ n) (m : ℕ) :
    (NewPos n ℓ p gt k m).card ≤
      sfBound p ℓ * sfBound p ℓ * (n - (ℓ + 1)).choose (k - (ℓ + 1)) := by
  by_cases hg : ∃ i j, gt m = .op min i j
  · obtain ⟨i, j, hg⟩ := hg
    have hsub : NewPos n ℓ p gt k m ⊆ (rdA n ℓ p gt m i ×ˢ rdA n ℓ p gt m j).biUnion
        fun XY => if ℓ < (XY.1 ∪ XY.2).card then
          (Finset.univ.powersetCard k).filter fun K : Finset (Fin n) => XY.1 ∪ XY.2 ⊆ K
        else ∅ := by
      intro K hK
      obtain ⟨hKk, i', j', hg', X, hX, Y, hY, hXYK, hlt⟩ := Finset.mem_filter.1 hK
      rw [hg] at hg'
      cases hg'
      refine Finset.mem_biUnion.2 ⟨(X, Y), Finset.mem_product.2 ⟨hX, hY⟩, ?_⟩
      rw [if_pos hlt]
      exact Finset.mem_filter.2 ⟨hKk, hXYK⟩
    have hbound : ∀ XY ∈ rdA n ℓ p gt m i ×ˢ rdA n ℓ p gt m j,
        (if ℓ < (XY.1 ∪ XY.2).card then
          (Finset.univ.powersetCard k).filter fun K : Finset (Fin n) => XY.1 ∪ XY.2 ⊆ K
        else ∅).card ≤ (n - (ℓ + 1)).choose (k - (ℓ + 1)) := by
      intro XY _
      split_ifs with hlt
      · exact (card_supsets_le n k _).trans (choose_sub_mono (by omega) _ _ hlt)
      · simp
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ XY ∈ rdA n ℓ p gt m i ×ˢ rdA n ℓ p gt m j, _ := Finset.card_biUnion_le
      _ ≤ ∑ _XY ∈ rdA n ℓ p gt m i ×ˢ rdA n ℓ p gt m j,
            (n - (ℓ + 1)).choose (k - (ℓ + 1)) := Finset.sum_le_sum hbound
      _ = (rdA n ℓ p gt m i).card * (rdA n ℓ p gt m j).card *
            (n - (ℓ + 1)).choose (k - (ℓ + 1)) := by
          rw [Finset.sum_const, Finset.card_product, smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul (rdA_card n ℓ p gt hp hℓ hn m i)
            (rdA_card n ℓ p gt hp hℓ hn m j))
  · have : NewPos n ℓ p gt k m = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro K hK
      obtain ⟨_, i, j, hg', _⟩ := Finset.mem_filter.1 hK
      exact hg ⟨i, j, hg'⟩
    rw [this]; simp

/-- Per sunflower error bound in the form used by `pluck_err`. -/
def sunE (n Kc ℓ p : ℕ) : ℕ := (ℓ * ℓ) ^ p * Kc ^ n / Kc ^ p

theorem sunE_spec {Kc : ℕ} (hKc : 1 ≤ Kc) (S : Finset (Finset (Fin n))) (Z : Finset (Fin n))
    (hS : S.card = p) (hsun : IsSunflower S Z) (hZ : ∀ X ∈ S, Z ⊆ X)
    (hℓS : ∀ X ∈ S, X.card ≤ ℓ) :
    (Finset.univ.filter fun c : Fin n → Fin Kc =>
      IsCl (negG c) Z ∧ ∀ X ∈ S, ¬ IsCl (negG c) X).card ≤ sunE n Kc ℓ p := by
  unfold sunE
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos hKc)]
  exact sunflower_err S Z hS hsun hZ hℓS

theorem newNeg_card (hp : 2 ≤ p) (hℓ : 2 ≤ ℓ) (hn : Nonempty (Fin n)) {Kc : ℕ} (hKc : 1 ≤ Kc)
    (m : ℕ) :
    (NewNeg n ℓ p gt Kc m).card ≤ sfBound p ℓ * sfBound p ℓ * sunE n Kc ℓ p := by
  have hsf : 2 ≤ sfBound p ℓ := by
    obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
    simp only [sfBound]
    have : 1 ≤ p * (ℓ' + 1) * sfBound p ℓ' := by
      have h1 : 1 ≤ sfBound p ℓ' := by
        cases ℓ' with
        | zero => simp [sfBound]
        | succ ℓ'' => simp [sfBound]
      have h2 : 1 ≤ p * (ℓ' + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
      nlinarith
    omega
  by_cases hg : ∃ f i j, gt m = .op f i j
  · obtain ⟨f, i, j, hg⟩ := hg
    set pre := preApx ℓ f (rdA n ℓ p gt m i) (rdA n ℓ p gt m j)
    have hsub : NewNeg n ℓ p gt Kc m ⊆ Finset.univ.filter fun c : Fin n → Fin Kc =>
        Acc (negG c) (pluck p ℓ pre) ∧ ¬ Acc (negG c) pre := by
      intro c hc
      obtain ⟨_, f', i', j', hg', hacc, hpre⟩ := Finset.mem_filter.1 hc
      rw [hg] at hg'
      cases hg'
      rw [apx_eq, hg] at hacc
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hacc, hpre⟩
    have herr := pluck_err (K := Kc) (p := p) (ℓ := ℓ) (E := sunE n Kc ℓ p)
      (fun S Z hS hsun hZ hℓS => sunE_spec n ℓ p hKc S Z hS hsun hZ hℓS) pre
    have hpre : pre.card ≤ sfBound p ℓ * sfBound p ℓ := by
      have hi := rdA_card n ℓ p gt hp hℓ hn m i
      have hj := rdA_card n ℓ p gt hp hℓ hn m j
      unfold pre preApx
      split_ifs
      · refine (normF_card_le _).trans ((Finset.card_union_le _ _).trans ?_)
        nlinarith
      · refine (normF_card_le _).trans ((Finset.card_filter_le _ _).trans
          (Finset.card_image_le.trans ?_))
        rw [Finset.card_product]
        exact Nat.mul_le_mul hi hj
      · simp
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ pre.card * sunE n Kc ℓ p := herr
      _ ≤ _ := Nat.mul_le_mul_right _ hpre
  · have : NewNeg n ℓ p gt Kc m = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro c hc
      obtain ⟨_, f, i, j, hg', _⟩ := Finset.mem_filter.1 hc
      exact hg ⟨f, i, j, hg'⟩
    rw [this]; simp

/-- Colorings that are not injective on `X`. -/
theorem nonInj_card {Kc : ℕ} (X : Finset (Fin n)) :
    (Finset.univ.filter fun c : Fin n → Fin Kc => ¬ Set.InjOn c X).card * Kc ≤
      X.card * X.card * Kc ^ n := by
  have hsub : (Finset.univ.filter fun c : Fin n → Fin Kc => ¬ Set.InjOn c X) ⊆
      (X ×ˢ X).biUnion fun uv => if uv.1 = uv.2 then ∅ else
        Finset.univ.filter fun c : Fin n → Fin Kc => ∀ u ∈ ({uv.1} : Finset (Fin n)),
          c u = c ((fun _ => uv.2) u) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.InjOn, not_forall] at hc
    obtain ⟨u, hu, v, hv, huv, hne⟩ := hc
    refine Finset.mem_biUnion.2 ⟨(u, v), Finset.mem_product.2 ⟨hu, hv⟩, ?_⟩
    rw [if_neg hne]
    simp [huv]
  have hone : ∀ uv ∈ X ×ˢ X, (if uv.1 = uv.2 then ∅ else
        Finset.univ.filter fun c : Fin n → Fin Kc => ∀ u ∈ ({uv.1} : Finset (Fin n)),
          c u = c ((fun _ => uv.2) u)).card * Kc ≤ Kc ^ n := by
    intro uv _
    split_ifs with h
    · simp
    · have := card_compat_le (K := Kc) {uv.1} (fun _ => uv.2) (by
        intro u hu; rw [Finset.mem_singleton] at hu ⊢; rw [hu]; exact Ne.symm h)
      simpa using this
  calc _ ≤ ((X ×ˢ X).biUnion _).card * Kc := Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (∑ uv ∈ X ×ˢ X, (if uv.1 = uv.2 then ∅ else
          Finset.univ.filter fun c : Fin n → Fin Kc => ∀ u ∈ ({uv.1} : Finset (Fin n)),
            c u = c ((fun _ => uv.2) u)).card) * Kc :=
        Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ uv ∈ X ×ˢ X, (if uv.1 = uv.2 then ∅ else
          Finset.univ.filter fun c : Fin n → Fin Kc => ∀ u ∈ ({uv.1} : Finset (Fin n)),
            c u = c ((fun _ => uv.2) u)).card * Kc := Finset.sum_mul _ _ _
    _ ≤ ∑ _uv ∈ X ×ˢ X, Kc ^ n := Finset.sum_le_sum hone
    _ = X.card * X.card * Kc ^ n := by rw [Finset.sum_const, Finset.card_product, smul_eq_mul]

variable {n ℓ p gt}

/-- The approximation method: a monotone Boolean circuit with `s` gates that is `1` on all
`k` clique tests and `0` on all `Kc` coloring tests is large. -/
theorem approx_lb {k Kc s : ℕ} (hp : 2 ≤ p) (hℓ : 2 ≤ ℓ) (hk : ℓ + 1 ≤ k) (hkn : k ≤ n)
    (hKc : 1 ≤ Kc) (hs : 1 ≤ s) (hB : ∀ m, BoolGate (gt m))
    (hI : ∀ m v, gt m = .inp v → v ∈ edgeVars n)
    (hpos : ∀ K : Finset (Fin n), K.card = k → ∃ a : Assignment,
      (∀ u w : Fin n, u ≠ w → (a (eVar n u w) = true ↔ u ∈ K ∧ w ∈ K)) ∧
        gateValue a gt (s - 1) = 1)
    (hneg : ∀ c : Fin n → Fin Kc, ∃ a : Assignment,
      (∀ u w : Fin n, u ≠ w → (a (eVar n u w) = true ↔ c u ≠ c w)) ∧
        gateValue a gt (s - 1) = 0) :
    n.choose k ≤ s * (sfBound p ℓ * sfBound p ℓ * (n - (ℓ + 1)).choose (k - (ℓ + 1))) ∨
      Kc ^ n * Kc ≤ s * (sfBound p ℓ * sfBound p ℓ * sunE n Kc ℓ p) * Kc + ℓ * ℓ * Kc ^ n := by
  have hn : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  by_cases hemp : apx n ℓ p gt (s - 1) = ∅
  · left
    have hsub : Finset.univ.powersetCard k ⊆
        (Finset.range s).biUnion fun m => NewPos n ℓ p gt k m := by
      intro K hK
      have hKc := (Finset.mem_powersetCard.1 hK).2
      obtain ⟨a, ha, hv⟩ := hpos K hKc
      rcases pos_claim hℓ hB hI hKc a ha (s - 1) hv with hacc | ⟨m', hm', hK'⟩
      · rw [hemp] at hacc; obtain ⟨X, hX, _⟩ := hacc; simp at hX
      · exact Finset.mem_biUnion.2 ⟨m', Finset.mem_range.2 (by omega), hK'⟩
    calc n.choose k = (Finset.univ.powersetCard k : Finset (Finset (Fin n))).card := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ m ∈ Finset.range s, (NewPos n ℓ p gt k m).card := Finset.card_biUnion_le
      _ ≤ ∑ _m ∈ Finset.range s,
            sfBound p ℓ * sfBound p ℓ * (n - (ℓ + 1)).choose (k - (ℓ + 1)) :=
          Finset.sum_le_sum fun m _ => newPos_card n ℓ p gt hp hℓ hn hk hkn m
      _ = _ := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  · right
    obtain ⟨X, hX⟩ := Finset.nonempty_iff_ne_empty.2 hemp
    have hXs := apx_small n ℓ p gt hℓ (s - 1) X hX
    have hsub : (Finset.univ.filter fun c : Fin n → Fin Kc => Set.InjOn c X) ⊆
        (Finset.range s).biUnion fun m => NewNeg n ℓ p gt Kc m := by
      intro c hc
      have hinj := (Finset.mem_filter.1 hc).2
      obtain ⟨a, ha, hv⟩ := hneg c
      rcases neg_claim hB hI c a ha (s - 1) ⟨X, hX, isCl_negG.2 hinj⟩ with h1 | ⟨m', hm', hc'⟩
      · rw [hv] at h1; norm_num at h1
      · exact Finset.mem_biUnion.2 ⟨m', Finset.mem_range.2 (by omega), hc'⟩
    have hinj : (Finset.univ.filter fun c : Fin n → Fin Kc => Set.InjOn c X).card ≤
        s * (sfBound p ℓ * sfBound p ℓ * sunE n Kc ℓ p) := by
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ ∑ m ∈ Finset.range s, (NewNeg n ℓ p gt Kc m).card := Finset.card_biUnion_le
        _ ≤ ∑ _m ∈ Finset.range s, sfBound p ℓ * sfBound p ℓ * sunE n Kc ℓ p :=
            Finset.sum_le_sum fun m _ => newNeg_card n ℓ p gt hp hℓ hn hKc m
        _ = _ := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hnon := nonInj_card n (Kc := Kc) X
    have htot : Kc ^ n = (Finset.univ.filter fun c : Fin n → Fin Kc => Set.InjOn c X).card +
        (Finset.univ.filter fun c : Fin n → Fin Kc => ¬ Set.InjOn c X).card := by
      rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_fin]
    have hX2 : X.card * X.card * Kc ^ n ≤ ℓ * ℓ * Kc ^ n :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hXs.1 hXs.1)
    have e : Kc ^ n * Kc =
        (Finset.univ.filter fun c : Fin n → Fin Kc => Set.InjOn c X).card * Kc +
        (Finset.univ.filter fun c : Fin n → Fin Kc => ¬ Set.InjOn c X).card * Kc := by
      rw [← add_mul, ← htot]
    rw [e]
    have := Nat.mul_le_mul_right Kc hinj
    omega

/-! ## Test assignments -/

theorem eVar_div {n : ℕ} {u w : Fin n} (h : u ≠ w) :
    eVar n u w / n = min u.val w.val ∧ eVar n u w % n = max u.val w.val := by
  unfold eVar
  have hn : 0 < n := by have := u.isLt; omega
  have hmax : max u.val w.val < n := max_lt u.isLt w.isLt
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hmax]; simp
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hmax]

theorem min_ne_max_val {n : ℕ} {u w : Fin n} (h : u ≠ w) : min u.val w.val ≠ max u.val w.val := by
  have : u.val ≠ w.val := fun e => h (Fin.ext e)
  omega

/-- Edge part of an assignment from a graph on vertex indices. -/
def edgePart (n : ℕ) (E : ℕ → ℕ → Prop) (v : ℕ) : Bool :=
  decide (v / n < n ∧ v % n < n ∧ v / n ≠ v % n ∧ E (v / n) (v % n))

theorem edgePart_eVar {n : ℕ} (E : ℕ → ℕ → Prop) (hE : ∀ x y, E x y ↔ E y x) {u w : Fin n}
    (h : u ≠ w) : edgePart n E (eVar n u w) = true ↔ E u.val w.val := by
  unfold edgePart
  obtain ⟨h1, h2⟩ := eVar_div h
  rw [h1, h2, decide_eq_true_iff]
  have hne := min_ne_max_val h
  constructor
  · rintro ⟨_, _, _, hE'⟩
    rcases le_total u.val w.val with hle | hle
    · rwa [min_eq_left hle, max_eq_right hle] at hE'
    · rw [min_eq_right hle, max_eq_left hle] at hE'; exact (hE _ _).1 hE'
  · intro hE'
    refine ⟨min_lt_iff.2 (Or.inl u.isLt), max_lt u.isLt w.isLt, hne, ?_⟩
    rcases le_total u.val w.val with hle | hle
    · rwa [min_eq_left hle, max_eq_right hle]
    · rw [min_eq_right hle, max_eq_left hle]; exact (hE _ _).1 hE'

/-- Positive test assignment: edges of the clique `K` and its clique variables. -/
def posAssign (n k : ℕ) (K : Finset (Fin n)) (hK : K.card = k) : Assignment := fun v =>
  if v < n * n then edgePart n (fun x y => ∃ hx : x < n, ∃ hy : y < n,
      (⟨x, hx⟩ : Fin n) ∈ K ∧ (⟨y, hy⟩ : Fin n) ∈ K) v
  else decide (∃ u : Fin k, v = n * n + u.val * n + (K.orderEmbOfFin hK u).val)

/-- Negative test assignment: edges between different colors and the color variables. -/
def negAssign (n k : ℕ) (c : Fin n → Fin (k - 1)) : Assignment := fun v =>
  if v < n * n then edgePart n (fun x y => ∃ hx : x < n, ∃ hy : y < n,
      c ⟨x, hx⟩ ≠ c ⟨y, hy⟩) v
  else decide (∃ i : Fin n, v = n * n + k * n + i.val * (k - 1) + (c i).val)

theorem posAssign_edge {n k : ℕ} (K : Finset (Fin n)) (hK : K.card = k) {u w : Fin n}
    (h : u ≠ w) : posAssign n k K hK (eVar n u w) = true ↔ u ∈ K ∧ w ∈ K := by
  unfold posAssign
  rw [if_pos (eVar_lt u w), edgePart_eVar _ (by
    intro x y; constructor <;> rintro ⟨hx, hy, h1, h2⟩ <;> exact ⟨hy, hx, h2, h1⟩) h]
  constructor
  · rintro ⟨_, _, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨u.isLt, w.isLt, h1, h2⟩

theorem negAssign_edge {n k : ℕ} (c : Fin n → Fin (k - 1)) {u w : Fin n} (h : u ≠ w) :
    negAssign n k c (eVar n u w) = true ↔ c u ≠ c w := by
  unfold negAssign
  rw [if_pos (eVar_lt u w), edgePart_eVar _ (by
    intro x y; constructor <;> rintro ⟨hx, hy, h1⟩ <;> exact ⟨hy, hx, Ne.symm h1⟩) h]
  constructor
  · rintro ⟨_, _, h1⟩; exact h1
  · intro h1; exact ⟨u.isLt, w.isLt, h1⟩

theorem qVar_ge {n k : ℕ} (u : Fin k) (i : Fin n) : n * n ≤ qVar n u i := by
  unfold qVar; omega

theorem rVar_ge {n k m : ℕ} (i : Fin n) (c : Fin m) : n * n + k * n ≤ rVar n k i c := by
  unfold rVar; omega

theorem posAssign_q {n k : ℕ} (K : Finset (Fin n)) (hK : K.card = k) (u : Fin k) (i : Fin n) :
    posAssign n k K hK (qVar n u i) = true ↔ K.orderEmbOfFin hK u = i := by
  unfold posAssign
  rw [if_neg (by have := qVar_ge (k := k) u i; omega), decide_eq_true_iff]
  unfold qVar
  constructor
  · rintro ⟨u', he⟩
    have hi := i.isLt
    have hu := u.isLt; have hu' := u'.isLt
    have hv := (K.orderEmbOfFin hK u').isLt
    -- decode `u * n + i` uniquely
    have e1 : u.val * n + i.val = u'.val * n + (K.orderEmbOfFin hK u').val := by omega
    have hd1 : (u.val * n + i.val) / n = u.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi]; simp
    have hd2 : (u'.val * n + (K.orderEmbOfFin hK u').val) / n = u'.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv]; simp
    have huu : u = u' := Fin.ext (by rw [← hd1, e1, hd2])
    subst huu
    exact Fin.ext (by omega)
  · intro he; exact ⟨u, by rw [he]⟩

theorem negAssign_r {n k : ℕ} (c : Fin n → Fin (k - 1)) (i : Fin n) (col : Fin (k - 1)) :
    negAssign n k c (rVar n k i col) = true ↔ c i = col := by
  unfold negAssign
  rw [if_neg (by have h1 := rVar_ge (k := k) i col; omega),
    decide_eq_true_iff]
  unfold rVar
  constructor
  · rintro ⟨i', he⟩
    have hc := col.isLt
    have hc' := (c i').isLt
    have e1 : i.val * (k - 1) + col.val = i'.val * (k - 1) + (c i').val := by omega
    have hd1 : (i.val * (k - 1) + col.val) / (k - 1) = i.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc]; simp
    have hd2 : (i'.val * (k - 1) + (c i').val) / (k - 1) = i'.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc']; simp
    have hii : i = i' := Fin.ext (by rw [← hd1, e1, hd2])
    subst hii
    exact Fin.ext (by omega)
  · intro he; exact ⟨i, by rw [he]⟩

theorem posAssign_sat {n k : ℕ} (K : Finset (Fin n)) (hK : K.card = k) :
    cnfSat (posAssign n k K hK) (cliqueCNF n k) := by
  intro C hC
  simp only [cliqueCNF, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and] at hC
  rcases hC with (⟨u, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
  · exact ⟨⟨qVar n u (K.orderEmbOfFin hK u), true⟩,
      Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (posAssign_q K hK u _).2 rfl⟩
  · by_cases h1 : K.orderEmbOfFin hK t.1 = t.2.2
    · refine ⟨⟨qVar n t.2.1 t.2.2, false⟩, by simp, ?_⟩
      show posAssign n k K hK (qVar n t.2.1 t.2.2) = false
      rw [Bool.eq_false_iff]
      intro h2
      rw [posAssign_q] at h2
      exact ht ((K.orderEmbOfFin hK).injective (h1.trans h2.symm))
    · exact ⟨⟨qVar n t.1 t.2.2, false⟩, by simp, by
        show posAssign n k K hK (qVar n t.1 t.2.2) = false
        rw [Bool.eq_false_iff]; intro h2; rw [posAssign_q] at h2; exact h1 h2⟩
  · by_cases h1 : K.orderEmbOfFin hK t.1 = t.2.2.1
    · by_cases h2 : K.orderEmbOfFin hK t.2.1 = t.2.2.2
      · refine ⟨⟨eVar n t.2.2.1 t.2.2.2, true⟩, by simp, ?_⟩
        show posAssign n k K hK (eVar n t.2.2.1 t.2.2.2) = true
        rw [posAssign_edge K hK ht.2]
        rw [← h1, ← h2]
        exact ⟨Finset.orderEmbOfFin_mem _ _ _, Finset.orderEmbOfFin_mem _ _ _⟩
      · exact ⟨⟨qVar n t.2.1 t.2.2.2, false⟩, by simp, by
          show posAssign n k K hK (qVar n t.2.1 t.2.2.2) = false
          rw [Bool.eq_false_iff]; intro h; rw [posAssign_q] at h; exact h2 h⟩
    · exact ⟨⟨qVar n t.1 t.2.2.1, false⟩, by simp, by
        show posAssign n k K hK (qVar n t.1 t.2.2.1) = false
        rw [Bool.eq_false_iff]; intro h; rw [posAssign_q] at h; exact h1 h⟩

theorem negAssign_sat {n k : ℕ} (c : Fin n → Fin (k - 1)) :
    cnfSat (negAssign n k c) (colorCNF n k (k - 1)) := by
  intro C hC
  simp only [colorCNF, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and] at hC
  rcases hC with ⟨i, rfl⟩ | ⟨t, ht, rfl⟩
  · exact ⟨⟨rVar n k i (c i), true⟩, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩,
      (negAssign_r c i _).2 rfl⟩
  · by_cases h1 : c t.1 = t.2.2
    · by_cases h2 : c t.2.1 = t.2.2
      · refine ⟨⟨eVar n t.1 t.2.1, false⟩, by simp, ?_⟩
        show negAssign n k c (eVar n t.1 t.2.1) = false
        rw [Bool.eq_false_iff]
        intro h; rw [negAssign_edge c ht] at h; exact h (h1.trans h2.symm)
      · exact ⟨⟨rVar n k t.2.1 t.2.2, false⟩, by simp, by
          show negAssign n k c (rVar n k t.2.1 t.2.2) = false
          rw [Bool.eq_false_iff]; intro h; rw [negAssign_r] at h; exact h2 h⟩
    · exact ⟨⟨rVar n k t.1 t.2.2, false⟩, by simp, by
        show negAssign n k c (rVar n k t.1 t.2.2) = false
        rw [Bool.eq_false_iff]; intro h; rw [negAssign_r] at h; exact h1 h⟩

end

end SATurday.ProofComplexity
