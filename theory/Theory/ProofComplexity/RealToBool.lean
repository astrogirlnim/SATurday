import Theory.ProofComplexity.CliqueBound

/-!
# From monotone real circuits with few values to monotone Boolean circuits (R3)

If every gate of a monotone real circuit takes values in a finite set `U` on 0/1 inputs,
then the threshold functions `[g ≥ u]`, `u ∈ U`, are computed by a monotone Boolean
circuit with `2 + s |U| (2|U|)` gates: for a binary gate `h = f(x, y)`,
`[f(x, y) ≥ u] = ⋁_{a ∈ U} ([x ≥ a] ∧ [y ≥ β(a, u)])` with `β(a, u)` the least
`b ∈ U` such that `f(a, b) ≥ u`.

LOG: R3 RealToBool module (threshold conversion)
-/

namespace SATurday.ProofComplexity

open Finset

noncomputable section

open Classical

section Conv

variable (gt : ℕ → MGate) (s : ℕ) (U : Finset ℝ)

/-- Thresholds in increasing order. -/
def Ul : List ℝ := U.sort (· ≤ ·)

theorem Ul_length : (Ul U).length = U.card := Finset.length_sort _

/-- Threshold number `j`. -/
def uAt (j : ℕ) : ℝ := (Ul U).getD j 0

theorem uAt_mem {j : ℕ} (hj : j < U.card) : uAt U j ∈ U := by
  unfold uAt
  have hl : j < (Ul U).length := by rw [Ul_length]; exact hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  exact (Finset.mem_sort _).1 (List.getElem_mem hl)

/-- Index of a threshold. -/
def uIdx (x : ℝ) : ℕ := (Ul U).idxOf x

theorem uIdx_spec {x : ℝ} (hx : x ∈ U) : uIdx U x < U.card ∧ uAt U (uIdx U x) = x := by
  have hm : x ∈ Ul U := (Finset.mem_sort _).2 hx
  have hl := List.idxOf_lt_length_of_mem hm
  refine ⟨by rw [← Ul_length]; exact hl, ?_⟩
  unfold uAt uIdx
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  exact List.getElem_idxOf hl

/-- Least `b ∈ U` with `f a b ≥ u`. -/
def betaT (f : ℝ → ℝ → ℝ) (a u : ℝ) : Option ℝ :=
  if h : (U.filter fun b => u ≤ f a b).Nonempty then some ((U.filter fun b => u ≤ f a b).min' h)
  else none

/-- Width of a block: two gates per candidate `a`. -/
def bw : ℕ := 2 * U.card

/-- Start of the block computing `[g_m ≥ u_j]`. -/
def bStart (m j : ℕ) : ℕ := 2 + (m * U.card + j) * bw U

/-- Result gate of `[g_m ≥ u_j]`. -/
def bRes (m j : ℕ) : ℕ := bStart U m j + bw U - 1

/-- Gate `q` of the block `(m, j)`. -/
def blockGate (m j q : ℕ) : MGate :=
  match gt m with
  | .inp v =>
      if q = 0 then
        (if uAt U j ≤ 0 then .cst 1 else if uAt U j ≤ 1 then .inp v else .cst 0)
      else .op max (bStart U m j + q - 1) (bStart U m j + q - 1)
  | .cst c =>
      if q = 0 then (if uAt U j ≤ c then .cst 1 else .cst 0)
      else .op max (bStart U m j + q - 1) (bStart U m j + q - 1)
  | .op f i i' =>
      if q % 2 = 0 then
        (match betaT U f (uAt U (q / 2)) (uAt U j) with
         | some b => .op min (bRes U i (q / 2)) (bRes U i' (uIdx U b))
         | none => .cst 0)
      else .op max (if q = 1 then 0 else bStart U m j + q - 2) (bStart U m j + q - 1)

/-- The Boolean circuit, as a gate function; gate `boolLen` is the output. -/
def boolLen : ℕ := 2 + s * U.card * bw U

def boolGate (jt : ℕ) (idx : ℕ) : MGate :=
  if idx = 0 then .cst 0
  else if idx = 1 then .cst 1
  else if idx < boolLen s U then
    blockGate gt U ((idx - 2) / bw U / U.card) ((idx - 2) / bw U % U.card) ((idx - 2) % bw U)
  else .op max (bRes U (s - 1) jt) (bRes U (s - 1) jt)

theorem boolGate_block (jt : ℕ) {m j q : ℕ} (hm : m < s) (hj : j < U.card) (hq : q < bw U) :
    boolGate gt s U jt (bStart U m j + q) = blockGate gt U m j q := by
  have hbw : 0 < bw U := by omega
  unfold boolGate bStart
  have h0 : 2 + (m * U.card + j) * bw U + q ≠ 0 := by omega
  have h1 : 2 + (m * U.card + j) * bw U + q ≠ 1 := by omega
  have hlt : 2 + (m * U.card + j) * bw U + q < boolLen s U := by
    unfold boolLen
    have : (m * U.card + j + 1) * bw U ≤ s * U.card * bw U := by
      apply Nat.mul_le_mul_right
      have : (m + 1) * U.card ≤ s * U.card := Nat.mul_le_mul_right _ hm
      nlinarith
    nlinarith
  rw [if_neg h0, if_neg h1, if_pos hlt]
  have e : 2 + (m * U.card + j) * bw U + q - 2 = q + (m * U.card + j) * bw U := by omega
  rw [e, Nat.add_mul_div_right _ _ hbw, Nat.div_eq_of_lt hq, Nat.zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
  have hd : (m * U.card + j) / U.card = m := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj]; simp
  have hmod : (m * U.card + j) % U.card = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  rw [hd, hmod]

end Conv

section Correct

variable {gt : ℕ → MGate} {s : ℕ} {U : Finset ℝ}

theorem bRes_lt_bStart {i m j α : ℕ} (him : i < m) (hα : α < U.card) :
    bRes U i α < bStart U m j := by
  unfold bRes bStart bw
  have h1 : (i * U.card + α + 1) * (2 * U.card) ≤ (m * U.card + j) * (2 * U.card) := by
    apply Nat.mul_le_mul_right
    have : (i + 1) * U.card ≤ m * U.card := Nat.mul_le_mul_right _ him
    nlinarith
  have : 0 < 2 * U.card := by omega
  have e : (i * U.card + α) * (2 * U.card) + 2 * U.card = (i * U.card + α + 1) * (2 * U.card) := by
    ring
  omega

/-- `[u ≤ f x y]` as a finite disjunction over thresholds. -/
theorem thresh_iff {f : ℝ → ℝ → ℝ}
    (hf : ∀ x x' y y' : ℝ, x ≤ x' → y ≤ y' → f x y ≤ f x' y') {x y u : ℝ}
    (hx : x ∈ U) (hy : y ∈ U) :
    (∃ α < U.card, uAt U α ≤ x ∧ ∃ b, betaT U f (uAt U α) u = some b ∧ b ≤ y) ↔ u ≤ f x y := by
  constructor
  · rintro ⟨α, hα, hax, b, hb, hby⟩
    unfold betaT at hb
    split_ifs at hb with hne
    cases hb
    have hmem := Finset.min'_mem _ hne
    have hub := (Finset.mem_filter.1 hmem).2
    exact hub.trans (hf _ _ _ _ hax hby)
  · intro h
    obtain ⟨hlt, hx'⟩ := uIdx_spec U hx
    refine ⟨uIdx U x, hlt, hx'.le, ?_⟩
    have hne : (U.filter fun b => u ≤ f (uAt U (uIdx U x)) b).Nonempty :=
      ⟨y, Finset.mem_filter.2 ⟨hy, by rw [hx']; exact h⟩⟩
    refine ⟨_, by unfold betaT; rw [dif_pos hne], Finset.min'_le _ _ ?_⟩
    exact Finset.mem_filter.2 ⟨hy, by rw [hx']; exact h⟩

variable (a : Assignment) (jt : ℕ)

/-- Boolean gate values (of `boolGate`). -/
abbrev bv (gt : ℕ → MGate) (s : ℕ) (U : Finset ℝ) (a : Assignment) (jt idx : ℕ) : ℝ :=
  gateValue a (boolGate gt s U jt) idx

theorem bv_read {idx i : ℕ} (h : i < idx) :
    (mcVals a ((List.range idx).map (boolGate gt s U jt))).getD i 0 = bv gt s U a jt i :=
  read_earlier a _ h

/-- Copy gates keep the value along a block. -/
theorem bv_copy {m j : ℕ} (hm : m < s) (hj : j < U.card)
    (hcopy : ∀ q, 0 < q → q < bw U →
      blockGate gt U m j q = .op max (bStart U m j + q - 1) (bStart U m j + q - 1)) :
    ∀ q, q < bw U → bv gt s U a jt (bStart U m j + q) = bv gt s U a jt (bStart U m j) := by
  intro q
  induction q with
  | zero => intro _; rfl
  | succ q ih =>
      intro hq
      have hg := boolGate_block gt s U jt hm hj hq
      rw [hcopy (q + 1) (by omega) hq] at hg
      have hv : bv gt s U a jt (bStart U m j + (q + 1)) =
          (boolGate gt s U jt (bStart U m j + (q + 1))).val a
            (mcVals a ((List.range (bStart U m j + (q + 1))).map (boolGate gt s U jt))) := rfl
      rw [hv, hg]
      simp only [MGate.val]
      have e : bStart U m j + (q + 1) - 1 = bStart U m j + q := by omega
      rw [e, bv_read a jt (by omega), ih (by omega), max_self]

end Correct

section Main

variable {gt : ℕ → MGate} {s : ℕ} {U : Finset ℝ} (a : Assignment) (jt : ℕ)

theorem bv_gate (idx : ℕ) :
    bv gt s U a jt idx = (boolGate gt s U jt idx).val a
      (mcVals a ((List.range idx).map (boolGate gt s U jt))) := rfl

theorem real_read {m i : ℕ} (h : i < m) :
    (mcVals a ((List.range m).map gt)).getD i 0 = gateValue a gt i := read_earlier a gt h

theorem bw_pos (hU : 0 < U.card) : 0 < bw U := by unfold bw; omega

/-- Correctness of the threshold blocks. -/
theorem bv_res (hU : 0 < U.card)
    (hWF : ∀ m < s, ∀ f i i', gt m = .op f i i' → i < m ∧ i' < m)
    (hMono : ∀ m < s, (gt m).Mono) (hT : ∀ m < s, gateValue a gt m ∈ U) :
    ∀ m < s, ∀ j < U.card,
      bv gt s U a jt (bRes U m j) = if uAt U j ≤ gateValue a gt m then 1 else 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm j hj
  have hbw := bw_pos hU
  have hres : bRes U m j = bStart U m j + (bw U - 1) := by unfold bRes; omega
  have hreal : gateValue a gt m = (gt m).val a (mcVals a ((List.range m).map gt)) := rfl
  rcases hgm : gt m with v | c | ⟨f, i, i'⟩
  · -- input
    have hcopy : ∀ q, 0 < q → q < bw U →
        blockGate gt U m j q = .op max (bStart U m j + q - 1) (bStart U m j + q - 1) := by
      intro q hq _; unfold blockGate; rw [hgm]; simp [Nat.pos_iff_ne_zero.1 hq]
    rw [hres, bv_copy a jt hm hj hcopy _ (by omega), bv_gate,
      show bStart U m j = bStart U m j + 0 from rfl, boolGate_block gt s U jt hm hj hbw]
    unfold blockGate
    rw [hgm, hreal, hgm]
    simp only [if_true, MGate.val]
    by_cases h0 : uAt U j ≤ 0
    · rw [if_pos h0]; simp only [MGate.val]
      rw [if_pos (by split_ifs <;> linarith)]
    · rw [if_neg h0]
      by_cases h1 : uAt U j ≤ 1
      · rw [if_pos h1]; simp only [MGate.val]
        by_cases hav : a v = true
        · simp [hav, h1]
        · simp only [hav, if_false, Bool.false_eq_true]
          rw [if_neg (by linarith)]
      · rw [if_neg h1]; simp only [MGate.val]
        rw [if_neg]
        split_ifs <;> linarith
  · -- constant
    have hcopy : ∀ q, 0 < q → q < bw U →
        blockGate gt U m j q = .op max (bStart U m j + q - 1) (bStart U m j + q - 1) := by
      intro q hq _; unfold blockGate; rw [hgm]; simp [Nat.pos_iff_ne_zero.1 hq]
    rw [hres, bv_copy a jt hm hj hcopy _ (by omega), bv_gate,
      show bStart U m j = bStart U m j + 0 from rfl, boolGate_block gt s U jt hm hj hbw]
    unfold blockGate
    rw [hgm, hreal, hgm]
    simp only [if_true, MGate.val]
    split_ifs <;> rfl
  · -- binary gate
    obtain ⟨hi, hi'⟩ := hWF m hm f i i' hgm
    have hxi := hT i (by omega)
    have hxi' := hT i' (by omega)
    set xi := gateValue a gt i
    set xi' := gateValue a gt i'
    let term : ℕ → Prop := fun α =>
      uAt U α ≤ xi ∧ ∃ b, betaT U f (uAt U α) (uAt U j) = some b ∧ b ≤ xi'
    -- term gates
    have hterm : ∀ α < U.card, bv gt s U a jt (bStart U m j + 2 * α) =
        if term α then 1 else 0 := by
      intro α hα
      rw [bv_gate, boolGate_block gt s U jt hm hj (by unfold bw; omega)]
      unfold blockGate
      rw [hgm]
      simp only [Nat.mul_mod_right, if_true, Nat.mul_div_cancel_left α (by norm_num : 0 < 2)]
      by_cases hex : ∃ b, betaT U f (uAt U α) (uAt U j) = some b
      swap
      · have hb : betaT U f (uAt U α) (uAt U j) = none := by
          cases h : betaT U f (uAt U α) (uAt U j) with
          | none => rfl
          | some b => exact absurd ⟨b, h⟩ hex
        simp only [hb, MGate.val]
        rw [if_neg]
        rintro ⟨_, b, hb', _⟩; exact hex ⟨b, hb'⟩
      · obtain ⟨b, hb⟩ := hex
        simp only [hb, MGate.val]
        have hbU : b ∈ U := by
          unfold betaT at hb
          split_ifs at hb with hne
          cases hb
          exact (Finset.mem_filter.1 (Finset.min'_mem _ hne)).1
        obtain ⟨hbl, hbe⟩ := uIdx_spec U hbU
        have r1 : bRes U i α < bStart U m j + 2 * α :=
          (bRes_lt_bStart (j := j) hi hα).trans_le (by omega)
        have r2 : bRes U i' (uIdx U b) < bStart U m j + 2 * α :=
          (bRes_lt_bStart (j := j) hi' hbl).trans_le (by omega)
        rw [bv_read a jt r1, bv_read a jt r2,
          ih i hi (by omega) α hα, ih i' hi' (by omega) _ hbl, hbe]
        by_cases h1 : uAt U α ≤ xi
        · by_cases h2 : b ≤ xi'
          · rw [if_pos h1, if_pos h2, if_pos (show term α from ⟨h1, b, hb, h2⟩)]; norm_num
          · rw [if_pos h1, if_neg h2, if_neg (show ¬ term α from by
              rintro ⟨_, b', hb', hb''⟩; rw [hb] at hb'; cases hb'; exact h2 hb'')]
            norm_num
        · rw [if_neg (show ¬ term α from fun h => h1 h.1), if_neg h1]
          split_ifs <;> norm_num
    -- accumulation gates
    have hacc : ∀ α < U.card, bv gt s U a jt (bStart U m j + (2 * α + 1)) =
        if ∃ α' ≤ α, term α' then 1 else 0 := by
      intro α
      induction α with
      | zero =>
          intro hα
          rw [bv_gate, boolGate_block gt s U jt hm hj (by unfold bw; omega)]
          unfold blockGate
          rw [hgm]
          simp only [show (2 * 0 + 1) % 2 = 1 by norm_num, show (1 : ℕ) ≠ 0 by norm_num,
            if_false, show 2 * 0 + 1 = 1 by norm_num, if_true, MGate.val]
          have h0 : (mcVals a ((List.range (bStart U m j + 1)).map (boolGate gt s U jt))).getD 0 0
              = 0 := by
            rw [bv_read a jt (by unfold bStart; omega)]
            rw [bv_gate]; unfold boolGate; simp [MGate.val]
          have h1 : (mcVals a ((List.range (bStart U m j + 1)).map (boolGate gt s U jt))).getD
              (bStart U m j + 1 - 1) 0 = if term 0 then 1 else 0 := by
            rw [Nat.add_sub_cancel, bv_read a jt (by omega)]
            have := hterm 0 hα; simpa using this
          rw [h0, h1]
          by_cases ht : term 0
          · rw [if_pos ht, if_pos ⟨0, le_rfl, ht⟩]; norm_num
          · rw [if_neg ht, if_neg]; · norm_num
            rintro ⟨α', hα', ht'⟩
            have : α' = 0 := by omega
            subst this; exact ht ht'
      | succ α ih' =>
          intro hα
          have hprev := ih' (by omega)
          rw [bv_gate, boolGate_block gt s U jt hm hj (by unfold bw; omega)]
          unfold blockGate
          rw [hgm]
          have hodd : (2 * (α + 1) + 1) % 2 = 1 := by omega
          have hne1 : 2 * (α + 1) + 1 ≠ 1 := by omega
          simp only [hodd, show (1 : ℕ) ≠ 0 by norm_num, if_false, hne1, MGate.val]
          have e1 : bStart U m j + (2 * (α + 1) + 1) - 2 = bStart U m j + (2 * α + 1) := by omega
          have e2 : bStart U m j + (2 * (α + 1) + 1) - 1 = bStart U m j + 2 * (α + 1) := by omega
          rw [e1, e2, bv_read a jt (by omega), bv_read a jt (by omega), hprev,
            hterm (α + 1) hα]
          by_cases h1 : ∃ α' ≤ α, term α'
          · obtain ⟨α', h1', h2'⟩ := h1
            rw [if_pos (show ∃ α'' ≤ α, term α'' from ⟨α', h1', h2'⟩),
              if_pos (show ∃ α'' ≤ α + 1, term α'' from ⟨α', by omega, h2'⟩)]
            split_ifs <;> norm_num
          · rw [if_neg h1]
            by_cases h2 : term (α + 1)
            · rw [if_pos h2, if_pos (show ∃ α'' ≤ α + 1, term α'' from ⟨α + 1, le_rfl, h2⟩)]
              norm_num
            · rw [if_neg h2, if_neg]; · norm_num
              rintro ⟨α', hα', ht'⟩
              rcases Nat.lt_or_ge α' (α + 1) with h | h
              · exact h1 ⟨α', by omega, ht'⟩
              · have : α' = α + 1 := by omega
                subst this; exact h2 ht'
    -- conclude
    have hlast := hacc (U.card - 1) (by omega)
    have e : bStart U m j + (2 * (U.card - 1) + 1) = bRes U m j := by unfold bRes bw; omega
    rw [e] at hlast
    have hx : gateValue a gt m = f xi xi' := by
      rw [hreal, hgm]; simp only [MGate.val]; rw [real_read a hi, real_read a hi']
    rw [hlast, hx]
    have hmono := hMono m hm
    rw [hgm] at hmono
    have key := thresh_iff (U := U) (f := f) hmono hxi hxi' (u := uAt U j)
    by_cases hh : uAt U j ≤ f xi xi'
    · rw [if_pos hh, if_pos]
      obtain ⟨α, hα, h⟩ := key.2 hh
      exact ⟨α, by omega, h⟩
    · rw [if_neg hh, if_neg]
      rintro ⟨α, hα, h⟩
      exact hh (key.1 ⟨α, by omega, h⟩)

end Main

section Package

theorem blk_lt {s : ℕ} {U : Finset ℝ} {idx : ℕ} (hU : 0 < U.card) (h2 : 2 ≤ idx)
    (hlt : idx < boolLen s U) : (idx - 2) / bw U / U.card < s := by
  unfold boolLen at hlt
  have hbw : 0 < bw U := by unfold bw; omega
  rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by positivity)]
  calc idx - 2 < s * U.card * bw U := by omega
    _ = s * (bw U * U.card) := by ring

theorem blockGate_bool (gt : ℕ → MGate) (U : Finset ℝ) {m j q : ℕ} :
    BoolGate (blockGate gt U m j q) := by
  unfold blockGate
  cases gt m with
  | inp v =>
      dsimp only
      split_ifs
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inl ⟨v, rfl⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩)))
  | cst c =>
      dsimp only
      split_ifs
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩)))
  | op f i i' =>
      dsimp only
      split_ifs
      · cases betaT U f (uAt U (q / 2)) (uAt U j) with
        | none => exact Or.inr (Or.inl rfl)
        | some b => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩)))

theorem blockGate_inp (gt : ℕ → MGate) (U : Finset ℝ) {m j q v : ℕ}
    (h : blockGate gt U m j q = .inp v) : gt m = .inp v := by
  unfold blockGate at h
  cases hg : gt m with
  | inp w =>
      rw [hg] at h; dsimp only at h
      split_ifs at h <;> simp_all
  | cst c =>
      rw [hg] at h; dsimp only at h
      split_ifs at h <;> simp_all
  | op f i i' =>
      rw [hg] at h; dsimp only at h
      split_ifs at h
      · cases hb : betaT U f (uAt U (q / 2)) (uAt U j) <;> rw [hb] at h <;> simp_all
      all_goals simp_all

theorem bRes_lt_boolLen {s : ℕ} {U : Finset ℝ} (hU : 0 < U.card) (hs : 1 ≤ s) {j : ℕ}
    (hj : j < U.card) : bRes U (s - 1) j < boolLen s U := by
  unfold bRes bStart boolLen bw
  have h1 : ((s - 1) * U.card + j + 1) * (2 * U.card) ≤ s * U.card * (2 * U.card) := by
    apply Nat.mul_le_mul_right
    have : (s - 1) * U.card + U.card = s * U.card := by
      rw [← Nat.succ_mul]; congr 1; omega
    omega
  have e : ((s - 1) * U.card + j) * (2 * U.card) + 2 * U.card =
      ((s - 1) * U.card + j + 1) * (2 * U.card) := by ring
  omega

/-- Monotone real circuits whose gates take values in a finite set `U` become monotone
Boolean circuits computing any threshold `[out ≥ t]`, `t ∈ U`. -/
theorem real_to_bool (gt : ℕ → MGate) (s : ℕ) (U : Finset ℝ) (P : Finset ℕ) (hs : 1 ≤ s)
    (hWF : ∀ m < s, ∀ f i i', gt m = .op f i i' → i < m ∧ i' < m)
    (hMono : ∀ m < s, (gt m).Mono) (hInp : ∀ m < s, ∀ v, gt m = .inp v → v ∈ P)
    (hT : ∀ a, ∀ m < s, gateValue a gt m ∈ U) {t : ℝ} (ht : t ∈ U) :
    ∃ B : List MGate, MCBool B ∧ MCInputsIn P B ∧ B.length = boolLen s U + 1 ∧
      ∀ a, mcEval a B = if t ≤ gateValue a gt (s - 1) then 1 else 0 := by
  have hU : 0 < U.card := Finset.card_pos.2 ⟨t, ht⟩
  set jt := uIdx U t
  obtain ⟨hjt, hjte⟩ := uIdx_spec U ht
  refine ⟨(List.range (boolLen s U + 1)).map (boolGate gt s U jt), ?_, ?_, by simp, ?_⟩
  · intro g hg
    obtain ⟨idx, hidx, rfl⟩ := List.mem_map.1 hg
    unfold boolGate
    split_ifs
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact blockGate_bool gt U
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩)))
  · intro v hv
    obtain ⟨idx, _, hidx⟩ := List.mem_map.1 hv
    unfold boolGate at hidx
    by_cases h0 : idx = 0
    · rw [if_pos h0] at hidx; cases hidx
    by_cases h1 : idx = 1
    · rw [if_neg h0, if_pos h1] at hidx; cases hidx
    by_cases h2 : idx < boolLen s U
    · rw [if_neg h0, if_neg h1, if_pos h2] at hidx
      exact hInp _ (blk_lt hU (by omega) h2) v (blockGate_inp gt U hidx)
    · rw [if_neg h0, if_neg h1, if_neg h2] at hidx; cases hidx
  · intro a
    rw [mcEval_range]
    have hfin : boolGate gt s U jt (boolLen s U) = .op max (bRes U (s - 1) jt) (bRes U (s - 1) jt) := by
      unfold boolGate
      have : boolLen s U ≠ 0 := by unfold boolLen; omega
      have : boolLen s U ≠ 1 := by unfold boolLen; omega
      simp [*]
    rw [show gateValue a (boolGate gt s U jt) (boolLen s U) = bv gt s U a jt (boolLen s U) from rfl,
      bv_gate, hfin]
    simp only [MGate.val]
    rw [bv_read a jt (bRes_lt_boolLen hU hs hjt), max_self,
      bv_res a jt hU hWF hMono (fun m hm => hT a m hm) (s - 1) (by omega) jt hjt, hjte]

end Package

end

end SATurday.ProofComplexity
