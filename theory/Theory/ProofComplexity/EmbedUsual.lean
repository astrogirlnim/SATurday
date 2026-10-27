import Theory.ProofComplexity.EmbedPangBack

/-!
# The usual literal encoding `x = 1` and the `-x = -1` encoding of `EmbedPang`

(Referee leftover, dossier Section 16 (i) and Section 17 item 1.)

`EmbedPang` encodes a positive literal `x` as `-x = -1` (`litLE`), so that `phi (litLE l)` is
Pang's literal polynomial. The usual encoding is `x = 1` (`litLEU`). The two clause encodings
are related by one `comb` line per literal: `A ∨ (-x = -1)` yields `A ∨ (x = 1)` by the
combination `(-1) * e + 0 * e` of the equation with itself (and conversely), where `A` is
unchanged. This file proves

* `conv_lines`: from the line `C.image s` one obtains the line `C.image t` with at most `C.card`
  additional lines, when `t l = cmb a 0 (s l) (s l)` for each literal and different literals have
  different `s`-images and `t l' ≠ s l`;
* `swap_axioms`: a derivation from the `t`-encoded axiom clauses (plus common axioms `B`) gives
  one from the `s`-encoded clauses with at most `sum (C.card + 1)` extra lines, the sum over the
  clauses of `Φ` whose `t`-line occurs in the derivation;
* `rldag_usual_to_pang`: `RLDag` refutation from the usual encoding gives a `Pang.Refutation`
  with `n + cost + 1` nodes;
* `pang_to_rldag_usual`: a `Pang.Refutation` with `S` nodes gives an `RLDag` refutation from the
  usual encoding with at most `2 S + cost` lines.
-/

open SATurday.ProofComplexity MvPolynomial

namespace SATurday.ProofComplexity

namespace RLF

noncomputable section

open Classical

variable {p : ℕ} [Fact p.Prime]

local instance instDecEqLEq'' : DecidableEq (LEq (ZMod p)) := leqDec (ZMod p)

/-- The usual encoding of a literal: `x = 1` for a positive literal, `x = 0` for a negative one. -/
def litLEU (l : Literal) : LEq (ZMod p) :=
  (Finsupp.single l.var 1, if l.pos then 1 else 0)

/-- A clause in the usual encoding. -/
def axClauseU (C : Clause) : Finset (LEq (ZMod p)) := C.image litLEU

/-- The CNF `Φ` as linear clauses, usual encoding. -/
def linAxU (Φ : CNF) : Set (Finset (LEq (ZMod p))) := {L | ∃ C ∈ Φ, L = axClauseU C}

section Generic

variable (s t : Literal → LEq (ZMod p))

/-- Hypotheses of the conversion. -/
structure ConvHyp : Prop where
  comb : ∀ l, ∃ a : ZMod p, t l = cmb a 0 (s l) (s l)
  sep : ∀ l l', l' ≠ l → s l' ≠ s l ∧ t l' ≠ s l

/-- The partially converted line: literals in `S` are encoded by `t`, the others by `s`. -/
def mixLine (S C : Clause) : Finset (LEq (ZMod p)) :=
  C.image fun l => if l ∈ S then t l else s l

theorem conv_lines {Ax : Set (Finset (LEq (ZMod p)))} (hyp : ConvHyp s t) {𝓛 : Finset (Finset (LEq (ZMod p)))}
    (hD : RLDag Ax 𝓛) (C : Clause) (h0 : C.image s ∈ 𝓛) :
    ∃ E : Finset (Finset (LEq (ZMod p))), RLDag Ax (𝓛 ∪ E) ∧ C.image t ∈ 𝓛 ∪ E ∧
      E.card ≤ C.card := by
  have key : ∀ S : Clause, S ⊆ C → ∃ E : Finset (Finset (LEq (ZMod p))),
      RLDag Ax (𝓛 ∪ E) ∧ mixLine s t S C ∈ 𝓛 ∪ E ∧ E.card ≤ S.card := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨∅, by simpa using hD, ?_, by simp⟩
      have : mixLine s t ∅ C = C.image s := by simp [mixLine]
      rw [this]; simpa using h0
    | @insert l S hl ih =>
      intro hsub
      obtain ⟨E, hE, hm, hc⟩ := ih ((Finset.subset_insert _ _).trans hsub)
      have hlC : l ∈ C := hsub (Finset.mem_insert_self _ _)
      have hel : s l ∈ mixLine s t S C := by
        refine Finset.mem_image.2 ⟨l, hlC, by simp [hl]⟩
      obtain ⟨a, ha⟩ := hyp.comb l
      have hstep := RLDag.comb (mixLine s t S C) (mixLine s t S C) (s l) (s l) a 0 hE hm hm hel hel
      have heq : (mixLine s t S C).erase (s l) ∪ (mixLine s t S C).erase (s l) ∪ {cmb a 0 (s l) (s l)}
          = mixLine s t (insert l S) C := by
        rw [Finset.union_self, ← ha]
        ext e
        simp only [mixLine, Finset.mem_union, Finset.mem_erase, Finset.mem_image,
          Finset.mem_singleton, Finset.mem_insert]
        constructor
        · rintro (⟨hne, l', hl', rfl⟩ | rfl)
          · refine ⟨l', hl', ?_⟩
            by_cases hl'l : l' = l
            · subst hl'l; exact absurd (by simp [hl]) hne
            · simp [hl'l]
          · exact ⟨l, hlC, by simp⟩
        · rintro ⟨l', hl', rfl⟩
          by_cases hl'l : l' = l
          · subst hl'l; right; simp
          · left
            refine ⟨?_, l', hl', by simp [hl'l]⟩
            have := hyp.sep l l' hl'l |>.1
            have h2 := (hyp.sep l l' hl'l).2
            by_cases hm' : l' ∈ S
            · have hin : l' ∈ insert l S := Finset.mem_insert_of_mem hm'
              simp [hl'l, hm']; exact h2
            · have hin : l' ∉ insert l S := by simp [hm', hl'l]
              simp [hl'l, hm']; exact this
      rw [heq] at hstep
      refine ⟨insert (mixLine s t (insert l S) C) E, ?_, ?_, ?_⟩
      · have : 𝓛 ∪ insert (mixLine s t (insert l S) C) E = insert (mixLine s t (insert l S) C) (𝓛 ∪ E) :=
          Finset.union_insert _ _ _
        rw [this]; exact hstep
      · simp
      · have := Finset.card_insert_le (mixLine s t (insert l S) C) E
        rw [Finset.card_insert_of_notMem hl]; omega
  obtain ⟨E, hE, hm, hc⟩ := key C (Finset.Subset.refl C)
  refine ⟨E, hE, ?_, hc⟩
  have : mixLine s t C C = C.image t :=
    Finset.image_congr fun l hl => if_pos (Finset.mem_coe.1 hl)
  rwa [this] at hm

/-- Axiom clauses of `Φ` under a literal encoding `e`. -/
def encAx (e : Literal → LEq (ZMod p)) (Φ : CNF) : Set (Finset (LEq (ZMod p))) :=
  {L | ∃ C ∈ Φ, L = C.image e}

/-- The cost of the encoding change: one more than the width of each clause of `Φ` whose
`t`-encoding occurs in `𝓛`. -/
def encCost (t : Literal → LEq (ZMod p)) (Φ : CNF) (𝓛 : Finset (Finset (LEq (ZMod p)))) : ℕ :=
  ∑ C ∈ Φ.filter (fun C => C.image t ∈ 𝓛), (C.card + 1)

theorem encCost_mono (t : Literal → LEq (ZMod p)) (Φ : CNF) {𝓛 𝓛' : Finset (Finset (LEq (ZMod p)))}
    (h : 𝓛 ⊆ 𝓛') : encCost t Φ 𝓛 ≤ encCost t Φ 𝓛' := by
  unfold encCost
  refine Finset.sum_le_sum_of_subset ?_
  intro C hC
  rw [Finset.mem_filter] at hC ⊢
  exact ⟨hC.1, h hC.2⟩

theorem swap_axioms (hyp : ConvHyp s t) (Φ : CNF) (B : Set (Finset (LEq (ZMod p))))
    {𝓛 : Finset (Finset (LEq (ZMod p)))} (h : RLDag (encAx t Φ ∪ B) 𝓛) :
    ∃ E : Finset (Finset (LEq (ZMod p))), RLDag (encAx s Φ ∪ B) (𝓛 ∪ E) ∧
      E.card ≤ encCost t Φ 𝓛 := by
  induction h with
  | empty => exact ⟨∅, by simpa using RLDag.empty, by simp⟩
  | @ax 𝓛 C0 hD hC0 ih =>
    obtain ⟨E, hE, hc⟩ := ih
    by_cases hmem : C0 ∈ 𝓛
    · rw [Finset.insert_eq_of_mem hmem]; exact ⟨E, hE, hc⟩
    · rcases hC0 with ⟨C, hC, rfl⟩ | hB
      · have h1 := RLDag.ax (C.image s) hE (Or.inl ⟨C, hC, rfl⟩)
        have h2 := Finset.mem_insert_self (C.image s) (𝓛 ∪ E)
        obtain ⟨E2, hE2, hm2, hc2⟩ := conv_lines s t hyp h1 C h2
        refine ⟨insert (C.image s) (E ∪ E2), ?_, ?_⟩
        · have : insert (C.image t) 𝓛 ∪ insert (C.image s) (E ∪ E2)
              = insert (C.image s) (𝓛 ∪ E) ∪ E2 := by
            ext X
            simp only [Finset.mem_union, Finset.mem_insert]
            have hm3 : C.image t ∈ insert (C.image s) (𝓛 ∪ E) ∪ E2 := hm2
            simp only [Finset.mem_union, Finset.mem_insert] at hm3
            constructor
            · rintro ((rfl | h) | (rfl | h | h))
              · exact hm3
              · tauto
              · tauto
              · tauto
              · tauto
            · tauto
          rw [this]; exact hE2
        · have hsum : encCost t Φ 𝓛 + (C.card + 1) ≤ encCost t Φ (insert (C.image t) 𝓛) := by
            unfold encCost
            have hnot : C ∉ Φ.filter (fun D => D.image t ∈ 𝓛) := by
              intro hh; exact hmem (Finset.mem_filter.1 hh).2
            rw [add_comm, ← Finset.sum_insert hnot (f := fun C : Clause => C.card + 1)]
            refine Finset.sum_le_sum_of_subset ?_
            intro D hD'
            rcases Finset.mem_insert.1 hD' with rfl | hD'
            · exact Finset.mem_filter.2 ⟨hC, Finset.mem_insert_self _ _⟩
            · have := Finset.mem_filter.1 hD'
              exact Finset.mem_filter.2 ⟨this.1, Finset.mem_insert_of_mem this.2⟩
          have := Finset.card_insert_le (C.image s) (E ∪ E2)
          have := Finset.card_union_le E E2
          omega
      · refine ⟨E, ?_, hc.trans (encCost_mono t Φ (Finset.subset_insert _ _))⟩
        rw [Finset.insert_union]; exact RLDag.ax C0 hE (Or.inr hB)
  | @weak 𝓛 L L' hD hL hsub ih =>
    obtain ⟨E, hE, hc⟩ := ih
    refine ⟨E, ?_, hc.trans (encCost_mono t Φ (Finset.subset_insert _ _))⟩
    rw [Finset.insert_union]
    exact RLDag.weak L L' hE (Finset.mem_union_left _ hL) hsub
  | @comb 𝓛 A B' e1 e2 α β hD hA hB he1 he2 ih =>
    obtain ⟨E, hE, hc⟩ := ih
    refine ⟨E, ?_, hc.trans (encCost_mono t Φ (Finset.subset_insert _ _))⟩
    rw [Finset.insert_union]
    exact RLDag.comb A B' e1 e2 α β hE (Finset.mem_union_left _ hA) (Finset.mem_union_left _ hB)
      he1 he2
  | @simp 𝓛 L c hD hc h0 ih =>
    obtain ⟨E, hE, hcE⟩ := ih
    refine ⟨E, ?_, hcE.trans (encCost_mono t Φ (Finset.subset_insert _ _))⟩
    rw [Finset.insert_union]
    exact RLDag.simp L c hE hc (Finset.mem_union_left _ h0)

theorem single_one_inj {i j : ℕ} (h : (Finsupp.single i (1 : ZMod p)) = Finsupp.single j 1) : i = j :=
  (Finsupp.single_left_inj (one_ne_zero)).1 h

theorem single_one_neg_inj {i j : ℕ} (h : (Finsupp.single i (1 : ZMod p)) = -Finsupp.single j 1) :
    i = j := by
  rw [← Finsupp.single_neg] at h
  by_contra hij
  have := DFunLike.congr_fun h i
  simp [Finsupp.single_apply, Ne.symm hij] at this

theorem neg_single_one_inj {i j : ℕ} (h : -(Finsupp.single i (1 : ZMod p)) = Finsupp.single j 1) :
    i = j := single_one_neg_inj (by rw [← h]; simp)

theorem convHyp_forward : ConvHyp (litLE (p := p)) litLEU := by
  constructor
  · intro l
    by_cases hl : l.pos
    · exact ⟨-1, by simp [litLE, litLEU, cmb, hl]⟩
    · exact ⟨1, by simp [litLE, litLEU, cmb, hl]⟩
  · intro l l' hne
    obtain ⟨x, b⟩ := l
    obtain ⟨y, c⟩ := l'
    have hne' : ¬ (y = x ∧ c = b) := fun h => hne (by rw [h.1, h.2])
    constructor <;> intro h <;> cases b <;> cases c <;>
      simp [litLE, litLEU, Prod.ext_iff] at h hne' <;>
      first
      | exact hne' (single_one_inj h)
      | exact hne' (single_one_inj h.1)
      | exact hne' (neg_single_one_inj h)
      | exact hne' (single_one_neg_inj h)
      | exact hne' (neg_single_one_inj h.1)
      | exact hne' (single_one_neg_inj h.1)
      | exact hne' (by simpa using h.1.symm)
      | skip

theorem convHyp_backward : ConvHyp (litLEU (p := p)) litLE := by
  constructor
  · intro l
    by_cases hl : l.pos
    · exact ⟨-1, by simp [litLE, litLEU, cmb, hl]⟩
    · exact ⟨1, by simp [litLE, litLEU, cmb, hl]⟩
  · intro l l' hne
    obtain ⟨x, b⟩ := l
    obtain ⟨y, c⟩ := l'
    have hne' : ¬ (y = x ∧ c = b) := fun h => hne (by rw [h.1, h.2])
    constructor <;> intro h <;> cases b <;> cases c <;>
      simp [litLE, litLEU, Prod.ext_iff] at h hne' <;>
      first
      | exact hne' (single_one_inj h)
      | exact hne' (single_one_inj h.1)
      | exact hne' (neg_single_one_inj h)
      | exact hne' (single_one_neg_inj h)
      | exact hne' (neg_single_one_inj h.1)
      | exact hne' (single_one_neg_inj h.1)
      | exact hne' (by simpa using h.1.symm)
      | skip

/-- **Usual encoding into Pang.** A refutation of `Φ` from the usual encoding `x = 1`
(`linAxU Φ`, with the Boolean axioms) with `n` lines of `RLDag` gives a `Pang.Refutation` with at
most `n + cost + 1` nodes, where `cost` is the sum of (width + 1) over the clauses of `Φ` used. -/
theorem rldag_usual_to_pang {Φ : CNF} {V : Finset ℕ} (hΦ : ∀ D ∈ Φ, ∀ l ∈ D, l.var ∈ V)
    {𝓛 : Finset (Finset (LEq (ZMod p)))}
    (h : RLDag (linAxU Φ ∪ boolAx) 𝓛) (h0 : (∅ : Finset (LEq (ZMod p))) ∈ 𝓛) :
    ∃ R : Pang.Refutation Φ V p, R.S ≤ 𝓛.card + encCost litLEU Φ 𝓛 + 1 := by
  obtain ⟨E, hE, hc⟩ := swap_axioms litLE litLEU convHyp_forward Φ boolAx h
  obtain ⟨R, hR⟩ := rldag_to_pang hΦ hE (Finset.mem_union_left _ h0)
  refine ⟨R, hR.trans ?_⟩
  have := Finset.card_union_le 𝓛 E
  omega

/-- **Pang into the usual encoding.** A `Pang.Refutation` with `S` nodes gives an `RLDag`
refutation from the usual encoding `linAxU Φ` (plus `zeroCl` and the Boolean axioms) with at most
`2 S + cost` lines, `cost` the sum of (width + 1) over the clauses of `Φ` used in the `litLE`
refutation. -/
theorem pang_to_rldag_usual {Φ : CNF} {V : Finset ℕ} (R : Pang.Refutation Φ V p) :
    ∃ 𝓛, RLDag (linAxU Φ ∪ {zeroCl} ∪ boolAx) 𝓛 ∧ (∅ : Finset (LEq (ZMod p))) ∈ 𝓛 ∧
      𝓛.card ≤ 2 * R.S + ∑ C ∈ Φ, (C.card + 1) := by
  obtain ⟨𝓛, hD, hmem, hc⟩ := pang_to_rldag R
  have hD' : RLDag (encAx litLE Φ ∪ ({zeroCl} ∪ boolAx)) 𝓛 := by
    have : (linAx Φ ∪ {zeroCl} ∪ boolAx : Set (Finset (LEq (ZMod p))))
        = encAx litLE Φ ∪ ({zeroCl} ∪ boolAx) := by
      rw [Set.union_assoc]; rfl
    rwa [this] at hD
  obtain ⟨E, hE, hcE⟩ := swap_axioms litLEU litLE convHyp_backward Φ _ hD'
  refine ⟨𝓛 ∪ E, ?_, Finset.mem_union_left _ hmem, ?_⟩
  · have : (linAxU Φ ∪ {zeroCl} ∪ boolAx : Set (Finset (LEq (ZMod p))))
        = encAx litLEU Φ ∪ ({zeroCl} ∪ boolAx) := by
      rw [Set.union_assoc]; rfl
    rwa [this]
  · have h1 := Finset.card_union_le 𝓛 E
    have h2 : encCost litLE Φ 𝓛 ≤ ∑ C ∈ Φ, (C.card + 1) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    omega

end Generic

end

end RLF

end SATurday.ProofComplexity
