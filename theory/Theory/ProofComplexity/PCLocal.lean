import Theory.ProofComplexity.PCOperator

/-!
# The local reduction theorem (Alekhnovich-Razborov Thm 3.1 / Cor 3.7) (Ladder Rung R4, AR-A, layer 4)

Variables are partitioned into `y`, `v`, `z` (`y` is everything outside `v ∪ z`).  `ZP` is a set of
Boolean points not depending on `z`; `ZQ` is a set of Boolean points depending only on `v ∪ z` whose
vanishing polynomials all have degree `≥ 2|v| + 1` (immunity).  Then a `z`-free term that is
reducible modulo the consequences of `ZP ∩ ZQ` is already reducible modulo those of `ZP`
(`isLT_of_isLT_inter`), hence the reduction operators agree on `z`-free terms (`rdc_inter`).

Differences to the paper: we do not go through the operator `R^θ` of Def. 3.2 and its Lemmas 3.3-3.6 with
irreducible terms of `f`; we construct directly an operator `Lam` with `Lam(V_{P,Q}) ⊆ V_P` (the paper's
Lemma 3.5), which fixes terms with `≤ |v|` variables in `z` (Lemma 3.4); that suffices for the leading
term argument and uses no property of the term order beyond refining the degree.

LOG: R4 AR-A local reduction layer
-/

namespace SATurday.ProofComplexity.PCL

open Finset

noncomputable section
open Classical

variable {F : Type} [Field F]

/-! ## The indicator of a subcube `v = e` -/

/-- Multiplication by the indicator `χ_e` of the subcube `v = e` (for `e ⊆ v`). -/
def chi (v e : Finset ℕ) : ML F →ₗ[F] ML F :=
  ∑ f ∈ (v \ e).powerset, ((-1 : F) ^ f.card) • shl (e ∪ f)

theorem powerset_filter_subset (s : Finset ℕ) (a : Set ℕ) :
    s.powerset.filter (fun f : Finset ℕ => (↑f : Set ℕ) ⊆ a) = (s.filter (fun x => x ∈ a)).powerset := by
  ext f
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff]
  constructor
  · rintro ⟨h1, h2⟩ x hx
    exact ⟨h1 hx, h2 (by simpa using hx)⟩
  · intro h
    exact ⟨fun x hx => (h hx).1, fun x hx => (h (by simpa using hx)).2⟩

theorem sum_powerset_neg_one_pow (s : Finset ℕ) :
    ∑ f ∈ s.powerset, ((-1 : F) ^ f.card) = if s = ∅ then 1 else 0 := by
  have := congrArg (Int.cast : ℤ → F) (Finset.sum_powerset_neg_one_pow_card (x := s))
  push_cast at this
  rw [this]

theorem ev_chi {v e : Finset ℕ} (he : e ⊆ v) (a : Set ℕ) (g : ML F) :
    ev a (chi v e g) = if (↑e : Set ℕ) = a ∩ ↑v then ev a g else 0 := by
  unfold chi
  rw [LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smul_apply, map_smul, ev_shl, Finset.coe_union, Set.union_subset_iff]
  by_cases hea : (↑e : Set ℕ) ⊆ a
  · have h1 : ∀ f ∈ (v \ e).powerset,
        (-1 : F) ^ f.card • (if (↑e : Set ℕ) ⊆ a ∧ (↑f : Set ℕ) ⊆ a then ev a g else 0) =
          if (↑f : Set ℕ) ⊆ a then (-1 : F) ^ f.card * ev a g else 0 := by
      intro f _
      by_cases hf : (↑f : Set ℕ) ⊆ a <;> simp [hea, hf]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, powerset_filter_subset,
      ← Finset.sum_mul, sum_powerset_neg_one_pow]
    have hiff : (↑e : Set ℕ) = a ∩ ↑v ↔ (v \ e).filter (fun x => x ∈ a) = ∅ := by
      constructor
      · intro h
        rw [Finset.filter_eq_empty_iff]
        intro x hx hxa
        have hxe : x ∈ (↑e : Set ℕ) := by
          rw [h]; exact ⟨hxa, by simpa using (Finset.mem_sdiff.1 hx).1⟩
        exact (Finset.mem_sdiff.1 hx).2 (by simpa using hxe)
      · intro h
        ext x
        constructor
        · intro hx; exact ⟨hea hx, by simpa using he (by simpa using hx)⟩
        · rintro ⟨hxa, hxv⟩
          by_contra hxe
          have : x ∈ (v \ e).filter (fun x => x ∈ a) := by
            simp only [Finset.mem_filter, Finset.mem_sdiff]
            exact ⟨⟨by simpa using hxv, fun h' => hxe (by simpa using h')⟩, hxa⟩
          rw [h] at this
          simp at this
    by_cases hc : (v \ e).filter (fun x => x ∈ a) = ∅
    · rw [if_pos hc, if_pos (hiff.2 hc)]; simp
    · rw [if_neg hc, if_neg (fun h => hc (hiff.1 h))]; simp
  · have : ¬ (↑e : Set ℕ) = a ∩ ↑v := fun h => hea (by rw [h]; exact Set.inter_subset_left)
    rw [if_neg this]
    refine Finset.sum_eq_zero fun f _ => ?_
    simp [hea]

theorem support_chi {v e : Finset ℕ} (he : e ⊆ v) (g : ML F) :
    ∀ U ∈ (chi v e g).support, ∃ T ∈ g.support, T ⊆ U ∧ U ⊆ T ∪ v := by
  intro U hU
  unfold chi at hU
  rw [LinearMap.sum_apply] at hU
  obtain ⟨f, hf, hU'⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hU)
  have hU'' := Finsupp.support_smul hU'
  simp only [LinearMap.smul_apply] at hU''
  obtain ⟨T, hT, rfl⟩ := support_shl_subset (e ∪ f) g U (by simpa using hU'')
  refine ⟨T, hT, Finset.subset_union_left, ?_⟩
  have hf' : f ⊆ v := (Finset.mem_powerset.1 hf).trans Finset.sdiff_subset
  intro x hx
  rcases Finset.mem_union.1 hx with h | h
  · exact Finset.mem_union_left _ h
  · rcases Finset.mem_union.1 h with h | h
    · exact Finset.mem_union_right _ (he h)
    · exact Finset.mem_union_right _ (hf' h)

theorem deg_chi_le {v e : Finset ℕ} (he : e ⊆ v) (g : ML F) : deg (chi v e g) ≤ v.card + deg g := by
  refine deg_le fun U hU => ?_
  obtain ⟨T, hT, h1, h2⟩ := support_chi he g U hU
  calc U.card ≤ (T ∪ v).card := Finset.card_le_card h2
    _ ≤ T.card + v.card := Finset.card_union_le _ _
    _ ≤ deg g + v.card := Nat.add_le_add_right (le_deg hT) _
    _ = v.card + deg g := Nat.add_comm _ _

/-! ## The subspace `V^e` and its reduction operator -/

/-- Polynomials in the variables `z` vanishing on the points of `ZQ` whose `v`-part is `e`. -/
def Ve (v z : Finset ℕ) (ZQ : Set (Set ℕ)) (e : Finset ℕ) : Submodule F (ML F) where
  carrier := {h | (∀ T ∈ h.support, T ⊆ z) ∧ ∀ a ∈ ZQ, (↑e : Set ℕ) = a ∩ ↑v → ev a h = 0}
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨fun T hT => ?_, fun a ha he => ?_⟩
    · rcases Finset.mem_union.1 (Finsupp.support_add hT) with h | h
      · exact hf1 T h
      · exact hg1 T h
    · simp [hf2 a ha he, hg2 a ha he]
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := by
    rintro c g ⟨hg1, hg2⟩
    exact ⟨fun T hT => hg1 T (Finsupp.support_smul hT), fun a ha he => by simp [hg2 a ha he]⟩

theorem chi_ne_zero {v z e : Finset ℕ} (he : e ⊆ v) (hvz : Disjoint v z) {h : ML F} (hne : h ≠ 0)
    (hz : ∀ T ∈ h.support, T ⊆ z) : chi v e h ≠ 0 := by
  intro h0
  have : ∃ a, ev a h ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_zero_of_ev hcon)
  obtain ⟨a0, ha0⟩ := this
  set a1 : Set ℕ := (a0 ∩ ↑z) ∪ ↑e with ha1
  have h1 : ev a1 h = ev a0 h := by
    rw [ev_apply, ev_apply]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTz := hz T hT
    have : (↑T : Set ℕ) ⊆ a1 ↔ (↑T : Set ℕ) ⊆ a0 := by
      constructor
      · intro hs x hx
        rcases hs hx with ⟨h', _⟩ | h'
        · exact h'
        · exact absurd (Finset.disjoint_left.1 hvz (he (by simpa using h')) (hTz (by simpa using hx))) id
      · intro hs x hx
        exact Or.inl ⟨hs hx, by simpa using hTz (by simpa using hx)⟩
    simp only [this]
  have h2 : (↑e : Set ℕ) = a1 ∩ ↑v := by
    ext x
    constructor
    · intro hx
      exact ⟨Or.inr hx, by simpa using he (by simpa using hx)⟩
    · rintro ⟨hx1, hx2⟩
      rcases hx1 with ⟨_, hxz⟩ | hxe
      · exact (Finset.disjoint_left.1 hvz (Finset.mem_coe.1 hx2) (Finset.mem_coe.1 hxz)).elim
      · exact hxe
  have := ev_chi he a1 h
  rw [h0, if_pos h2, h1] at this
  simp at this
  exact ha0 this.symm

/-- Immunity of `ZQ` forces every nonzero element of `V^e` to have degree `> |v|`. -/
theorem Ve_deg {v z e : Finset ℕ} {ZQ : Set (Set ℕ)} (he : e ⊆ v) (hvz : Disjoint v z)
    (himm : ∀ g : ML F, g ≠ 0 → (∀ a ∈ ZQ, ev a g = 0) → 2 * v.card + 1 ≤ deg g)
    {h : ML F} (hh : h ∈ Ve v z ZQ e) (hne : h ≠ 0) : v.card + 1 ≤ deg h := by
  have hc := chi_ne_zero he hvz hne hh.1
  have := himm (chi v e h) hc (by
    intro a ha
    rw [ev_chi he]
    split_ifs with hae
    · exact hh.2 a ha hae
    · rfl)
  have h2 := deg_chi_le he h
  omega

/-- The reduction operator of `V^e`. -/
def Re (v z : Finset ℕ) (ZQ : Set (Set ℕ)) (e : Finset ℕ) : ML F →ₗ[F] ML F := rdc (Ve v z ZQ e)

theorem Re_fix {v z e : Finset ℕ} {ZQ : Set (Set ℕ)} (he : e ⊆ v) (hvz : Disjoint v z)
    (himm : ∀ g : ML F, g ≠ 0 → (∀ a ∈ ZQ, ev a g = 0) → 2 * v.card + 1 ≤ deg g)
    {w : Finset ℕ} (hw : w ⊆ z) (hcard : w.card ≤ v.card) :
    Re v z ZQ e (Finsupp.single w (1 : F)) = Finsupp.single w 1 := by
  refine rdc_eq_of_spec ⟨?_, by simp⟩
  intro T hT
  have hTw : T = w := by
    have := Finsupp.support_single_subset hT
    simpa using this
  subst hTw
  rintro ⟨g, hg, hTg, hmax⟩
  have hne : g ≠ 0 := fun h0 => by simp [h0] at hTg
  have h1 := Ve_deg he hvz himm hg hne
  have h2 := card_of_leading hTg hmax
  omega

theorem support_Re {v z e : Finset ℕ} {ZQ : Set (Set ℕ)} {w : Finset ℕ} (hw : w ⊆ z) (c : F) :
    ∀ U ∈ (Re v z ZQ e (Finsupp.single w c)).support, U ⊆ z := by
  intro U hU
  have hmem := (rdc_spec (Ve v z ZQ e) (Finsupp.single w c)).mem
  set r := rdc (Ve v z ZQ e) (Finsupp.single w c) with hr
  have e1 : r = Finsupp.single w c - (Finsupp.single w c - r) := by abel
  have hU' : U ∈ r.support := hU
  rw [e1] at hU'
  rcases Finset.mem_union.1 (Finsupp.support_sub hU') with h | h
  · have := Finsupp.support_single_subset h
    rw [Finset.mem_singleton] at this
    rw [this]; exact hw
  · exact hmem.1 U h

/-! ## The operator `Lam` -/

/-- The image of a term `T` under the local operator. -/
def Lterm (v z : Finset ℕ) (ZQ : Set (Set ℕ)) (T : Finset ℕ) : ML F :=
  ∑ e ∈ v.powerset.filter (fun e => T ∩ v ⊆ e),
    chi v e (shl (T \ (v ∪ z)) (Re v z ZQ e (Finsupp.single (T ∩ z) (1 : F))))

/-- The local operator (the paper's `R^θ`, Definition 3.2, in a form adapted to the proof). -/
def Lam (v z : Finset ℕ) (ZQ : Set (Set ℕ)) : ML F →ₗ[F] ML F :=
  Finsupp.linearCombination F (Lterm v z ZQ)

theorem coe_sdiff_subset_iff {v z : Finset ℕ} (hvz : Disjoint v z) (T : Finset ℕ) (a : Set ℕ) :
    (↑(T \ z) : Set ℕ) ⊆ a ↔ (↑(T ∩ v) : Set ℕ) ⊆ a ∧ (↑(T \ (v ∪ z)) : Set ℕ) ⊆ a := by
  constructor
  · intro h
    refine ⟨fun x hx => h ?_, fun x hx => h ?_⟩
    · have := Finset.mem_inter.1 (Finset.mem_coe.1 hx)
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe]
      exact ⟨this.1, fun hz => Finset.disjoint_left.1 hvz this.2 hz⟩
    · have := Finset.mem_sdiff.1 (Finset.mem_coe.1 hx)
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe]
      exact ⟨this.1, fun hz => this.2 (Finset.mem_union_right _ hz)⟩
  · rintro ⟨h1, h2⟩ x hx
    have hx' := Finset.mem_sdiff.1 (Finset.mem_coe.1 hx)
    by_cases hxv : x ∈ v
    · exact h1 (Finset.mem_coe.2 (Finset.mem_inter.2 ⟨hx'.1, hxv⟩))
    · exact h2 (Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨hx'.1, fun h => by
        rcases Finset.mem_union.1 h with h | h
        · exact hxv h
        · exact hx'.2 h⟩))

theorem ev_Lterm {v z : Finset ℕ} (ZQ : Set (Set ℕ)) (hvz : Disjoint v z) (a : Set ℕ) (T : Finset ℕ) :
    ev a (Lterm v z ZQ T) =
      if (↑(T \ z) : Set ℕ) ⊆ a then
        ev a (Re v z ZQ (v.filter (fun x => x ∈ a)) (Finsupp.single (T ∩ z) (1 : F))) else 0 := by
  set ea : Finset ℕ := v.filter (fun x => x ∈ a) with hea
  have hea_sub : ea ⊆ v := Finset.filter_subset _ _
  unfold Lterm
  rw [map_sum]
  have step : ∀ e ∈ v.powerset.filter (fun e => T ∩ v ⊆ e),
      ev a (chi v e (shl (T \ (v ∪ z)) (Re v z ZQ e (Finsupp.single (T ∩ z) (1 : F))))) =
        if e = ea then (if (↑(T \ (v ∪ z)) : Set ℕ) ⊆ a then
          ev a (Re v z ZQ ea (Finsupp.single (T ∩ z) (1 : F))) else 0) else 0 := by
    intro e he
    have hev : e ⊆ v := Finset.mem_powerset.1 (Finset.mem_filter.1 he).1
    rw [ev_chi hev, ev_shl]
    have heq : (↑e : Set ℕ) = a ∩ ↑v ↔ e = ea := by
      constructor
      · intro h
        ext x
        simp only [hea, Finset.mem_filter]
        constructor
        · intro hx
          have : x ∈ (↑e : Set ℕ) := hx
          rw [h] at this
          exact ⟨Finset.mem_coe.1 this.2, this.1⟩
        · rintro ⟨hxv, hxa⟩
          have : x ∈ a ∩ ↑v := ⟨hxa, hxv⟩
          rw [← h] at this
          exact this
      · rintro rfl
        ext x
        simp only [hea, Finset.coe_filter, Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_coe]
        tauto
    by_cases h1 : e = ea
    · subst h1
      simp [heq]
    · rw [if_neg (fun h => h1 (heq.1 h)), if_neg h1]
  rw [Finset.sum_congr rfl step, Finset.sum_ite_eq']
  have hmem : ea ∈ v.powerset.filter (fun e => T ∩ v ⊆ e) ↔ (↑(T ∩ v) : Set ℕ) ⊆ a := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨_, h⟩ x hx
      have : x ∈ ea := h (Finset.mem_coe.1 hx)
      exact (Finset.mem_filter.1 this).2
    · intro h
      refine ⟨hea_sub, fun x hx => ?_⟩
      exact Finset.mem_filter.2 ⟨(Finset.mem_inter.1 hx).2, h (Finset.mem_coe.2 hx)⟩
  rw [coe_sdiff_subset_iff hvz]
  by_cases h1 : (↑(T ∩ v) : Set ℕ) ⊆ a <;> by_cases h2 : (↑(T \ (v ∪ z)) : Set ℕ) ⊆ a
  · rw [if_pos (hmem.2 h1), if_pos h2, if_pos ⟨h1, h2⟩]
  · rw [if_pos (hmem.2 h1), if_neg h2, if_neg (fun h => h2 h.2)]
  · rw [if_neg (fun h => h1 (hmem.1 h)), if_neg (fun h => h1 h.1)]
  · rw [if_neg (fun h => h1 (hmem.1 h)), if_neg (fun h => h1 h.1)]

/-- Terms with at most `|v|` variables in `z` are fixed by `Lam`. -/
theorem Lterm_fix {v z : Finset ℕ} {ZQ : Set (Set ℕ)} (hvz : Disjoint v z)
    (himm : ∀ g : ML F, g ≠ 0 → (∀ a ∈ ZQ, ev a g = 0) → 2 * v.card + 1 ≤ deg g)
    {T : Finset ℕ} (hT : (T ∩ z).card ≤ v.card) : Lterm v z ZQ T = Finsupp.single T (1 : F) := by
  have h0 : Lterm v z ZQ T - Finsupp.single T (1 : F) = 0 := by
    apply eq_zero_of_ev
    intro a
    rw [map_sub, ev_Lterm ZQ hvz, Re_fix (Finset.filter_subset _ _) hvz himm Finset.inter_subset_right hT,
      ev_single, ev_single]
    have : (↑T : Set ℕ) ⊆ a ↔ (↑(T \ z) : Set ℕ) ⊆ a ∧ (↑(T ∩ z) : Set ℕ) ⊆ a := by
      constructor
      · intro h; exact ⟨fun x hx => h (Finset.mem_sdiff.1 (Finset.mem_coe.1 hx)).1,
          fun x hx => h (Finset.mem_inter.1 (Finset.mem_coe.1 hx)).1⟩
      · rintro ⟨h1, h2⟩ x hx
        by_cases hxz : x ∈ z
        · exact h2 (Finset.mem_coe.2 (Finset.mem_inter.2 ⟨hx, hxz⟩))
        · exact h1 (Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨hx, hxz⟩))
    by_cases h1 : (↑(T \ z) : Set ℕ) ⊆ a <;> by_cases h2 : (↑(T ∩ z) : Set ℕ) ⊆ a
    · rw [if_pos h1, if_pos h2, if_pos (this.2 ⟨h1, h2⟩), sub_self]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 (this.1 h).2), sub_self]
    · rw [if_neg h1, if_neg (fun h => h1 (this.1 h).1), sub_self]
    · rw [if_neg h1, if_neg (fun h => h1 (this.1 h).1), sub_self]
  exact sub_eq_zero.1 h0

/-- Terms of `Lterm T` free of `z` have few variables when `T` has many variables in `z`. -/
theorem card_Lterm_le {v z : Finset ℕ} {ZQ : Set (Set ℕ)} {T U : Finset ℕ}
    (hU : U ∈ (Lterm (F := F) v z ZQ T).support) (hUz : Disjoint U z) :
    U.card ≤ v.card + (T \ (v ∪ z)).card := by
  unfold Lterm at hU
  obtain ⟨e, he, hU1⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hU)
  have hev : e ⊆ v := Finset.mem_powerset.1 (Finset.mem_filter.1 he).1
  obtain ⟨T1, hT1, h1, h2⟩ := support_chi hev _ U hU1
  obtain ⟨T2, hT2, rfl⟩ := support_shl_subset _ _ T1 hT1
  have hT2z : T2 ⊆ z := support_Re Finset.inter_subset_right 1 T2 hT2
  have hT2e : T2 = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    have hxU : x ∈ U := h1 (Finset.mem_union_left _ hx)
    exact Finset.disjoint_left.1 hUz hxU (hT2z hx)
  subst hT2e
  simp only [Finset.empty_union] at h2
  calc U.card ≤ ((T \ (v ∪ z)) ∪ v).card := Finset.card_le_card h2
    _ ≤ (T \ (v ∪ z)).card + v.card := Finset.card_union_le _ _
    _ = v.card + (T \ (v ∪ z)).card := Nat.add_comm _ _

end

end SATurday.ProofComplexity.PCL
