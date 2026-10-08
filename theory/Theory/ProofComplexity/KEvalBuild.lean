import Theory.ProofComplexity.KEval
import Theory.ProofComplexity.MatchingSwitch

/-!
# Building k-evaluations level by level (Ladder Rung R4, 1B.5)

* `resE ρ' E`: restricting an evaluation to an extension `ρ' ⊇ ρ` (drop branches incompatible
  with `ρ'`, remove the edges of `ρ'`) preserves `Good` (`good_res`).
* `E0`: the depth zero evaluation over the empty restriction (`good_E0`).
* `canon`: for `OR l` (resp. `AND l`) of the next depth, the branches of the canonical matching
  tree of the DNF of true (resp. false) branches of the children; `level_step` shows the new
  evaluation is `Good` up to the next depth when every such DNF has canonical depth at most `s`
  under `ρ'` and `2 s ≤ k`.

LOG: R4 KEvalBuild module (constructing k-evaluations)
-/

namespace SATurday.ProofComplexity

open Finset

noncomputable section

open Classical

/-! ## Depth lemmas -/

theorem le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem foldr_max_le {l : List ℕ} {d : ℕ} (h : ∀ x ∈ l, x ≤ d) : l.foldr max 0 ≤ d := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem depth_or (l : List Fm) : (Fm.or l).depth = (l.map Fm.depth).foldr max 0 + 1 := by
  rw [Fm.depth]; have := Fm.attach_map l Fm.depth; simp only at this; rw [this]

theorem depth_and (l : List Fm) : (Fm.and l).depth = (l.map Fm.depth).foldr max 0 + 1 := by
  rw [Fm.depth]; have := Fm.attach_map l Fm.depth; simp only at this; rw [this]

theorem depth_mod (r : ℕ) (l : List Fm) :
    (Fm.mod r l).depth = (l.map Fm.depth).foldr max 0 + 1 := by
  rw [Fm.depth]; have := Fm.attach_map l Fm.depth; simp only at this; rw [this]

theorem depth_neg (φ : Fm) : (Fm.neg φ).depth = φ.depth := by rw [Fm.depth]

theorem depth_child_or {l : List Fm} {ψ : Fm} (h : ψ ∈ l) : ψ.depth + 1 ≤ (Fm.or l).depth := by
  rw [depth_or]; have := le_foldr_max (List.mem_map.2 ⟨ψ, h, rfl⟩ : Fm.depth ψ ∈ l.map Fm.depth); omega

theorem depth_child_and {l : List Fm} {ψ : Fm} (h : ψ ∈ l) : ψ.depth + 1 ≤ (Fm.and l).depth := by
  rw [depth_and]; have := le_foldr_max (List.mem_map.2 ⟨ψ, h, rfl⟩ : Fm.depth ψ ∈ l.map Fm.depth); omega

theorem depth_child_mod {r : ℕ} {l : List Fm} {ψ : Fm} (h : ψ ∈ l) :
    ψ.depth + 1 ≤ (Fm.mod r l).depth := by
  rw [depth_mod]; have := le_foldr_max (List.mem_map.2 ⟨ψ, h, rfl⟩ : Fm.depth ψ ∈ l.map Fm.depth); omega

theorem depth_subs : ∀ (φ : Fm) {ψ : Fm}, ψ ∈ subs φ → ψ.depth ≤ φ.depth
  | .var i, ψ, h => by simp [subs] at h; subst h; rfl
  | .neg χ, ψ, h => by
      rw [subs, List.mem_cons] at h
      rcases h with rfl | h
      · rfl
      · rw [depth_neg]; exact depth_subs χ h
  | .and l, ψ, h => by
      rw [subs_and, List.mem_cons] at h
      rcases h with rfl | h
      · rfl
      · obtain ⟨_, ⟨χ, hχ, rfl⟩, hψ⟩ :=
          List.mem_flatten.1 h |>.imp fun _ => And.imp_left List.mem_map.1
        have : sizeOf χ < sizeOf (Fm.and l) := by
          have := List.sizeOf_lt_of_mem hχ; simp only [Fm.and.sizeOf_spec]; omega
        exact (depth_subs χ hψ).trans (by have := depth_child_and hχ; omega)
  | .or l, ψ, h => by
      rw [subs_or, List.mem_cons] at h
      rcases h with rfl | h
      · rfl
      · obtain ⟨_, ⟨χ, hχ, rfl⟩, hψ⟩ :=
          List.mem_flatten.1 h |>.imp fun _ => And.imp_left List.mem_map.1
        have : sizeOf χ < sizeOf (Fm.or l) := by
          have := List.sizeOf_lt_of_mem hχ; simp only [Fm.or.sizeOf_spec]; omega
        exact (depth_subs χ hψ).trans (by have := depth_child_or hχ; omega)
  | .mod r l, ψ, h => by
      rw [subs_mod, List.mem_cons] at h
      rcases h with rfl | h
      · rfl
      · obtain ⟨_, ⟨χ, hχ, rfl⟩, hψ⟩ :=
          List.mem_flatten.1 h |>.imp fun _ => And.imp_left List.mem_map.1
        have : sizeOf χ < sizeOf (Fm.mod r l) := by
          have := List.sizeOf_lt_of_mem hχ; simp only [Fm.mod.sizeOf_spec]; omega
        exact (depth_subs χ hψ).trans (by have := depth_child_mod (r := r) hχ; omega)

theorem depth_lineF {S : Seq} {d : ℕ} (h : ∀ φ ∈ S.1 ++ S.2, φ.depth ≤ d) :
    (lineF S).depth ≤ d + 1 := by
  rw [lineF, depth_or]
  have : ((dsOf S).map Fm.depth).foldr max 0 ≤ d := by
    refine foldr_max_le fun x hx => ?_
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hx
    rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
    · rw [depth_neg]; exact h χ (List.mem_append_left _ hχ)
    · exact h ψ (List.mem_append_right _ hψ)
  omega

/-! ## Restricting an evaluation -/

/-- Restriction of a branch set to `ρ'`. -/
def resS (ρ' : Mt) (S : Finset Mt) : Finset Mt := (S.filter fun α => Compat ρ' α).image (· \ ρ')

/-- Restriction of an evaluation to `ρ'`. -/
def resE (ρ' : Mt) (E : Eval) : Eval := fun φ => (resS ρ' (E φ).1, resS ρ' (E φ).2)

theorem mem_resS {ρ' : Mt} {S : Finset Mt} {β : Mt} :
    β ∈ resS ρ' S ↔ ∃ α ∈ S, Compat ρ' α ∧ β = α \ ρ' := by
  simp only [resS, mem_image, mem_filter]
  constructor
  · rintro ⟨α, ⟨hα, hc⟩, rfl⟩; exact ⟨α, hα, hc, rfl⟩
  · rintro ⟨α, hα, hc, rfl⟩; exact ⟨α, ⟨hα, hc⟩, rfl⟩

theorem compat_back {ρ' α β : Mt} (ha : Compat ρ' α) (hb : Compat ρ' β)
    (h : Compat (α \ ρ') (β \ ρ')) : Compat α β := by
  have h1 : Compat (α \ ρ') ρ' := compat_symm (compat_mono ha subset_rfl sdiff_subset)
  have h2 : Compat (β \ ρ') ρ' := compat_symm (compat_mono hb subset_rfl sdiff_subset)
  refine isMatch_mono (isMatch_union3 h h1 h2) ?_
  intro e he
  simp only [mem_union, mem_sdiff] at he ⊢
  tauto

section Res

variable {P H : Finset ℕ} {vx : ℕ → ℕ × ℕ} {k : ℕ}

theorem good_res {ρ ρ' : Mt} {E : Eval} {φ : Fm} (hsub : ρ ⊆ ρ') (hρ : IsMatch ρ)
    (hρ' : IsMatch ρ') (hU' : InU P H ρ') (hG : Good P H vx ρ k E φ) :
    Good P H vx ρ' k (resE ρ' E) φ := by
  have hfree : ∀ α ∈ (E φ).1 ∪ (E φ).2, Compat ρ' α → α \ ρ' ⊆ freeE P H ρ' := fun α hα hc =>
    sdiff_free hc ((hG.mem α hα).1.trans freeE_sub)
  refine ⟨fun β hβ => ?_, fun β1 hβ1 β2 hβ2 hc => ?_, fun π hπ hπm hroom => ?_, ?_⟩
  · simp only [resE, mem_union, mem_resS] at hβ
    rcases hβ with ⟨α, hα, hc, rfl⟩ | ⟨α, hα, hc, rfl⟩
    · have hm := hG.mem α (mem_union.2 (Or.inl hα))
      exact ⟨hfree α (mem_union.2 (Or.inl hα)) hc, isMatch_mono hm.2.1 sdiff_subset,
        (card_le_card sdiff_subset).trans hm.2.2⟩
    · have hm := hG.mem α (mem_union.2 (Or.inr hα))
      exact ⟨hfree α (mem_union.2 (Or.inr hα)) hc, isMatch_mono hm.2.1 sdiff_subset,
        (card_le_card sdiff_subset).trans hm.2.2⟩
  · simp only [resE, mem_resS] at hβ1 hβ2
    obtain ⟨α1, hα1, hc1, rfl⟩ := hβ1
    obtain ⟨α2, hα2, hc2, rfl⟩ := hβ2
    exact hG.inc α1 hα1 α2 hα2 (compat_back hc1 hc2 hc)
  · -- cover `π ∪ (ρ' \ ρ)` over `ρ`
    have hnew : ρ' \ ρ ⊆ freeE P H ρ := by
      intro e he
      have hd := disj_ext hρ' hsub e he
      have hu := mem_product.1 (hU' (mem_sdiff.1 he).1)
      refine mem_freeE.2 ⟨⟨hu.1, fun hi => ?_⟩, ⟨hu.2, fun hj => ?_⟩⟩
      · obtain ⟨f, hf, hfe⟩ := mem_pigs.1 hi; exact (hd f hf).1 hfe.symm
      · obtain ⟨f, hf, hfe⟩ := mem_hols.1 hj; exact (hd f hf).2 hfe.symm
    have hπρ : π ⊆ freeE P H ρ := hπ.trans (freeE_mono hsub)
    have hm' : IsMatch (π ∪ (ρ' \ ρ)) := by
      refine isMatch_union.2 ⟨hπm, isMatch_mono hρ' sdiff_subset, cross_of_disj ?_⟩
      intro e he f hf
      exact disj_free hπ e he f (mem_sdiff.1 hf).1
    have hcardH : ρ'.card ≤ H.card := by
      rw [← card_hols hρ']; exact card_le_card (hols_sub hU')
    have hU : InU P H ρ := hsub.trans hU'
    have hroom' : (π ∪ (ρ' \ ρ)).card + 3 * k ≤ (fH H ρ).card := by
      have h1 := card_union_le π (ρ' \ ρ)
      rw [card_sdiff_of_subset hsub] at h1
      rw [fH_card hρ (hols_sub hU)]
      rw [fH_card hρ' (hols_sub hU')] at hroom
      have := card_le_card hsub
      omega
    obtain ⟨α, hα, hc⟩ := hG.cov _ (union_subset hπρ hnew) hm' hroom'
    have hαm := hG.mem α hα
    have hαρ' : Compat ρ' α := by
      have h1 : Compat α ρ := compat_free hρ hαm.2.1 hαm.1
      have h2 : Compat α (ρ' \ ρ) := compat_mono hc subset_rfl subset_union_right
      have h3 : Compat ρ (ρ' \ ρ) := isMatch_mono hρ' (union_subset hsub sdiff_subset)
      refine compat_symm (isMatch_mono (isMatch_union3 h1 h2 h3) ?_)
      intro e he
      simp only [mem_union, mem_sdiff] at he ⊢
      by_cases heρ : e ∈ ρ <;> tauto
    refine ⟨α \ ρ', ?_, compat_mono hc sdiff_subset subset_union_left⟩
    simp only [resE, mem_union, mem_resS]
    rcases mem_union.1 hα with hα | hα
    · exact Or.inl ⟨α, hα, hαρ', rfl⟩
    · exact Or.inr ⟨α, hα, hαρ', rfl⟩
  · have hl := hG.loc
    cases φ with
    | var v =>
      simp only [Local] at hl ⊢
      intro hu
      obtain ⟨h1, h0⟩ := hl hu
      refine ⟨fun β hβ => ?_, fun β hβ hm => ?_⟩
      · obtain ⟨α, hα, hc, rfl⟩ := mem_resS.1 hβ
        have := h1 α hα
        simp only [mem_union, mem_sdiff] at this ⊢
        by_cases hx : vx v ∈ ρ' <;> tauto
      · obtain ⟨α, hα, hc, rfl⟩ := mem_resS.1 hβ
        refine h0 α hα (isMatch_mono hm ?_)
        intro e he
        simp only [mem_insert, mem_union, mem_sdiff] at he ⊢
        by_cases heρ : e ∈ ρ'
        · tauto
        · rcases he with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨h, heρ⟩)
          · exact absurd (hsub h) heρ
    | neg ψ =>
      simp only [Local] at hl ⊢
      simp only [resE, hl]
    | and l =>
      simp only [Local] at hl ⊢
      refine ⟨fun β hβ => ?_, fun β hβ ψ hψ γ hγ hc => ?_⟩
      · obtain ⟨α, hα, hcα, rfl⟩ := mem_resS.1 hβ
        obtain ⟨ψ, hψ, γ, hγ, hγα⟩ := hl.1 α hα
        exact ⟨ψ, hψ, γ \ ρ', mem_resS.2 ⟨γ, hγ, compat_mono hcα subset_rfl hγα, rfl⟩,
          sdiff_subset_sdiff hγα subset_rfl⟩
      · obtain ⟨α, hα, hcα, rfl⟩ := mem_resS.1 hβ
        obtain ⟨γ', hγ', hcγ, rfl⟩ := mem_resS.1 hγ
        exact hl.2 α hα ψ hψ γ' hγ' (compat_back hcα hcγ hc)
    | or l =>
      simp only [Local] at hl ⊢
      refine ⟨fun β hβ => ?_, fun β hβ ψ hψ γ hγ hc => ?_⟩
      · obtain ⟨α, hα, hcα, rfl⟩ := mem_resS.1 hβ
        obtain ⟨ψ, hψ, γ, hγ, hγα⟩ := hl.1 α hα
        exact ⟨ψ, hψ, γ \ ρ', mem_resS.2 ⟨γ, hγ, compat_mono hcα subset_rfl hγα, rfl⟩,
          sdiff_subset_sdiff hγα subset_rfl⟩
      · obtain ⟨α, hα, hcα, rfl⟩ := mem_resS.1 hβ
        obtain ⟨γ', hγ', hcγ, rfl⟩ := mem_resS.1 hγ
        exact hl.2 α hα ψ hψ γ' hγ' (compat_back hcα hcγ hc)
    | mod r l => trivial

end Res

/-! ## Congruence, swapping -/

section Gen

variable {P H : Finset ℕ} {vx : ℕ → ℕ × ℕ} {k : ℕ} {ρ : Mt}

theorem good_congr {E1 E2 : Eval} {φ : Fm} (h : ∀ χ ∈ subs φ, E1 χ = E2 χ)
    (hG : Good P H vx ρ k E1 φ) : Good P H vx ρ k E2 φ := by
  have e := h φ (self_mem_subs φ)
  obtain ⟨hm, hi, hc, hl⟩ := hG
  refine ⟨by rw [← e]; exact hm, by rw [← e]; exact hi, by rw [← e]; exact hc, ?_⟩
  cases φ with
  | var v => simp only [Local] at hl ⊢; rw [← e]; exact hl
  | neg ψ =>
    simp only [Local] at hl ⊢
    rw [← e, hl, h ψ (by rw [subs]; exact List.mem_cons_of_mem _ (self_mem_subs ψ))]
  | and l =>
    simp only [Local] at hl ⊢
    have hc' : ∀ ψ ∈ l, E1 ψ = E2 ψ := fun ψ hψ => h ψ (sub_and (self_mem_subs _) hψ)
    rw [← e]
    refine ⟨fun α hα => ?_, fun α hα ψ hψ β hβ => ?_⟩
    · obtain ⟨ψ, hψ, β, hβ, hβα⟩ := hl.1 α hα
      exact ⟨ψ, hψ, β, by rw [← hc' ψ hψ]; exact hβ, hβα⟩
    · exact hl.2 α hα ψ hψ β (by rw [hc' ψ hψ]; exact hβ)
  | or l =>
    simp only [Local] at hl ⊢
    have hc' : ∀ ψ ∈ l, E1 ψ = E2 ψ := fun ψ hψ => h ψ (sub_or (self_mem_subs _) hψ)
    rw [← e]
    refine ⟨fun α hα => ?_, fun α hα ψ hψ β hβ => ?_⟩
    · obtain ⟨ψ, hψ, β, hβ, hβα⟩ := hl.1 α hα
      exact ⟨ψ, hψ, β, by rw [← hc' ψ hψ]; exact hβ, hβα⟩
    · exact hl.2 α hα ψ hψ β (by rw [hc' ψ hψ]; exact hβ)
  | mod r l => trivial

theorem good_swap {E : Eval} {ψ : Fm} (hG : Good P H vx ρ k E ψ)
    (hE : E (.neg ψ) = ((E ψ).2, (E ψ).1)) : Good P H vx ρ k E (.neg ψ) := by
  refine ⟨fun α hα => ?_, fun α hα β hβ hc => ?_, fun π hπ hπm hroom => ?_, ?_⟩
  · rw [hE] at hα; exact hG.mem α (by rw [mem_union] at hα ⊢; tauto)
  · rw [hE] at hα hβ; exact hG.inc β hβ α hα (compat_symm hc)
  · obtain ⟨α, hα, hc⟩ := hG.cov π hπ hπm hroom
    exact ⟨α, by rw [hE]; rw [mem_union] at hα ⊢; tauto, hc⟩
  · simp only [Local]; exact hE

end Gen

/-! ## The depth zero evaluation -/

/-- Branch sets of a variable over the empty restriction. -/
def varSets (P H : Finset ℕ) (e : ℕ × ℕ) : Finset Mt × Finset Mt :=
  if e ∈ P ×ˢ H then ({{e}}, (H.erase e.2).image fun j => {(e.1, j)}) else ({∅}, ∅)

/-- The depth zero evaluation. -/
def E0 (P H : Finset ℕ) (vx : ℕ → ℕ × ℕ) : Eval
  | .var v => varSets P H (vx v)
  | .neg ψ => ((E0 P H vx ψ).2, (E0 P H vx ψ).1)
  | _ => (∅, ∅)

theorem single_compat {f : ℕ × ℕ} {π : Mt} (hπm : IsMatch π)
    (h : f ∈ π ∨ (f.1 ∉ pigs π ∧ f.2 ∉ hols π)) : Compat {f} π := by
  rcases h with h | ⟨h1, h2⟩
  · unfold Compat; rwa [union_eq_right.2 (singleton_subset_iff.2 h)]
  · refine compat_iff.2 ⟨fun e he e' he' _ => by simp at he he'; rw [he, he'], hπm,
      cross_of_disj fun e he f' hf' => ?_⟩
    simp only [mem_singleton] at he; subst he
    exact ⟨fun h => h1 (mem_pigs.2 ⟨f', hf', h.symm⟩), fun h => h2 (mem_hols.2 ⟨f', hf', h.symm⟩)⟩

theorem good_E0 {P H : Finset ℕ} {vx : ℕ → ℕ × ℕ} {k : ℕ} (hk : 1 ≤ k) :
    ∀ φ : Fm, φ.depth = 0 → Good P H vx ∅ k (E0 P H vx) φ
  | .var v, _ => by
    have hfree : ∀ e ∈ P ×ˢ H, e ∈ freeE P H ∅ := fun e he => by
      have := mem_product.1 he; exact mem_freeE.2 ⟨⟨this.1, by simp [pigs]⟩, ⟨this.2, by simp [hols]⟩⟩
    have hfH : fH H ∅ = H := by simp [fH, hols]
    by_cases he : vx v ∈ P ×ˢ H
    · set e := vx v with hedef
      have heP := (mem_product.1 he).1
      have hS : E0 P H vx (.var v) = ({{e}}, (H.erase e.2).image fun j => {(e.1, j)}) := by
        simp only [E0, varSets]; exact if_pos he
      have hconf : ∀ j, j ≠ e.2 → ¬ IsMatch ({e} ∪ {(e.1, j)}) := by
        intro j hj hm
        have := hm e (by simp) (e.1, j) (by simp) (Or.inl rfl)
        exact hj (congrArg Prod.snd this).symm
      refine ⟨fun α hα => ?_, fun α hα β hβ hc => ?_, fun π hπ hπm hroom => ?_, ?_⟩
      · rw [hS] at hα
        simp only [mem_union, mem_singleton, mem_image, mem_erase] at hα
        rcases hα with rfl | ⟨j, ⟨-, hj⟩, rfl⟩
        · exact ⟨singleton_subset_iff.2 (hfree e he),
            fun a ha b hb _ => by simp at ha hb; rw [ha, hb], by simp; omega⟩
        · exact ⟨singleton_subset_iff.2 (hfree _ (mem_product.2 ⟨heP, hj⟩)),
            fun a ha b hb _ => by simp at ha hb; rw [ha, hb], by simp; omega⟩
      · rw [hS] at hα hβ
        simp only [mem_singleton, mem_image, mem_erase] at hα hβ
        obtain ⟨j, ⟨hj, -⟩, rfl⟩ := hβ
        subst hα
        exact hconf j hj hc
      · rw [hfH] at hroom
        rw [hS]
        simp only [mem_union, mem_singleton, mem_image, mem_erase]
        have hπU : π ⊆ P ×ˢ H := hπ.trans freeE_sub
        by_cases hp : e.1 ∈ pigs π
        · obtain ⟨f, hf, hfe⟩ := mem_pigs.1 hp
          by_cases hfe2 : f = e
          · exact ⟨{e}, Or.inl rfl, single_compat hπm (Or.inl (hfe2 ▸ hf))⟩
          · have hf2 : f.2 ≠ e.2 := fun h => hfe2 (Prod.ext hfe h)
            refine ⟨{(e.1, f.2)}, Or.inr ⟨f.2, ⟨hf2, (mem_product.1 (hπU hf)).2⟩, rfl⟩, ?_⟩
            have : (e.1, f.2) = f := Prod.ext hfe.symm rfl
            rw [this]; exact single_compat hπm (Or.inl hf)
        · have hlt : (hols π).card < H.card := by rw [card_hols hπm]; omega
          obtain ⟨j, hjH, hjπ⟩ := exists_mem_notMem_of_card_lt_card hlt
          by_cases hj : j = e.2
          · refine ⟨{e}, Or.inl rfl, single_compat hπm (Or.inr ⟨hp, by rw [← hj]; exact hjπ⟩)⟩
          · exact ⟨{(e.1, j)}, Or.inr ⟨j, ⟨hj, hjH⟩, rfl⟩, single_compat hπm (Or.inr ⟨hp, hjπ⟩)⟩
      · simp only [Local]
        intro _
        rw [hS]
        refine ⟨fun α hα => ?_, fun α hα hm => ?_⟩
        · simp only [mem_singleton] at hα; subst hα; simp [hedef]
        · simp only [mem_image, mem_erase] at hα
          obtain ⟨j, ⟨hj, -⟩, rfl⟩ := hα
          refine hconf j hj (isMatch_mono hm ?_)
          intro x hx; simp only [mem_union, mem_singleton] at hx
          simp only [mem_insert, mem_union, mem_singleton]
          rcases hx with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
    · have hS : E0 P H vx (.var v) = ({∅}, ∅) := by simp only [E0, varSets, if_neg he]
      refine ⟨fun α hα => ?_, fun α _ β hβ => by rw [hS] at hβ; simp at hβ,
        fun π _ hπm _ => ⟨∅, by rw [hS]; simp, by unfold Compat; rwa [empty_union]⟩, ?_⟩
      · rw [hS] at hα; simp at hα; subst hα; exact ⟨empty_subset _, isMatch_empty, by simp⟩
      · simp only [Local]; intro hu; exact absurd hu he
  | .neg ψ, h => by
    rw [depth_neg] at h
    exact good_swap (good_E0 hk ψ h) (by simp only [E0])
  | .and l, h => by rw [depth_and] at h; omega
  | .or l, h => by rw [depth_or] at h; omega
  | .mod r l, h => by rw [depth_mod] at h; omega

/-! ## The canonical step -/

/-- Branches of the canonical tree containing a restricted term. -/
def Acan (P H : Finset ℕ) (ρ' : Mt) (k : ℕ) (D : MDNF) : Finset Mt :=
  (freeE P H ρ').powerset.filter fun σ => IsMatch σ ∧ σ.card ≤ k ∧
    ∃ t ∈ D, Compat ρ' t ∧ t \ ρ' ⊆ σ

/-- Branches incompatible with every restricted term. -/
def Bcan (P H : Finset ℕ) (ρ' : Mt) (k : ℕ) (D : MDNF) : Finset Mt :=
  (freeE P H ρ').powerset.filter fun σ => IsMatch σ ∧ σ.card ≤ k ∧
    ∀ t ∈ D, Compat ρ' t → ¬ Compat σ (t \ ρ')

/-- The DNF of true branches of the disjuncts. -/
def Dor (E : Eval) (l : List Fm) : MDNF := (l.map fun ψ => ((E ψ).1).toList).flatten

/-- The DNF of false branches of the conjuncts. -/
def Dand (E : Eval) (l : List Fm) : MDNF := (l.map fun ψ => ((E ψ).2).toList).flatten

theorem mem_Dor {E : Eval} {l : List Fm} {t : Mt} : t ∈ Dor E l ↔ ∃ ψ ∈ l, t ∈ (E ψ).1 := by
  simp [Dor, List.mem_flatten, List.mem_map]

theorem mem_Dand {E : Eval} {l : List Fm} {t : Mt} : t ∈ Dand E l ↔ ∃ ψ ∈ l, t ∈ (E ψ).2 := by
  simp [Dand, List.mem_flatten, List.mem_map]

/-- The canonical evaluation of the formulas of the next depth. -/
def canon (P H : Finset ℕ) (ρ' : Mt) (k : ℕ) (E : Eval) : Fm → Finset Mt × Finset Mt
  | .or l => (Acan P H ρ' k (Dor E l), Bcan P H ρ' k (Dor E l))
  | .and l => (Bcan P H ρ' k (Dand E l), Acan P H ρ' k (Dand E l))
  | .neg ψ => ((canon P H ρ' k E ψ).2, (canon P H ρ' k E ψ).1)
  | _ => (∅, ∅)

/-- The evaluation at the next level. -/
def nextE (P H : Finset ℕ) (ρ' : Mt) (k t : ℕ) (E : Eval) : Eval :=
  fun φ => if φ.depth ≤ t then resE ρ' E φ else canon P H ρ' k E φ

section Canon

variable {P H : Finset ℕ} {vx : ℕ → ℕ × ℕ} {k : ℕ}

theorem canon_core {ρ' : Mt} {D : MDNF} (hDU : ∀ t ∈ D, InU P H t) (hDw : ∀ t ∈ D, t.card ≤ k)
    (hρ' : IsMatch ρ') (hU' : InU P H ρ') (hPH : H.card ≤ P.card) {s : ℕ}
    (hdep : mdepth P H D ρ' ≤ s) (h2s : 2 * s ≤ k) :
    (∀ α ∈ Acan P H ρ' k D ∪ Bcan P H ρ' k D, α ⊆ freeE P H ρ' ∧ IsMatch α ∧ α.card ≤ k) ∧
    (∀ α ∈ Acan P H ρ' k D, ∀ β ∈ Bcan P H ρ' k D, ¬ Compat α β) ∧
    (∀ π, π ⊆ freeE P H ρ' → IsMatch π → π.card + 3 * k ≤ (fH H ρ').card →
      ∃ α ∈ Acan P H ρ' k D ∪ Bcan P H ρ' k D, Compat α π) := by
  refine ⟨fun α hα => ?_, fun α hα β hβ hc => ?_, fun π hπ hπm hroom => ?_⟩
  · rcases mem_union.1 hα with hα | hα
    · obtain ⟨h1, h2, h3, -⟩ := mem_filter.1 hα; exact ⟨mem_powerset.1 h1, h2, h3⟩
    · obtain ⟨h1, h2, h3, -⟩ := mem_filter.1 hα; exact ⟨mem_powerset.1 h1, h2, h3⟩
  · obtain ⟨-, -, -, t, ht, hct, hts⟩ := mem_filter.1 hα
    obtain ⟨-, -, -, hall⟩ := mem_filter.1 hβ
    exact hall t ht hct (compat_mono (compat_symm hc) subset_rfl hts)
  · obtain ⟨σ, hσf, hσm, hσc, hσπ, hdich⟩ := cover_of_mdepth hDU hDw hPH _ s ρ' rfl hρ' hU'
      hdep π hπ hπm (by omega)
    refine ⟨σ, ?_, hσπ⟩
    rcases hdich with ⟨t, ht, hct, hts⟩ | hall
    · exact mem_union.2 (Or.inl (mem_filter.2 ⟨mem_powerset.2 hσf, hσm, by omega, t, ht, hct, hts⟩))
    · exact mem_union.2 (Or.inr (mem_filter.2 ⟨mem_powerset.2 hσf, hσm, by omega, hall⟩))

/-- **Level step**: from a `k`-evaluation over `ρ` up to depth `t` to one over `ρ' ⊇ ρ` up to
depth `t + 1`, when the DNFs of the new `OR`/`AND` formulas have canonical depth at most `s`. -/
theorem level_step {Φ : List Fm} {t s : ℕ} {ρ ρ' : Mt} {E : Eval}
    (hcl : ∀ φ ∈ Φ, (∀ ψ, φ = .neg ψ → ψ ∈ Φ) ∧ (∀ l, φ = .or l → ∀ ψ ∈ l, ψ ∈ Φ) ∧
      (∀ l, φ = .and l → ∀ ψ ∈ l, ψ ∈ Φ))
    (hmod : ∀ φ ∈ Φ, isMod φ = false)
    (hG : ∀ φ ∈ Φ, φ.depth ≤ t → Good P H vx ρ k E φ)
    (hρ : IsMatch ρ) (hsub : ρ ⊆ ρ') (hρ' : IsMatch ρ') (hU' : InU P H ρ') (hPH : H.card ≤ P.card)
    (h2s : 2 * s ≤ k)
    (hsh1 : ∀ l, Fm.or l ∈ Φ → (Fm.or l).depth = t + 1 → mdepth P H (Dor E l) ρ' ≤ s)
    (hsh2 : ∀ l, Fm.and l ∈ Φ → (Fm.and l).depth = t + 1 → mdepth P H (Dand E l) ρ' ≤ s) :
    ∀ φ ∈ Φ, φ.depth ≤ t + 1 → Good P H vx ρ' k (nextE P H ρ' k t E) φ := by
  have hU : InU P H ρ := hsub.trans hU'
  -- formulas of depth at most `t`
  have hlow : ∀ φ ∈ Φ, φ.depth ≤ t → Good P H vx ρ' k (nextE P H ρ' k t E) φ := by
    intro φ hφ hd
    refine good_congr (fun χ hχ => ?_) (good_res hsub hρ hρ' hU' (hG φ hφ hd))
    have := depth_subs φ hχ
    simp only [nextE, if_pos (show χ.depth ≤ t by omega)]
  have hchildU : ∀ ψ ∈ Φ, ψ.depth ≤ t → ∀ α ∈ (E ψ).1 ∪ (E ψ).2, InU P H α ∧ α.card ≤ k :=
    fun ψ hψ hd α hα => ⟨((hG ψ hψ hd).mem α hα).1.trans freeE_sub, ((hG ψ hψ hd).mem α hα).2.2⟩
  have htop : ∀ φ : Fm, φ ∈ Φ → φ.depth = t + 1 → Good P H vx ρ' k (nextE P H ρ' k t E) φ := by
    intro φ
    induction φ using Fm.rec (motive_2 := fun _ => True) with
    | var v => intro _ h; simp [Fm.depth] at h
    | neg ψ ih =>
      intro hφ hd
      rw [depth_neg] at hd
      have hψ := (hcl _ hφ).1 ψ rfl
      refine good_swap (ih hψ hd) ?_
      simp only [nextE, depth_neg, if_neg (show ¬ ψ.depth ≤ t by omega), canon]
    | or l _ =>
      intro hφ hd
      have hch : ∀ ψ ∈ l, ψ ∈ Φ ∧ ψ.depth ≤ t := fun ψ hψ =>
        ⟨(hcl _ hφ).2.1 l rfl ψ hψ, by have := depth_child_or hψ; omega⟩
      have hE1 : nextE P H ρ' k t E (.or l) = (Acan P H ρ' k (Dor E l), Bcan P H ρ' k (Dor E l)) := by
        simp only [nextE, if_neg (show ¬ (Fm.or l).depth ≤ t by omega), canon]
      have hEc : ∀ ψ ∈ l, nextE P H ρ' k t E ψ = resE ρ' E ψ := fun ψ hψ => by
        simp only [nextE, if_pos (hch ψ hψ).2]
      have hDU : ∀ x ∈ Dor E l, InU P H x ∧ x.card ≤ k := by
        intro x hx; obtain ⟨ψ, hψ, hx⟩ := mem_Dor.1 hx
        exact hchildU ψ (hch ψ hψ).1 (hch ψ hψ).2 x (mem_union.2 (Or.inl hx))
      obtain ⟨c1, c2, c3⟩ := canon_core (fun x hx => (hDU x hx).1) (fun x hx => (hDU x hx).2)
        hρ' hU' hPH (hsh1 l hφ hd) h2s
      refine ⟨by rw [hE1]; exact c1, by rw [hE1]; exact c2, by rw [hE1]; exact c3, ?_⟩
      simp only [Local]
      rw [hE1]
      refine ⟨fun α hα => ?_, fun α hα ψ hψ β hβ hc => ?_⟩
      · obtain ⟨-, -, -, x, hx, hcx, hxα⟩ := mem_filter.1 hα
        obtain ⟨ψ, hψ, hxψ⟩ := mem_Dor.1 hx
        exact ⟨ψ, hψ, x \ ρ', by rw [hEc ψ hψ]; exact mem_resS.2 ⟨x, hxψ, hcx, rfl⟩, hxα⟩
      · obtain ⟨-, -, -, hall⟩ := mem_filter.1 hα
        rw [hEc ψ hψ] at hβ
        obtain ⟨x, hx, hcx, rfl⟩ := mem_resS.1 hβ
        exact hall x (mem_Dor.2 ⟨ψ, hψ, hx⟩) hcx hc
    | and l _ =>
      intro hφ hd
      have hch : ∀ ψ ∈ l, ψ ∈ Φ ∧ ψ.depth ≤ t := fun ψ hψ =>
        ⟨(hcl _ hφ).2.2 l rfl ψ hψ, by have := depth_child_and hψ; omega⟩
      have hE1 : nextE P H ρ' k t E (.and l) =
          (Bcan P H ρ' k (Dand E l), Acan P H ρ' k (Dand E l)) := by
        simp only [nextE, if_neg (show ¬ (Fm.and l).depth ≤ t by omega), canon]
      have hEc : ∀ ψ ∈ l, nextE P H ρ' k t E ψ = resE ρ' E ψ := fun ψ hψ => by
        simp only [nextE, if_pos (hch ψ hψ).2]
      have hDU : ∀ x ∈ Dand E l, InU P H x ∧ x.card ≤ k := by
        intro x hx; obtain ⟨ψ, hψ, hx⟩ := mem_Dand.1 hx
        exact hchildU ψ (hch ψ hψ).1 (hch ψ hψ).2 x (mem_union.2 (Or.inr hx))
      obtain ⟨c1, c2, c3⟩ := canon_core (fun x hx => (hDU x hx).1) (fun x hx => (hDU x hx).2)
        hρ' hU' hPH (hsh2 l hφ hd) h2s
      refine ⟨fun α hα => ?_, fun α hα β hβ hc => ?_, fun π hπ hπm hroom => ?_, ?_⟩
      · rw [hE1] at hα; exact c1 α (by rw [mem_union] at hα ⊢; tauto)
      · rw [hE1] at hα hβ; exact c2 β hβ α hα (compat_symm hc)
      · obtain ⟨α, hα, hc⟩ := c3 π hπ hπm hroom
        exact ⟨α, by rw [hE1]; rw [mem_union] at hα ⊢; tauto, hc⟩
      · simp only [Local]
        rw [hE1]
        refine ⟨fun α hα => ?_, fun α hα ψ hψ β hβ hc => ?_⟩
        · obtain ⟨-, -, -, x, hx, hcx, hxα⟩ := mem_filter.1 hα
          obtain ⟨ψ, hψ, hxψ⟩ := mem_Dand.1 hx
          exact ⟨ψ, hψ, x \ ρ', by rw [hEc ψ hψ]; exact mem_resS.2 ⟨x, hxψ, hcx, rfl⟩, hxα⟩
        · obtain ⟨-, -, -, hall⟩ := mem_filter.1 hα
          rw [hEc ψ hψ] at hβ
          obtain ⟨x, hx, hcx, rfl⟩ := mem_resS.1 hβ
          exact hall x (mem_Dand.2 ⟨ψ, hψ, hx⟩) hcx hc
    | mod r l _ =>
      intro hφ _
      have := hmod _ hφ; simp [isMod] at this
    | nil => trivial
    | cons _ _ _ _ => trivial
  intro φ hφ hd
  by_cases h : φ.depth ≤ t
  · exact hlow φ hφ h
  · exact htop φ hφ (by omega)

end Canon

end

end SATurday.ProofComplexity
