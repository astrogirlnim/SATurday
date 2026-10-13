import Theory.ProofComplexity.ResLinFImg

/-!
# Lifting restricted derivations (Ladder Rung R4, Phase 2.2, layer 3d)

Part-Tzameret Proposition 42 and Corollary 43 at plain width. Let `ℓ ∈ U` be an equation with
pivot `i` (`ℓ.1 i ≠ 0`), `U` derived from `Ax ⊇ Γ`, and `Q = U \ {ℓ}`. Every restricted axiom
`rst ℓ i C` (`C ∈ Γ`) is derived with `Q` added (`rld_ax_lift`), hence every derivation from the
restricted axioms `rstSet ℓ i Γ` lifts to a derivation with `Q` added to each line, at the price
of `|Q|` extra width (`rld_lift`). For `U` the image clause this gives `∨_{v ≠ B} f = v`
(Corollary 43), for `U` a unit it gives a refutation of `Γ ∪ {U}` (`rld_subst` then removes `U`).

LOG: R4 Phase 2.2 ResLinFLift module
-/

namespace SATurday.ProofComplexity

namespace RLF

open scoped Classical

noncomputable section

variable {F : Type} [Field F]

theorem cmb_elim (ℓ : LEq F) (i : ℕ) (e : LEq F) :
    cmb (1 : F) (-(e.1 i / ℓ.1 i)) e ℓ = elimE ℓ i e := by
  unfold cmb elimE
  ext <;> simp [sub_eq_add_neg]

/-- Removing false constants from the last line of a derivation. -/
theorem rld_dropZ {Ax : Set (Finset (LEq F))} {w : ℕ} :
    ∀ (n : ℕ) (L : Finset (LEq F)) {s : ℕ}, (L.filter fun e => IsZ e).card = n →
      RLD Ax w L s → ∃ s', RLD Ax w (L.filter fun e => ¬ IsZ e) s' := by
  intro n
  induction n with
  | zero =>
    intro L s hn h
    refine ⟨s, ?_⟩
    have : L.filter (fun e => ¬ IsZ e) = L := by
      apply Finset.filter_true_of_mem
      intro e he hz
      have : e ∈ L.filter fun e => IsZ e := Finset.mem_filter.2 ⟨he, hz⟩
      rw [Finset.card_eq_zero.1 hn] at this; simp at this
    rw [this]; exact h
  | succ n ih =>
    intro L s hn h
    obtain ⟨z, hz⟩ := Finset.card_pos.1 (by omega : 0 < (L.filter fun e => IsZ e).card)
    obtain ⟨hzL, hzZ⟩ := Finset.mem_filter.1 hz
    have hz' : z = ((0 : ℕ →₀ F), z.2) := Prod.ext hzZ.1 rfl
    have h' : RLD Ax w (L.erase z) s := by
      refine RLD.simp z.2 hzZ.2 ?_
      rw [← hz', Finset.insert_erase hzL]; exact h
    have hc : ((L.erase z).filter fun e => IsZ e).card = n := by
      have : (L.erase z).filter (fun e => IsZ e) = (L.filter fun e => IsZ e).erase z := by
        ext x; simp [Finset.mem_filter, Finset.mem_erase, and_assoc, and_comm, and_left_comm]
      rw [this, Finset.card_erase_of_mem hz]; omega
    obtain ⟨s', d⟩ := ih (L.erase z) hc h'
    refine ⟨s', ?_⟩
    have : (L.erase z).filter (fun e => ¬ IsZ e) = L.filter fun e => ¬ IsZ e := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, hx⟩, hn⟩; exact ⟨hx, hn⟩
      · rintro ⟨hx, hn⟩; exact ⟨⟨fun h => hn (h ▸ hzZ), hx⟩, hn⟩
    rwa [this] at d

/-- **Axiom lifting**: the restricted axiom `rst ℓ i C` with `Q` added is derived from `C` and `U`. -/
theorem rld_ax_lift {Ax : Set (Finset (LEq F))} {w : ℕ} {ℓ : LEq F} {i : ℕ} {U : Finset (LEq F)}
    {sU : ℕ} (hU : RLD Ax w U sU) (hℓU : ℓ ∈ U) (hℓ : ℓ.1 i ≠ 0) {C : Finset (LEq F)}
    (hC : C ∈ Ax) (hCw : C.card + (U.erase ℓ).card ≤ w) :
    ∃ s, RLD Ax w (rst ℓ i C ∪ U.erase ℓ) s := by
  set Q := U.erase ℓ with hQ
  let X : Finset (LEq F) → Finset (LEq F) := fun S => S.image (elimE ℓ i) ∪ (C \ S) ∪ Q
  have hXcard : ∀ S, S ⊆ C → (X S).card ≤ w := by
    intro S hS
    refine le_trans ?_ hCw
    have e1 := Finset.card_union_le (S.image (elimE ℓ i) ∪ (C \ S)) Q
    have e2 := Finset.card_union_le (S.image (elimE ℓ i)) (C \ S)
    have e3 : (S.image (elimE ℓ i)).card ≤ S.card := Finset.card_image_le
    have e4 : (C \ S).card = C.card - S.card := Finset.card_sdiff_of_subset hS
    have e5 := Finset.card_le_card hS
    show (S.image (elimE ℓ i) ∪ (C \ S) ∪ Q).card ≤ _
    omega
  have key : ∀ S : Finset (LEq F), S ⊆ C → ∃ s, RLD Ax w (X S) s := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro h
      have hCw' : C.card ≤ w := by omega
      refine ⟨1, RLD.weak (RLD.ax hC hCw') ?_ (hXcard _ h)⟩
      intro e he
      simp only [X, Finset.image_empty, Finset.sdiff_empty, Finset.empty_union]
      exact Finset.mem_union_left _ he
    | @insert e S he ih =>
      intro hsub
      obtain ⟨s0, d0⟩ := ih ((Finset.subset_insert _ _).trans hsub)
      have heC : e ∈ C := hsub (Finset.mem_insert_self _ _)
      have hmem : e ∈ X S := by
        simp only [X]
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨heC, he⟩))
      refine ⟨_, rld_comb' (Ax := Ax) (w := w) e ℓ 1 (-(e.1 i / ℓ.1 i)) d0 hU hmem hℓU ?_
        (hXcard _ hsub)⟩
      rw [cmb_elim]
      intro x hx
      simp only [X]
      rcases Finset.mem_union.1 hx with hx | hx
      · rcases Finset.mem_union.1 hx with hx | hx
        · obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
          simp only [X, Finset.mem_union] at hx
          rcases hx with (hx | hx) | hx
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.image_subset_image (Finset.subset_insert _ _) hx))
          · obtain ⟨hxC, hxS⟩ := Finset.mem_sdiff.1 hx
            exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_sdiff.2 ⟨hxC, fun h => by
                rcases Finset.mem_insert.1 h with rfl | h
                · exact hne rfl
                · exact hxS h⟩))
          · exact Finset.mem_union_right _ hx
        · exact Finset.mem_union_right _ hx
      · rw [Finset.mem_singleton.1 hx]
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_image.2 ⟨e, Finset.mem_insert_self _ _, rfl⟩))
  obtain ⟨s, d⟩ := key C subset_rfl
  have hX : X C = C.image (elimE ℓ i) ∪ Q := by simp [X]
  rw [hX] at d
  obtain ⟨s', d'⟩ := rld_dropZ _ _ rfl d
  refine ⟨s', RLD.weak d' ?_ ?_⟩
  · intro x hx
    obtain ⟨hx, hz⟩ := Finset.mem_filter.1 hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Finset.mem_union_left _ (mem_rst.2 ⟨Finset.mem_image.1 hx |>.imp fun y hy => hy, hz⟩)
    · exact Finset.mem_union_right _ hx
  · refine le_trans (Finset.card_union_le _ _) ?_
    have : (rst ℓ i C).card ≤ C.card := (Finset.card_filter_le _ _).trans Finset.card_image_le
    omega

/-- **Derivation lifting**: a derivation from the restricted axioms lifts, with `Q` added to every
line, to a derivation from the original axioms. -/
theorem rld_lift {Ax Γ' : Set (Finset (LEq F))} (Q : Finset (LEq F)) {wL w' : ℕ}
    (hAx : ∀ C ∈ Γ', ∃ s, RLD Ax wL (C ∪ Q) s) {L : Finset (LEq F)} {s : ℕ}
    (h : RLD Γ' w' L s) : ∃ s', RLD Ax (max wL (w' + Q.card)) (L ∪ Q) s' := by
  induction h with
  | ax hC hc =>
    obtain ⟨s, d⟩ := hAx _ hC
    exact ⟨s, rld_mono_w (le_max_left _ _) d⟩
  | @weak L0 L' s0 _ hsub hc ih =>
    obtain ⟨s', d⟩ := ih
    refine ⟨s', RLD.weak d (Finset.union_subset_union hsub subset_rfl) ?_⟩
    exact le_max_of_le_right ((Finset.card_union_le _ _).trans (Nat.add_le_add_right hc _))
  | @comb A B s1 s2 e1 e2 α β _ _ h1 h2 hc ihA ihB =>
    obtain ⟨sA, dA⟩ := ihA
    obtain ⟨sB, dB⟩ := ihB
    refine ⟨_, rld_comb' (Ax := Ax) e1 e2 α β dA dB (Finset.mem_union_left _ h1)
      (Finset.mem_union_left _ h2) (T := (A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2}) ∪ Q) ?_ ?_⟩
    · intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · rcases Finset.mem_union.1 hx with hx | hx
        · obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
          rcases Finset.mem_union.1 hx with hx | hx
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_erase.2 ⟨hne, hx⟩)))
          · exact Finset.mem_union_right _ hx
        · obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
          rcases Finset.mem_union.1 hx with hx | hx
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_erase.2 ⟨hne, hx⟩)))
          · exact Finset.mem_union_right _ hx
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
    · exact le_max_of_le_right ((Finset.card_union_le _ _).trans (Nat.add_le_add_right hc _))
  | @simp L0 s0 c hc _ ih =>
    obtain ⟨s', d⟩ := ih
    rw [Finset.insert_union] at d
    exact ⟨s', RLD.simp c hc d⟩

/-- Substituting a derivation for an axiom. -/
theorem rld_subst {Γ : Set (Finset (LEq F))} {w : ℕ} {U : Finset (LEq F)} {sU : ℕ}
    (hU : RLD Γ w U sU) {L : Finset (LEq F)} {s : ℕ} (h : RLD (insert U Γ) w L s) :
    ∃ s', RLD Γ w L s' := by
  induction h with
  | ax hC hc =>
    rcases hC with rfl | hC
    · exact ⟨sU, hU⟩
    · exact ⟨1, RLD.ax hC hc⟩
  | weak _ hsub hc ih =>
    obtain ⟨s', d⟩ := ih
    exact ⟨s', RLD.weak d hsub hc⟩
  | comb e1 e2 α β _ _ h1 h2 hc ihA ihB =>
    obtain ⟨sA, dA⟩ := ihA
    obtain ⟨sB, dB⟩ := ihB
    exact ⟨_, RLD.comb e1 e2 α β dA dB h1 h2 hc⟩
  | simp c hc _ ih =>
    obtain ⟨s', d⟩ := ih
    exact ⟨s', RLD.simp c hc d⟩

end

end RLF

end SATurday.ProofComplexity
