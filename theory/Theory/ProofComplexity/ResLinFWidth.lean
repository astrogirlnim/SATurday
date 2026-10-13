import Theory.ProofComplexity.ResLinFLift

/-!
# Size versus width for tree-like Res(lin F) (Ladder Rung R4, Phase 2.2, layer 3e)

Part-Tzameret Theorem 44 over a finite field `F` with `q` elements, at plain width: a tree-like
refutation of `Γ` (clauses of at most `w0 ≥ 2` equations, Boolean axioms in `Γ`) with at most
`2^k` leaves gives a refutation of width `w0 + (q-1) k` (`rld_size_width`). The induction is on
the number of variables, following the paper: the root of a normal refutation resolves two units
`f = a` and `f' = b` (`f' ∝ f`); restricting the smaller subtree by `f = B` for each `B ≠ a`
refutes `Γ ↾ (f = B)`, which lifts to the clause `∨_{v ≠ B} f = v` (Corollary 43), the chain of
Proposition 14 gives the unit `f = a`, and the other subtree restricted by `f = a` gives a
refutation of `Γ ∪ {f = a}`.

LOG: R4 Phase 2.2 ResLinFWidth module
-/

namespace SATurday.ProofComplexity

namespace RLF

open scoped Classical

noncomputable section

variable {F : Type} [Field F]

theorem cmb_comm (α β : F) (e1 e2 : LEq F) : cmb α β e1 e2 = cmb β α e2 e1 := by
  unfold cmb; ext <;> simp [add_comm]

theorem rst_singleton_Z (ℓ : LEq F) (i : ℕ) {e : LEq F} (h : IsZ (elimE ℓ i e)) :
    rst ℓ i {e} = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  obtain ⟨⟨y, hy, rfl⟩, hz⟩ := mem_rst.1 hx
  rw [Finset.mem_singleton.1 hy] at hz
  exact hz h

theorem rst_card_le (ℓ : LEq F) (i : ℕ) (C : Finset (LEq F)) : (rst ℓ i C).card ≤ C.card :=
  (Finset.card_filter_le _ _).trans Finset.card_image_le

theorem rst_noZ (ℓ : LEq F) (i : ℕ) (C : Finset (LEq F)) : ∀ e ∈ rst ℓ i C, ¬ IsZ e :=
  fun _ he => (mem_rst.1 he).2

theorem rst_boolCl (ℓ : LEq F) {i j : ℕ} (hji : j ≠ i) :
    rst ℓ i (boolCl j : Finset (LEq F)) = boolCl j := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨y, hy, rfl⟩, _⟩ := mem_rst.1 hx
    have : y.1 i = 0 := by
      simp only [boolCl, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> simp [Finsupp.single_apply, Ne.symm hji]
    rwa [elimE_of_zero ℓ this]
  · intro hx
    have hi : x.1 i = 0 := by
      simp only [boolCl, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [Finsupp.single_apply, Ne.symm hji]
    refine mem_rst.2 ⟨⟨x, hx, elimE_of_zero ℓ hi⟩, ?_⟩
    simp only [boolCl, Finset.mem_insert, Finset.mem_singleton] at hx
    rintro ⟨h1, _⟩
    rcases hx with rfl | rfl <;> simp [Finsupp.single_eq_zero] at h1

theorem clSupp_rst {ℓ : LEq F} {i : ℕ} (hℓ : ℓ.1 i ≠ 0) {V : Finset ℕ} {C : Finset (LEq F)}
    (hC : ClSupp V C) (hℓV : ℓ.1.support ⊆ V) : ClSupp (V.erase i) (rst ℓ i C) := by
  intro x hx
  obtain ⟨⟨y, hy, rfl⟩, _⟩ := mem_rst.1 hx
  refine (elimE_support ℓ hℓ y).trans ?_
  exact Finset.erase_subset_erase _ (Finset.union_subset (hC y hy) hℓV)

/-- Facts about the two units of a normal refutation. -/
theorem unit_pair {e1 e2 : LEq F} {α β : F} (h1 : ¬ IsZ e1) (h2 : ¬ IsZ e2)
    (hz : IsZ (cmb α β e1 e2)) :
    e1.1 ≠ 0 ∧ ∃ μ : F, e2.1 = μ • e1.1 ∧ e2.2 - μ * e1.2 ≠ 0 := by
  have hvec : α • e1.1 + β • e2.1 = 0 := hz.1
  have hc : α * e1.2 + β * e2.2 ≠ 0 := hz.2
  have hf : e1.1 ≠ 0 := by
    intro h0
    have ha : e1.2 = 0 := by
      by_contra hne; exact h1 ⟨h0, hne⟩
    rw [ha, mul_zero, zero_add] at hc
    have hβ : β ≠ 0 := left_ne_zero_of_mul hc
    have hb2 : e2.2 ≠ 0 := right_ne_zero_of_mul hc
    rw [h0, smul_zero, zero_add] at hvec
    exact h2 ⟨(smul_eq_zero.1 hvec).resolve_left hβ, hb2⟩
  have hβ : β ≠ 0 := by
    intro hb
    rw [hb, zero_smul, add_zero] at hvec
    have : α = 0 := (smul_eq_zero.1 hvec).resolve_right hf
    apply hc; rw [this, hb]; ring
  refine ⟨hf, -α / β, ?_, ?_⟩
  · have h3 : β • e2.1 = -(α • e1.1) := eq_neg_of_add_eq_zero_right hvec
    calc e2.1 = β⁻¹ • (β • e2.1) := (inv_smul_smul₀ hβ _).symm
      _ = (-α / β) • e1.1 := by
        rw [h3, smul_neg, smul_smul, ← neg_smul]; congr 1; field_simp
  · intro h0
    apply hc
    have : e2.2 = (-α / β) * e1.2 := sub_eq_zero.1 h0
    rw [this]; field_simp; ring

variable [Fintype F]

/-- The size-width induction (Part-Tzameret Theorem 44 at plain width). -/
theorem narrow_main : ∀ (n : ℕ) (V : Finset ℕ), V.card = n → ∀ (Γ : Set (Finset (LEq F)))
    (w0 k : ℕ), 2 ≤ w0 → (∀ C ∈ Γ, C.card ≤ w0) → (∀ C ∈ Γ, ∀ e ∈ C, ¬ IsZ e) →
    (∀ j ∈ V, (boolCl j : Finset (LEq F)) ∈ Γ) → ∀ s, s ≤ 2 ^ k →
    RD {C ∈ Γ | ClSupp V C} ∅ s → ∃ s', RLD Γ (w0 + (Fintype.card F - 1) * k) ∅ s' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V hVn Γ w0 k hw0 hΓw hΓz hΓb s hs hRD
  have hq2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hZV : ∀ C ∈ {C ∈ Γ | ClSupp V C}, ∀ e ∈ C, ¬ IsZ e := fun C hC => hΓz C hC.1
  obtain ⟨L0, s0, hL0, hs0, nd⟩ := rd_to_nd hZV hRD
  have hL0e : L0 = ∅ := Finset.subset_empty.1 hL0
  rcases nd_empty_cases nd hL0e with ⟨hmem, _⟩ | ⟨e1, e2, α, β, s1, s2, nd1, nd2, hz, hsum⟩
  · exact ⟨1, RLD.ax hmem.1 (by simp)⟩
  -- the two units
  have key : ∀ (e1 e2 : LEq F) (α β : F) (s1 s2 : ℕ), ND {C ∈ Γ | ClSupp V C} {e1} s1 →
      ND {C ∈ Γ | ClSupp V C} {e2} s2 → IsZ (cmb α β e1 e2) → s1 + s2 ≤ 2 ^ k → s1 ≤ s2 →
      ∃ s', RLD Γ (w0 + (Fintype.card F - 1) * k) ∅ s' := by
    intro e1 e2 α β s1 s2 nd1 nd2 hz hsz hs12
    have h1z := nd_noZ nd1 e1 (Finset.mem_singleton_self _)
    have h2z := nd_noZ nd2 e2 (Finset.mem_singleton_self _)
    obtain ⟨hf, μ, hμ, hμc⟩ := unit_pair h1z h2z hz
    obtain ⟨f, a⟩ := e1
    simp only at hf hμ hμc
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.2 hf
    have hfi : f i ≠ 0 := Finsupp.mem_support_iff.1 hi
    have hsupV : ClSupp V {((f, a) : LEq F)} := nd_supp (fun C hC => hC.2) nd1
    have hfV : f.support ⊆ V := hsupV _ (Finset.mem_singleton_self _)
    have hiV : i ∈ V := hfV hi
    have hp1 := nd_pos nd1
    have hp2 := nd_pos nd2
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp at hsz; omega
      · omega⟩
    set q := Fintype.card F with hq
    have hWq : q + 1 ≤ w0 + (q - 1) * (k' + 1) := by
      have : q - 1 ≤ (q - 1) * (k' + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have hs1 : s1 ≤ 2 ^ k' := by
      have : 2 ^ (k' + 1) = 2 * 2 ^ k' := by ring
      omega
    have hVlt : (V.erase i).card < n := by rw [Finset.card_erase_of_mem hiV]; have := Finset.card_pos.2 ⟨i, hiV⟩; omega
    -- restriction and the induction hypothesis
    have restrictIH : ∀ (ℓ : LEq F), ℓ.1 i ≠ 0 → ℓ.1.support ⊆ V → ∀ (e : LEq F) (t kk : ℕ),
        ND {C ∈ Γ | ClSupp V C} {e} t → IsZ (elimE ℓ i e) → t ≤ 2 ^ kk →
        ∃ s', RLD (rstSet ℓ i Γ) (w0 + (q - 1) * kk) ∅ s' := by
      intro ℓ hℓi hℓV e t kk nde hZe hte
      obtain ⟨t', ht', d⟩ := rd_rst ℓ i (nd_to_rd nde)
      rw [rst_singleton_Z ℓ i hZe] at d
      refine ih (V.erase i).card hVlt (V.erase i) rfl (rstSet ℓ i Γ) w0 kk hw0 ?_ ?_ ?_ t'
        (ht'.trans hte) (rd_mono_ax ?_ d)
      · rintro _ ⟨C, hC, rfl⟩; exact (rst_card_le ℓ i C).trans (hΓw C hC)
      · rintro _ ⟨C, hC, rfl⟩; exact rst_noZ ℓ i C
      · intro j hj
        exact ⟨boolCl j, hΓb j (Finset.mem_of_mem_erase hj), rst_boolCl ℓ (Finset.ne_of_mem_erase hj)⟩
      · rintro _ ⟨C, hC, rfl⟩
        exact ⟨⟨C, hC.1, rfl⟩, clSupp_rst hℓi hC.2 hℓV⟩
    -- the image clause
    obtain ⟨sT, hTd⟩ := rld_T (Γ := Γ) (w := w0 + (q - 1) * (k' + 1)) (V := V)
      (fun j hj => hΓb j hj) hWq f.support.card f hf hfV rfl
    -- Corollary 43: the clauses `∨_{v ≠ B} f = v`
    have hQ : ∀ B, B ≠ a → ∃ s, RLD Γ (w0 + (q - 1) * (k' + 1)) ((Tset f).erase (f, B)) s := by
      intro B hB
      have hℓi : ((f, B) : LEq F).1 i ≠ 0 := hfi
      have hZe : IsZ (elimE (f, B) i (f, a)) := by
        rw [elimE_prop ((f, B) : LEq F) hℓi (e := (f, a)) (μ := 1) (by simp)]
        exact ⟨rfl, by simpa using sub_ne_zero.2 (Ne.symm hB)⟩
      obtain ⟨sr, dr⟩ := restrictIH (f, B) hℓi hfV (f, a) s1 k' nd1 hZe hs1
      have hQc : ((Tset f).erase (f, B)).card ≤ q - 1 := by
        rw [Finset.card_erase_of_mem (mem_Tset.2 ⟨B, rfl⟩)]
        have := card_Tset_le f; omega
      obtain ⟨s', d⟩ := rld_lift (Ax := Γ) (Γ' := rstSet (f, B) i Γ) ((Tset f).erase (f, B))
        (wL := w0 + (q - 1) * (k' + 1)) (by
          rintro _ ⟨C, hC, rfl⟩
          exact rld_ax_lift hTd (mem_Tset.2 ⟨B, rfl⟩) hℓi hC (by
            have := hΓw C hC
            have : q - 1 ≤ (q - 1) * (k' + 1) := Nat.le_mul_of_pos_right _ (by omega)
            omega)) dr
      rw [Finset.empty_union] at d
      refine ⟨s', rld_mono_w ?_ d⟩
      have : (q - 1) * (k' + 1) = (q - 1) * k' + (q - 1) := by ring
      refine max_le le_rfl ?_
      omega
    obtain ⟨sa, da⟩ := rld_chain hWq f a hTd hQ
    -- the second subtree, restricted by `f = a`
    have hℓ0i : ((f, a) : LEq F).1 i ≠ 0 := hfi
    have hZ2 : IsZ (elimE (f, a) i e2) := by
      rw [elimE_prop ((f, a) : LEq F) hℓ0i (e := e2) (μ := μ) hμ]
      exact ⟨rfl, hμc⟩
    obtain ⟨sr, dr⟩ := restrictIH (f, a) hℓ0i hfV e2 s2 (k' + 1) nd2 hZ2 (by omega)
    have hU : RLD (insert ({((f, a) : LEq F)} : Finset (LEq F)) Γ) (w0 + (q - 1) * (k' + 1))
        {((f, a) : LEq F)} 1 :=
      RLD.ax (Set.mem_insert _ _) (by simp; omega)
    obtain ⟨s', d⟩ := rld_lift (Ax := insert ({((f, a) : LEq F)} : Finset (LEq F)) Γ)
      (Γ' := rstSet (f, a) i Γ) (({((f, a) : LEq F)} : Finset (LEq F)).erase (f, a))
      (wL := w0 + (q - 1) * (k' + 1)) (by
        rintro _ ⟨C, hC, rfl⟩
        exact rld_ax_lift hU (Finset.mem_singleton_self _) hℓ0i (Set.mem_insert_of_mem _ hC) (by
          have := hΓw C hC
          simp
          omega)) dr
    rw [Finset.erase_singleton, Finset.empty_union] at d
    have d' := rld_mono_w (w' := w0 + (q - 1) * (k' + 1)) (by simp) d
    exact rld_subst da d'
  rcases le_total s1 s2 with h | h
  · exact key e1 e2 α β s1 s2 nd1 nd2 hz (by omega) h
  · exact key e2 e1 β α s2 s1 nd2 nd1 (by rwa [cmb_comm] at hz) (by omega) h

theorem boolAx_noZ : ∀ C ∈ (boolAx : Set (Finset (LEq F))), ∀ e ∈ C, ¬ IsZ e := by
  rintro _ ⟨j, rfl⟩ e he ⟨h1, _⟩
  simp only [boolCl, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl <;> simp [Finsupp.single_eq_zero] at h1

/-- **Theorem 44 (Part-Tzameret), tree-like size-width at plain width**: a tree-like `Res(lin F)`
refutation of `Ax ∪ boolAx` (clauses of `Ax` free of false constants and of at most `w0 ≥ 2`
equations) with `s` leaves, of arbitrary width, gives a refutation of width
`w0 + (q - 1) ⌈log₂ s⌉`, `q = |F|`. -/
theorem rld_size_width {Ax : Set (Finset (LEq F))} {w0 : ℕ} (hw0 : 2 ≤ w0)
    (hAw : ∀ C ∈ Ax, C.card ≤ w0) (hAz : ∀ C ∈ Ax, ∀ e ∈ C, ¬ IsZ e) {w s : ℕ}
    (h : RLD (Ax ∪ boolAx) w ∅ s) :
    ∃ s', RLD (Ax ∪ boolAx) (w0 + (Fintype.card F - 1) * Nat.clog 2 s) ∅ s' := by
  have hZ : ∀ C ∈ Ax ∪ boolAx, ∀ e ∈ C, ¬ IsZ e := by
    rintro C (hC | hC)
    · exact hAz C hC
    · exact boolAx_noZ C hC
  obtain ⟨L0, s0, hL0, hs0, nd⟩ := rd_to_nd hZ (rd_of_rld h)
  have hL0e : L0 = ∅ := Finset.subset_empty.1 hL0
  subst hL0e
  obtain ⟨V, ndV⟩ := nd_exists_V nd
  refine narrow_main V.card V rfl (Ax ∪ boolAx) w0 (Nat.clog 2 s) hw0 ?_ hZ
    (fun j _ => Or.inr (boolCl_mem_boolAx j)) s0 (hs0.trans (Nat.le_pow_clog (by norm_num) s))
    (nd_to_rd ndV)
  rintro C (hC | ⟨j, rfl⟩)
  · exact hAw C hC
  · rw [boolCl_card]; exact hw0

end

end RLF

end SATurday.ProofComplexity
