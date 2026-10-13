import Theory.ProofComplexity.ResLinFRst

/-!
# Image clauses and the unit chain (Ladder Rung R4, Phase 2.2, layer 3c)

Over a finite field `F` with `q` elements: for a nonzero linear form `f` the clause
`Tset f = ∨_{v ∈ F} (f = v)` has a `Res(lin F)` derivation of width `q + 1` from the Boolean
axioms of the variables of `f` (Part-Tzameret Proposition 12, `rld_T`), and the unit `f = a` is
derived from `Tset f` and the clauses `∨_{v ≠ B} (f = v)`, `B ≠ a` (Proposition 14, `rld_chain`).

LOG: R4 Phase 2.2 ResLinFImg module
-/

namespace SATurday.ProofComplexity

namespace RLF

open scoped Classical

noncomputable section

variable {F : Type} [Field F] [Fintype F]

/-- The clause `∨_{v ∈ F} (f = v)`. -/
def Tset (f : ℕ →₀ F) : Finset (LEq F) := Finset.univ.image fun v => (f, v)

theorem mem_Tset {f : ℕ →₀ F} {e : LEq F} : e ∈ Tset f ↔ ∃ v, e = (f, v) := by
  unfold Tset; simp [eq_comm]

theorem card_Tset_le (f : ℕ →₀ F) : (Tset f).card ≤ Fintype.card F :=
  (Finset.card_image_le).trans (by simp)

/-! ### Resolving a false constant away -/

section Tderiv

variable {Γ : Set (Finset (LEq F))} {w : ℕ}

theorem cmb_const_false (x : ℕ →₀ F) (b : F) :
    cmb (1 : F) (-1) ((x, b) : LEq F) (x, 0) = (0, b) := by
  unfold cmb; ext <;> simp

/-- From `∨_v (h = v)` and the Boolean axiom of `x_j` derive `(x_j = b') ∨ ∨_v (h + c x_j = v)`. -/
theorem rld_T_half {h : ℕ →₀ F} {j : ℕ} {c : F} {sh : ℕ} (hT : RLD Γ w (Tset h) sh)
    (Bc : Finset (LEq F)) {sB : ℕ} (hB : RLD Γ w Bc sB) (b b' : F)
    (hbm : (Finsupp.single j (1 : F), b) ∈ Bc)
    (hBsub : Bc.erase (Finsupp.single j (1 : F), b) ⊆ {(Finsupp.single j (1 : F), b')})
    (hw : Fintype.card F + 1 ≤ w) :
    ∃ s, RLD Γ w (insert (Finsupp.single j (1 : F), b') (Tset (h + c • Finsupp.single j (1 : F)))) s := by
  set x : ℕ →₀ F := Finsupp.single j 1 with hx
  set f : ℕ →₀ F := h + c • x with hf
  let XS : Finset F → Finset (LEq F) := fun S =>
    (Finset.univ.filter fun v => v ∉ S).image (fun v => (h, v)) ∪ {(x, b')} ∪
      S.image (fun v => ((f, v + c * b) : LEq F))
  have hXcard : ∀ S, (XS S).card ≤ Fintype.card F + 1 := by
    intro S
    have h1 : ((Finset.univ.filter fun v => v ∉ S).image (fun v => ((h, v) : LEq F))).card
        ≤ (Finset.univ.filter fun v => v ∉ S).card := Finset.card_image_le
    have h2 : (S.image (fun v => ((f, v + c * b) : LEq F))).card ≤ S.card := Finset.card_image_le
    have h3 : (Finset.univ.filter fun v => v ∉ S).card + S.card ≤ Fintype.card F := by
      rw [← Finset.card_union_of_disjoint]
      · exact (Finset.card_le_univ _)
      · rw [Finset.disjoint_left]; intro a ha; simp at ha; simp [ha]
    have e1 := Finset.card_union_le
      (((Finset.univ.filter fun v => v ∉ S).image (fun v => ((h, v) : LEq F))) ∪ {(x, b')})
      (S.image (fun v => ((f, v + c * b) : LEq F)))
    have e2 := Finset.card_union_le
      ((Finset.univ.filter fun v => v ∉ S).image (fun v => ((h, v) : LEq F))) {((x, b') : LEq F)}
    have e3 : ({((x, b') : LEq F)} : Finset (LEq F)).card = 1 := Finset.card_singleton _
    show (XS S).card ≤ _
    simp only [XS]
    omega
  have key : ∀ S : Finset F, ∃ s, RLD Γ w (XS S) s := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨sh, RLD.weak hT ?_ ((hXcard _).trans hw)⟩
      intro e he
      obtain ⟨v, rfl⟩ := mem_Tset.1 he
      simp only [XS]
      refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨v, ?_, rfl⟩))
      simp
    | @insert v S hv ih =>
      obtain ⟨s0, d0⟩ := ih
      have hmem : ((h, v) : LEq F) ∈ XS S := by
        simp only [XS]
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨v, by simp [hv], rfl⟩))
      have hcm : cmb (1 : F) c ((h, v) : LEq F) ((x, b) : LEq F) = (f, v + c * b) := by
        unfold cmb; ext <;> simp [hf]
      refine ⟨_, rld_comb' (Ax := Γ) (w := w) ((h, v) : LEq F) ((x, b) : LEq F) 1 c d0 hB hmem hbm ?_
        ((hXcard _).trans hw)⟩
      rw [hcm]
      intro e he
      simp only [XS]
      rcases Finset.mem_union.1 he with he | he
      · rcases Finset.mem_union.1 he with he | he
        · obtain ⟨hne, he⟩ := Finset.mem_erase.1 he
          simp only [XS, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
            true_and, Finset.mem_singleton] at he
          simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
            true_and, Finset.mem_singleton, Finset.mem_insert]
          rcases he with (⟨u, hu, rfl⟩ | rfl) | ⟨u, hu, rfl⟩
          · left; left
            refine ⟨u, ?_, rfl⟩
            intro hh
            rcases hh with rfl | hh
            · exact hne rfl
            · exact hu hh
          · left; right; rfl
          · right; exact ⟨u, Or.inr hu, rfl⟩
        · have := hBsub (by simpa using he)
          rw [Finset.mem_singleton] at this
          simp only [Finset.mem_union, Finset.mem_singleton]
          left; right; exact this
      · rw [Finset.mem_singleton.1 he]
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert]
        right; exact ⟨v, Or.inl rfl, rfl⟩
  obtain ⟨s, d⟩ := key Finset.univ
  refine ⟨s, RLD.weak d ?_ ?_⟩
  · intro e he
    simp only [XS] at he
    rcases Finset.mem_union.1 he with he | he
    · rcases Finset.mem_union.1 he with he | he
      · obtain ⟨v, hv, _⟩ := Finset.mem_image.1 he
        simp at hv
      · rw [Finset.mem_singleton.1 he]; exact Finset.mem_insert_self _ _
    · obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 he
      exact Finset.mem_insert_of_mem (mem_Tset.2 ⟨_, rfl⟩)
  · refine (Finset.card_insert_le _ _).trans ?_
    have := card_Tset_le f
    omega

/-- Resolving `{x = 1} ∨ T` with `{x = 0} ∨ T` on the Boolean equation removes it. -/
theorem rld_T_fin {f x : ℕ →₀ F} {s0 s1 : ℕ}
    (h0 : RLD Γ w (insert (x, (1 : F)) (Tset f)) s0) (h1 : RLD Γ w (insert (x, (0 : F)) (Tset f)) s1)
    (hw : Fintype.card F + 1 ≤ w) : ∃ s, RLD Γ w (Tset f) s := by
  refine ⟨_, rld_res_false (Ax := Γ) (w := w) (x, (1 : F)) (x, (0 : F)) 1 (-1) 1 one_ne_zero
    (by rw [cmb_const_false]) h0 h1 (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _) ?_ ?_⟩
  · intro e he
    rcases Finset.mem_union.1 he with he | he
    · obtain ⟨hne, he⟩ := Finset.mem_erase.1 he
      exact (Finset.mem_insert.1 he).resolve_left hne
    · obtain ⟨hne, he⟩ := Finset.mem_erase.1 he
      exact (Finset.mem_insert.1 he).resolve_left hne
  · have := card_Tset_le f
    omega

theorem boolCl_erase (j : ℕ) (b b' : F) (hb : b ≠ b')
    (hs : (boolCl j : Finset (LEq F)) = {(Finsupp.single j (1 : F), b), (Finsupp.single j (1 : F), b')}) :
    (boolCl j : Finset (LEq F)).erase (Finsupp.single j (1 : F), b) ⊆ {(Finsupp.single j (1 : F), b')} := by
  rw [hs]
  intro e he
  obtain ⟨hne, he⟩ := Finset.mem_erase.1 he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he ⊢
  exact he.resolve_left hne

theorem boolCl_erase0 (j : ℕ) :
    (boolCl j : Finset (LEq F)).erase (Finsupp.single j (1 : F), 0) ⊆ {(Finsupp.single j (1 : F), 1)} :=
  boolCl_erase j 0 1 zero_ne_one rfl

theorem boolCl_erase1 (j : ℕ) :
    (boolCl j : Finset (LEq F)).erase (Finsupp.single j (1 : F), 1) ⊆ {(Finsupp.single j (1 : F), 0)} := by
  intro e he
  obtain ⟨hne, he⟩ := Finset.mem_erase.1 he
  simp only [boolCl, Finset.mem_insert, Finset.mem_singleton] at he ⊢
  exact he.resolve_right hne

theorem card_two_le {w : ℕ} (hw : Fintype.card F + 1 ≤ w) : 2 ≤ w := by
  have : 1 < Fintype.card F := Fintype.one_lt_card
  omega

/-- **Proposition 12 (Part-Tzameret)**: `∨_{v ∈ F} (f = v)` is derivable at width `q + 1`
from the Boolean axioms of the variables of `f`. -/
theorem rld_T {Γ : Set (Finset (LEq F))} {w : ℕ} {V : Finset ℕ}
    (hB : ∀ j ∈ V, (boolCl j : Finset (LEq F)) ∈ Γ) (hw : Fintype.card F + 1 ≤ w) :
    ∀ (n : ℕ) (f : ℕ →₀ F), f ≠ 0 → f.support ⊆ V → f.support.card = n →
      ∃ s, RLD Γ w (Tset f) s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hf hV hn
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.2 hf
  have hjV : j ∈ V := hV hj
  set c : F := f j with hc
  set h : ℕ →₀ F := f.erase j with hh
  have hdec : f = h + c • Finsupp.single j (1 : F) := by
    rw [Finsupp.smul_single_one, hh, hc, Finsupp.erase_add_single]
  have hBc : RLD Γ w (boolCl j) 1 := RLD.ax (hB j hjV) (by rw [boolCl_card]; exact card_two_le hw)
  have hmem0 : ((Finsupp.single j (1 : F), (0 : F)) : LEq F) ∈ boolCl j := by simp [boolCl]
  have hmem1 : ((Finsupp.single j (1 : F), (1 : F)) : LEq F) ∈ boolCl j := by simp [boolCl]
  by_cases hh0 : h = 0
  · -- base case: f = c • x_j
    have hf' : f = c • Finsupp.single j (1 : F) := by rw [hdec, hh0, zero_add]
    set x : ℕ →₀ F := Finsupp.single j 1 with hx
    have hcard : (insert ((x, (1 : F)) : LEq F) (Tset f)).card ≤ w := by
      refine (Finset.card_insert_le _ _).trans ?_
      have := card_Tset_le f; omega
    have hcard' : (insert ((x, (0 : F)) : LEq F) (Tset f)).card ≤ w := by
      refine (Finset.card_insert_le _ _).trans ?_
      have := card_Tset_le f; omega
    have E0 : ∃ s, RLD Γ w (insert ((x, (1 : F)) : LEq F) (Tset f)) s := by
      refine ⟨_, rld_comb' (Ax := Γ) (w := w) ((x, (0 : F)) : LEq F) ((x, (0 : F)) : LEq F) c 0
        hBc hBc hmem0 hmem0 ?_ hcard⟩
      have hcm : cmb c (0 : F) ((x, (0 : F)) : LEq F) ((x, (0 : F)) : LEq F) = (f, 0) := by
        unfold cmb; ext <;> simp [hf']
      rw [hcm]
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact (boolCl_erase0 j).trans (by intro e he; rw [Finset.mem_singleton.1 he]; exact Finset.mem_insert_self _ _)
      · exact (boolCl_erase0 j).trans (by intro e he; rw [Finset.mem_singleton.1 he]; exact Finset.mem_insert_self _ _)
      · intro e he; rw [Finset.mem_singleton.1 he]
        exact Finset.mem_insert_of_mem (mem_Tset.2 ⟨0, rfl⟩)
    have E1 : ∃ s, RLD Γ w (insert ((x, (0 : F)) : LEq F) (Tset f)) s := by
      refine ⟨_, rld_comb' (Ax := Γ) (w := w) ((x, (1 : F)) : LEq F) ((x, (1 : F)) : LEq F) c 0
        hBc hBc hmem1 hmem1 ?_ hcard'⟩
      have hcm : cmb c (0 : F) ((x, (1 : F)) : LEq F) ((x, (1 : F)) : LEq F) = (f, c) := by
        unfold cmb; ext <;> simp [hf']
      rw [hcm]
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact (boolCl_erase1 j).trans (by intro e he; rw [Finset.mem_singleton.1 he]; exact Finset.mem_insert_self _ _)
      · exact (boolCl_erase1 j).trans (by intro e he; rw [Finset.mem_singleton.1 he]; exact Finset.mem_insert_self _ _)
      · intro e he; rw [Finset.mem_singleton.1 he]
        exact Finset.mem_insert_of_mem (mem_Tset.2 ⟨c, rfl⟩)
    obtain ⟨s0, d0⟩ := E0
    obtain ⟨s1, d1⟩ := E1
    exact rld_T_fin d0 d1 hw
  · -- step
    have hsupp : h.support.card < n := by
      rw [hh, Finsupp.support_erase, Finset.card_erase_of_mem hj]
      have : 0 < f.support.card := Finset.card_pos.2 ⟨j, hj⟩
      omega
    have hhV : h.support ⊆ V := by
      intro i hi
      rw [hh, Finsupp.support_erase] at hi
      exact hV (Finset.mem_of_mem_erase hi)
    obtain ⟨sh, dh⟩ := ih _ hsupp h hh0 hhV rfl
    obtain ⟨s0, d0⟩ := rld_T_half (c := c) dh (boolCl j) hBc 0 1 hmem0 (boolCl_erase0 j) hw
    obtain ⟨s1, d1⟩ := rld_T_half (c := c) dh (boolCl j) hBc 1 0 hmem1 (boolCl_erase1 j) hw
    rw [← hdec] at d0 d1
    exact rld_T_fin d0 d1 hw

theorem cmb_const (x : ℕ →₀ F) (b b' : F) :
    cmb (1 : F) (-1) ((x, b) : LEq F) (x, b') = (0, b - b') := by
  unfold cmb; ext <;> simp [sub_eq_add_neg]

/-- **Proposition 14 (Part-Tzameret)**: the unit `f = a` follows from `∨_v (f = v)` and the
clauses `∨_{v ≠ B} (f = v)`, `B ≠ a`. -/
theorem rld_chain {Γ : Set (Finset (LEq F))} {w : ℕ} (hw : Fintype.card F + 1 ≤ w)
    (f : ℕ →₀ F) (a : F) {sT : ℕ} (hT : RLD Γ w (Tset f) sT)
    (hQ : ∀ B, B ≠ a → ∃ s, RLD Γ w ((Tset f).erase (f, B)) s) :
    ∃ s, RLD Γ w {((f, a) : LEq F)} s := by
  let Y : Finset F → Finset (LEq F) := fun S =>
    (Finset.univ.filter fun v => v ∉ S).image (fun v => ((f, v) : LEq F))
  have hYcard : ∀ S, (Y S).card + 1 ≤ w := by
    intro S
    have : (Y S).card ≤ Fintype.card F := Finset.card_image_le.trans (Finset.card_le_univ _)
    omega
  have claim : ∀ S : Finset F, a ∉ S → ∃ s, RLD Γ w (Y S) s := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨sT, RLD.weak hT ?_ (by have := hYcard ∅; omega)⟩
      intro e he
      obtain ⟨v, rfl⟩ := mem_Tset.1 he
      exact Finset.mem_image.2 ⟨v, by simp, rfl⟩
    | @insert B S hB ih =>
      intro haS
      have haB : a ≠ B := fun h => haS (h ▸ Finset.mem_insert_self _ _)
      have haS' : a ∉ S := fun h => haS (Finset.mem_insert_of_mem h)
      obtain ⟨sS, dS⟩ := ih haS'
      obtain ⟨sQ, dQ⟩ := hQ B (Ne.symm haB)
      let X : Finset F → Finset (LEq F) := fun S' =>
        (Finset.univ.filter fun u => u ≠ B ∧ u ∉ S').image (fun u => ((f, u) : LEq F))
      have hXcard : ∀ S', (X S').card + 1 ≤ w := by
        intro S'
        have : (X S').card ≤ Fintype.card F := Finset.card_image_le.trans (Finset.card_le_univ _)
        omega
      have inner : ∀ S' : Finset F, S' ⊆ S → ∃ s, RLD Γ w (X S') s := by
        intro S'
        induction S' using Finset.induction_on with
        | empty =>
          intro _
          refine ⟨sQ, RLD.weak dQ ?_ (by have := hXcard ∅; omega)⟩
          intro e he
          obtain ⟨hne, he⟩ := Finset.mem_erase.1 he
          obtain ⟨v, rfl⟩ := mem_Tset.1 he
          exact Finset.mem_image.2 ⟨v, by simp; intro hv; exact hne (by rw [hv]), rfl⟩
        | @insert u S' hu ih2 =>
          intro hsub
          obtain ⟨s2, d2⟩ := ih2 ((Finset.subset_insert _ _).trans hsub)
          have huS : u ∈ S := hsub (Finset.mem_insert_self _ _)
          have huB : u ≠ B := fun h => hB (h ▸ huS)
          have m1 : ((f, u) : LEq F) ∈ X S' :=
            Finset.mem_image.2 ⟨u, by simp [huB, hu], rfl⟩
          have m2 : ((f, B) : LEq F) ∈ Y S :=
            Finset.mem_image.2 ⟨B, by simp [hB], rfl⟩
          refine ⟨_, rld_res_false (Ax := Γ) (w := w) ((f, u) : LEq F) ((f, B) : LEq F) 1 (-1) (u - B)
            (sub_ne_zero.2 huB) (cmb_const f u B) d2 dS m1 m2 ?_ (hXcard _)⟩
          intro e he
          rcases Finset.mem_union.1 he with he | he
          · obtain ⟨hne, he⟩ := Finset.mem_erase.1 he
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
            refine Finset.mem_image.2 ⟨v, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, not_or]
            refine ⟨hv.1, ?_, hv.2⟩
            rintro rfl; exact hne rfl
          · obtain ⟨hne, he⟩ := Finset.mem_erase.1 he
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
            refine Finset.mem_image.2 ⟨v, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, not_or]
            refine ⟨?_, ?_, ?_⟩
            · intro hvB; exact hne (by rw [hvB])
            · intro hvu; exact hv (hvu ▸ huS)
            · intro hvS'; exact hv (hsub (Finset.mem_insert_of_mem hvS'))
      obtain ⟨s3, d3⟩ := inner S subset_rfl
      refine ⟨s3, RLD.weak d3 ?_ (by have := hYcard (insert B S); omega)⟩
      intro e he
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      refine Finset.mem_image.2 ⟨v, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, not_or]
      exact ⟨hv.1, hv.2⟩
  obtain ⟨s, d⟩ := claim (Finset.univ.erase a) (by simp)
  refine ⟨s, RLD.weak d ?_ (by simp; omega)⟩
  intro e he
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
  have hv' := (Finset.mem_filter.1 hv).2
  have hva : v = a := by
    by_contra hne
    exact hv' (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩)
  rw [Finset.mem_singleton, hva]

end Tderiv

end

end RLF

end SATurday.ProofComplexity
