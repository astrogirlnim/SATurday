import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Matching restrictions and matching decision trees (Ladder Rung R4, 1B.3)

Partial matchings between pigeons `P` and holes `H` (edges `(i, j)`), matching DNFs (lists of
partial matchings), and the canonical matching decision tree depth `mdepth`: take the first
term compatible with the restriction; if it is contained in the restriction the depth is `0`,
otherwise query all its free vertices (branching over every cover of them by free edges) and
continue. The depth counts the term edges, so a branch has at most twice that many edges.

`cover_of_mdepth`: if the canonical depth is at most `s`, then for every free partial matching
`π` with enough room there is a branch `σ` of size at most `2 s`, compatible with `π`, which
either contains a restricted term or is incompatible with every restricted term.

LOG: R4 Matching module (matching restrictions, canonical matching trees)
-/

namespace SATurday.ProofComplexity

open Finset

noncomputable section

open Classical

/-- Edge sets (partial matchings when `IsMatch`). -/
abbrev Mt := Finset (ℕ × ℕ)

/-- No two edges of `A` and `B` share an endpoint unless they are equal. -/
def Cross (A B : Mt) : Prop := ∀ e ∈ A, ∀ f ∈ B, (e.1 = f.1 ∨ e.2 = f.2) → e = f

/-- A partial matching. -/
def IsMatch (A : Mt) : Prop := Cross A A

/-- Two partial matchings are compatible when their union is a matching. -/
def Compat (A B : Mt) : Prop := IsMatch (A ∪ B)

/-- Pigeons and holes touched by an edge set. -/
def pigs (A : Mt) : Finset ℕ := A.image Prod.fst
def hols (A : Mt) : Finset ℕ := A.image Prod.snd

/-- Free pigeons, free holes and free edges of a restriction. -/
def fP (P : Finset ℕ) (ρ : Mt) : Finset ℕ := P \ pigs ρ
def fH (H : Finset ℕ) (ρ : Mt) : Finset ℕ := H \ hols ρ
def freeE (P H : Finset ℕ) (ρ : Mt) : Mt := fP P ρ ×ˢ fH H ρ

theorem cross_symm {A B : Mt} (h : Cross A B) : Cross B A :=
  fun e he f hf hef => (h f hf e he (hef.imp Eq.symm Eq.symm)).symm

theorem cross_mono {A B A' B' : Mt} (h : Cross A B) (hA : A' ⊆ A) (hB : B' ⊆ B) :
    Cross A' B' := fun e he f hf => h e (hA he) f (hB hf)

theorem cross_union_left {A B C : Mt} : Cross (A ∪ B) C ↔ Cross A C ∧ Cross B C := by
  constructor
  · intro h; exact ⟨cross_mono h subset_union_left subset_rfl,
      cross_mono h subset_union_right subset_rfl⟩
  · rintro ⟨h1, h2⟩ e he f hf
    rcases mem_union.1 he with he | he
    · exact h1 e he f hf
    · exact h2 e he f hf

theorem cross_union_right {A B C : Mt} : Cross A (B ∪ C) ↔ Cross A B ∧ Cross A C := by
  constructor
  · intro h; exact ⟨cross_mono h subset_rfl subset_union_left,
      cross_mono h subset_rfl subset_union_right⟩
  · rintro ⟨h1, h2⟩ e he f hf
    rcases mem_union.1 hf with hf | hf
    · exact h1 e he f hf
    · exact h2 e he f hf

theorem isMatch_union {A B : Mt} : IsMatch (A ∪ B) ↔ IsMatch A ∧ IsMatch B ∧ Cross A B := by
  unfold IsMatch
  rw [cross_union_left, cross_union_right, cross_union_right]
  constructor
  · rintro ⟨⟨h1, h2⟩, _, h4⟩; exact ⟨h1, h4, h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, cross_symm h3, h2⟩

theorem isMatch_mono {A B : Mt} (h : IsMatch B) (hAB : A ⊆ B) : IsMatch A :=
  cross_mono h hAB hAB

theorem isMatch_empty : IsMatch ∅ := fun e he => by simp at he

theorem compat_symm {A B : Mt} (h : Compat A B) : Compat B A := by
  unfold Compat; rwa [union_comm]

theorem compat_mono {A B A' B' : Mt} (h : Compat A B) (hA : A' ⊆ A) (hB : B' ⊆ B) :
    Compat A' B' := isMatch_mono h (union_subset_union hA hB)

theorem compat_iff {A B : Mt} : Compat A B ↔ IsMatch A ∧ IsMatch B ∧ Cross A B :=
  isMatch_union

/-- Union of three edge sets is a matching when each pair is compatible. -/
theorem isMatch_union3 {A B C : Mt} (h1 : Compat A B) (h2 : Compat A C) (h3 : Compat B C) :
    IsMatch (A ∪ B ∪ C) := by
  rw [isMatch_union, isMatch_union]
  rw [compat_iff] at h1 h2 h3
  exact ⟨⟨h1.1, h1.2.1, h1.2.2⟩, h2.2.1, cross_union_left.2 ⟨h2.2.2, h3.2.2⟩⟩

theorem cross_of_disj {A B : Mt} (h : ∀ e ∈ A, ∀ f ∈ B, e.1 ≠ f.1 ∧ e.2 ≠ f.2) :
    Cross A B := by
  intro e he f hf hef
  rcases hef with hef | hef
  · exact absurd hef (h e he f hf).1
  · exact absurd hef (h e he f hf).2

theorem mem_pigs {A : Mt} {i : ℕ} : i ∈ pigs A ↔ ∃ e ∈ A, e.1 = i := by simp [pigs]
theorem mem_hols {A : Mt} {j : ℕ} : j ∈ hols A ↔ ∃ e ∈ A, e.2 = j := by simp [hols]

theorem mem_freeE {P H : Finset ℕ} {ρ : Mt} {e : ℕ × ℕ} :
    e ∈ freeE P H ρ ↔ (e.1 ∈ P ∧ e.1 ∉ pigs ρ) ∧ (e.2 ∈ H ∧ e.2 ∉ hols ρ) := by
  simp [freeE, fP, fH, mem_product, mem_sdiff]

/-- Free edges are vertex disjoint from the restriction. -/
theorem disj_free {P H : Finset ℕ} {ρ A : Mt} (hA : A ⊆ freeE P H ρ) :
    ∀ e ∈ A, ∀ f ∈ ρ, e.1 ≠ f.1 ∧ e.2 ≠ f.2 := by
  intro e he f hf
  have := mem_freeE.1 (hA he)
  exact ⟨fun h => this.1.2 (mem_pigs.2 ⟨f, hf, h.symm⟩),
    fun h => this.2.2 (mem_hols.2 ⟨f, hf, h.symm⟩)⟩

theorem compat_free {P H : Finset ℕ} {ρ A : Mt} (hρ : IsMatch ρ) (hAm : IsMatch A)
    (hA : A ⊆ freeE P H ρ) : Compat A ρ :=
  compat_iff.2 ⟨hAm, hρ, cross_of_disj (disj_free hA)⟩

theorem card_pigs {A : Mt} (h : IsMatch A) : (pigs A).card = A.card :=
  card_image_of_injOn fun e he f hf hef => h e he f hf (Or.inl hef)

theorem card_hols {A : Mt} (h : IsMatch A) : (hols A).card = A.card :=
  card_image_of_injOn fun e he f hf hef => h e he f hf (Or.inr hef)

theorem pigs_union (A B : Mt) : pigs (A ∪ B) = pigs A ∪ pigs B := image_union _ _
theorem hols_union (A B : Mt) : hols (A ∪ B) = hols A ∪ hols B := image_union _ _

theorem pigs_mono {A B : Mt} (h : A ⊆ B) : pigs A ⊆ pigs B := image_subset_image h
theorem hols_mono {A B : Mt} (h : A ⊆ B) : hols A ⊆ hols B := image_subset_image h

theorem fH_card {H : Finset ℕ} {ρ : Mt} (hρ : IsMatch ρ) (hsub : hols ρ ⊆ H) :
    (fH H ρ).card = H.card - ρ.card := by
  rw [fH, card_sdiff_of_subset hsub, card_hols hρ]

theorem fP_card {P : Finset ℕ} {ρ : Mt} (hρ : IsMatch ρ) (hsub : pigs ρ ⊆ P) :
    (fP P ρ).card = P.card - ρ.card := by
  rw [fP, card_sdiff_of_subset hsub, card_pigs hρ]

/-- Edges of `A` lying in a universe. -/
def InU (P H : Finset ℕ) (A : Mt) : Prop := A ⊆ P ×ˢ H

theorem pigs_sub {P H : Finset ℕ} {A : Mt} (h : InU P H A) : pigs A ⊆ P := by
  intro i hi; obtain ⟨e, he, rfl⟩ := mem_pigs.1 hi; exact (mem_product.1 (h he)).1

theorem hols_sub {P H : Finset ℕ} {A : Mt} (h : InU P H A) : hols A ⊆ H := by
  intro j hj; obtain ⟨e, he, rfl⟩ := mem_hols.1 hj; exact (mem_product.1 (h he)).2

/-- The part of a term compatible with `ρ` outside `ρ` is free. -/
theorem sdiff_free {P H : Finset ℕ} {ρ t : Mt} (hc : Compat ρ t) (ht : InU P H t) :
    t \ ρ ⊆ freeE P H ρ := by
  intro e he
  obtain ⟨het, heρ⟩ := mem_sdiff.1 he
  have hu := mem_product.1 (ht het)
  have hm := (compat_iff.1 hc).2.2
  refine mem_freeE.2 ⟨⟨hu.1, fun hi => ?_⟩, ⟨hu.2, fun hj => ?_⟩⟩
  · obtain ⟨f, hf, hfe⟩ := mem_pigs.1 hi
    exact heρ (hm f hf e het (Or.inl hfe) ▸ hf)
  · obtain ⟨f, hf, hfe⟩ := mem_hols.1 hj
    exact heρ (hm f hf e het (Or.inr hfe) ▸ hf)

/-! ## Matching DNFs and the canonical depth -/

/-- A matching DNF: an ordered list of partial matchings (terms). -/
abbrev MDNF := List Mt

/-- First term compatible with the restriction. -/
def mfirst (ρ : Mt) (D : MDNF) : Option Mt := D.find? fun t => Compat ρ t

/-- Covers of the vertices of `τ` by free edges, each edge touching a vertex of `τ`. -/
def covers (P H : Finset ℕ) (ρ τ : Mt) : Finset Mt :=
  (freeE P H ρ).powerset.filter fun σ => IsMatch σ ∧ pigs τ ⊆ pigs σ ∧ hols τ ⊆ hols σ ∧
    ∀ e ∈ σ, e.1 ∈ pigs τ ∨ e.2 ∈ hols τ

theorem covers_nonempty {P H : Finset ℕ} {ρ τ σ : Mt} (hσ : σ ∈ covers P H ρ τ)
    (hτ : τ.Nonempty) : σ.Nonempty := by
  obtain ⟨e, he⟩ := hτ
  have := (mem_filter.1 hσ).2.2.1 (mem_pigs.2 ⟨e, he, rfl⟩)
  obtain ⟨f, hf, -⟩ := mem_pigs.1 this
  exact ⟨f, hf⟩

theorem fH_union_lt {P H : Finset ℕ} {ρ σ : Mt} (hσ : σ ⊆ freeE P H ρ) (hne : σ.Nonempty) :
    (fH H (ρ ∪ σ)).card < (fH H ρ).card := by
  apply card_lt_card
  refine ⟨fun j hj => ?_, fun h => ?_⟩
  · simp only [fH, mem_sdiff, hols_union, mem_union, not_or] at hj ⊢
    exact ⟨hj.1, hj.2.1⟩
  · obtain ⟨e, he⟩ := hne
    have hfree := mem_freeE.1 (hσ he)
    have := h (mem_sdiff.2 ⟨hfree.2.1, hfree.2.2⟩)
    simp only [fH, mem_sdiff, hols_union, mem_union, not_or] at this
    exact this.2.2 (mem_hols.2 ⟨e, he, rfl⟩)

theorem mfirst_compat {ρ : Mt} {D : MDNF} {t : Mt} (h : mfirst ρ D = some t) : Compat ρ t := by
  have := List.find?_some h
  simpa using this

theorem mfirst_mem {ρ : Mt} {D : MDNF} {t : Mt} (h : mfirst ρ D = some t) : t ∈ D :=
  List.mem_of_find?_eq_some h

theorem mfirst_none {ρ : Mt} {D : MDNF} (h : mfirst ρ D = none) : ∀ t ∈ D, ¬ Compat ρ t := by
  intro t ht hc
  have := List.find?_eq_none.1 h t ht
  simp_all

/-- Canonical matching decision tree depth (counting term edges). -/
def mdepth (P H : Finset ℕ) (D : MDNF) : Mt → ℕ
  | ρ => match h : mfirst ρ D with
    | none => 0
    | some t =>
        if hs : t ⊆ ρ then 0
        else (t \ ρ).card + (covers P H ρ (t \ ρ)).attach.sup fun σ =>
          mdepth P H D (ρ ∪ σ.1)
termination_by ρ => (fH H ρ).card
decreasing_by
  have hσ := mem_filter.1 σ.2
  refine fH_union_lt (mem_powerset.1 hσ.1) (covers_nonempty σ.2 ?_)
  obtain ⟨e, he⟩ := not_subset.1 hs
  exact ⟨e, mem_sdiff.2 he⟩

theorem mdepth_none {P H : Finset ℕ} {D : MDNF} {ρ : Mt} (h : mfirst ρ D = none) :
    mdepth P H D ρ = 0 := by
  rw [mdepth]; split <;> simp_all

theorem mdepth_some {P H : Finset ℕ} {D : MDNF} {ρ t : Mt}
    (h : mfirst ρ D = some t) :
    mdepth P H D ρ = if t ⊆ ρ then 0 else (t \ ρ).card +
      (covers P H ρ (t \ ρ)).attach.sup fun σ => mdepth P H D (ρ ∪ σ.1) := by
  rw [mdepth]; split
  · simp_all
  · rename_i t' h'
    rw [h] at h'; cases h'
    by_cases hs : t ⊆ ρ <;> simp [hs]

theorem le_mdepth_cover {P H : Finset ℕ} {D : MDNF} {ρ t σ : Mt}
    (h : mfirst ρ D = some t) (hs : ¬ t ⊆ ρ) (hσ : σ ∈ covers P H ρ (t \ ρ)) :
    (t \ ρ).card + mdepth P H D (ρ ∪ σ) ≤ mdepth P H D ρ := by
  rw [mdepth_some h, if_neg hs]
  exact Nat.add_le_add_left (le_sup (f := fun σ : {x // x ∈ covers P H ρ (t \ ρ)} =>
    mdepth P H D (ρ ∪ σ.1)) (mem_attach _ ⟨σ, hσ⟩)) _

/-- Covers have at most twice as many edges as the covered matching. -/
theorem covers_card {P H : Finset ℕ} {ρ τ σ : Mt} (hσ : σ ∈ covers P H ρ τ) (hτ : IsMatch τ) :
    σ.card ≤ 2 * τ.card := by
  obtain ⟨-, hm, -, -, htouch⟩ := mem_filter.1 hσ
  have h1 : (σ.filter fun e => e.1 ∈ pigs τ).card ≤ τ.card := by
    rw [← card_pigs hτ]
    refine card_le_card_of_injOn Prod.fst (fun e he => (mem_filter.1 he).2) ?_
    intro e he f hf hef
    exact hm e (mem_filter.1 he).1 f (mem_filter.1 hf).1 (Or.inl hef)
  have h2 : (σ.filter fun e => ¬ e.1 ∈ pigs τ).card ≤ τ.card := by
    rw [← card_hols hτ]
    refine card_le_card_of_injOn Prod.snd (fun e he => ?_) ?_
    · have := mem_filter.1 he
      exact (htouch e this.1).resolve_left this.2
    · intro e he f hf hef
      exact hm e (mem_filter.1 he).1 f (mem_filter.1 hf).1 (Or.inr hef)
  have := card_filter_add_card_filter_not (s := σ) (fun e => e.1 ∈ pigs τ)
  omega

/-! ## Building covers and the coverage lemma -/

theorem exists_inj (B : Finset ℕ) : ∀ A : Finset ℕ, A.card ≤ B.card →
    ∃ f : ℕ → ℕ, (∀ a ∈ A, f a ∈ B) ∧ Set.InjOn f A := by
  intro A
  induction A using Finset.induction_on with
  | empty => exact fun _ => ⟨id, by simp, by simp⟩
  | insert a A ha ih =>
    intro hc
    rw [card_insert_of_notMem ha] at hc
    obtain ⟨f, hf, hinj⟩ := ih (by omega)
    obtain ⟨b, hb, hbn⟩ : ∃ b ∈ B, b ∉ A.image f :=
      exists_mem_notMem_of_card_lt_card (lt_of_le_of_lt card_image_le (by omega))
    refine ⟨Function.update f a b, fun x hx => ?_, fun x hx y hy hxy => ?_⟩
    · rcases mem_insert.1 hx with rfl | hx
      · simpa using hb
      · have : x ≠ a := fun h => ha (h ▸ hx)
        simpa [this] using hf x hx
    · simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · rfl
      · have hya : y ≠ x := fun h => ha (h ▸ hy)
        simp [hya] at hxy
        exact absurd (mem_image.2 ⟨y, hy, hxy.symm⟩) hbn
      · have hxa : x ≠ y := fun h => ha (h ▸ hx)
        simp [hxa] at hxy
        exact absurd (mem_image.2 ⟨x, hx, hxy⟩) hbn
      · have hxa : x ≠ a := fun h => ha (h ▸ hx)
        have hya : y ≠ a := fun h => ha (h ▸ hy)
        simp [hxa, hya] at hxy
        exact hinj hx hy hxy

theorem card_sdiff_ge (X Y : Finset ℕ) : X.card - Y.card ≤ (X \ Y).card := by
  have := card_sdiff_add_card_inter X Y
  have := card_le_card (inter_subset_right (s₁ := X) (s₂ := Y))
  omega

/-- Covering a free matching `τ` compatibly with a free matching `π`, given room. -/
theorem exists_cover {P H : Finset ℕ} {ρ τ π : Mt} (hτ : τ ⊆ freeE P H ρ) (hτm : IsMatch τ)
    (hπ : π ⊆ freeE P H ρ) (hπm : IsMatch π) (hH : π.card + 2 * τ.card ≤ (fH H ρ).card)
    (hP : π.card + 2 * τ.card ≤ (fP P ρ).card) : ∃ σ ∈ covers P H ρ τ, Compat σ π := by
  set UP := pigs τ \ pigs π
  set UH := hols τ \ hols π
  set FH := (fH H ρ \ hols π) \ hols τ
  set FP := (fP P ρ \ pigs π) \ pigs τ
  have hUP : UP.card ≤ FH.card := by
    have h1 := card_sdiff_ge (fH H ρ \ hols π) (hols τ)
    rw [show ((fH H ρ \ hols π) \ hols τ) = FH from rfl] at h1
    have h2 := card_sdiff_ge (fH H ρ) (hols π)
    have h3 : UP.card ≤ τ.card := (card_le_card sdiff_subset).trans (card_pigs hτm).le
    rw [card_hols hπm] at h2; rw [card_hols hτm] at h1
    omega
  have hUH : UH.card ≤ FP.card := by
    have h1 := card_sdiff_ge (fP P ρ \ pigs π) (pigs τ)
    rw [show ((fP P ρ \ pigs π) \ pigs τ) = FP from rfl] at h1
    have h2 := card_sdiff_ge (fP P ρ) (pigs π)
    have h3 : UH.card ≤ τ.card := (card_le_card sdiff_subset).trans (card_hols hτm).le
    rw [card_pigs hπm] at h2; rw [card_pigs hτm] at h1
    omega
  obtain ⟨f, hf, hfi⟩ := exists_inj FH UP hUP
  obtain ⟨g, hg, hgi⟩ := exists_inj FP UH hUH
  set A : Mt := UP.image fun i => (i, f i)
  set B : Mt := UH.image fun j => (g j, j)
  set πf : Mt := π.filter fun e => e.1 ∈ pigs τ ∨ e.2 ∈ hols τ
  have hfF : ∀ i ∈ UP, f i ∈ fH H ρ ∧ f i ∉ hols π ∧ f i ∉ hols τ := by
    intro i hi; have := hf i hi; simp only [FH, mem_sdiff] at this; tauto
  have hgF : ∀ j ∈ UH, g j ∈ fP P ρ ∧ g j ∉ pigs π ∧ g j ∉ pigs τ := by
    intro j hj; have := hg j hj; simp only [FP, mem_sdiff] at this; tauto
  have hUPτ : ∀ i ∈ UP, i ∈ pigs τ ∧ i ∉ pigs π := fun i hi => mem_sdiff.1 hi
  have hUHτ : ∀ j ∈ UH, j ∈ hols τ ∧ j ∉ hols π := fun j hj => mem_sdiff.1 hj
  have hA : ∀ e ∈ A, ∃ i ∈ UP, e = (i, f i) := by
    intro e he; obtain ⟨i, hi, rfl⟩ := mem_image.1 he; exact ⟨i, hi, rfl⟩
  have hB : ∀ e ∈ B, ∃ j ∈ UH, e = (g j, j) := by
    intro e he; obtain ⟨j, hj, rfl⟩ := mem_image.1 he; exact ⟨j, hj, rfl⟩
  have hbig : IsMatch (π ∪ A ∪ B) := by
    rw [isMatch_union, isMatch_union]
    refine ⟨⟨hπm, ?_, ?_⟩, ?_, ?_⟩
    · intro e he e' he' h
      obtain ⟨i, hi, rfl⟩ := hA e he; obtain ⟨i', hi', rfl⟩ := hA e' he'
      rcases h with h | h
      · simp only at h; subst h; rfl
      · simp only at h; rw [hfi hi hi' h]
    · refine cross_of_disj fun e he e' he' => ?_
      obtain ⟨i, hi, rfl⟩ := hA e' he'
      exact ⟨fun h => (hUPτ i hi).2 (mem_pigs.2 ⟨e, he, h⟩),
        fun h => (hfF i hi).2.1 (mem_hols.2 ⟨e, he, h⟩)⟩
    · intro e he e' he' h
      obtain ⟨j, hj, rfl⟩ := hB e he; obtain ⟨j', hj', rfl⟩ := hB e' he'
      rcases h with h | h
      · simp only at h; rw [hgi hj hj' h]
      · simp only at h; subst h; rfl
    · rw [cross_union_left]
      refine ⟨cross_of_disj fun e he e' he' => ?_, cross_of_disj fun e he e' he' => ?_⟩
      · obtain ⟨j, hj, rfl⟩ := hB e' he'
        exact ⟨fun h => (hgF j hj).2.1 (mem_pigs.2 ⟨e, he, h⟩),
          fun h => (hUHτ j hj).2 (mem_hols.2 ⟨e, he, h⟩)⟩
      · obtain ⟨i, hi, rfl⟩ := hA e he; obtain ⟨j, hj, rfl⟩ := hB e' he'
        refine ⟨fun h => (hgF j hj).2.2 ?_, fun h => (hfF i hi).2.2 ?_⟩
        · simp only at h; rw [← h]; exact (hUPτ i hi).1
        · simp only at h; rw [h]; exact (hUHτ j hj).1
  have hσsub : πf ∪ A ∪ B ∪ π ⊆ π ∪ A ∪ B := by
    intro e he
    simp only [mem_union] at he ⊢
    rcases he with ((he | he) | he) | he
    · exact Or.inl (Or.inl (mem_filter.1 he).1)
    · exact Or.inl (Or.inr he)
    · exact Or.inr he
    · exact Or.inl (Or.inl he)
  have hmatch : IsMatch (πf ∪ A ∪ B ∪ π) := isMatch_mono hbig hσsub
  refine ⟨πf ∪ A ∪ B, ?_, hmatch⟩
  refine mem_filter.2 ⟨mem_powerset.2 ?_, isMatch_mono hmatch subset_union_left, ?_, ?_, ?_⟩
  · intro e he
    simp only [mem_union] at he
    rcases he with (he | he) | he
    · exact hπ (mem_filter.1 he).1
    · obtain ⟨i, hi, rfl⟩ := hA e he
      have hiτ := (hUPτ i hi).1
      obtain ⟨e', he', rfl⟩ := mem_pigs.1 hiτ
      have := mem_freeE.1 (hτ he')
      exact mem_freeE.2 ⟨this.1, (mem_sdiff.1 (hfF _ hi).1).1, (mem_sdiff.1 (hfF _ hi).1).2⟩
    · obtain ⟨j, hj, rfl⟩ := hB e he
      have hjτ := (hUHτ j hj).1
      obtain ⟨e', he', rfl⟩ := mem_hols.1 hjτ
      have := mem_freeE.1 (hτ he')
      exact mem_freeE.2 ⟨⟨(mem_sdiff.1 (hgF _ hj).1).1, (mem_sdiff.1 (hgF _ hj).1).2⟩, this.2⟩
  · intro i hi
    by_cases hπi : i ∈ pigs π
    · obtain ⟨e, he, rfl⟩ := mem_pigs.1 hπi
      exact mem_pigs.2 ⟨e, mem_union.2 (Or.inl (mem_union.2 (Or.inl
        (mem_filter.2 ⟨he, Or.inl hi⟩)))), rfl⟩
    · exact mem_pigs.2 ⟨(i, f i), mem_union.2 (Or.inl (mem_union.2 (Or.inr
        (mem_image.2 ⟨i, mem_sdiff.2 ⟨hi, hπi⟩, rfl⟩)))), rfl⟩
  · intro j hj
    by_cases hπj : j ∈ hols π
    · obtain ⟨e, he, rfl⟩ := mem_hols.1 hπj
      exact mem_hols.2 ⟨e, mem_union.2 (Or.inl (mem_union.2 (Or.inl
        (mem_filter.2 ⟨he, Or.inr hj⟩)))), rfl⟩
    · exact mem_hols.2 ⟨(g j, j), mem_union.2 (Or.inr
        (mem_image.2 ⟨j, mem_sdiff.2 ⟨hj, hπj⟩, rfl⟩)), rfl⟩
  · intro e he
    simp only [mem_union] at he
    rcases he with (he | he) | he
    · exact (mem_filter.1 he).2
    · obtain ⟨i, hi, rfl⟩ := hA e he; exact Or.inl (hUPτ i hi).1
    · obtain ⟨j, hj, rfl⟩ := hB e he; exact Or.inr (hUHτ j hj).1

theorem freeE_mono {P H : Finset ℕ} {ρ ρ' : Mt} (h : ρ ⊆ ρ') : freeE P H ρ' ⊆ freeE P H ρ := by
  intro e he
  have := mem_freeE.1 he
  exact mem_freeE.2 ⟨⟨this.1.1, fun hi => this.1.2 (pigs_mono h hi)⟩,
    ⟨this.2.1, fun hj => this.2.2 (hols_mono h hj)⟩⟩

theorem freeE_sub {P H : Finset ℕ} {ρ : Mt} : freeE P H ρ ⊆ P ×ˢ H := by
  intro e he; have := mem_freeE.1 he; exact mem_product.2 ⟨this.1.1, this.2.1⟩

theorem fH_union {H : Finset ℕ} (ρ σ : Mt) : fH H (ρ ∪ σ) = fH H ρ \ hols σ := by
  ext j; simp [fH, hols_union, mem_sdiff, mem_union, not_or, and_assoc]

theorem fP_union {P : Finset ℕ} (ρ σ : Mt) : fP P (ρ ∪ σ) = fP P ρ \ pigs σ := by
  ext j; simp [fP, pigs_union, mem_sdiff, mem_union, not_or, and_assoc]

theorem hols_free {P H : Finset ℕ} {ρ σ : Mt} (h : σ ⊆ freeE P H ρ) : hols σ ⊆ fH H ρ := by
  intro j hj; obtain ⟨e, he, rfl⟩ := mem_hols.1 hj
  have := mem_freeE.1 (h he); exact mem_sdiff.2 this.2

theorem pigs_free {P H : Finset ℕ} {ρ σ : Mt} (h : σ ⊆ freeE P H ρ) : pigs σ ⊆ fP P ρ := by
  intro j hj; obtain ⟨e, he, rfl⟩ := mem_pigs.1 hj
  have := mem_freeE.1 (h he); exact mem_sdiff.2 this.1

/-- Edges of a compatible matching outside a cover are free after the cover. -/
theorem sdiff_free_union {P H : Finset ℕ} {ρ σ π : Mt} (hπ : π ⊆ freeE P H ρ)
    (hc : Compat σ π) : π \ σ ⊆ freeE P H (ρ ∪ σ) := by
  intro e he
  obtain ⟨heπ, heσ⟩ := mem_sdiff.1 he
  have hf := mem_freeE.1 (hπ heπ)
  have hx := (compat_iff.1 hc).2.2
  refine mem_freeE.2 ⟨⟨hf.1.1, ?_⟩, ⟨hf.2.1, ?_⟩⟩
  · rw [pigs_union, mem_union, not_or]
    refine ⟨hf.1.2, fun hi => ?_⟩
    obtain ⟨f, hfσ, hfe⟩ := mem_pigs.1 hi
    exact heσ (hx f hfσ e heπ (Or.inl hfe) ▸ hfσ)
  · rw [hols_union, mem_union, not_or]
    refine ⟨hf.2.2, fun hj => ?_⟩
    obtain ⟨f, hfσ, hfe⟩ := mem_hols.1 hj
    exact heσ (hx f hfσ e heπ (Or.inr hfe) ▸ hfσ)

/-- **Coverage**: a matching DNF of canonical depth at most `s` is decided, compatibly with any
free partial matching `π` leaving enough room, by a branch of at most `2 s` edges. -/
theorem cover_of_mdepth {P H : Finset ℕ} {D : MDNF} (hU : ∀ t ∈ D, InU P H t) {w : ℕ}
    (hw : ∀ t ∈ D, t.card ≤ w) (hPH : H.card ≤ P.card) :
    ∀ N s (ρ : Mt), (fH H ρ).card = N → IsMatch ρ → InU P H ρ → mdepth P H D ρ ≤ s →
    ∀ π, π ⊆ freeE P H ρ → IsMatch π → π.card + 2 * s + 2 * w ≤ (fH H ρ).card →
    ∃ σ, σ ⊆ freeE P H ρ ∧ IsMatch σ ∧ σ.card ≤ 2 * s ∧ Compat σ π ∧
      ((∃ t ∈ D, Compat ρ t ∧ t \ ρ ⊆ σ) ∨ (∀ t ∈ D, Compat ρ t → ¬ Compat σ (t \ ρ))) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro s ρ hN hρ hρU hs π hπ hπm hroom
  have hempty : Compat ∅ π := by unfold Compat; rwa [empty_union]
  cases hF : mfirst ρ D with
  | none =>
    exact ⟨∅, empty_subset _, isMatch_empty, by simp, hempty,
      Or.inr fun t ht hc => absurd hc (mfirst_none hF t ht)⟩
  | some t =>
  have htD := mfirst_mem hF
  have hct := mfirst_compat hF
  by_cases hts : t ⊆ ρ
  · exact ⟨∅, empty_subset _, isMatch_empty, by simp, hempty,
      Or.inl ⟨t, htD, hct, by rw [sdiff_eq_empty_iff_subset.2 hts]⟩⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = t \ ρ := ⟨_, rfl⟩
  have hτf : τ ⊆ freeE P H ρ := hτdef ▸ sdiff_free hct (hU t htD)
  have hτm : IsMatch τ :=
    hτdef ▸ isMatch_mono (isMatch_mono hct subset_union_right) sdiff_subset
  have hτw : τ.card ≤ w := hτdef ▸ (card_le_card sdiff_subset).trans (hw t htD)
  have hfPH : (fH H ρ).card ≤ (fP P ρ).card := by
    rw [fH_card hρ (hols_sub hρU), fP_card hρ (pigs_sub hρU)]; omega
  have hτs : τ.card ≤ s := by
    have := hs; rw [mdepth_some hF, if_neg hts, ← hτdef] at this; omega
  obtain ⟨σ1, hσ1, hc1⟩ := exists_cover hτf hτm hπ hπm (by omega) (by omega)
  have hσ1f : σ1 ⊆ freeE P H ρ := mem_powerset.1 (mem_filter.1 hσ1).1
  have hσ1m : IsMatch σ1 := (mem_filter.1 hσ1).2.1
  have hσ1c : σ1.card ≤ 2 * τ.card := covers_card hσ1 hτm
  have hdep : τ.card + mdepth P H D (ρ ∪ σ1) ≤ mdepth P H D ρ := by
    have := le_mdepth_cover hF hts (hτdef ▸ hσ1); rwa [← hτdef] at this
  have hρ1 : IsMatch (ρ ∪ σ1) := by
    have := compat_free hρ hσ1m hσ1f; unfold Compat at this; rwa [union_comm]
  have hρ1U : InU P H (ρ ∪ σ1) := union_subset hρU (hσ1f.trans freeE_sub)
  have hfH1 : (fH H (ρ ∪ σ1)).card = (fH H ρ).card - σ1.card := by
    rw [fH_union, card_sdiff_of_subset (hols_free hσ1f), card_hols hσ1m]
  have hσ1le : σ1.card ≤ (fH H ρ).card := by
    rw [← card_hols hσ1m]; exact card_le_card (hols_free hσ1f)
  have hne : σ1.Nonempty := covers_nonempty hσ1 (by
    obtain ⟨e, he⟩ := not_subset.1 hts; exact ⟨e, hτdef ▸ mem_sdiff.2 he⟩)
  have hπ' : π \ σ1 ⊆ freeE P H (ρ ∪ σ1) := sdiff_free_union hπ (compat_symm hc1 |> compat_symm)
  have hπ'm : IsMatch (π \ σ1) := isMatch_mono hπm sdiff_subset
  have hπ'c : (π \ σ1).card ≤ π.card := card_le_card sdiff_subset
  obtain ⟨σ2, hσ2f, hσ2m, hσ2c, hc2, hD2⟩ := ih _ (by rw [← hN, hfH1]; have := hne.card_pos; omega)
    (s - τ.card) (ρ ∪ σ1) rfl hρ1 hρ1U (by omega) (π \ σ1) hπ' hπ'm (by rw [hfH1]; omega)
  have hσ2ρ : σ2 ⊆ freeE P H ρ := hσ2f.trans (freeE_mono subset_union_left)
  have h12 : Compat σ1 σ2 := by
    refine compat_iff.2 ⟨hσ1m, hσ2m, cross_symm (cross_of_disj fun e he f hf => ?_)⟩
    exact disj_free hσ2f e he f (mem_union.2 (Or.inr hf))
  have h2π : Compat σ2 π := by
    refine isMatch_mono (isMatch_union3 hc2 (compat_symm h12) ?_) ?_
    · exact compat_mono (compat_symm hc1) sdiff_subset subset_rfl
    · intro e he
      simp only [mem_union, mem_sdiff] at he ⊢
      tauto
  refine ⟨σ1 ∪ σ2, union_subset hσ1f hσ2ρ, isMatch_union.2 ⟨hσ1m, hσ2m, (compat_iff.1 h12).2.2⟩,
    (card_union_le _ _).trans (by omega), isMatch_union3 h12 hc1 h2π, ?_⟩
  rcases hD2 with ⟨t', ht', hct', hsub⟩ | hall
  · refine Or.inl ⟨t', ht', compat_mono hct' subset_union_left subset_rfl, ?_⟩
    intro e he
    obtain ⟨het, heρ⟩ := mem_sdiff.1 he
    by_cases he1 : e ∈ σ1
    · exact mem_union.2 (Or.inl he1)
    · exact mem_union.2 (Or.inr (hsub (mem_sdiff.2 ⟨het, by simp [heρ, he1]⟩)))
  · refine Or.inr fun t' ht' hct' hcomp => hall t' ht' ?_ ?_
    · -- `ρ ∪ σ1` is compatible with `t'`
      have hc3 : Compat σ1 t' := by
        have hA : Compat σ1 (t' \ ρ) := compat_mono hcomp subset_union_left subset_rfl
        have hB : Compat σ1 (t' ∩ ρ) := by
          refine compat_mono (compat_free hρ hσ1m hσ1f) subset_rfl inter_subset_right
        refine isMatch_mono (isMatch_union3 hA hB (isMatch_mono hct' ?_)) ?_
        · intro e he
          simp only [mem_union, mem_sdiff, mem_inter] at he ⊢
          tauto
        · intro e he
          simp only [mem_union, mem_sdiff, mem_inter] at he ⊢
          tauto
      have := isMatch_union3 (compat_free hρ hσ1m hσ1f |> compat_symm) hct' hc3
      unfold Compat; exact this
    · exact compat_mono hcomp subset_union_right (sdiff_subset_sdiff subset_rfl subset_union_left)

end

end SATurday.ProofComplexity
