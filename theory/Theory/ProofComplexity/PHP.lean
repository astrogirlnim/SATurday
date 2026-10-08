import Theory.ProofComplexity.KEval

/-!
# The pigeonhole principle and its clauses under k-evaluations (Ladder Rung R4, 1B.4)

`PHP n`: pigeons `0..n`, holes `0..n-1`, variable `x_{ij} = Nat.pair i j`; every pigeon goes to
some hole, no two pigeons share a hole. It is unsatisfiable (`php_unsat`). Under a
`k`-evaluation over a matching restriction with room, every PHP clause is hit by a true branch
of one of its literals (`php_clauseHit`).

LOG: R4 PHP module (pigeonhole clauses)
-/

namespace SATurday.ProofComplexity

open Finset

noncomputable section

open Classical

/-- Pigeon `i` goes to some hole. -/
def pigeonClause (n i : ℕ) : Clause := (range n).image fun j => ⟨Nat.pair i j, true⟩

/-- Pigeons `i` and `i'` do not share hole `j`. -/
def holeClause (i i' j : ℕ) : Clause := {⟨Nat.pair i j, false⟩, ⟨Nat.pair i' j, false⟩}

/-- The pigeonhole principle with `n + 1` pigeons and `n` holes. -/
def PHP (n : ℕ) : CNF :=
  (range (n + 1)).image (pigeonClause n) ∪
    (((range (n + 1) ×ˢ range (n + 1)) ×ˢ range n).filter fun x => x.1.1 < x.1.2).image
      fun x => holeClause x.1.1 x.1.2 x.2

theorem mem_PHP {n : ℕ} {C : Clause} : C ∈ PHP n ↔ (∃ i < n + 1, C = pigeonClause n i) ∨
    ∃ i i' j, i < i' ∧ i' < n + 1 ∧ j < n ∧ C = holeClause i i' j := by
  simp only [PHP, mem_union, mem_image, mem_range, mem_filter, mem_product]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨⟨⟨i, i'⟩, j⟩, ⟨⟨⟨_, hi'⟩, hj⟩, hlt⟩, rfl⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨i, i', j, hlt, hi', hj, rfl⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨i, i', j, hlt, hi', hj, rfl⟩)
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨((i, i'), j), ⟨⟨⟨by simp only; omega, hi'⟩, hj⟩, hlt⟩, rfl⟩

/-- PHP is unsatisfiable. -/
theorem php_unsat (n : ℕ) : ¬ Satisfiable (PHP n) := by
  rintro ⟨a, ha⟩
  have hp : ∀ i : Fin (n + 1), ∃ j : Fin n, a (Nat.pair i j) = true := by
    intro i
    obtain ⟨l, hl, hs⟩ := ha _ (mem_PHP.2 (Or.inl ⟨i, i.2, rfl⟩))
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hl
    exact ⟨⟨j, mem_range.1 hj⟩, hs⟩
  choose f hf using hp
  have hinj : Function.Injective f := by
    intro i i' h
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · obtain ⟨l, hl, hs⟩ := ha _ (mem_PHP.2 (Or.inr ⟨i, i', f i, hlt, i'.2, (f i).2, rfl⟩))
      simp only [holeClause, mem_insert, mem_singleton] at hl
      rcases hl with rfl | rfl
      · have := hf i; simp [litSat] at hs; rw [hs] at this; cases this
      · have := hf i'; rw [← h] at this; simp [litSat] at hs; rw [hs] at this; cases this
    · obtain ⟨l, hl, hs⟩ := ha _ (mem_PHP.2 (Or.inr ⟨i', i, f i', hlt, i.2, (f i').2, rfl⟩))
      simp only [holeClause, mem_insert, mem_singleton] at hl
      rcases hl with rfl | rfl
      · have := hf i'; simp [litSat] at hs; rw [hs] at this; cases this
      · have := hf i; rw [h] at this; simp [litSat] at hs; rw [hs] at this; cases this
  have := Fintype.card_le_of_injective f hinj
  simp at this

/-! ## Variables under a k-evaluation -/

section Hit

variable {P H : Finset ℕ} {ρ : Mt} {k : ℕ} {E : Eval}

/-- Two distinct edges sharing an endpoint. -/
def Conf (e f : ℕ × ℕ) : Prop := f ≠ e ∧ (f.1 = e.1 ∨ f.2 = e.2)

theorem good_var {v : ℕ} (hG : Good P H ρ k E (.var v)) (hu : Nat.unpair v ∈ P ×ˢ H) :
    (∀ α ∈ (E (.var v)).1, Nat.unpair v ∈ α ∪ ρ) ∧
      (∀ α ∈ (E (.var v)).2, ¬ IsMatch (insert (Nat.unpair v) (α ∪ ρ))) := by
  have := hG.loc; simp only [Local] at this; exact this hu

/-- A free matching containing the edge (or with the edge in `ρ`) meets a true branch. -/
theorem hit_true {v : ℕ} (hG : Good P H ρ k E (.var v)) (hu : Nat.unpair v ∈ P ×ˢ H)
    (hρ : IsMatch ρ) {π : Mt} (hπ : π ⊆ freeE P H ρ) (hπm : IsMatch π)
    (hroom : π.card + 3 * k ≤ (fH H ρ).card) (he : Nat.unpair v ∈ π ∪ ρ) :
    ∃ γ ∈ (E (.var v)).1, Compat γ π := by
  obtain ⟨γ, hγ, hc⟩ := hG.cov π hπ hπm hroom
  rcases mem_union.1 hγ with hγ | hγ
  · exact ⟨γ, hγ, hc⟩
  · exfalso
    obtain ⟨hγf, hγm, -⟩ := hG.mem γ (mem_union.2 (Or.inr hγ))
    have hbig := isMatch_union3 hc (compat_free hρ hγm hγf) (compat_free hρ hπm hπ)
    refine (good_var hG hu).2 γ hγ (isMatch_mono hbig ?_)
    intro x hx
    simp only [mem_insert, mem_union] at hx he ⊢
    rcases hx with rfl | hx | hx
    · tauto
    · tauto
    · tauto

/-- A free matching conflicting with the edge (possibly through `ρ`) meets a false branch. -/
theorem hit_false {v : ℕ} (hG : Good P H ρ k E (.var v)) (hu : Nat.unpair v ∈ P ×ˢ H)
    (hρ : IsMatch ρ) {π : Mt} (hπ : π ⊆ freeE P H ρ) (hπm : IsMatch π)
    (hroom : π.card + 3 * k ≤ (fH H ρ).card) {f : ℕ × ℕ} (hf : f ∈ π ∪ ρ)
    (hcf : Conf (Nat.unpair v) f) : ∃ γ ∈ (E (.var v)).2, Compat γ π := by
  obtain ⟨γ, hγ, hc⟩ := hG.cov π hπ hπm hroom
  rcases mem_union.1 hγ with hγ | hγ
  · exfalso
    obtain ⟨hγf, hγm, -⟩ := hG.mem γ (mem_union.2 (Or.inl hγ))
    have hbig := isMatch_union3 hc (compat_free hρ hγm hγf) (compat_free hρ hπm hπ)
    have he := (good_var hG hu).1 γ hγ
    have h1 : Nat.unpair v ∈ γ ∪ π ∪ ρ := by
      simp only [mem_union] at he ⊢; tauto
    have h2 : f ∈ γ ∪ π ∪ ρ := by
      simp only [mem_union] at hf ⊢; tauto
    exact hcf.1 (hbig f h2 _ h1 hcf.2)
  · exact ⟨γ, hγ, hc⟩

theorem exists_free_hole {H : Finset ℕ} {ρ β : Mt} (avoid : Finset ℕ)
    (h : (hols β).card + avoid.card < (fH H ρ).card) :
    ∃ j ∈ fH H ρ, j ∉ hols β ∧ j ∉ avoid := by
  have : ((hols β) ∪ avoid).card < (fH H ρ).card := (card_union_le _ _).trans_lt h
  obtain ⟨j, hj, hjn⟩ := exists_mem_notMem_of_card_lt_card this
  simp only [mem_union, not_or] at hjn
  exact ⟨j, hj, hjn⟩

theorem insert_free {P H : Finset ℕ} {ρ β : Mt} {i j : ℕ} (hβ : β ⊆ freeE P H ρ)
    (hβm : IsMatch β) (hi : i ∈ P) (hiρ : i ∉ pigs ρ) (hiβ : i ∉ pigs β) (hj : j ∈ fH H ρ)
    (hjβ : j ∉ hols β) : insert (i, j) β ⊆ freeE P H ρ ∧ IsMatch (insert (i, j) β) := by
  refine ⟨insert_subset (mem_freeE.2 ⟨⟨hi, hiρ⟩, mem_sdiff.1 hj⟩) hβ, ?_⟩
  rw [insert_eq, isMatch_union]
  refine ⟨fun e he f hf _ => by simp at he hf; rw [he, hf], hβm, ?_⟩
  intro e he f hf h
  simp only [mem_singleton] at he; subst he
  rcases h with h | h
  · exact absurd (mem_pigs.2 ⟨f, hf, h.symm⟩) hiβ
  · exact absurd (mem_hols.2 ⟨f, hf, h.symm⟩) hjβ

/-- Every PHP clause is hit by a true branch of one of its literals. -/
theorem php_clauseHit {n : ℕ} (hP : P = range (n + 1)) (hH : H = range n) (hρ : IsMatch ρ)
    (hρU : InU P H ρ) (hk : 1 ≤ k) (hroom : 5 * k ≤ (fH H ρ).card) :
    ClauseHit P H ρ k E (PHP n) := by
  intro C hC hGC β hβ hβm hβk
  have hroom1 : β.card + 3 * k ≤ (fH H ρ).card := by omega
  have hβh : (hols β).card = β.card := card_hols hβm
  have hlit : ∀ l ∈ C, Good P H ρ k E (.var l.var) := by
    intro l hl
    have hm : litFm l ∈ subs (clauseFm C) :=
      sub_or (self_mem_subs _) (List.mem_map.2 ⟨l, mem_toList.2 hl, rfl⟩)
    by_cases hp : l.pos
    · exact hGC _ (by simpa [litFm, hp] using hm)
    · exact hGC _ (sub_neg (by simpa [litFm, hp] using hm))
  have hneg : ∀ l ∈ C, l.pos = false → (E (litFm l)).1 = (E (.var l.var)).2 := by
    intro l hl hp
    have hm : litFm l ∈ subs (clauseFm C) :=
      sub_or (self_mem_subs _) (List.mem_map.2 ⟨l, mem_toList.2 hl, rfl⟩)
    simp only [litFm, hp] at hm ⊢
    exact (good_neg (hGC _ hm)).1
  rcases mem_PHP.1 hC with ⟨i, hi, rfl⟩ | ⟨i, i', j, hii', hi', hj, rfl⟩
  · -- pigeon clause
    have hpos : ∀ j < n, ∀ γ ∈ (E (.var (Nat.pair i j))).1, Compat γ β →
        ∃ l ∈ pigeonClause n i, ∃ γ ∈ (E (litFm l)).1, Compat γ β := by
      intro j hj γ hγ hc
      exact ⟨⟨Nat.pair i j, true⟩, mem_image.2 ⟨j, mem_range.2 hj, rfl⟩, γ, by simpa [litFm], hc⟩
    have hgood : ∀ j < n, Good P H ρ k E (.var (Nat.pair i j)) := fun j hj =>
      hlit ⟨Nat.pair i j, true⟩ (mem_image.2 ⟨j, mem_range.2 hj, rfl⟩)
    have hu : ∀ j < n, Nat.unpair (Nat.pair i j) ∈ P ×ˢ H := fun j hj => by
      rw [Nat.unpair_pair, hP, hH]; exact mem_product.2 ⟨mem_range.2 hi, mem_range.2 hj⟩
    by_cases hiρ : i ∈ pigs ρ
    · obtain ⟨e, he, rfl⟩ := mem_pigs.1 hiρ
      have hej : e.2 < n := by
        have := mem_product.1 (hρU he); rw [hH] at this; exact mem_range.1 this.2
      obtain ⟨γ, hγ, hc⟩ := hit_true (hgood _ hej) (hu _ hej) hρ hβ hβm hroom1
        (by rw [Nat.unpair_pair]; exact mem_union.2 (Or.inr he))
      exact hpos _ hej γ hγ hc
    · by_cases hiβ : i ∈ pigs β
      · obtain ⟨e, he, rfl⟩ := mem_pigs.1 hiβ
        have hej : e.2 < n := by
          have := (mem_freeE.1 (hβ he)).2.1; rw [hH] at this; exact mem_range.1 this
        obtain ⟨γ, hγ, hc⟩ := hit_true (hgood _ hej) (hu _ hej) hρ hβ hβm hroom1
          (by rw [Nat.unpair_pair]; exact mem_union.2 (Or.inl he))
        exact hpos _ hej γ hγ hc
      · obtain ⟨j, hjf, hjβ, -⟩ := exists_free_hole (H := H) (ρ := ρ) (β := β) ∅
          (by rw [hβh]; simp; omega)
        have hjn : j < n := by have := (mem_sdiff.1 hjf).1; rw [hH] at this; exact mem_range.1 this
        obtain ⟨hπf, hπm⟩ := insert_free hβ hβm (by rw [hP]; exact mem_range.2 hi) hiρ hiβ hjf hjβ
        obtain ⟨γ, hγ, hc⟩ := hit_true (hgood _ hjn) (hu _ hjn) hρ hπf hπm
          (by have := card_insert_le (i, j) β; omega)
          (by rw [Nat.unpair_pair]; exact mem_union.2 (Or.inl (mem_insert_self _ _)))
        exact hpos _ hjn γ hγ (compat_mono hc subset_rfl (subset_insert _ _))
  · -- hole clause
    have hl1 : (⟨Nat.pair i j, false⟩ : Literal) ∈ holeClause i i' j := by simp [holeClause]
    have hl2 : (⟨Nat.pair i' j, false⟩ : Literal) ∈ holeClause i i' j := by simp [holeClause]
    have hu1 : Nat.unpair (Nat.pair i j) ∈ P ×ˢ H := by
      rw [Nat.unpair_pair, hP, hH]; exact mem_product.2 ⟨mem_range.2 (by omega), mem_range.2 hj⟩
    have hu2 : Nat.unpair (Nat.pair i' j) ∈ P ×ˢ H := by
      rw [Nat.unpair_pair, hP, hH]; exact mem_product.2 ⟨mem_range.2 hi', mem_range.2 hj⟩
    have hfin1 : ∀ π, β ⊆ π → ∀ γ ∈ (E (.var (Nat.pair i j))).2, Compat γ π →
        ∃ l ∈ holeClause i i' j, ∃ γ ∈ (E (litFm l)).1, Compat γ β := by
      intro π hβπ γ hγ hc
      exact ⟨_, hl1, γ, by rw [hneg _ hl1 rfl]; exact hγ, compat_mono hc subset_rfl hβπ⟩
    have hfin2 : ∀ γ ∈ (E (.var (Nat.pair i' j))).2, Compat γ β →
        ∃ l ∈ holeClause i i' j, ∃ γ ∈ (E (litFm l)).1, Compat γ β := by
      intro γ hγ hc
      exact ⟨_, hl2, γ, by rw [hneg _ hl2 rfl]; exact hγ, hc⟩
    by_cases hc1 : ∃ f ∈ β ∪ ρ, Conf (i, j) f
    · obtain ⟨f, hf, hcf⟩ := hc1
      obtain ⟨γ, hγ, hc⟩ := hit_false (hlit _ hl1) hu1 hρ hβ hβm hroom1 hf
        (by rw [Nat.unpair_pair]; exact hcf)
      exact hfin1 β subset_rfl γ hγ hc
    by_cases hc2 : ∃ f ∈ β ∪ ρ, Conf (i', j) f
    · obtain ⟨f, hf, hcf⟩ := hc2
      obtain ⟨γ, hγ, hc⟩ := hit_false (hlit _ hl2) hu2 hρ hβ hβm hroom1 hf
        (by rw [Nat.unpair_pair]; exact hcf)
      exact hfin2 γ hγ hc
    push Not at hc1 hc2
    -- `(i, j)` is not present: otherwise `(i', j)` would conflict with it
    have hnot : (i, j) ∉ β ∪ ρ := by
      intro h
      exact hc2 _ h ⟨fun h' => by simp at h'; omega, Or.inr rfl⟩
    have hiρ : i ∉ pigs ρ := by
      intro h; obtain ⟨f, hf, hfe⟩ := mem_pigs.1 h
      have hfne : f ≠ (i, j) := fun h' => hnot (mem_union.2 (Or.inr (h' ▸ hf)))
      exact hc1 f (mem_union.2 (Or.inr hf)) ⟨hfne, Or.inl hfe⟩
    have hiβ : i ∉ pigs β := by
      intro h; obtain ⟨f, hf, hfe⟩ := mem_pigs.1 h
      have hfne : f ≠ (i, j) := fun h' => hnot (mem_union.2 (Or.inl (h' ▸ hf)))
      exact hc1 f (mem_union.2 (Or.inl hf)) ⟨hfne, Or.inl hfe⟩
    obtain ⟨j', hjf, hjβ, hjj⟩ := exists_free_hole (H := H) (ρ := ρ) (β := β) {j}
      (by rw [hβh]; simp; omega)
    simp only [mem_singleton] at hjj
    obtain ⟨hπf, hπm⟩ := insert_free hβ hβm (by rw [hP]; exact mem_range.2 (by omega)) hiρ hiβ
      hjf hjβ
    obtain ⟨γ, hγ, hc⟩ := hit_false (hlit _ hl1) hu1 hρ hπf hπm
      (by have := card_insert_le (i, j') β; omega)
      (f := (i, j')) (mem_union.2 (Or.inl (mem_insert_self _ _)))
      (by rw [Nat.unpair_pair]; exact ⟨by simp [hjj], Or.inl rfl⟩)
    exact hfin1 _ (subset_insert _ _) γ hγ hc

end Hit

end

end SATurday.ProofComplexity
