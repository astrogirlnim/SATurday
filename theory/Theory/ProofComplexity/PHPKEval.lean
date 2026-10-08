import Theory.ProofComplexity.KEval
import Theory.ProofComplexity.PHP

/-!
# Pigeonhole clauses under k-evaluations (Ladder Rung R4, 1B.4)

For the R1 pigeonhole CNF `phpCNF n` (variable `pvar n i j = i n + j`), the variable `v`
corresponds to the edge `phpVx n v = (v / n, v % n)` between pigeons `range (n + 1)` and holes
`range n`. Under a `k`-evaluation over a matching restriction with room, every clause of
`phpCNF n` is hit by a true branch of one of its literals (`php_clauseHit`).

LOG: R4 PHPKEval module (pigeonhole clauses under k-evaluations)
-/

namespace SATurday.ProofComplexity

open Finset

noncomputable section

open Classical

/-- The edge of a PHP variable. -/
def phpVx (n : ℕ) (v : ℕ) : ℕ × ℕ := (v / n, v % n)

theorem phpVx_pvar {n : ℕ} (i : Fin (n + 1)) (j : Fin n) : phpVx n (pvar n i j) = (i.val, j.val) := by
  have hn : 0 < n := Fin.pos j
  unfold phpVx pvar
  refine Prod.ext ?_ ?_
  · simp only
    rw [show i.val * n + j.val = j.val + n * i.val by ring, Nat.add_mul_div_left _ _ hn,
      Nat.div_eq_of_lt j.2, zero_add]
  · simp only
    rw [show i.val * n + j.val = j.val + n * i.val by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt j.2]

section Hit

variable {P H : Finset ℕ} {vx : ℕ → ℕ × ℕ} {ρ : Mt} {k : ℕ} {E : Eval}

/-- Two distinct edges sharing an endpoint. -/
def Conf (e f : ℕ × ℕ) : Prop := f ≠ e ∧ (f.1 = e.1 ∨ f.2 = e.2)

theorem good_var {v : ℕ} (hG : Good P H vx ρ k E (.var v)) (hu : vx v ∈ P ×ˢ H) :
    (∀ α ∈ (E (.var v)).1, vx v ∈ α ∪ ρ) ∧
      (∀ α ∈ (E (.var v)).2, ¬ IsMatch (insert (vx v) (α ∪ ρ))) := by
  have := hG.loc; simp only [Local] at this; exact this hu

/-- A free matching containing the edge (or with the edge in `ρ`) meets a true branch. -/
theorem hit_true {v : ℕ} (hG : Good P H vx ρ k E (.var v)) (hu : vx v ∈ P ×ˢ H)
    (hρ : IsMatch ρ) {π : Mt} (hπ : π ⊆ freeE P H ρ) (hπm : IsMatch π)
    (hroom : π.card + 3 * k ≤ (fH H ρ).card) (he : vx v ∈ π ∪ ρ) :
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
theorem hit_false {v : ℕ} (hG : Good P H vx ρ k E (.var v)) (hu : vx v ∈ P ×ˢ H)
    (hρ : IsMatch ρ) {π : Mt} (hπ : π ⊆ freeE P H ρ) (hπm : IsMatch π)
    (hroom : π.card + 3 * k ≤ (fH H ρ).card) {f : ℕ × ℕ} (hf : f ∈ π ∪ ρ)
    (hcf : Conf (vx v) f) : ∃ γ ∈ (E (.var v)).2, Compat γ π := by
  obtain ⟨γ, hγ, hc⟩ := hG.cov π hπ hπm hroom
  rcases mem_union.1 hγ with hγ | hγ
  · exfalso
    obtain ⟨hγf, hγm, -⟩ := hG.mem γ (mem_union.2 (Or.inl hγ))
    have hbig := isMatch_union3 hc (compat_free hρ hγm hγf) (compat_free hρ hπm hπ)
    have he := (good_var hG hu).1 γ hγ
    have h1 : vx v ∈ γ ∪ π ∪ ρ := by
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

theorem mem_phpCNF {n : ℕ} {C : Clause} (hC : C ∈ phpCNF n) :
    (∃ i : Fin (n + 1), C = pigeonClause n i) ∨
    ∃ (i i' : Fin (n + 1)) (j : Fin n), i < i' ∧
      C = ({⟨pvar n i j, false⟩, ⟨pvar n i' j, false⟩} : Clause) := by
  rcases mem_union.1 hC with hC | hC
  · obtain ⟨i, -, rfl⟩ := mem_image.1 hC; exact Or.inl ⟨i, rfl⟩
  · simp only [holeClauses, mem_biUnion, mem_univ, true_and, mem_image, mem_filter] at hC
    obtain ⟨j, i, i', hlt, rfl⟩ := hC
    exact Or.inr ⟨i, i', j, hlt, rfl⟩

/-- Every clause of `phpCNF n` is hit by a true branch of one of its literals. -/
theorem php_clauseHit {n : ℕ} (hP : P = range (n + 1)) (hH : H = range n) (hvx : vx = phpVx n)
    (hρ : IsMatch ρ) (hρU : InU P H ρ) (hk : 1 ≤ k) (hroom : 5 * k ≤ (fH H ρ).card) :
    ClauseHit P H vx ρ k E (phpCNF n) := by
  subst hvx
  intro C hC hGC β hβ hβm hβk
  have hroom1 : β.card + 3 * k ≤ (fH H ρ).card := by omega
  have hβh : (hols β).card = β.card := card_hols hβm
  have hlit : ∀ l ∈ C, Good P H (phpVx n) ρ k E (.var l.var) := by
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
  have hu : ∀ (i : Fin (n + 1)) (j : Fin n), phpVx n (pvar n i j) ∈ P ×ˢ H := by
    intro i j; rw [phpVx_pvar, hP, hH]; exact mem_product.2 ⟨mem_range.2 i.2, mem_range.2 j.2⟩
  rcases mem_phpCNF hC with ⟨i, rfl⟩ | ⟨i, i', j, hii', rfl⟩
  · -- pigeon clause
    have hmemC : ∀ j : Fin n, (⟨pvar n i j, true⟩ : Literal) ∈ pigeonClause n i :=
      fun j => mem_image.2 ⟨j, mem_univ _, rfl⟩
    have hpos : ∀ j : Fin n, ∀ γ ∈ (E (.var (pvar n i j))).1, Compat γ β →
        ∃ l ∈ pigeonClause n i, ∃ γ ∈ (E (litFm l)).1, Compat γ β :=
      fun j γ hγ hc => ⟨_, hmemC j, γ, by simpa [litFm] using hγ, hc⟩
    have hgood : ∀ j : Fin n, Good P H (phpVx n) ρ k E (.var (pvar n i j)) :=
      fun j => hlit _ (hmemC j)
    by_cases hiρ : i.val ∈ pigs ρ
    · obtain ⟨e, he, hei⟩ := mem_pigs.1 hiρ
      have hej : e.2 < n := by
        have := mem_product.1 (hρU he); rw [hH] at this; exact mem_range.1 this.2
      obtain ⟨γ, hγ, hc⟩ := hit_true (hgood ⟨e.2, hej⟩) (hu _ _) hρ hβ hβm hroom1
        (by rw [phpVx_pvar]; exact mem_union.2 (Or.inr (by rw [← hei]; exact he)))
      exact hpos _ γ hγ hc
    · by_cases hiβ : i.val ∈ pigs β
      · obtain ⟨e, he, hei⟩ := mem_pigs.1 hiβ
        have hej : e.2 < n := by
          have := (mem_freeE.1 (hβ he)).2.1; rw [hH] at this; exact mem_range.1 this
        obtain ⟨γ, hγ, hc⟩ := hit_true (hgood ⟨e.2, hej⟩) (hu _ _) hρ hβ hβm hroom1
          (by rw [phpVx_pvar]; exact mem_union.2 (Or.inl (by rw [← hei]; exact he)))
        exact hpos _ γ hγ hc
      · obtain ⟨j, hjf, hjβ, -⟩ := exists_free_hole (H := H) (ρ := ρ) (β := β) ∅
          (by rw [hβh]; simp; omega)
        have hjn : j < n := by have := (mem_sdiff.1 hjf).1; rw [hH] at this; exact mem_range.1 this
        obtain ⟨hπf, hπm⟩ := insert_free hβ hβm (by rw [hP]; exact mem_range.2 i.2) hiρ hiβ hjf hjβ
        obtain ⟨γ, hγ, hc⟩ := hit_true (hgood ⟨j, hjn⟩) (hu _ _) hρ hπf hπm
          (by have := card_insert_le (i.val, j) β; omega)
          (by rw [phpVx_pvar]; exact mem_union.2 (Or.inl (mem_insert_self _ _)))
        exact hpos _ γ hγ (compat_mono hc subset_rfl (subset_insert _ _))
  · -- hole clause
    have hl1 : (⟨pvar n i j, false⟩ : Literal) ∈
        ({⟨pvar n i j, false⟩, ⟨pvar n i' j, false⟩} : Clause) := by simp
    have hl2 : (⟨pvar n i' j, false⟩ : Literal) ∈
        ({⟨pvar n i j, false⟩, ⟨pvar n i' j, false⟩} : Clause) := by simp
    have hii : i.val < i'.val := hii'
    have hfin1 : ∀ π, β ⊆ π → ∀ γ ∈ (E (.var (pvar n i j))).2, Compat γ π →
        ∃ l ∈ ({⟨pvar n i j, false⟩, ⟨pvar n i' j, false⟩} : Clause),
          ∃ γ ∈ (E (litFm l)).1, Compat γ β := by
      intro π hβπ γ hγ hc
      exact ⟨_, hl1, γ, by rw [hneg _ hl1 rfl]; exact hγ, compat_mono hc subset_rfl hβπ⟩
    have hfin2 : ∀ γ ∈ (E (.var (pvar n i' j))).2, Compat γ β →
        ∃ l ∈ ({⟨pvar n i j, false⟩, ⟨pvar n i' j, false⟩} : Clause),
          ∃ γ ∈ (E (litFm l)).1, Compat γ β := by
      intro γ hγ hc
      exact ⟨_, hl2, γ, by rw [hneg _ hl2 rfl]; exact hγ, hc⟩
    by_cases hc1 : ∃ f ∈ β ∪ ρ, Conf (i.val, j.val) f
    · obtain ⟨f, hf, hcf⟩ := hc1
      obtain ⟨γ, hγ, hc⟩ := hit_false (hlit _ hl1) (hu _ _) hρ hβ hβm hroom1 hf
        (by rw [phpVx_pvar]; exact hcf)
      exact hfin1 β subset_rfl γ hγ hc
    by_cases hc2 : ∃ f ∈ β ∪ ρ, Conf (i'.val, j.val) f
    · obtain ⟨f, hf, hcf⟩ := hc2
      obtain ⟨γ, hγ, hc⟩ := hit_false (hlit _ hl2) (hu _ _) hρ hβ hβm hroom1 hf
        (by rw [phpVx_pvar]; exact hcf)
      exact hfin2 γ hγ hc
    push Not at hc1 hc2
    have hnot : (i.val, j.val) ∉ β ∪ ρ := by
      intro h
      exact hc2 _ h ⟨fun h' => by simp at h'; omega, Or.inr rfl⟩
    have hiρ : i.val ∉ pigs ρ := by
      intro h; obtain ⟨f, hf, hfe⟩ := mem_pigs.1 h
      have hfne : f ≠ (i.val, j.val) := fun h' => hnot (mem_union.2 (Or.inr (h' ▸ hf)))
      exact hc1 f (mem_union.2 (Or.inr hf)) ⟨hfne, Or.inl hfe⟩
    have hiβ : i.val ∉ pigs β := by
      intro h; obtain ⟨f, hf, hfe⟩ := mem_pigs.1 h
      have hfne : f ≠ (i.val, j.val) := fun h' => hnot (mem_union.2 (Or.inl (h' ▸ hf)))
      exact hc1 f (mem_union.2 (Or.inl hf)) ⟨hfne, Or.inl hfe⟩
    obtain ⟨j', hjf, hjβ, hjj⟩ := exists_free_hole (H := H) (ρ := ρ) (β := β) {j.val}
      (by rw [hβh]; simp; omega)
    simp only [mem_singleton] at hjj
    obtain ⟨hπf, hπm⟩ := insert_free hβ hβm (by rw [hP]; exact mem_range.2 i.2) hiρ hiβ
      hjf hjβ
    obtain ⟨γ, hγ, hc⟩ := hit_false (hlit _ hl1) (hu _ _) hρ hπf hπm
      (by have := card_insert_le (i.val, j') β; omega)
      (f := (i.val, j')) (mem_union.2 (Or.inl (mem_insert_self _ _)))
      (by rw [phpVx_pvar]; exact ⟨by simp [hjj], Or.inl rfl⟩)
    exact hfin1 _ (subset_insert _ _) γ hγ hc

end Hit

end

end SATurday.ProofComplexity
