import Theory.ProofComplexity.QPart

/-!
# The design mass argument against Count_p axiom instances (Ladder Rung R4, 1D.2)

Let `s` be a design over `ZMod p` on the universe `W`, `α` a partial q-partition of mass `1`, and
for each `p`-subset `g` of `[M]` (with `p ∤ M`) let `T g` be a q-decision tree. Suppose, below
`α`, the trees `A i` (one per point `i < M`) only have branches extending a `1`-branch of some
`T g` with `i ∈ g`, and the trees `C g g'` (one per pair of distinct overlapping `g, g'`) only
have branches extending a `0`-branch of `T g` or `T g'`. Then the `1`-masses `π g` of the trees
satisfy `Σ_{g ∋ i} π g = 1` for every `i`, so `M = Σ_i Σ_{g ∋ i} π g = p Σ_g π g = 0` in
`ZMod p`, a contradiction (`count_mass_false`), as soon as the degree exceeds `|α| + 3 h`.

LOG: R4 CountMass module (design mass against Count_p instances)
-/

namespace SATurday.ProofComplexity

namespace QP

open Finset

noncomputable section

open Classical

variable {q : ℕ} {α : Type}

open QT

/-! ## Tree facts -/

theorem pp_mono {E F : Finset (Finset ℕ)} (h : PP q E) (hFE : F ⊆ E) : PP q F :=
  ⟨fun e he => h.1 e (hFE he), fun e he f hf hef => h.2 e (hFE he) f (hFE hf) hef⟩

/-- Compatible branches of a tree coincide. -/
theorem branch_eq : ∀ (T : QT α) (W : Finset ℕ) (B B' : Finset (Finset ℕ) × α),
    B ∈ br q T W → B' ∈ br q T W → Compat q B.1 B'.1 → B = B'
  | leaf a, W, B, B', h, h', _ => by
    simp [br] at h h'; rw [h, h']
  | node v ch, W, B, B', h, h', hc => by
    obtain ⟨e, he, B1, hB1, rfl⟩ := mem_br_node.1 h
    obtain ⟨e', he', B1', hB1', rfl⟩ := mem_br_node.1 h'
    have hee : e = e' := pp_eq_of_mem hc (mem_union.2 (Or.inl (mem_insert_self _ _)))
      (mem_union.2 (Or.inr (mem_insert_self _ _))) (mem_blocks.1 he).2.2 (mem_blocks.1 he').2.2
    subst hee
    have := branch_eq (ch e) (W \ e) B1 B1' hB1 hB1'
      (pp_mono hc (union_subset_union (subset_insert _ _) (subset_insert _ _)))
    rw [this]

/-! ## Commuting weighted sums -/

section Comm

variable {R : Type} [CommRing R] {β : Type}

theorem wsum_comm : ∀ (T1 : QT α) (W1 : Finset ℕ) (T2 : QT β) (W2 : Finset ℕ)
    (f : Finset (Finset ℕ) × α → Finset (Finset ℕ) × β → R),
    wsum q T1 W1 (fun x => wsum q T2 W2 (fun y => f x y)) =
      wsum q T2 W2 (fun y => wsum q T1 W1 (fun x => f x y))
  | leaf a, W1, T2, W2, f => rfl
  | node v ch, W1, T2, W2, f => by
    simp only [wsum]
    rw [wsum_sum]
    refine sum_congr rfl fun e _ => ?_
    exact wsum_comm (ch e) (W1 \ e) T2 W2 _

end Comm

/-! ## The mass argument -/

section Mass3

variable {p : ℕ}

/-- `(α ∪ β) ∪ B` is a partial partition iff the two orders of compatibility checks agree. -/
theorem compat_swap {A X Y : Finset (Finset ℕ)} :
    (Compat q A X ∧ Compat q (A ∪ X) Y) ↔ (Compat q A Y ∧ Compat q (A ∪ Y) X) := by
  unfold Compat
  have : A ∪ X ∪ Y = A ∪ Y ∪ X := union_right_comm _ _ _
  constructor
  · rintro ⟨-, h⟩
    rw [this] at h
    exact ⟨pp_mono h subset_union_left, h⟩
  · rintro ⟨-, h⟩
    rw [← this] at h
    exact ⟨pp_mono h subset_union_left, h⟩

theorem br_blocks {T : QT α} {W : Finset ℕ} {B : Finset (Finset ℕ) × α} (h : B ∈ br q T W) :
    ∀ f ∈ B.1, f ⊆ W := (br_props T W B h).2.1

theorem br_card {T : QT α} {W : Finset ℕ} {B : Finset (Finset ℕ) × α} (h : B ∈ br q T W) :
    B.1.card ≤ ht q T W := (br_props T W B h).2.2

/-- The mass lemma on the full universe. -/
theorem mass_full {W : Finset ℕ} {D : ℕ} (ds : Design q (ZMod p) W D) {T : QT α}
    (hT : WF q T W) {F : Finset (Finset ℕ)} (hF : PP q F) (hFW : ∀ f ∈ F, f ⊆ W)
    (hdeg : F.card + ht q T W ≤ D) :
    wsum q T W (fun B => if Compat q F B.1 then ds.s (F ∪ B.1) else 0) = ds.s F :=
  mass ds T W F hT subset_rfl hF hFW subset_union_left (fun f hf => Or.inl (hFW f hf)) hdeg

theorem union_blocks {F B : Finset (Finset ℕ)} {W : Finset ℕ} (hF : ∀ f ∈ F, f ⊆ W)
    (hB : ∀ f ∈ B, f ⊆ W) : ∀ f ∈ F ∪ B, f ⊆ W := by
  intro f hf; rcases mem_union.1 hf with h | h
  · exact hF f h
  · exact hB f h

/-- **Design mass against Count_p instances.** -/
theorem count_mass_false [Fact p.Prime] {W : Finset ℕ} {D : ℕ} (ds : Design q (ZMod p) W D)
    {a : Finset (Finset ℕ)} (ha : PP q a) (haW : ∀ f ∈ a, f ⊆ W) (hsa : ds.s a = 1)
    {h M : ℕ} (hM : ¬ p ∣ M) (T : Finset ℕ → QT Bool) (A : ℕ → QT Bool)
    (C : Finset ℕ → Finset ℕ → QT Bool)
    (hT : ∀ g, WF q (T g) W ∧ ht q (T g) W ≤ h) (hA : ∀ i, WF q (A i) W ∧ ht q (A i) W ≤ h)
    (hC : ∀ g g', WF q (C g g') W ∧ ht q (C g g') W ≤ h)
    (hAc : ∀ i < M, ∀ B ∈ br q (A i) W, Compat q a B.1 →
      ∃ g ∈ powersetCard p (range M), i ∈ g ∧ ∃ β ∈ br q (T g) W, β.2 = true ∧ β.1 ⊆ B.1)
    (hCc : ∀ g ∈ powersetCard p (range M), ∀ g' ∈ powersetCard p (range M), g ≠ g' →
      ¬ Disjoint g g' → ∀ γ ∈ br q (C g g') W, Compat q a γ.1 →
      ∃ δ, (δ ∈ br q (T g) W ∨ δ ∈ br q (T g') W) ∧ δ.2 = false ∧ δ.1 ⊆ γ.1)
    (hdeg : a.card + 3 * h ≤ D) : False := by
  set G := powersetCard p (range M)
  -- `1`-mass of a tree below `a`
  let π : Finset ℕ → ZMod p := fun g =>
    wsum q (T g) W (fun β => if β.2 = true ∧ Compat q a β.1 then ds.s (a ∪ β.1) else 0)
  have hcardU : ∀ {X Y : Finset (Finset ℕ)}, (X ∪ Y).card ≤ X.card + Y.card :=
    fun {X Y} => card_union_le X Y
  -- (★) below a branch of `A i`
  have star : ∀ i < M, ∀ B ∈ br q (A i) W, Compat q a B.1 →
      ∑ g ∈ G.filter (i ∈ ·), wsum q (T g) W (fun β =>
        if β.2 = true ∧ Compat q (a ∪ B.1) β.1 then ds.s (a ∪ B.1 ∪ β.1) else 0) = ds.s (a ∪ B.1) := by
    intro i hi B hB hcB
    obtain ⟨g0, hg0, hig0, β0, hβ0, hβ02, hβ0B⟩ := hAc i hi B hB hcB
    have hFW := union_blocks haW (br_blocks hB)
    have hBc := br_card hB
    rw [sum_eq_single g0]
    · rw [← mass_full ds (hT g0).1 hcB hFW (by
        have := (hT g0).2; have := (hA i).2; have := hcardU (X := a) (Y := B.1); omega)]
      refine wsum_congr _ _ _ _ fun β hβ => ?_
      by_cases hc : Compat q (a ∪ B.1) β.1
      · have hβ2 : β.2 = true := by
          by_contra hne
          have : β = β0 := branch_eq _ _ _ _ hβ (hβ0) (pp_mono hc (by
            intro x hx; rcases mem_union.1 hx with hx | hx
            · exact mem_union.2 (Or.inr hx)
            · exact mem_union.2 (Or.inl (mem_union.2 (Or.inr (hβ0B hx))))))
          rw [this] at hne; exact hne hβ02
        rw [if_pos ⟨hβ2, hc⟩, if_pos hc]
      · rw [if_neg (fun h => hc h.2), if_neg hc]
    · intro g hg hne
      obtain ⟨hgG, hig⟩ := mem_filter.1 hg
      refine wsum_zero fun β hβ => ?_
      split_ifs with hcond
      · obtain ⟨hβ2, hc⟩ := hcond
        set F' := a ∪ B.1 ∪ β.1
        have hF'W := union_blocks hFW (br_blocks hβ)
        have hβc := br_card hβ
        rw [← mass_full ds (hC g g0).1 hc hF'W (by
          have := (hC g g0).2; have := (hT g).2; have := (hA i).2
          have := hcardU (X := a ∪ B.1) (Y := β.1); have := hcardU (X := a) (Y := B.1); omega)]
        refine wsum_zero fun γ hγ => ?_
        rw [if_neg]
        intro hcγ
        have hcaγ : Compat q a γ.1 := pp_mono hcγ (union_subset_union
          (subset_union_left.trans subset_union_left) subset_rfl)
        obtain ⟨δ, hδ, hδ2, hδγ⟩ := hCc g hgG g0 hg0 hne
          (not_disjoint_iff.2 ⟨i, hig, hig0⟩) γ hγ hcaγ
        rcases hδ with hδ | hδ
        · have : δ = β := branch_eq _ _ _ _ hδ hβ (pp_mono hcγ (by
            intro x hx; rcases mem_union.1 hx with hx | hx
            · exact mem_union.2 (Or.inr (hδγ hx))
            · exact mem_union.2 (Or.inl (mem_union.2 (Or.inr hx)))))
          rw [this, hβ2] at hδ2; exact Bool.noConfusion hδ2
        · have : δ = β0 := branch_eq _ _ _ _ hδ hβ0 (pp_mono hcγ (by
            intro x hx; rcases mem_union.1 hx with hx | hx
            · exact mem_union.2 (Or.inr (hδγ hx))
            · exact mem_union.2 (Or.inl (mem_union.2 (Or.inl (mem_union.2 (Or.inr (hβ0B hx))))))))
          rw [this, hβ02] at hδ2; exact Bool.noConfusion hδ2
      · rfl
    · intro h; exact absurd (mem_filter.2 ⟨hg0, hig0⟩) h
  -- the masses around each point sum to one
  have hpt : ∀ i < M, ∑ g ∈ G.filter (i ∈ ·), π g = 1 := by
    intro i hi
    have hexp : ∀ g, π g = wsum q (T g) W (fun β => wsum q (A i) W (fun B =>
        if β.2 = true ∧ Compat q a β.1 ∧ Compat q (a ∪ β.1) B.1 then ds.s (a ∪ β.1 ∪ B.1) else 0)) := by
      intro g
      refine wsum_congr _ _ _ _ fun β hβ => ?_
      by_cases hc : β.2 = true ∧ Compat q a β.1
      · rw [if_pos hc, ← mass_full ds (hA i).1 hc.2 (union_blocks haW (br_blocks hβ)) (by
          have := (hT g).2; have := (hA i).2; have := br_card hβ
          have := hcardU (X := a) (Y := β.1); omega)]
        refine wsum_congr _ _ _ _ fun B _ => ?_
        by_cases hc' : Compat q (a ∪ β.1) B.1
        · rw [if_pos hc', if_pos ⟨hc.1, hc.2, hc'⟩]
        · rw [if_neg hc', if_neg (fun h => hc' h.2.2)]
      · rw [if_neg hc]
        symm
        refine wsum_zero fun B _ => ?_
        rw [if_neg (fun h => hc ⟨h.1, h.2.1⟩)]
    simp only [hexp]
    simp only [wsum_comm (T1 := T _)]
    rw [← wsum_sum]
    rw [← hsa, ← mass_full ds (hA i).1 ha haW (by have := (hA i).2; omega)]
    refine wsum_congr _ _ _ _ fun B hB => ?_
    by_cases hcB : Compat q a B.1
    · rw [if_pos hcB, ← star i hi B hB hcB]
      refine sum_congr rfl fun g _ => wsum_congr _ _ _ _ fun β _ => ?_
      have hiff : (β.2 = true ∧ Compat q a β.1 ∧ Compat q (a ∪ β.1) B.1) ↔
          (β.2 = true ∧ Compat q (a ∪ B.1) β.1) := by
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h1, (compat_swap.1 ⟨h2, h3⟩).2⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, compat_swap.2 ⟨hcB, h2⟩⟩
      exact if_congr hiff (by rw [union_right_comm]) rfl
    · rw [if_neg hcB]
      refine sum_eq_zero fun g _ => wsum_zero fun β _ => ?_
      rw [if_neg]
      rintro ⟨-, h2, h3⟩
      exact hcB (compat_swap.1 ⟨h2, h3⟩).1
  -- double counting
  have h1 : ∑ i ∈ range M, ∑ g ∈ G.filter (i ∈ ·), π g = (M : ZMod p) := by
    rw [sum_congr rfl fun i hi => hpt i (mem_range.1 hi), sum_const, card_range, nsmul_eq_mul,
      mul_one]
  have h2 : ∑ i ∈ range M, ∑ g ∈ G.filter (i ∈ ·), π g = 0 := by
    simp only [sum_filter]
    rw [sum_comm]
    refine sum_eq_zero fun g hg => ?_
    rw [← sum_filter]
    obtain ⟨hgM, hgc⟩ := mem_powersetCard.1 hg
    have : (range M).filter (· ∈ g) = g := by
      ext x; simp only [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hgM h, h⟩⟩
    rw [this, sum_const, hgc, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [h1] at h2
  exact hM ((ZMod.natCast_eq_zero_iff M p).1 h2)

end Mass3

end

end QP

end SATurday.ProofComplexity
