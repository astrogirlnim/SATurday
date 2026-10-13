import Theory.ProofComplexity.ResLinFDag
import Theory.ProofComplexity.ResLinFPC
import Theory.ProofComplexity.ResDag

/-!
# Khaniki's extension-variable translation, forward half (Ladder Rung R4, Phase 2.2, K3)

Replace every linear equation `e` by a propositional atom `y_e` (variable number `aid e`, `aid`
injective). A linear clause `L` becomes the clause `aCl L` of positive atom literals. A dag-like
`Res(lin F)` refutation `𝓛` of a CNF `Φ` (with Boolean axioms) becomes a dag-like Resolution
refutation (`DDer`) from the hypotheses `AtomHyp Φ`:
* atom clauses of the axiom lines (`aCl (ofCl C)`, `aCl (boolCl i)`),
* the implication clauses `¬y_e1 ∨ ¬y_e2 ∨ y_(cmb α β e1 e2)` (`qCl`),
* the unit clauses `¬y_(0 = c)` for `c ≠ 0`.
Weakening needs no axiom: a line is represented by a SUBSUMING atom clause. The atom dag has at
most `3 |𝓛|` lines (`atom_translate`).

LOG: R4 Phase 2.2 ResLinFAtom module (forward translation)
-/

namespace SATurday.ProofComplexity

namespace RLF

open scoped Classical
open Finset

noncomputable section

variable {F : Type} [Field F] (aid : LEq F → ℕ)

/-- The positive atom literal of an equation. -/
def apos (e : LEq F) : Literal := ⟨aid e, true⟩

/-- The negative atom literal of an equation. -/
def aneg (e : LEq F) : Literal := ⟨aid e, false⟩

/-- The atom clause of a linear clause. -/
def aCl (L : Finset (LEq F)) : Clause := L.image (apos aid)

/-- The implication clause `¬y_e1 ∨ ¬y_e2 ∨ y_e3`. -/
def qCl (e1 e2 e3 : LEq F) : Clause := {aneg aid e1, aneg aid e2, apos aid e3}

/-- The unit clause `¬y_(0 = c)`. -/
def uCl (c : F) : Clause := {aneg aid ((0 : ℕ →₀ F), c)}

/-- Hypotheses of the atom translation of a CNF `Φ`. -/
inductive AtomHyp (Φ : CNF) : Clause → Prop
  | phi (C : Clause) : C ∈ Φ → AtomHyp Φ (aCl aid (ofCl (F := F) C))
  | bool (i : ℕ) : AtomHyp Φ (aCl aid (boolCl (F := F) i))
  | imp (e1 e2 : LEq F) (α β : F) : cmb α β e1 e2 ≠ e1 → cmb α β e1 e2 ≠ e2 →
      AtomHyp Φ (qCl aid e1 e2 (cmb α β e1 e2))
  | unit (c : F) : c ≠ 0 → AtomHyp Φ (uCl aid c)

/-- The invariant of the translation. -/
def TrInv (Φ : CNF) (𝓛 : Finset (Finset (LEq F))) (S : Finset Clause) : Prop :=
  DDer (S.filter (AtomHyp aid Φ)) S ∧ S.card ≤ 3 * 𝓛.card ∧
    ((∅ : Clause) ∈ S ∨ ∀ L ∈ 𝓛, ∃ X ∈ S, X ⊆ aCl aid L)

section Translate

variable {aid} (haid : Function.Injective aid)
include haid

theorem apos_inj : Function.Injective (apos aid : LEq F → Literal) := by
  intro a b h
  exact haid (congrArg Literal.var h)

theorem aCl_mono {L L' : Finset (LEq F)} (h : L ⊆ L') : aCl aid L ⊆ aCl aid L' :=
  image_subset_image h

theorem aCl_empty : aCl aid (∅ : Finset (LEq F)) = ∅ := by simp [aCl]

theorem mem_aCl {L : Finset (LEq F)} {e : LEq F} : apos aid e ∈ aCl aid L ↔ e ∈ L := by
  unfold aCl
  rw [mem_image]
  constructor
  · rintro ⟨a, ha, h⟩; exact (apos_inj haid h) ▸ ha
  · intro he; exact ⟨e, he, rfl⟩

/-- Erasing the atom of `e` from a subclause of `aCl L` lands in `aCl (L.erase e)`. -/
theorem erase_sub {X : Clause} {L : Finset (LEq F)} (hX : X ⊆ aCl aid L) (e : LEq F) :
    X.erase (apos aid e) ⊆ aCl aid (L.erase e) := by
  intro x hx
  obtain ⟨hne, hxX⟩ := mem_erase.1 hx
  obtain ⟨a, ha, rfl⟩ := mem_image.1 (hX hxX)
  exact mem_image.2 ⟨a, mem_erase.2 ⟨fun h => hne (h ▸ rfl), ha⟩, rfl⟩

end Translate

section Steps

variable {H : Clause → Prop}

theorem dd_hyp {S : Finset Clause} {C : Clause} (hS : DDer (S.filter H) S) (hC : H C) :
    DDer ((insert C S).filter H) (insert C S) :=
  DDer.hyp C (hS.mono (filter_subset_filter _ (subset_insert _ _)))
    (mem_filter.2 ⟨mem_insert_self _ _, hC⟩)

theorem dd_res {S : Finset Clause} {C D : Clause} {x : ℕ} (hS : DDer (S.filter H) S)
    (hC : C ∈ S) (hD : D ∈ S) (hx : (⟨x, true⟩ : Literal) ∈ C) (hnx : (⟨x, false⟩ : Literal) ∈ D) :
    DDer ((insert (resolvent C D x) S).filter H) (insert (resolvent C D x) S) :=
  DDer.res x C D (hS.mono (filter_subset_filter _ (subset_insert _ _))) hC hD hx hnx

end Steps

section Main

variable {aid} (haid : Function.Injective aid) {Φ : CNF}
include haid

theorem trInv_pack {𝓛 : Finset (Finset (LEq F))} {L' : Finset (LEq F)} (hnot : L' ∉ 𝓛)
    {S S'' : Finset Clause} (hS : TrInv aid Φ 𝓛 S)
    (hinv : ∀ L ∈ 𝓛, ∃ X ∈ S, X ⊆ aCl aid L)
    (hS'' : DDer (S''.filter (AtomHyp aid Φ)) S'') (hsub : S ⊆ S'')
    (hc : S''.card ≤ S.card + 3) (hnew : ∃ X ∈ S'', X ⊆ aCl aid L') :
    TrInv aid Φ (insert L' 𝓛) S'' := by
  refine ⟨hS'', ?_, Or.inr ?_⟩
  · rw [card_insert_of_notMem hnot]
    have := hS.2.1
    omega
  · intro L hL
    rcases mem_insert.1 hL with rfl | hL
    · exact hnew
    · obtain ⟨X, hX, hXs⟩ := hinv L hL
      exact ⟨X, hsub hX, hXs⟩

theorem trInv_skip {𝓛 : Finset (Finset (LEq F))} {L' : Finset (LEq F)} {S : Finset Clause}
    (hS : TrInv aid Φ 𝓛 S) (h : (∅ : Clause) ∈ S) : TrInv aid Φ (insert L' 𝓛) S := by
  refine ⟨hS.1, hS.2.1.trans ?_, Or.inl h⟩
  have := card_le_card (subset_insert L' 𝓛)
  omega

theorem atom_translate {𝓛 : Finset (Finset (LEq F))}
    (h : RLDag (((fun C => (ofCl C : Finset (LEq F))) '' Φ) ∪ boolAx) 𝓛) :
    ∃ S : Finset Clause, TrInv aid Φ 𝓛 S := by
  induction h with
  | empty => exact ⟨∅, by simpa [TrInv] using DDer.empty, by simp⟩
  | ax C hrec hC ih =>
    rename_i 𝓛
    obtain ⟨S, hS⟩ := ih
    by_cases hmem : C ∈ 𝓛
    · rw [insert_eq_of_mem hmem]; exact ⟨S, hS⟩
    rcases hS.2.2 with h0 | hinv
    · exact ⟨S, trInv_skip haid hS h0⟩
    · have hH : AtomHyp aid Φ (aCl aid C) := by
        rcases hC with ⟨C0, hC0, rfl⟩ | ⟨i, rfl⟩
        · exact AtomHyp.phi C0 hC0
        · exact AtomHyp.bool i
      exact ⟨insert (aCl aid C) S, trInv_pack haid hmem hS hinv (dd_hyp hS.1 hH) (subset_insert _ _)
        ((card_insert_le _ _).trans (by omega)) ⟨aCl aid C, mem_insert_self _ _, Subset.rfl⟩⟩
  | weak L L' hrec hL hsub ih =>
    rename_i 𝓛
    obtain ⟨S, hS⟩ := ih
    by_cases hmem : L' ∈ 𝓛
    · rw [insert_eq_of_mem hmem]; exact ⟨S, hS⟩
    rcases hS.2.2 with h0 | hinv
    · exact ⟨S, trInv_skip haid hS h0⟩
    · obtain ⟨X, hX, hXs⟩ := hinv L hL
      exact ⟨S, trInv_pack haid hmem hS hinv hS.1 Subset.rfl (by omega)
        ⟨X, hX, hXs.trans (aCl_mono haid hsub)⟩⟩
  | simp L c hrec hc hL ih =>
    rename_i 𝓛
    obtain ⟨S, hS⟩ := ih
    by_cases hmem : L ∈ 𝓛
    · rw [insert_eq_of_mem hmem]; exact ⟨S, hS⟩
    rcases hS.2.2 with h0 | hinv
    · exact ⟨S, trInv_skip haid hS h0⟩
    · obtain ⟨X, hX, hXs⟩ := hinv _ hL
      set z : LEq F := ((0 : ℕ →₀ F), c) with hz
      by_cases hpz : apos aid z ∈ X
      · have hU : AtomHyp aid Φ (uCl aid c) := AtomHyp.unit c hc
        have hS1 : DDer ((insert (uCl aid c) S).filter (AtomHyp aid Φ)) (insert (uCl aid c) S) :=
          dd_hyp hS.1 hU
        have hnx : (⟨aid z, false⟩ : Literal) ∈ uCl aid c := by
          unfold uCl aneg; exact mem_singleton.2 rfl
        have hxx : (⟨aid z, true⟩ : Literal) ∈ X := hpz
        have hS2 := dd_res (H := AtomHyp aid Φ) hS1 (mem_insert_of_mem hX)
          (mem_insert_self _ _) hxx hnx
        refine ⟨insert (resolvent X (uCl aid c) (aid z)) (insert (uCl aid c) S),
          trInv_pack haid hmem hS hinv hS2 ((subset_insert _ _).trans (subset_insert _ _))
          ((card_insert_le _ _).trans (by have := card_insert_le (uCl aid c) S; omega))
          ⟨_, mem_insert_self _ _, ?_⟩⟩
        intro y hy
        rcases mem_union.1 hy with hy | hy
        · obtain ⟨hne, hyX⟩ := mem_erase.1 hy
          have := hXs hyX
          obtain ⟨a, ha, rfl⟩ := mem_image.1 this
          rcases mem_insert.1 ha with rfl | ha
          · exact absurd rfl hne
          · exact mem_image.2 ⟨a, ha, rfl⟩
        · have : y ∈ uCl aid c := mem_of_mem_erase hy
          have hyeq : y = ⟨aid z, false⟩ := by simpa [uCl, aneg] using this
          exact absurd hyeq (mem_erase.1 hy).1
      · refine ⟨S, trInv_pack haid hmem hS hinv hS.1 Subset.rfl (by omega) ⟨X, hX, ?_⟩⟩
        intro y hy
        have := hXs hy
        obtain ⟨a, ha, rfl⟩ := mem_image.1 this
        rcases mem_insert.1 ha with rfl | ha
        · exact absurd hy hpz
        · exact mem_image.2 ⟨a, ha, rfl⟩
  | comb A B e1 e2 α β hrec hA hB h1 h2 ih =>
    rename_i 𝓛
    obtain ⟨S, hS⟩ := ih
    by_cases hmem : A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2} ∈ 𝓛
    · rw [insert_eq_of_mem hmem]; exact ⟨S, hS⟩
    rcases hS.2.2 with h0 | hinv
    · exact ⟨S, trInv_skip haid hS h0⟩
    · obtain ⟨X1, hX1, hX1s⟩ := hinv A hA
      obtain ⟨X2, hX2, hX2s⟩ := hinv B hB
      set e3 : LEq F := cmb α β e1 e2 with he3
      set R : Finset (LEq F) := A.erase e1 ∪ B.erase e2 ∪ {e3} with hR
      have hRA : A.erase e1 ⊆ R := fun a ha =>
        mem_union_left _ (mem_union_left _ ha)
      have hRB : B.erase e2 ⊆ R := fun a ha =>
        mem_union_left _ (mem_union_right _ ha)
      have hR3 : e3 ∈ R := mem_union_right _ (mem_singleton_self _)
      by_cases hp1 : apos aid e1 ∈ X1
      swap
      · refine ⟨S, trInv_pack haid hmem hS hinv hS.1 Subset.rfl (by omega) ⟨X1, hX1, ?_⟩⟩
        have := erase_sub haid hX1s e1
        rw [erase_eq_of_notMem hp1] at this
        exact this.trans (aCl_mono haid hRA)
      by_cases hp2 : apos aid e2 ∈ X2
      swap
      · refine ⟨S, trInv_pack haid hmem hS hinv hS.1 Subset.rfl (by omega) ⟨X2, hX2, ?_⟩⟩
        have := erase_sub haid hX2s e2
        rw [erase_eq_of_notMem hp2] at this
        exact this.trans (aCl_mono haid hRB)
      by_cases h31 : e3 = e1
      · refine ⟨S, trInv_pack haid hmem hS hinv hS.1 Subset.rfl (by omega) ⟨X1, hX1, ?_⟩⟩
        refine hX1s.trans (aCl_mono haid ?_)
        intro a ha
        by_cases hae : a = e1
        · rw [hae, ← h31]; exact hR3
        · exact hRA (mem_erase.2 ⟨hae, ha⟩)
      by_cases h32 : e3 = e2
      · refine ⟨S, trInv_pack haid hmem hS hinv hS.1 Subset.rfl (by omega) ⟨X2, hX2, ?_⟩⟩
        refine hX2s.trans (aCl_mono haid ?_)
        intro a ha
        by_cases hae : a = e2
        · rw [hae, ← h32]; exact hR3
        · exact hRB (mem_erase.2 ⟨hae, ha⟩)
      -- the implication clause is needed
      have hQ : AtomHyp aid Φ (qCl aid e1 e2 e3) := AtomHyp.imp e1 e2 α β h31 h32
      have hS1 := dd_hyp hS.1 hQ
      have hxQ1 : (⟨aid e1, false⟩ : Literal) ∈ qCl aid e1 e2 e3 := by simp [qCl, aneg]
      have hx1 : (⟨aid e1, true⟩ : Literal) ∈ X1 := hp1
      have hS2 := dd_res (H := AtomHyp aid Φ) hS1 (mem_insert_of_mem hX1)
        (mem_insert_self _ _) hx1 hxQ1
      set Q := qCl aid e1 e2 e3 with hQdef
      set Y1 := resolvent X1 Q (aid e1) with hY1
      have hY1sub : ∀ y ∈ Y1, y ∈ aCl aid (A.erase e1) ∨ y = aneg aid e2 ∨ y = apos aid e3 := by
        intro y hy
        rcases mem_union.1 hy with hy | hy
        · exact Or.inl (erase_sub haid hX1s e1 hy)
        · obtain ⟨hne, hyQ⟩ := mem_erase.1 hy
          simp only [hQdef, qCl, mem_insert, mem_singleton] at hyQ
          rcases hyQ with h | h | h
          · exact absurd h hne
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
      have he3R : apos aid e3 ∈ aCl aid R := mem_image.2 ⟨e3, hR3, rfl⟩
      by_cases h12 : e1 = e2
      · refine ⟨insert Y1 (insert Q S), trInv_pack haid hmem hS hinv hS2
          ((subset_insert _ _).trans (subset_insert _ _))
          ((card_insert_le _ _).trans (by have := card_insert_le Q S; omega)) ⟨Y1, mem_insert_self _ _, ?_⟩⟩
        intro y hy
        rcases hY1sub y hy with h | h | h
        · exact aCl_mono haid hRA h
        · exfalso
          have hy' := mem_union.1 hy
          rcases hy' with hy' | hy'
          · have := hX1s (mem_erase.1 hy').2
            rw [h] at this
            obtain ⟨a, _, ha⟩ := mem_image.1 this
            simp [apos, aneg] at ha
          · exact (mem_erase.1 hy').1 (by rw [h, aneg, h12])
        · rw [h]; exact he3R
      · have hne12 : aneg aid e2 ≠ aneg aid e1 := by
          intro h
          exact h12 (haid (congrArg Literal.var h)).symm
        have hxQ2 : (⟨aid e2, false⟩ : Literal) ∈ Y1 :=
          mem_union_right _ (mem_erase.2 ⟨hne12, by
            simp only [hQdef, qCl, mem_insert, mem_singleton]; exact Or.inr (Or.inl rfl)⟩)
        have hx2 : (⟨aid e2, true⟩ : Literal) ∈ X2 := hp2
        have hS3 := dd_res (H := AtomHyp aid Φ) hS2 (mem_insert_of_mem (mem_insert_of_mem hX2))
          (mem_insert_self _ _) hx2 hxQ2
        refine ⟨insert (resolvent X2 Y1 (aid e2)) (insert Y1 (insert Q S)),
          trInv_pack haid hmem hS hinv hS3
          ((subset_insert _ _).trans ((subset_insert _ _).trans (subset_insert _ _)))
          ((card_insert_le _ _).trans (by
            have := card_insert_le Y1 (insert Q S); have := card_insert_le Q S; omega))
          ⟨_, mem_insert_self _ _, ?_⟩⟩
        intro y hy
        rcases mem_union.1 hy with hy | hy
        · exact aCl_mono haid hRB (erase_sub haid hX2s e2 hy)
        · obtain ⟨hne, hyY⟩ := mem_erase.1 hy
          rcases hY1sub y hyY with h | h | h
          · exact aCl_mono haid hRA h
          · exact absurd h hne
          · rw [h]; exact he3R

/-- **Forward translation (Khaniki, Lemma 4.3(1))**: a dag-like `Res(lin F)` refutation with `s`
lines gives a dag-like Resolution refutation from the atom hypotheses with at most `3 s` lines. -/
theorem atom_refutation {𝓛 : Finset (Finset (LEq F))}
    (h : RLDag (((fun C => (ofCl C : Finset (LEq F))) '' Φ) ∪ boolAx) 𝓛)
    (h0 : (∅ : Finset (LEq F)) ∈ 𝓛) :
    ∃ S : Finset Clause, DDer (S.filter (AtomHyp aid Φ)) S ∧ (∅ : Clause) ∈ S ∧
      S.card ≤ 3 * 𝓛.card := by
  obtain ⟨S, hS, hc, hinv⟩ := atom_translate haid h
  refine ⟨S, hS, ?_, hc⟩
  rcases hinv with hE | hinv
  · exact hE
  · obtain ⟨X, hX, hXs⟩ := hinv ∅ h0
    rw [aCl_empty haid] at hXs
    obtain rfl : X = ∅ := Subset.antisymm hXs (empty_subset _)
    exact hX

end Main

/-- Non vacuity: the dag system refutes `x ∧ ¬x` in four lines (`x = 1`, `x = 0`, `0 = 1`, `⊥`). -/
theorem rldag_refutes_unit_pair :
    ∃ 𝓛 : Finset (Finset (LEq F)),
      RLDag (((fun C => (ofCl C : Finset (LEq F))) ''
        (({{⟨0, true⟩}, {⟨0, false⟩}} : Finset Clause) : Set Clause)) ∪ boolAx) 𝓛 ∧
      (∅ : Finset (LEq F)) ∈ 𝓛 ∧ 𝓛.card ≤ 4 := by
  set A : Finset (LEq F) := {(Finsupp.single 0 1, 1)} with hA
  set B : Finset (LEq F) := {(Finsupp.single 0 1, 0)} with hB
  have hAx : A ∈ (((fun C => (ofCl C : Finset (LEq F))) ''
        (({{⟨0, true⟩}, {⟨0, false⟩}} : Finset Clause) : Set Clause)) ∪ boolAx) :=
    Or.inl ⟨{⟨0, true⟩}, by simp, by simp [ofCl, litEq, hA]⟩
  have hBx : B ∈ (((fun C => (ofCl C : Finset (LEq F))) ''
        (({{⟨0, true⟩}, {⟨0, false⟩}} : Finset Clause) : Set Clause)) ∪ boolAx) :=
    Or.inl ⟨{⟨0, false⟩}, by simp, by simp [ofCl, litEq, hB]⟩
  have h1 := RLDag.ax A RLDag.empty hAx
  have h2 := RLDag.ax B h1 hBx
  have hAm : A ∈ insert B (insert A (∅ : Finset (Finset (LEq F)))) := by simp
  have hBm : B ∈ insert B (insert A (∅ : Finset (Finset (LEq F)))) := by simp
  have e1 : (Finsupp.single 0 1, 1) ∈ A := by simp [hA]
  have e2 : (Finsupp.single 0 1, 0) ∈ B := by simp [hB]
  have h3 := RLDag.comb A B _ _ (1 : F) (-1) h2 hAm hBm e1 e2
  have hR : A.erase (Finsupp.single 0 1, 1) ∪ B.erase (Finsupp.single 0 1, 0) ∪
      {cmb (1 : F) (-1) (Finsupp.single 0 1, 1) (Finsupp.single 0 1, 0)} =
      insert ((0 : ℕ →₀ F), (1 : F)) (∅ : Finset (LEq F)) := by
    simp [hA, hB, cmb]
  rw [hR] at h3
  have hm : insert ((0 : ℕ →₀ F), (1 : F)) (∅ : Finset (LEq F)) ∈
      insert (insert ((0 : ℕ →₀ F), (1 : F)) (∅ : Finset (LEq F)))
        (insert B (insert A (∅ : Finset (Finset (LEq F))))) := mem_insert_self _ _
  have h4 := RLDag.simp (∅ : Finset (LEq F)) (1 : F) h3 one_ne_zero hm
  refine ⟨_, h4, Finset.mem_insert_self _ _, ?_⟩
  refine (Finset.card_insert_le _ _).trans ?_
  refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
  refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
  exact Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp))

end

end RLF

end SATurday.ProofComplexity
