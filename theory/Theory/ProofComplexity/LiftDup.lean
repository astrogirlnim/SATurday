import Theory.ProofComplexity.Lift

/-!
# MAJ₃ realizability: lifting a base Duplicator to a Res(⊕) Duplicator (Alekseev–Itsykson,
# ECCC TR24-128, section 3)

A base family `G C β` ("the partial assignment `β` restricted to the block set `C` is in the
family") that is a Duplicator strategy for the width game on a CNF `F0` lifts, through the
`MAJ₃` gadget, to a Duplicator strategy for the rank game on `F0 ∘ MAJ₃`. The lifted family
consists of the linear systems `Φ` of rank `≤ W + 1` that have a solution `τ` whose gadget values
on the closure of the forms of `Φ` lie in the base family. Realizability is `solve_closure`.

LOG: R4 LiftDup module (lifted Duplicator and the lifting theorem)
-/

namespace SATurday.ProofComplexity

namespace RL

noncomputable section

open Classical
open Finset

/-- A linear clause read as a system of `Frm` equations. -/
def toSys (L : LClause) : Sys := L.image fun e => (fv e.1, e.2)

theorem satSys_toSys (L : LClause) (x : ℕ → ZMod 2) : satSys (toSys L) x ↔ satS L x := by
  unfold satSys satS toSys
  constructor
  · intro h e he
    have := h (fv e.1, e.2) (mem_image_of_mem _ he)
    simpa [ev_fv] using this
  · intro h e he
    obtain ⟨e0, he0, rfl⟩ := mem_image.1 he
    simpa [ev_fv] using h e0 he0

theorem forms_insert (g : Frm) (a : ZMod 2) (E : Sys) :
    forms (insert (g, a) E) = Submodule.span (ZMod 2) (insert g ((E.image Prod.fst : Finset Frm) : Set Frm)) := by
  unfold forms
  rw [Finset.image_insert]
  simp

theorem forms_insert_eq (g : Frm) (a a' : ZMod 2) (E : Sys) :
    forms (insert (g, a) E) = forms (insert (g, a') E) := by
  rw [forms_insert, forms_insert]

theorem finrank_forms_insert (g : Frm) (a : ZMod 2) (E : Sys) :
    Module.finrank (ZMod 2) (forms (insert (g, a) E)) ≤ Module.finrank (ZMod 2) (forms E) + 1 := by
  rw [forms_insert, Submodule.span_insert]
  have h1 := Submodule.finrank_add_le_finrank_add_finrank (Submodule.span (ZMod 2) {g})
    (forms E)
  have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {g}) ≤ 1 := by
    have : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (({g} : Finset Frm) : Set Frm)) ≤
        ({g} : Finset Frm).card := finrank_span_finset_le_card _
    rw [Finset.coe_singleton, Finset.card_singleton] at this
    exact this
  have h3 : (forms E) = Submodule.span (ZMod 2) ((E.image Prod.fst : Finset Frm) : Set Frm) := rfl
  rw [← h3]
  omega

theorem rk_eq_finrank (L : LClause) : rk L = Module.finrank (ZMod 2) (forms (toSys L)) := by
  let ι : Frm →ₗ[ZMod 2] (ℕ → ZMod 2) := Finsupp.lcoeFun
  have hinj : Function.Injective ι := DFunLike.coe_injective
  have himg : (toSys L).image Prod.fst = L.image (fun e => fv e.1) := by
    simp [toSys, Finset.image_image, Function.comp_def]
  have hmap : (forms (toSys L)).map ι = Submodule.span (ZMod 2)
      (((L.image fun e => ind e.1) : Finset (ℕ → ZMod 2)) : Set (ℕ → ZMod 2)) := by
    unfold forms
    rw [Submodule.map_span, himg, Finset.coe_image, Finset.coe_image, Set.image_image]
    congr 2
    funext e
    ext w
    simp [ι, fv_apply, ind]
  unfold rk
  rw [← hmap]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective ι hinj _)).symm

theorem forms_le_of_imp {F G : LClause} (hF : ∃ τ, satS F τ) (h : ∀ x, satS F x → satS G x) :
    forms (toSys G) ≤ forms (toSys F) := by
  obtain ⟨τ, hτ⟩ := hF
  unfold forms
  apply Submodule.span_le.2
  intro g hg
  have hg' : g ∈ (toSys G).image Prod.fst := hg
  obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 hg'
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 he'
  by_contra hnot
  change ¬ fv e.1 ∈ Submodule.span (ZMod 2) (((toSys F).image Prod.fst : Finset Frm) : Set Frm)
    at hnot
  obtain ⟨f, hfg, hker⟩ := Submodule.exists_le_ker_of_notMem hnot
  let y : ℕ → ZMod 2 := fun w => f (Finsupp.single w 1)
  have hev : ev y = f := by
    apply Finsupp.lhom_ext
    intro a b
    rw [← Finsupp.smul_single_one a b, map_smul, map_smul]
    simp [ev, y, Finsupp.linearCombination_single]
  have hy : ∀ e' ∈ F, lf e'.1 y = 0 := by
    intro e' he'
    rw [← ev_fv, hev]
    have hmem : fv e'.1 ∈ Submodule.span (ZMod 2) (((toSys F).image Prod.fst : Finset Frm) : Set Frm) :=
      Submodule.subset_span (by
        simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
        exact ⟨(fv e'.1, e'.2), mem_image_of_mem _ he', rfl⟩)
    exact hker hmem
  have hsat : satS F (τ + y) := by
    intro e' he'
    rw [lf_add, hτ e' he', hy e' he', add_zero]
  have h1 := h _ hsat e he
  have h2 := h τ hτ e he
  rw [lf_add, h2] at h1
  have h3 : lf e.1 y = 0 := by
    have : e.2 + lf e.1 y = e.2 + 0 := by rw [add_zero]; exact h1
    exact add_left_cancel this
  apply hfg
  rw [← hev, ev_fv]
  exact h3

/-! ## MAJ₃ clauses -/

theorem z2_ne_bv : ∀ (a : ZMod 2) (s : Bool), a ≠ bv s → a = bv (!s) := by decide

theorem maj_of_cfalse {x : ℕ → ZMod 2} {D : Clause} {ch : Literal → Fin 3}
    (hf : cfalse x (liftC D ch)) : ∀ l ∈ D, maj x l.var = !l.pos := by
  intro l hl
  have h1 := hf ⟨lv l.var (pr1 (ch l)), l.pos⟩ (mem_biUnion.2 ⟨l, hl, by simp⟩)
  have h2 := hf ⟨lv l.var (pr2 (ch l)), l.pos⟩ (mem_biUnion.2 ⟨l, hl, by simp⟩)
  have h1' : x (lv l.var (pr1 (ch l))) ≠ bv l.pos := h1
  have h2' : x (lv l.var (pr2 (ch l))) ≠ bv l.pos := h2
  exact maj_of_two x l.var (!l.pos) (pr1 (ch l)) (pr2 (ch l)) (pr_lt _).1 (pr_lt _).2
    (pr_ne _) (z2_ne_bv _ _ h1') (z2_ne_bv _ _ h2')

/-! ## Base Duplicator and its lift -/

/-- A Duplicator family for the width game on the CNF `F0`, stated on block sets: `G C β` says
that `β` restricted to `C` is in the family. -/
structure BaseDup (F0 : CNF) (W : ℕ) (G : Finset ℕ → (ℕ → Bool) → Prop) : Prop where
  congr : ∀ C β β', (∀ v ∈ C, β v = β' v) → G C β → G C β'
  mono : ∀ C C' β, C' ⊆ C → G C β → G C' β
  empty : ∃ β, G ∅ β
  sat : ∀ C β, G C β → ∀ D ∈ F0, ∃ β', (∀ v ∈ C, β' v = β v) ∧ clauseSat β' D
  ext : ∀ C β, G C β → C.card ≤ W → ∀ v, ∃ β', (∀ w ∈ C, β' w = β w) ∧ G (insert v C) β'

/-- The lifted family of linear systems. -/
def Hset (W : ℕ) (G : Finset ℕ → (ℕ → Bool) → Prop) : Set LClause :=
  {L | rk L ≤ W + 1 ∧ ∃ τ, satS L τ ∧ G (Closure.cl blkOf (forms (toSys L))) (maj τ)}

theorem extend_to {F0 : CNF} {W : ℕ} {G : Finset ℕ → (ℕ → Bool) → Prop} (hG : BaseDup F0 W G) :
    ∀ (k : ℕ) (A B : Finset ℕ) (β : ℕ → Bool), (B \ A).card = k → A ⊆ B → B.card ≤ W + 1 →
      G A β → ∃ β', (∀ w ∈ A, β' w = β w) ∧ G B β' := by
  intro k
  induction k with
  | zero =>
    intro A B β hk hAB _ hA
    have : B ⊆ A := by
      intro w hw
      by_contra hn
      have : w ∈ B \ A := mem_sdiff.2 ⟨hw, hn⟩
      rw [Finset.card_eq_zero] at hk
      rw [hk] at this; simp at this
    have hEq : A = B := Finset.Subset.antisymm hAB this
    subst hEq
    exact ⟨β, fun _ _ => rfl, hA⟩
  | succ k ih =>
    intro A B β hk hAB hB hA
    obtain ⟨v, hv⟩ : (B \ A).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨hvB, hvA⟩ := mem_sdiff.1 hv
    have hsub : insert v A ⊆ B := Finset.insert_subset hvB hAB
    have hcard : (insert v A).card ≤ B.card := Finset.card_le_card hsub
    have hAc : A.card ≤ W := by
      rw [Finset.card_insert_of_notMem hvA] at hcard; omega
    obtain ⟨β1, h1, hG1⟩ := hG.ext A β hA hAc v
    have hk' : (B \ insert v A).card = k := by
      have : B \ insert v A = (B \ A).erase v := by
        ext w; simp only [mem_sdiff, mem_insert, mem_erase]; tauto
      rw [this, Finset.card_erase_of_mem hv]; omega
    obtain ⟨β', h2, hG2⟩ := ih (insert v A) B β1 hk' hsub hB hG1
    exact ⟨β', fun w hw => by rw [h2 w (mem_insert_of_mem hw), h1 w hw], hG2⟩

theorem cl_eq_of_forms_eq {E E' : Sys} (h : forms E = forms E') :
    Closure.cl blkOf (forms E) = Closure.cl blkOf (forms E') := by
  have key : ∀ (V V' : Submodule (ZMod 2) Frm) [FiniteDimensional (ZMod 2) V]
      [FiniteDimensional (ZMod 2) V'], V = V' → Closure.cl blkOf V = Closure.cl blkOf V' := by
    intro V V' _ _ hv; subst hv; rfl
  exact key _ _ h

theorem cl_card_le_rk (L : LClause) : (Closure.cl blkOf (forms (toSys L))).card ≤ rk L := by
  rw [rk_eq_finrank]; exact Closure.cl_card_le blkOf (forms (toSys L))

theorem hset_duplicator {F0 : CNF} {W : ℕ} {G : Finset ℕ → (ℕ → Bool) → Prop}
    (hG : BaseDup F0 W G) : Duplicator (lifted F0) W (Hset W G) where
  empty := by
    refine ⟨by simp [rk_empty], 0, fun e he => by simp at he, ?_⟩
    have h0 : Module.finrank (ZMod 2) (forms (toSys (∅ : LClause))) = 0 := by
      rw [← rk_eq_finrank, rk_empty]
    have hc : Closure.cl blkOf (forms (toSys (∅ : LClause))) = ∅ :=
      Finset.card_eq_zero.1 (Nat.le_zero.1 ((Closure.cl_card_le blkOf _).trans h0.le))
    rw [hc]
    obtain ⟨β, hβ⟩ := hG.empty
    exact hG.congr ∅ β _ (fun v hv => by simp at hv) hβ
  sat := by
    intro F hF D' hD'
    obtain ⟨hrk, τ, hτ, hGc⟩ := hF
    obtain ⟨D, hD, ch, rfl⟩ := hD'
    obtain ⟨β', hagree, hsatD⟩ := hG.sat _ _ hGc D hD
    obtain ⟨τ', hτ', hmaj⟩ := solve_closure (toSys F) τ ((satSys_toSys F τ).2 hτ) β'
      (fun v hv => hagree v hv)
    refine ⟨τ', (satSys_toSys F τ').1 hτ', fun hcf => ?_⟩
    obtain ⟨l, hl, hls⟩ := hsatD
    have h1 := maj_of_cfalse hcf l hl
    rw [hmaj] at h1
    have h2 : β' l.var = l.pos := hls
    rw [h2] at h1
    cases hp : l.pos <;> simp [hp] at h1
  rank := fun F hF => hF.1
  imp := by
    intro F hF Gc hFG
    obtain ⟨hrk, τ, hτ, hGc⟩ := hF
    have hle := forms_le_of_imp ⟨τ, hτ⟩ hFG
    refine ⟨?_, τ, hFG τ hτ, ?_⟩
    · rw [rk_eq_finrank]; rw [rk_eq_finrank] at hrk
      exact (Submodule.finrank_mono hle).trans hrk
    · exact hG.mono _ _ _ (Closure.cl_mono blkOf hle) hGc
  ext := by
    intro F hF hrkW f
    obtain ⟨hrk, τ, hτ, hGc⟩ := hF
    obtain ⟨L0, hL0⟩ : ∃ L0 : LClause, L0 = insert (f, 0) F := ⟨_, rfl⟩
    have hsysL : ∀ a, toSys (insert (f, a) F) = insert (fv f, a) (toSys F) := by
      intro a; simp [toSys, Finset.image_insert]
    have hformsEq : ∀ a, forms (toSys (insert (f, a) F)) = forms (toSys L0) := by
      intro a; rw [hL0, hsysL, hsysL]; exact forms_insert_eq _ _ _ _
    have hrkL : ∀ a, rk (insert (f, a) F) ≤ rk F + 1 := by
      intro a
      rw [rk_eq_finrank, rk_eq_finrank, hsysL]; exact finrank_forms_insert _ _ _
    have hrkL0 : rk L0 ≤ W + 1 := by
      have := hrkL 0
      rw [← hL0] at this; omega
    obtain ⟨B, hBdef⟩ : ∃ B, B = Closure.cl blkOf (forms (toSys L0)) := ⟨_, rfl⟩
    have hBcard : B.card ≤ W + 1 := by
      rw [hBdef]; exact (cl_card_le_rk L0).trans hrkL0
    have hAB : Closure.cl blkOf (forms (toSys F)) ⊆ B := by
      rw [hBdef]
      apply Closure.cl_mono blkOf
      rw [← hformsEq 0, hsysL, forms_insert]
      unfold forms
      exact Submodule.span_mono (Set.subset_insert _ _)
    obtain ⟨β', hagree, hGB⟩ := extend_to hG _ _ B (maj τ) rfl hAB hBcard hGc
    obtain ⟨τ', hτ', hmaj⟩ := solve_closure (toSys F) τ ((satSys_toSys F τ).2 hτ) β'
      (fun v hv => hagree v hv)
    have hmajeq : maj τ' = β' := funext hmaj
    refine ⟨lf f τ', ?_, τ', ?_, ?_⟩
    · have := hrkL (lf f τ'); omega
    · intro e he
      rcases mem_insert.1 he with rfl | he
      · rfl
      · exact (satSys_toSys F τ').1 hτ' e he
    · rw [cl_eq_of_forms_eq (hformsEq _), ← hBdef, hmajeq]; exact hGB

/-- **Lifting through MAJ₃** (Alekseev–Itsykson, Theorem 3.1 shape): if a base Duplicator family
exists for the width game on `F0`, no dag-like Res(⊕) refutation of `F0 ∘ MAJ₃` has all lines of
rank at most `W`. -/
theorem maj3_lifting {F0 : CNF} {W : ℕ} {G : Finset ℕ → (ℕ → Bool) → Prop}
    (hG : BaseDup F0 W G) {P : Finset LClause} (hD : Der (lifted F0) P)
    (hr : ∀ L ∈ P, rk L ≤ W) : (∅ : LClause) ∉ P :=
  duplicator_no_refutation (hset_duplicator hG) hD hr

/-- Every dag-like Res(⊕) refutation of `F0 ∘ MAJ₃` has a line of rank above `W`. -/
theorem maj3_lifting_rank {F0 : CNF} {W : ℕ} {G : Finset ℕ → (ℕ → Bool) → Prop}
    (hG : BaseDup F0 W G) {P : Finset LClause} (hD : Der (lifted F0) P)
    (h0 : (∅ : LClause) ∈ P) : ∃ L ∈ P, W < rk L := by
  by_contra hc
  push Not at hc
  exact maj3_lifting hG hD hc h0

end

end RL

end SATurday.ProofComplexity
