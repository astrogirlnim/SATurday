import Theory.ProofComplexity.ResLinFNorm

/-!
# Restriction of Res(lin F) derivations by a hyperplane (Ladder Rung R4, Phase 2.2, layer 3b)

`elimE ℓ i` is the substitution that uses the equation `ℓ` (with `ℓ.1 i ≠ 0`) to eliminate the
pivot variable `x_i`; it is linear on equations (`elimE_cmb`), so it commutes with resolution.
`rst ℓ i L` is the image of a clause with false constants removed. A derivation of `L` from `Γ`
restricts to a derivation of `rst ℓ i L` from `rstSet ℓ i Γ` with at most as many leaves
(`rd_rst`).

LOG: R4 Phase 2.2 ResLinFRst module
-/

namespace SATurday.ProofComplexity

namespace RLF

open scoped Classical

noncomputable section

variable {F : Type} [Field F]

/-- Eliminate the pivot variable `i` of an equation using the equation `ℓ`. -/
def elimE (ℓ : LEq F) (i : ℕ) (e : LEq F) : LEq F :=
  (e.1 - (e.1 i / ℓ.1 i) • ℓ.1, e.2 - (e.1 i / ℓ.1 i) * ℓ.2)

theorem elimE_cmb (ℓ : LEq F) (i : ℕ) (e1 e2 : LEq F) (α β : F) :
    elimE ℓ i (cmb α β e1 e2) = cmb α β (elimE ℓ i e1) (elimE ℓ i e2) := by
  unfold elimE cmb
  refine Prod.ext ?_ ?_
  · ext j
    simp only [Finsupp.coe_sub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply, Finsupp.smul_apply,
      smul_eq_mul]
    ring
  · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply, smul_eq_mul]
    ring

theorem elimE_pivot (ℓ : LEq F) {i : ℕ} (hℓ : ℓ.1 i ≠ 0) (e : LEq F) : (elimE ℓ i e).1 i = 0 := by
  unfold elimE
  simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem elimE_of_zero (ℓ : LEq F) {i : ℕ} {e : LEq F} (h : e.1 i = 0) : elimE ℓ i e = e := by
  unfold elimE
  simp [h]

theorem elimE_prop (ℓ : LEq F) {i : ℕ} (hℓ : ℓ.1 i ≠ 0) {e : LEq F} {μ : F} (hμ : e.1 = μ • ℓ.1) :
    elimE ℓ i e = (0, e.2 - μ * ℓ.2) := by
  unfold elimE
  have : e.1 i / ℓ.1 i = μ := by
    rw [hμ]; simp only [Finsupp.smul_apply, smul_eq_mul]; field_simp
  rw [this, hμ]
  simp

theorem elimE_support (ℓ : LEq F) {i : ℕ} (hℓ : ℓ.1 i ≠ 0) (e : LEq F) :
    (elimE ℓ i e).1.support ⊆ (e.1.support ∪ ℓ.1.support).erase i := by
  intro j hj
  rw [Finsupp.mem_support_iff] at hj
  have hne : j ≠ i := by
    rintro rfl; exact hj (elimE_pivot ℓ hℓ e)
  refine Finset.mem_erase.2 ⟨hne, ?_⟩
  by_contra hcon
  rw [Finset.mem_union, not_or, Finsupp.mem_support_iff, Finsupp.mem_support_iff,
    not_not, not_not] at hcon
  apply hj
  unfold elimE
  simp [hcon.1, hcon.2]

/-- Restriction of a clause: image under `elimE`, false constants dropped. -/
def rst (ℓ : LEq F) (i : ℕ) (L : Finset (LEq F)) : Finset (LEq F) :=
  (L.image (elimE ℓ i)).filter fun e => ¬ IsZ e

/-- Restriction of a clause set. -/
def rstSet (ℓ : LEq F) (i : ℕ) (Γ : Set (Finset (LEq F))) : Set (Finset (LEq F)) :=
  rst ℓ i '' Γ

theorem mem_rst {ℓ : LEq F} {i : ℕ} {L : Finset (LEq F)} {x : LEq F} :
    x ∈ rst ℓ i L ↔ (∃ y ∈ L, elimE ℓ i y = x) ∧ ¬ IsZ x := by
  unfold rst; simp [Finset.mem_filter, Finset.mem_image]

theorem rst_union (ℓ : LEq F) (i : ℕ) (L1 L2 : Finset (LEq F)) :
    rst ℓ i (L1 ∪ L2) = rst ℓ i L1 ∪ rst ℓ i L2 := by
  unfold rst; rw [Finset.image_union, Finset.filter_union]

theorem rst_mono (ℓ : LEq F) (i : ℕ) {L L' : Finset (LEq F)} (h : L ⊆ L') :
    rst ℓ i L ⊆ rst ℓ i L' := by
  intro x hx
  obtain ⟨⟨y, hy, rfl⟩, hz⟩ := mem_rst.1 hx
  exact mem_rst.2 ⟨⟨y, h hy, rfl⟩, hz⟩

theorem rst_insert_zero (ℓ : LEq F) (i : ℕ) {c : F} (hc : c ≠ 0) (L : Finset (LEq F)) :
    rst ℓ i (insert ((0 : ℕ →₀ F), c) L) = rst ℓ i L := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨y, hy, rfl⟩, hz⟩ := mem_rst.1 hx
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exfalso
      apply hz
      rw [elimE_of_zero ℓ (by simp)]
      exact ⟨rfl, hc⟩
    · exact mem_rst.2 ⟨⟨y, hy, rfl⟩, hz⟩
  · exact fun hx => rst_mono ℓ i (Finset.subset_insert _ _) hx

theorem rst_erase_sub (ℓ : LEq F) (i : ℕ) (A : Finset (LEq F)) (e : LEq F) :
    (rst ℓ i A).erase (elimE ℓ i e) ⊆ rst ℓ i (A.erase e) := by
  intro x hx
  obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
  obtain ⟨⟨y, hy, rfl⟩, hz⟩ := mem_rst.1 hx
  refine mem_rst.2 ⟨⟨y, Finset.mem_erase.2 ⟨?_, hy⟩, rfl⟩, hz⟩
  rintro rfl; exact hne rfl

theorem rst_erase_sub' (ℓ : LEq F) (i : ℕ) (A : Finset (LEq F)) (e : LEq F)
    (hz : IsZ (elimE ℓ i e)) : rst ℓ i A ⊆ rst ℓ i (A.erase e) := by
  intro x hx
  have hne : x ≠ elimE ℓ i e := by
    rintro rfl; exact (mem_rst.1 hx).2 hz
  exact rst_erase_sub ℓ i A e (Finset.mem_erase.2 ⟨hne, hx⟩)

/-- **Restriction of derivations**. -/
theorem rd_rst (ℓ : LEq F) (i : ℕ) {Γ : Set (Finset (LEq F))} {L : Finset (LEq F)} {s : ℕ}
    (h : RD Γ L s) : ∃ s' ≤ s, RD (rstSet ℓ i Γ) (rst ℓ i L) s' := by
  induction h with
  | @ax C hC => exact ⟨1, le_rfl, RD.ax ⟨C, hC, rfl⟩⟩
  | weak _ hsub ih =>
    obtain ⟨s', hs', h'⟩ := ih
    exact ⟨s', hs', RD.weak h' (rst_mono ℓ i hsub)⟩
  | @comb A B s1 s2 e1 e2 α β _ _ h1 h2 ih1 ih2 =>
    obtain ⟨t1, ht1, d1⟩ := ih1
    obtain ⟨t2, ht2, d2⟩ := ih2
    set T := rst ℓ i (A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2}) with hT
    have hTA : rst ℓ i (A.erase e1) ⊆ T := rst_mono ℓ i
      (fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx))
    have hTB : rst ℓ i (B.erase e2) ⊆ T := rst_mono ℓ i
      (fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx))
    by_cases hz1 : IsZ (elimE ℓ i e1)
    · exact ⟨t1, by omega, RD.weak d1 ((rst_erase_sub' ℓ i A e1 hz1).trans hTA)⟩
    by_cases hz2 : IsZ (elimE ℓ i e2)
    · exact ⟨t2, by omega, RD.weak d2 ((rst_erase_sub' ℓ i B e2 hz2).trans hTB)⟩
    have m1 : elimE ℓ i e1 ∈ rst ℓ i A := mem_rst.2 ⟨⟨e1, h1, rfl⟩, hz1⟩
    have m2 : elimE ℓ i e2 ∈ rst ℓ i B := mem_rst.2 ⟨⟨e2, h2, rfl⟩, hz2⟩
    have hc := RD.comb (elimE ℓ i e1) (elimE ℓ i e2) α β d1 d2 m1 m2
    rw [← elimE_cmb] at hc
    have hL : (rst ℓ i A).erase (elimE ℓ i e1) ∪ (rst ℓ i B).erase (elimE ℓ i e2) ⊆ T :=
      Finset.union_subset ((rst_erase_sub ℓ i A e1).trans hTA) ((rst_erase_sub ℓ i B e2).trans hTB)
    by_cases hz3 : IsZ (elimE ℓ i (cmb α β e1 e2))
    · refine ⟨t1 + t2, by omega, RD.weak ?_ hL⟩
      refine RD.simp (elimE ℓ i (cmb α β e1 e2)).2 hz3.2 ?_
      have e' : elimE ℓ i (cmb α β e1 e2) = ((0 : ℕ →₀ F), (elimE ℓ i (cmb α β e1 e2)).2) :=
        Prod.ext hz3.1 rfl
      rw [e'] at hc
      rw [Finset.insert_eq, Finset.union_comm]
      exact hc
    · refine ⟨t1 + t2, by omega, RD.weak hc ?_⟩
      refine Finset.union_subset hL ?_
      intro x hx
      rw [Finset.mem_singleton.1 hx]
      exact mem_rst.2 ⟨⟨cmb α β e1 e2, Finset.mem_union_right _ (Finset.mem_singleton_self _), rfl⟩, hz3⟩
  | @simp L s c hc _ ih =>
    obtain ⟨s', hs', h'⟩ := ih
    rw [rst_insert_zero ℓ i hc] at h'
    exact ⟨s', hs', h'⟩

/-! ## Supports -/

/-- All equations of the clause only mention variables in `V`. -/
def ClSupp (V : Finset ℕ) (L : Finset (LEq F)) : Prop := ∀ e ∈ L, e.1.support ⊆ V

theorem cmb_support (α β : F) (e1 e2 : LEq F) :
    (cmb α β e1 e2).1.support ⊆ e1.1.support ∪ e2.1.support := by
  intro j hj
  unfold cmb at hj
  simp only [Finsupp.mem_support_iff, Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply,
    smul_eq_mul] at hj
  rw [Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff]
  by_contra hcon
  push_neg at hcon
  apply hj; rw [hcon.1, hcon.2]; ring

theorem nd_supp {Ax : Set (Finset (LEq F))} {V : Finset ℕ} (hAx : ∀ C ∈ Ax, ClSupp V C)
    {L : Finset (LEq F)} {s : ℕ} (h : ND Ax L s) : ClSupp V L := by
  induction h with
  | ax hC _ => exact hAx _ hC
  | comb e1 e2 α β _ _ _ _ _ ih1 ih2 =>
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · rcases Finset.mem_union.1 he with he | he
      · exact ih1 e (Finset.mem_of_mem_erase he)
      · exact ih2 e (Finset.mem_of_mem_erase he)
    · rw [Finset.mem_singleton.1 he]
      exact (cmb_support α β e1 e2).trans (Finset.union_subset (ih1 _ (by assumption)) (ih2 _ (by assumption)))
  | fin e1 e2 α β _ _ _ _ _ ih1 ih2 =>
    intro e he
    rcases Finset.mem_union.1 he with he | he
    · exact ih1 e (Finset.mem_of_mem_erase he)
    · exact ih2 e (Finset.mem_of_mem_erase he)

theorem nd_exists_V {Ax : Set (Finset (LEq F))} {L : Finset (LEq F)} {s : ℕ} (h : ND Ax L s) :
    ∃ V : Finset ℕ, ND {C ∈ Ax | ClSupp V C} L s := by
  induction h with
  | @ax C hC hz =>
    refine ⟨C.biUnion fun e => e.1.support, ND.ax ⟨hC, fun e he => ?_⟩ hz⟩
    exact Finset.subset_biUnion_of_mem (fun e : LEq F => e.1.support) he
  | comb e1 e2 α β _ _ h1 h2 hz ih1 ih2 =>
    obtain ⟨V1, d1⟩ := ih1
    obtain ⟨V2, d2⟩ := ih2
    refine ⟨V1 ∪ V2, ND.comb e1 e2 α β (nd_mono_ax ?_ d1) (nd_mono_ax ?_ d2) h1 h2 hz⟩
    · exact fun C hC => ⟨hC.1, fun e he => (hC.2 e he).trans Finset.subset_union_left⟩
    · exact fun C hC => ⟨hC.1, fun e he => (hC.2 e he).trans Finset.subset_union_right⟩
  | fin e1 e2 α β _ _ h1 h2 hz ih1 ih2 =>
    obtain ⟨V1, d1⟩ := ih1
    obtain ⟨V2, d2⟩ := ih2
    refine ⟨V1 ∪ V2, ND.fin e1 e2 α β (nd_mono_ax ?_ d1) (nd_mono_ax ?_ d2) h1 h2 hz⟩
    · exact fun C hC => ⟨hC.1, fun e he => (hC.2 e he).trans Finset.subset_union_left⟩
    · exact fun C hC => ⟨hC.1, fun e he => (hC.2 e he).trans Finset.subset_union_right⟩

end

end RLF

end SATurday.ProofComplexity
