import Theory.ProofComplexity.ClosurePivot
import Theory.ProofComplexity.ResLinGame

/-!
# Lifting a Duplicator strategy through MAJ₃: the solving lemmas (Alekseev–Itsykson, ECCC TR24-128,
# Lemmas 2.9 and 2.10)

Systems are finite sets of equations `(g, a)` with `g` a finitely supported form. Block of the
variable `w` is `w / 3`, and the gadget is `MAJ₃` (`maj`, 1-stifling).

LOG: R4 Lift module (solving safe systems with prescribed gadget values)
-/

namespace SATurday.ProofComplexity

namespace RL

noncomputable section

open Classical
open Finset

abbrev Frm := ℕ →₀ ZMod 2

/-- Evaluation of a form on an assignment. -/
def ev (x : ℕ → ZMod 2) : Frm →ₗ[ZMod 2] ZMod 2 := Finsupp.linearCombination (ZMod 2) x

theorem ev_apply (x : ℕ → ZMod 2) (f : Frm) : ev x f = ∑ w ∈ f.support, f w * x w := by
  unfold ev
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  simp [smul_eq_mul]

theorem ev_add_assign (x y : ℕ → ZMod 2) (f : Frm) : ev (x + y) f = ev x f + ev y f := by
  simp only [ev_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ev_smul_assign (c : ZMod 2) (x : ℕ → ZMod 2) (f : Frm) : ev (c • x) f = c * ev x f := by
  simp only [ev_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _; ring

theorem ev_single_assign (u : ℕ) (f : Frm) : ev (Pi.single u 1) f = f u := by
  rw [ev_apply]
  by_cases hu : u ∈ f.support
  · rw [Finset.sum_eq_single u]
    · simp
    · intro w _ hw; simp [Pi.single_apply, hw]
    · intro h; exact absurd hu h
  · have : f u = 0 := Finsupp.notMem_support_iff.1 hu
    rw [this]
    apply Finset.sum_eq_zero
    intro w hw
    have : w ≠ u := fun h => hu (h ▸ hw)
    simp [Pi.single_apply, this]

/-- The form of a finite set of variables. -/
def fv (S : Finset ℕ) : Frm := ∑ w ∈ S, Finsupp.single w 1

theorem fv_apply (S : Finset ℕ) (w : ℕ) : fv S w = if w ∈ S then 1 else 0 := by
  unfold fv
  rw [Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

theorem ev_fv (x : ℕ → ZMod 2) (S : Finset ℕ) : ev x (fv S) = lf S x := by
  unfold fv lf
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro w _
  simp [ev]

theorem ev_zero_assign (f : Frm) : ev (0 : ℕ → ZMod 2) f = 0 := by simp [ev_apply]

theorem ev_sum_assign {J : Type*} (s : Finset J) (xs : J → ℕ → ZMod 2) (f : Frm) :
    ev (∑ j ∈ s, xs j) f = ∑ j ∈ s, ev (xs j) f := by
  induction s using Finset.induction_on with
  | empty => simp [ev_zero_assign]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ev_add_assign, ih]

/-- Systems: finite sets of equations `ev x g = a`. -/
abbrev Sys := Finset (Frm × ZMod 2)

def satSys (E : Sys) (x : ℕ → ZMod 2) : Prop := ∀ e ∈ E, ev x e.1 = e.2

/-- The space spanned by the left sides of a system. -/
def forms (E : Sys) : Submodule (ZMod 2) Frm :=
  Submodule.span (ZMod 2) ((E.image Prod.fst : Finset Frm) : Set Frm)

/-- The block of a lifted variable (`MAJ₃` blocks have three variables). -/
def blkOf (w : ℕ) : ℕ := w / 3

instance finDimForms (E : Sys) : FiniteDimensional (ZMod 2) (forms E) :=
  FiniteDimensional.span_of_finite (ZMod 2) (Finset.finite_toSet _)

def majZ (a b c : ZMod 2) : Bool := decide ((a = 1 ∧ b = 1) ∨ (a = 1 ∧ c = 1) ∨ (b = 1 ∧ c = 1))

theorem maj_eq (x : ℕ → ZMod 2) (v : ℕ) : maj x v = majZ (x (lv v 0)) (x (lv v 1)) (x (lv v 2)) := rfl

theorem majZ_two : ∀ (a b c : ZMod 2) (s : Bool),
    (a = bv s → b = bv s → majZ a b c = s) ∧ (a = bv s → c = bv s → majZ a b c = s) ∧
    (b = bv s → c = bv s → majZ a b c = s) := by decide

theorem maj_of_two (x : ℕ → ZMod 2) (v : ℕ) (s : Bool) (k1 k2 : ℕ) (h1 : k1 < 3) (h2 : k2 < 3)
    (hne : k1 ≠ k2) (e1 : x (lv v k1) = bv s) (e2 : x (lv v k2) = bv s) : maj x v = s := by
  rw [maj_eq]
  have := majZ_two (x (lv v 0)) (x (lv v 1)) (x (lv v 2)) s
  unfold lv at *
  interval_cases k1 <;> interval_cases k2 <;> simp at hne <;> simp_all

theorem exists_solution {k : ℕ} (M : Fin k → Fin k → ZMod 2)
    (hli : LinearIndependent (ZMod 2) (fun j => fun i => M i j)) (a : Fin k → ZMod 2) :
    ∃ c : Fin k → ZMod 2, ∀ i, ∑ j, M i j * c j = a i := by
  let L : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) := Matrix.mulVecLin (Matrix.of M)
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h1 : ∑ j, c j • (fun i => M i j) = 0 := by
      funext i
      have := congrFun hc i
      simp only [L, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply,
        Matrix.of_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm]
    funext j
    exact Fintype.linearIndependent_iff.1 hli c h1 j
  obtain ⟨c, hc⟩ := (LinearMap.injective_iff_surjective.1 hinj) a
  refine ⟨c, fun i => ?_⟩
  have := congrFun hc i
  simpa [L, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] using this

theorem two_good (P : ℕ → Prop) (amo : ∀ k k', k < 3 → k' < 3 → P k → P k' → k = k') :
    ∃ k1 k2, k1 < 3 ∧ k2 < 3 ∧ k1 ≠ k2 ∧ ¬ P k1 ∧ ¬ P k2 := by
  by_cases p0 : P 0
  · refine ⟨1, 2, by omega, by omega, by omega, fun h => ?_, fun h => ?_⟩
    · exact absurd (amo 0 1 (by omega) (by omega) p0 h) (by omega)
    · exact absurd (amo 0 2 (by omega) (by omega) p0 h) (by omega)
  · by_cases p1 : P 1
    · refine ⟨0, 2, by omega, by omega, by omega, p0, fun h => ?_⟩
      exact absurd (amo 1 2 (by omega) (by omega) p1 h) (by omega)
    · exact ⟨0, 1, by omega, by omega, by omega, p0, p1⟩

theorem solve_gadget (E : Sys) (x0 : ℕ → ZMod 2) (h0 : satSys E x0)
    (hs : Closure.Safe blkOf (forms E)) (σ : ℕ → Bool) :
    ∃ τ : ℕ → ZMod 2, satSys E τ ∧ ∀ v, maj τ v = σ v := by
  let bs := Module.finBasis (ZMod 2) (forms E)
  set k := Module.finrank (ZMod 2) (forms E) with hk
  let f : Fin k → Frm := fun i => (bs i : Frm)
  have hli : LinearIndependent (ZMod 2) f :=
    bs.linearIndependent.map' (forms E).subtype (Submodule.ker_subtype _)
  have hfW : ∀ i, f i ∈ forms E := fun i => (bs i).2
  have hspan : Submodule.span (ZMod 2) (Set.range f) ≤ forms E :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hfW i)
  have hsafe : Closure.Safe blkOf (Submodule.span (ZMod 2) (Set.range f)) :=
    Closure.Safe.mono blkOf hs hspan
  obtain ⟨z, hzb, hzli⟩ := Closure.pivot blkOf f hli hsafe
  have hzinj : Function.Injective z := fun j j' h => hzb (by simp [Function.comp, h])
  let τ1 : ℕ → ZMod 2 := fun w => if w ∈ Set.range z then 0 else bv (σ (w / 3))
  obtain ⟨c, hc⟩ := exists_solution (fun i j => f i (z j)) hzli (fun i => ev x0 (f i) - ev τ1 (f i))
  let τ : ℕ → ZMod 2 := τ1 + ∑ j, c j • (Pi.single (z j) 1 : ℕ → ZMod 2)
  have hτf : ∀ i, ev τ (f i) = ev x0 (f i) := by
    intro i
    simp only [τ, ev_add_assign, ev_sum_assign, ev_smul_assign, ev_single_assign]
    have := hc i
    simp only at this
    have h2 : ∑ j, c j * f i (z j) = ev x0 (f i) - ev τ1 (f i) := by
      rw [← this]; apply Finset.sum_congr rfl; intro j _; ring
    rw [h2]; ring
  have htr : ∀ g ∈ forms E, ev τ g = ev x0 g := by
    intro g hg
    have hrep := congrArg Subtype.val (bs.sum_repr ⟨g, hg⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hrep
    rw [← hrep, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, map_smul, hτf i]
  refine ⟨τ, fun e he => ?_, fun v => ?_⟩
  · have : e.1 ∈ forms E := Submodule.subset_span (by simp only [coe_image]; exact ⟨e, he, rfl⟩)
    rw [htr _ this]; exact h0 e he
  · -- the block of `v` has at most one pivot
    have amo : ∀ k k', k < 3 → k' < 3 → (∃ j, z j = lv v k) → (∃ j, z j = lv v k') → k = k' := by
      intro k k' hk hk' ⟨j, hj⟩ ⟨j', hj'⟩
      have h1 : blkOf (z j) = v := by rw [hj]; unfold blkOf lv; omega
      have h2 : blkOf (z j') = v := by rw [hj']; unfold blkOf lv; omega
      have : j = j' := hzb (h1.trans h2.symm)
      subst this
      rw [hj] at hj'; unfold lv at hj'; omega
    obtain ⟨k1, k2, hk1, hk2, hne, p1, p2⟩ := two_good (fun k => ∃ j, z j = lv v k) amo
    have val : ∀ k, k < 3 → ¬ (∃ j, z j = lv v k) → τ (lv v k) = bv (σ v) := by
      intro k hk hP
      have hnot : lv v k ∉ Set.range z := fun ⟨j, hj⟩ => hP ⟨j, hj⟩
      simp only [τ, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, τ1, if_pos, if_neg hnot]
      have : ∀ j, (if lv v k = z j then (1 : ZMod 2) else 0) = 0 := by
        intro j; rw [if_neg]; intro h; exact hP ⟨j, h.symm⟩
      simp only [this, smul_zero, Finset.sum_const_zero, add_zero]
      have : lv v k / 3 = v := by unfold lv; omega
      rw [this]
    exact maj_of_two τ v (σ v) k1 k2 hk1 hk2 hne (val k1 hk1 p1) (val k2 hk2 p2)

theorem ev_apply_of_subset (x : ℕ → ZMod 2) (f : Frm) {s : Finset ℕ} (hs : f.support ⊆ s) :
    ev x f = ∑ w ∈ s, f w * x w := by
  rw [ev_apply]
  apply Finset.sum_subset hs
  intro w _ hw
  rw [Finsupp.notMem_support_iff.1 hw]; simp

/-- Solving a system whose gadget values are prescribed outside the closure
(Alekseev–Itsykson, Lemma 2.10). -/
theorem solve_closure (E : Sys) (σ0 : ℕ → ZMod 2) (h0 : satSys E σ0) (π : ℕ → Bool)
    (hπ : ∀ v ∈ Closure.cl blkOf (forms E), π v = maj σ0 v) :
    ∃ τ : ℕ → ZMod 2, satSys E τ ∧ ∀ v, maj τ v = π v := by
  set C := Closure.cl blkOf (forms E) with hC
  let P : Frm →ₗ[ZMod 2] Frm := Closure.proj blkOf C
  let E' : Sys := E.image (fun e => (P e.1, e.2 - ev σ0 (e.1 - P e.1)))
  have hforms : forms E' = (forms E).map P := by
    unfold forms
    rw [Submodule.map_span]
    congr 1
    simp only [E', Finset.image_image, Finset.coe_image, Set.image_image]
    rfl
  have hsafe : Closure.Safe blkOf (forms E') := by
    rw [hforms]; exact Closure.cl_safe blkOf (forms E)
  have hsplit : ∀ x g, ev x g = ev x (P g) + ev x (g - P g) := by
    intro x g; rw [← map_add]; simp
  have h0' : satSys E' σ0 := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 he'
    simp only
    have := h0 e he
    rw [hsplit σ0 e.1] at this
    rw [← this]; ring
  obtain ⟨γ, hγ, hγm⟩ := solve_gadget E' σ0 h0' hsafe π
  let τ : ℕ → ZMod 2 := fun w => if blkOf w ∈ C then σ0 w else γ w
  have hev : ∀ g : Frm, ev τ g = ev γ (P g) + ev σ0 (g - P g) := by
    intro g
    have hP : (P g).support ⊆ g.support := by
      intro w hw
      rw [Finsupp.mem_support_iff] at hw ⊢
      intro h0; apply hw
      simp [P, Closure.proj_apply, h0]
    have hQ : (g - P g).support ⊆ g.support := by
      intro w hw
      rw [Finsupp.mem_support_iff] at hw ⊢
      intro h0; apply hw
      simp [P, Closure.proj_apply, h0]
    rw [ev_apply_of_subset τ g (Finset.Subset.refl _), ev_apply_of_subset γ (P g) hP,
      ev_apply_of_subset σ0 (g - P g) hQ, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : blkOf w ∈ C
    · simp [τ, P, Closure.proj_apply, hw]
    · simp [τ, P, Closure.proj_apply, hw]
  refine ⟨τ, fun e he => ?_, fun v => ?_⟩
  · have := hγ _ (Finset.mem_image_of_mem _ he)
    simp only at this
    rw [hev, this]; ring
  · by_cases hv : v ∈ C
    · have : maj τ v = maj σ0 v := by
        unfold maj
        have : ∀ k, k < 3 → τ (lv v k) = σ0 (lv v k) := by
          intro k hk
          have : blkOf (lv v k) = v := by unfold blkOf lv; omega
          simp [τ, this, hv]
        simp only [this 0 (by omega), this 1 (by omega), this 2 (by omega)]
      rw [this, hπ v hv]
    · have : maj τ v = maj γ v := by
        unfold maj
        have : ∀ k, k < 3 → τ (lv v k) = γ (lv v k) := by
          intro k hk
          have : blkOf (lv v k) = v := by unfold blkOf lv; omega
          simp [τ, this, hv]
        simp only [this 0 (by omega), this 1 (by omega), this 2 (by omega)]
      rw [this, hγm v]

end

end RL

end SATurday.ProofComplexity
