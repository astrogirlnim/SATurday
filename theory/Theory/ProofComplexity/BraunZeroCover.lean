import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# Binary affine zero cover (R4 Phase 2.1, layer 4a)

Credit. Port, with our own proofs, of K. Braun (arXiv 2609.23015, author's Lean development):
`BinaryAffineZeroCover.lean` (`binary_affine_zero_cover`, `binary_affine_halves_translate`) and
the clause vocabulary it introduces (`ParityClause`, `clauseHolds`, `clauseZero`,
`clauseEntails`, `clause_not_holds`, `clause_zero_three`). If `A, B ⊨ D` semantically (both
premises binary, none of them alone entailing `D`), then on the zero set of `D` there is one
literal `u ∈ A` whose 0 and 1 fibers are exactly the zero sets of `A` and `B`; the two halves are
translates. No finite dimensionality is needed. Statements keep his quantifier shape.

LOG: R4 BraunZeroCover module (Phase 2.1 layer 4a)
-/

namespace SATurday.ProofComplexity.BraunPC

noncomputable section

open scoped Affine

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A clause over `V`: a finite set of affine maps `V → F₂`. -/
abbrev ParityClause (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] :=
  Finset (V →ᵃ[ZMod 2] ZMod 2)

/-- The clause is true at `x` when some literal takes value `1`. -/
def clauseHolds (C : ParityClause V) (x : V) : Prop := ∃ g ∈ C, g x = 1

/-- All literals vanish at `x` (the clause is falsified). -/
def clauseZero (C : ParityClause V) (x : V) : Prop := ∀ g ∈ C, g x = 0

/-- Semantic entailment between clauses. -/
def clauseEntails (C D : ParityClause V) : Prop := ∀ x, clauseHolds C x → clauseHolds D x

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

theorem clause_not_holds (C : ParityClause V) (x : V) :
    ¬ clauseHolds C x ↔ clauseZero C x := by
  refine ⟨fun h g hg => ?_, fun h ⟨g, hg, h1⟩ => ?_⟩
  · exact (zmod2_cases (g x)).resolve_right fun h1 => h ⟨g, hg, h1⟩
  · have := h g hg
    rw [h1] at this
    exact one_ne_zero this

theorem parity_three (g : V →ᵃ[ZMod 2] ZMod 2) (a b x : V) :
    g (a - b + x) = g a - g b + g x :=
  (g.map_vadd x (a - b)).trans (congrArg (· + g x) (g.linearMap_vsub a b))

theorem clause_zero_three (C : ParityClause V) {a b x : V}
    (ha : clauseZero C a) (hb : clauseZero C b) (hx : clauseZero C x) :
    clauseZero C (a - b + x) := by
  intro g hg
  rw [parity_three, ha g hg, hb g hg, hx g hg]
  simp

theorem binary_affine_zero_cover (A B D : ParityClause V)
    (sound : ∀ x, clauseHolds A x → clauseHolds B x → clauseHolds D x)
    (notA : ¬ clauseEntails A D) (notB : ¬ clauseEntails B D) :
    ∃ u ∈ A, ∃ a b : V,
      clauseZero D a ∧ clauseZero D b ∧ u a = 1 ∧ u b = 0 ∧
      ∀ x, clauseZero D x →
        (clauseZero A x ↔ u x = 0) ∧ (clauseZero B x ↔ u x = 1) := by
  classical
  have cover (x : V) (hx : clauseZero D x) : clauseZero A x ∨ clauseZero B x := by
    by_cases ha : clauseHolds A x
    · exact Or.inr ((clause_not_holds B x).mp fun hb =>
        (clause_not_holds D x).mpr hx (sound x ha hb))
    · exact Or.inl ((clause_not_holds A x).mp ha)
  obtain ⟨a, ha, hda⟩ : ∃ a, clauseHolds A a ∧ ¬ clauseHolds D a := by
    simpa [clauseEntails, not_forall] using notA
  obtain ⟨b, hb, hdb⟩ : ∃ b, clauseHolds B b ∧ ¬ clauseHolds D b := by
    simpa [clauseEntails, not_forall] using notB
  have zda := (clause_not_holds D a).mp hda
  have zdb := (clause_not_holds D b).mp hdb
  have zba : clauseZero B a := (clause_not_holds B a).mp fun h => hda (sound a ha h)
  have zab : clauseZero A b := (clause_not_holds A b).mp fun h => hdb (sound b h hb)
  obtain ⟨u, hu, hua⟩ := ha
  obtain ⟨v, hv, hvb⟩ := hb
  have hub := zab u hu
  have key (x : V) (hx : clauseZero D x) (hbx : clauseZero B x) : u x = 1 := by
    rcases zmod2_cases (u x) with h0 | h1
    · have hz := clause_zero_three D zda zdb hx
      have huz : u (a - b + x) = 1 := by rw [parity_three, hua, hub, h0]; simp
      have hvz : v (a - b + x) = 1 := by rw [parity_three, zba v hv, hvb, hbx v hv]; decide
      exact absurd (sound _ ⟨u, hu, huz⟩ ⟨v, hv, hvz⟩) ((clause_not_holds D _).mpr hz)
    · exact h1
  refine ⟨u, hu, a, b, zda, zdb, hua, hub, fun x hx => ⟨⟨fun h => h u hu, fun h0 => ?_⟩,
    ⟨key x hx, fun h1 => ?_⟩⟩⟩
  · rcases cover x hx with hA | hB
    · exact hA
    · exact absurd (h0.symm.trans (key x hx hB)) zero_ne_one
  · rcases cover x hx with hA | hB
    · exact absurd (h1.symm.trans (hA u hu)) one_ne_zero
    · exact hB

theorem binary_affine_halves_translate (A B D : ParityClause V)
    (sound : ∀ x, clauseHolds A x → clauseHolds B x → clauseHolds D x)
    (notA : ¬ clauseEntails A D) (notB : ¬ clauseEntails B D) :
    ∃ a b : V, ∃ e : {x : V // clauseZero D x ∧ clauseZero A x} ≃
        {x : V // clauseZero D x ∧ clauseZero B x},
      ∀ x, (e x).val = a - b + x.val := by
  obtain ⟨u, _, a, b, hda, hdb, hua, hub, fibers⟩ := binary_affine_zero_cover A B D sound notA notB
  have flipA (x : V) (hx : clauseZero D x ∧ clauseZero A x) :
      clauseZero D (a - b + x) ∧ clauseZero B (a - b + x) := by
    have hd := clause_zero_three D hda hdb hx.1
    refine ⟨hd, (fibers _ hd).2.mpr ?_⟩
    rw [parity_three, hua, hub, (fibers x hx.1).1.mp hx.2]
    simp
  have flipB (x : V) (hx : clauseZero D x ∧ clauseZero B x) :
      clauseZero D (a - b + x) ∧ clauseZero A (a - b + x) := by
    have hd := clause_zero_three D hda hdb hx.1
    refine ⟨hd, (fibers _ hd).1.mpr ?_⟩
    rw [parity_three, hua, hub, (fibers x hx.1).2.mp hx.2]
    decide
  have twice (x : V) : a - b + (a - b + x) = x := by
    rw [← add_assoc, ZModModule.add_self, zero_add]
  exact ⟨a, b, { toFun := fun x => ⟨a - b + x.val, flipA x.val x.property⟩
                 invFun := fun x => ⟨a - b + x.val, flipB x.val x.property⟩
                 left_inv := fun x => Subtype.ext (twice x.val)
                 right_inv := fun x => Subtype.ext (twice x.val) }, fun _ => rfl⟩

end

end SATurday.ProofComplexity.BraunPC
