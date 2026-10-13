import Theory.ProofComplexity.BraunZeroCover
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Clause compression and binary semantic cover (R4 Phase 2.1, layer 4b)

Credit. Port, with our own proofs, of K. Braun (arXiv 2609.23015, author's Lean development):
`AffineClauseCompression.lean` (`affine_clause_basis_compression`,
`affine_clause_registry_compression`) and `BinarySemanticAffineCover.lean`
(`binary_semantic_affine_cover`, `ParityDerivation`, `binary_semantic_three_steps`,
`parity_derivation_sound`, `binary_auxiliary_count`, `binary_semantic_restriction`,
`binary_semantic_compressed`). Every clause has an equivalent subclause with at most `dim V + 1`
literals; a binary semantic inference is one weakening or two weakenings plus one resolution.

LOG: R4 BraunClauseCover module (Phase 2.1 layer 4b)
-/

namespace SATurday.ProofComplexity.BraunPC

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem clause_zero_span (C : ParityClause V) (x : V) (hx : clauseZero C x)
    (g : V →ᵃ[ZMod 2] ZMod 2)
    (hg : g ∈ Submodule.span (ZMod 2) (C : Set (V →ᵃ[ZMod 2] ZMod 2))) : g x = 0 := by
  let ev : (V →ᵃ[ZMod 2] ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun f => f x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hs : Submodule.span (ZMod 2) (C : Set (V →ᵃ[ZMod 2] ZMod 2)) ≤ LinearMap.ker ev :=
    Submodule.span_le.mpr fun f hf => hx f hf
  exact hs hg

theorem affine_clause_basis_compression [FiniteDimensional (ZMod 2) V]
    (C : ParityClause V) :
    ∃ S : ParityClause V, S ⊆ C ∧ S.card ≤ Module.finrank (ZMod 2) V + 1 ∧
      ∀ x, clauseHolds S x ↔ clauseHolds C x := by
  classical
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent (ZMod 2)
    (C : Set (V →ᵃ[ZMod 2] ZMod 2))
  have hfinite : s.Finite := C.finite_toSet.subset hs
  let S : ParityClause V := hfinite.toFinset
  have hSC : S ⊆ C := by simpa [S] using hs
  have hspanS : Submodule.span (ZMod 2) (S : Set (V →ᵃ[ZMod 2] ZMod 2)) =
      Submodule.span (ZMod 2) (C : Set (V →ᵃ[ZMod 2] ZMod 2)) := by simpa [S] using hspan
  have hliS : LinearIndependent (ZMod 2) (fun g : S => (g : V →ᵃ[ZMod 2] ZMod 2)) :=
    hli.comp (fun g : S => (⟨g.val, hfinite.mem_toFinset.mp g.property⟩ : s))
      (fun x y h => Subtype.ext (congrArg (fun z : s => z.val) h))
  refine ⟨S, hSC, ?_, fun x => ?_⟩
  · simpa [AffineMap.finrank_eq] using hliS.finset_card_le_finrank
  · have zeros : clauseZero S x ↔ clauseZero C x :=
      ⟨fun h g hg => clause_zero_span S x h g (hspanS ▸ Submodule.subset_span hg),
       fun h g hg => h g (hSC hg)⟩
    simpa only [← clause_not_holds, not_not] using not_congr zeros

theorem affine_clause_registry_compression [FiniteDimensional (ZMod 2) V]
    (N : ℕ) (C : Fin N → ParityClause V) :
    ∃ S : Fin N → ParityClause V,
      (∀ i, S i ⊆ C i ∧ (S i).card ≤ Module.finrank (ZMod 2) V + 1 ∧
        ∀ x, clauseHolds (S i) x ↔ clauseHolds (C i) x) ∧
      (∑ i, (S i).card * (Module.finrank (ZMod 2) V + 1)) ≤
        N * (Module.finrank (ZMod 2) V + 1) ^ 2 := by
  classical
  choose S hS using fun i => affine_clause_basis_compression (C i)
  refine ⟨S, hS, ?_⟩
  calc
    _ ≤ ∑ _i : Fin N, (Module.finrank (ZMod 2) V + 1) ^ 2 :=
      Finset.sum_le_sum fun i _ => by
        simpa [pow_two] using Nat.mul_le_mul_right (Module.finrank (ZMod 2) V + 1) (hS i).2.1
    _ = _ := by simp

local instance : DecidableEq (V →ᵃ[ZMod 2] ZMod 2) := Classical.decEq _

/-- The complementary literal `1 - u`. -/
def oppositeParity (u : V →ᵃ[ZMod 2] ZMod 2) : V →ᵃ[ZMod 2] ZMod 2 :=
  AffineMap.const (ZMod 2) V 1 - u

@[simp] theorem oppositeParity_apply (u : V →ᵃ[ZMod 2] ZMod 2) (x : V) :
    oppositeParity u x = 1 - u x := rfl

theorem clause_holds_insert (C : ParityClause V) (u : V →ᵃ[ZMod 2] ZMod 2) (x : V) :
    clauseHolds (insert u C) x ↔ u x = 1 ∨ clauseHolds C x := by
  simp [clauseHolds]

theorem binary_semantic_affine_cover (A B D : ParityClause V)
    (sound : ∀ x, clauseHolds A x → clauseHolds B x → clauseHolds D x) :
    clauseEntails A D ∨ clauseEntails B D ∨
      ∃ u ∈ A, clauseEntails A (insert u D) ∧
        clauseEntails B (insert (oppositeParity u) D) := by
  by_cases hA : clauseEntails A D
  · exact Or.inl hA
  by_cases hB : clauseEntails B D
  · exact Or.inr (Or.inl hB)
  obtain ⟨u, hu, a, b, hda, hdb, hua, hub, fibers⟩ := binary_affine_zero_cover A B D sound hA hB
  refine Or.inr (Or.inr ⟨u, hu, fun x hx => ?_, fun x hx => ?_⟩)
  · refine (clause_holds_insert D u x).mpr ?_
    by_cases hd : clauseHolds D x
    · exact Or.inr hd
    · have hz := (clause_not_holds D x).mp hd
      exact Or.inl ((fibers x hz).2.mp ((clause_not_holds B x).mp fun h => hd (sound x hx h)))
  · refine (clause_holds_insert D (oppositeParity u) x).mpr ?_
    by_cases hd : clauseHolds D x
    · exact Or.inr hd
    · have hz := (clause_not_holds D x).mp hd
      have ha := (clause_not_holds A x).mp fun h => hd (sound x h hx)
      left
      simp [oppositeParity_apply, (fibers x hz).1.mp ha]

/-- Basic rules only: premises, semantic weakening, and resolution with a shared context;
the natural number counts new inference nodes. -/
inductive ParityDerivation (A B : ParityClause V) : ParityClause V → ℕ → Prop
  | leftPremise : ParityDerivation A B A 0
  | rightPremise : ParityDerivation A B B 0
  | weaken {C D : ParityClause V} {n : ℕ} : ParityDerivation A B C n →
      clauseEntails C D → ParityDerivation A B D (n + 1)
  | resolve {D : ParityClause V} {u : V →ᵃ[ZMod 2] ZMod 2} {n m : ℕ} :
      ParityDerivation A B (insert u D) n →
      ParityDerivation A B (insert (oppositeParity u) D) m →
      ParityDerivation A B D (n + m + 1)

theorem binary_semantic_three_steps (A B D : ParityClause V)
    (sound : ∀ x, clauseHolds A x → clauseHolds B x → clauseHolds D x) :
    ∃ n ≤ 3, ParityDerivation A B D n := by
  rcases binary_semantic_affine_cover A B D sound with hA | hB | ⟨u, _, hA, hB⟩
  · exact ⟨1, by decide, .weaken .leftPremise hA⟩
  · exact ⟨1, by decide, .weaken .rightPremise hB⟩
  · exact ⟨3, by decide, .resolve (.weaken .leftPremise hA) (.weaken .rightPremise hB)⟩

theorem parity_derivation_sound {A B D : ParityClause V} {n : ℕ}
    (proof : ParityDerivation A B D n) :
    ∀ x, clauseHolds A x → clauseHolds B x → clauseHolds D x := by
  induction proof with
  | leftPremise => exact fun _ h _ => h
  | rightPremise => exact fun _ _ h => h
  | weaken _ h ih => exact fun x ha hb => h x (ih x ha hb)
  | resolve _ _ ih₁ ih₂ =>
    intro x ha hb
    rcases (clause_holds_insert _ _ _).mp (ih₁ x ha hb) with hu | hd
    · rcases (clause_holds_insert _ _ _).mp (ih₂ x ha hb) with hv | hd
      · simp [oppositeParity_apply, hu] at hv
      · exact hd
    · exact hd

/-- The two auxiliary clauses of a resolution step. -/
def binaryAuxiliaryClauses (D : ParityClause V) (u : V →ᵃ[ZMod 2] ZMod 2) :
    Finset (ParityClause V) := {insert u D, insert (oppositeParity u) D}

theorem binary_auxiliary_count (D : ParityClause V) (u : V →ᵃ[ZMod 2] ZMod 2) :
    (binaryAuxiliaryClauses D u).card ≤ 2 ∧
      ∀ C ∈ binaryAuxiliaryClauses D u, C.card ≤ D.card + 1 := by
  refine ⟨(Finset.card_insert_le _ _).trans (by simp), fun C hC => ?_⟩
  simp only [binaryAuxiliaryClauses, Finset.mem_insert, Finset.mem_singleton] at hC
  rcases hC with rfl | rfl <;> exact Finset.card_insert_le _ _

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

/-- Pull a clause back along an affine map. -/
def restrictParityClause (C : ParityClause V) (f : U →ᵃ[ZMod 2] V) : ParityClause U :=
  Finset.image (fun g => g.comp f) C

theorem restrict_clause_holds (C : ParityClause V) (f : U →ᵃ[ZMod 2] V) (x : U) :
    clauseHolds (restrictParityClause C f) x ↔ clauseHolds C (f x) := by
  classical
  simp [clauseHolds, restrictParityClause, AffineMap.coe_comp]

theorem binary_semantic_restriction (A B D : ParityClause V)
    (sound : ∀ x, clauseHolds A x → clauseHolds B x → clauseHolds D x)
    (f : U →ᵃ[ZMod 2] V) :
    ∀ x, clauseHolds (restrictParityClause A f) x →
      clauseHolds (restrictParityClause B f) x → clauseHolds (restrictParityClause D f) x :=
  fun x ha hb => (restrict_clause_holds D f x).mpr
    (sound (f x) ((restrict_clause_holds A f x).mp ha) ((restrict_clause_holds B f x).mp hb))

theorem binary_semantic_compressed [FiniteDimensional (ZMod 2) V]
    (A B D : ParityClause V)
    (sound : ∀ x, clauseHolds A x → clauseHolds B x → clauseHolds D x) :
    ∃ A' B' D' : ParityClause V,
      A'.card ≤ Module.finrank (ZMod 2) V + 1 ∧
      B'.card ≤ Module.finrank (ZMod 2) V + 1 ∧
      D'.card ≤ Module.finrank (ZMod 2) V + 1 ∧
      (∀ x, clauseHolds A' x ↔ clauseHolds A x) ∧
      (∀ x, clauseHolds B' x ↔ clauseHolds B x) ∧
      (∀ x, clauseHolds D' x ↔ clauseHolds D x) ∧
      ∃ n ≤ 3, ParityDerivation A' B' D' n := by
  obtain ⟨A', _, hA, eA⟩ := affine_clause_basis_compression A
  obtain ⟨B', _, hB, eB⟩ := affine_clause_basis_compression B
  obtain ⟨D', _, hD, eD⟩ := affine_clause_basis_compression D
  refine ⟨A', B', D', hA, hB, hD, eA, eB, eD, binary_semantic_three_steps _ _ _ ?_⟩
  exact fun x ha hb => (eD x).mpr (sound x ((eA x).mp ha) ((eB x).mp hb))

end

end SATurday.ProofComplexity.BraunPC
