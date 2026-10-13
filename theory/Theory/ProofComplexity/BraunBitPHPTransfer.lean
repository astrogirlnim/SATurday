import Theory.ProofComplexity.BraunBitPHPInitial

/-!
# Bit pigeonhole clause transfer to ordinary PC (R4 Phase 2.1, layer 5d)

Credit. Port, with our own proofs, of K. Braun (arXiv 2609.23015, author's Lean development):
`BitPHPClauseTransfer.lean` (`pigeonPair_card`, `compact_bitPHP_PC_transfer`,
`usual_bitPHP_PC_transfer`): a finite affine dag refuting the compact pair clauses, or the usual
bit PHP clauses, with `S` nodes yields one fixed complete old affine registry with at most
`3S + C(m,2)` slots, clause width at most `max ℓ (m ℓ + 2)`, an explicit variable count, and an
ordinary PC refutation (derivation of `1`) of degree `max (2h+ℓ) (4h+1)` from the compact base.

Not ported: his `registry_system_eq_ensFamily` (identification with the family removal interface)
is a restatement already available through `BraunENSRemoval`; it will be added when layer 8 needs it.

Conversion (ours). His dag type `AffineDAG` is `Type` valued (it carries the justification data);
our bridge `RL.Braun.PDag` is `Prop` valued. `pdag_to_affineDAG` converts by classical choice
(`Nonempty`), so `usual_bitPHP_PC_transfer_of_pdag` and `bphp_dagRefutes_PC_transfer` apply to
`RL.DagRefutes` directly.

LOG: R4 BraunBitPHPTransfer module (Phase 2.1 layer 5d)
-/

namespace SATurday.ProofComplexity.BraunPC

noncomputable section

open SATurday.ProofComplexity.RL.Braun (BitVar usualCNFClause usualInitials)
open scoped BigOperators

local instance transferClauseDecidableEq {σ : Type} :
    DecidableEq ((σ → ZMod 2) →ᵃ[ZMod 2] ZMod 2) := Classical.decEq _

/-! ## From the `Prop` valued bridge dag to the `Type` valued dag -/

section Convert

variable {σ : Type} {S : ℕ}

/-- Every `Prop` valued step is inhabited by a `Type` valued one. -/
theorem pstep_nonempty {I : Set (FiniteParityClause σ)} {C : Fin S → FiniteParityClause σ}
    {i : Fin S} (h : RL.Braun.PStep I C i) : Nonempty (AffineDAGStep I C i) := by
  cases h with
  | initial hi => exact ⟨.initial hi⟩
  | weaken a ha he => exact ⟨.weaken a ha he⟩
  | resolve a b A B u ha hb h1 h2 h3 => exact ⟨.resolve a b A B u ha hb h1 h2 h3⟩
  | binary a b ha hb hs => exact ⟨.binary a b ha hb hs⟩

/-- A `Prop` valued dag of the bridge file yields Braun's `Type` valued `AffineDAG`. -/
theorem pdag_to_affineDAG {I : Set (FiniteParityClause σ)} {C : Fin S → FiniteParityClause σ}
    (h : RL.Braun.PDag I C) : Nonempty (AffineDAG I C) :=
  ⟨⟨fun i => Classical.choice (pstep_nonempty (h i))⟩⟩

end Convert

/-! ## The transfer -/

abbrev PigeonPair (m : ℕ) := {p : Fin m × Fin m // p.1 < p.2}

theorem pigeonPair_card (m : ℕ) : Fintype.card (PigeonPair m) = m.choose 2 := by
  change Fintype.card {p : Fin m × Fin m // p.1 < p.2} = m.choose 2
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  have h1 : ∀ i : Fin m, (∑ j : Fin m, if i < j then 1 else 0) = m - 1 - i.val := by
    intro i
    rw [← Finset.card_filter]
    have : (Finset.univ.filter (fun j : Fin m => i < j)) = Finset.Ioi i := by ext; simp
    rw [this, Fin.card_Ioi]
  simp only [h1]
  rw [Fin.sum_univ_eq_sum_range (fun i => m - 1 - i) m]
  have hr := Finset.sum_range_reflect (fun j => j) m
  simp only at hr
  rw [hr]
  have h2 := Finset.sum_range_id_mul_two m
  rw [Nat.choose_two_right]
  omega

def compactPairInitials (m ℓ : ℕ) : Set (FiniteParityClause (BitVar m ℓ)) :=
  {C | ∃ i i' : Fin m, i < i' ∧ C = compactPairClause (ℓ := ℓ) i i'}

private def pairInitialFamily (m ℓ : ℕ) (p : PigeonPair m) : FiniteParityClause (BitVar m ℓ) :=
  compactPairClause p.val.1 p.val.2

private theorem pairInitial_width (m ℓ : ℕ) (p : PigeonPair m) :
    (pairInitialFamily m ℓ p).card ≤ ℓ := by
  exact (Finset.card_image_le).trans (by simp)

private theorem bitPHP_transfer_of_cover {m ℓ S : ℕ}
    (I : Set (FiniteParityClause (BitVar m ℓ))) (C : Fin S → FiniteParityClause (BitVar m ℓ))
    (dag : AffineDAG I C) (finish : Fin S) (hempty : C finish = ∅)
    (cover : ∀ A ∈ I, ∃ p : PigeonPair m, clauseEntails (pairInitialFamily m ℓ p) A)
    (h : ℕ) (hh : 1 ≤ h) :
    ∃ (N : ℕ) (R : Fin N → FiniteParityClause (BitVar m ℓ)),
      N ≤ 3 * S + m.choose 2 ∧
      (∀ c, (R c).card ≤ max ℓ (m * ℓ + 2)) ∧
      (∑ c, (R c).card) ≤ N * max ℓ (m * ℓ + 2) ∧
      Fintype.card (ClauseRegistryVars R h) ≤ m * ℓ + h * N * max ℓ (m * ℓ + 2) ∧
      Derives (registrySystem R h (compactBitBase m ℓ)) (max (2 * h + ℓ) (4 * h + 1)) 1 := by
  obtain ⟨N, R, initial, node, hN, hinit, hnode, hwidth, replay⟩ :=
    affine_dag_registry I C dag (pairInitialFamily m ℓ) ℓ (pairInitial_width m ℓ) cover
  have hw : ∀ c, (R c).card ≤ max ℓ (m * ℓ + 2) := by
    simpa only [RL.Braun.BitVar, Fintype.card_prod, Fintype.card_fin] using hwidth
  have hinv := registry_inventory_bound R h (max ℓ (m * ℓ + 2)) hw
  have hv : Fintype.card (ClauseRegistryVars R h) ≤ m * ℓ + h * N * max ℓ (m * ℓ + 2) := by
    simpa only [RL.Braun.BitVar, Fintype.card_prod, Fintype.card_fin] using hinv.2
  refine ⟨N, R, ?_, hw, hinv.1, hv, ?_⟩
  · rw [hN, pigeonPair_card]
  · have hi (p : PigeonPair m) :
        Derives (registrySystem R h (compactBitBase m ℓ)) (max (2 * h + ℓ) (4 * h + 1))
          (registryValue R h (initial p)) :=
      (registry_compact_initial R h (initial p) p.val.1 p.val.2 p.property (hinit p)).mono
        (fun _ h => h) (le_max_left _ _)
    have hp := replay h (compactBitBase m ℓ) (max (2 * h + ℓ) (4 * h + 1)) hh (le_max_right _ _)
      hi finish
    have hzero : R (node finish) = ∅ := by
      apply Finset.subset_empty.mp
      simpa only [hempty] using (hnode finish).1
    rwa [registry_empty_value R h (node finish) hzero] at hp

theorem compact_bitPHP_PC_transfer {m ℓ S : ℕ}
    (C : Fin S → FiniteParityClause (BitVar m ℓ)) (dag : AffineDAG (compactPairInitials m ℓ) C)
    (finish : Fin S) (hempty : C finish = ∅) (h : ℕ) (hh : 1 ≤ h) :
    ∃ (N : ℕ) (R : Fin N → FiniteParityClause (BitVar m ℓ)),
      N ≤ 3 * S + m.choose 2 ∧
      (∀ c, (R c).card ≤ max ℓ (m * ℓ + 2)) ∧
      (∑ c, (R c).card) ≤ N * max ℓ (m * ℓ + 2) ∧
      Fintype.card (ClauseRegistryVars R h) ≤ m * ℓ + h * N * max ℓ (m * ℓ + 2) ∧
      Derives (registrySystem R h (compactBitBase m ℓ)) (max (2 * h + ℓ) (4 * h + 1)) 1 := by
  apply bitPHP_transfer_of_cover _ C dag finish hempty ?_ h hh
  rintro A ⟨i, i', hii, rfl⟩
  exact ⟨⟨(i, i'), hii⟩, fun _ hx => hx⟩

theorem usual_bitPHP_PC_transfer {m ℓ S : ℕ}
    (C : Fin S → FiniteParityClause (BitVar m ℓ)) (dag : AffineDAG (usualInitials m ℓ) C)
    (finish : Fin S) (hempty : C finish = ∅) (h : ℕ) (hh : 1 ≤ h) :
    ∃ (N : ℕ) (R : Fin N → FiniteParityClause (BitVar m ℓ)),
      N ≤ 3 * S + m.choose 2 ∧
      (∀ c, (R c).card ≤ max ℓ (m * ℓ + 2)) ∧
      (∑ c, (R c).card) ≤ N * max ℓ (m * ℓ + 2) ∧
      Fintype.card (ClauseRegistryVars R h) ≤ m * ℓ + h * N * max ℓ (m * ℓ + 2) ∧
      Derives (registrySystem R h (compactBitBase m ℓ)) (max (2 * h + ℓ) (4 * h + 1)) 1 := by
  apply bitPHP_transfer_of_cover _ C dag finish hempty ?_ h hh
  rintro A ⟨i, i', hii, z, rfl⟩
  exact ⟨⟨(i, i'), hii⟩, compact_clause_entails_CNF i i' z⟩

/-- The transfer for a `Prop` valued dag of the bridge file. -/
theorem usual_bitPHP_PC_transfer_of_pdag {m ℓ S : ℕ}
    (C : Fin S → FiniteParityClause (BitVar m ℓ)) (dag : RL.Braun.PDag (usualInitials m ℓ) C)
    (finish : Fin S) (hempty : C finish = ∅) (h : ℕ) (hh : 1 ≤ h) :
    ∃ (N : ℕ) (R : Fin N → FiniteParityClause (BitVar m ℓ)),
      N ≤ 3 * S + m.choose 2 ∧
      (∀ c, (R c).card ≤ max ℓ (m * ℓ + 2)) ∧
      (∑ c, (R c).card) ≤ N * max ℓ (m * ℓ + 2) ∧
      Fintype.card (ClauseRegistryVars R h) ≤ m * ℓ + h * N * max ℓ (m * ℓ + 2) ∧
      Derives (registrySystem R h (compactBitBase m ℓ)) (max (2 * h + ℓ) (4 * h + 1)) 1 := by
  obtain ⟨d⟩ := pdag_to_affineDAG dag
  exact usual_bitPHP_PC_transfer C d finish hempty h hh

/-- The transfer for our dag like `Res(⊕)` refutations of the bit PHP CNF with `s` lines. -/
theorem bphp_dagRefutes_PC_transfer {l m s : ℕ}
    (hs : RL.DagRefutes (↑(RL.bphpCNF l m) : Set Clause) s) (h : ℕ) (hh : 1 ≤ h) :
    ∃ (N : ℕ) (R : Fin N → FiniteParityClause (BitVar m l)),
      N ≤ 3 * s + m.choose 2 ∧
      (∀ c, (R c).card ≤ max l (m * l + 2)) ∧
      (∑ c, (R c).card) ≤ N * max l (m * l + 2) ∧
      Fintype.card (ClauseRegistryVars R h) ≤ m * l + h * N * max l (m * l + 2) ∧
      Derives (registrySystem R h (compactBitBase m l)) (max (2 * h + l) (4 * h + 1)) 1 := by
  obtain ⟨S, C, hS, hd, f, hf⟩ := RL.Braun.bphp_dag_to_pdag l m s hs
  obtain ⟨N, R, hN, hrest⟩ := usual_bitPHP_PC_transfer_of_pdag C hd f hf h hh
  exact ⟨N, R, hN.trans (by omega), hrest⟩

end

end SATurday.ProofComplexity.BraunPC
