import Theory.ProofComplexity.BraunDag
import Theory.ProofComplexity.BraunDagRegistry
import Theory.ProofComplexity.BraunLiteralProduct
import Theory.ProofComplexity.BraunCompactDecoder
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination

/-!
# Bit pigeonhole initial clause bridge (R4 Phase 2.1, layer 5c)

Credit. Port, with our own proofs, of K. Braun (arXiv 2609.23015, author's Lean development):
`BitPHPInitialBridge.lean` (`compactPairClause`, `compact_clause_entails_CNF`,
`registry_compact_initial`, `usual_CNF_zero_iff`, `compact_pair_zero_iff`): the compact pair
clause `⋁_t (x_{i,t} + x_{i',t})` semantically entails each usual bit PHP axiom, and its value in
the fixed registry has an ordinary PC derivation of degree `2h + ℓ` from the compact old base.

Reuse: `BitVar`, `bitAffine`, `labelBitLiteral` and `usualCNFClause` are the ones of our bridge
file `BraunDag.lean` (`RL.Braun`), which coincide with his definitions.

LOG: R4 BraunBitPHPInitial module (Phase 2.1 layer 5c)
-/

namespace SATurday.ProofComplexity.BraunPC

noncomputable section

open MvPolynomial
open SATurday.ProofComplexity.BraunLA
open SATurday.ProofComplexity.RL.Braun (BitVar bitAffine labelBitLiteral usualCNFClause)
open scoped BigOperators

local instance bitInitialClauseDecidableEq {ν : Type} :
    DecidableEq ((ν → ZMod 2) →ᵃ[ZMod 2] ZMod 2) := Classical.decEq _

/-- The literal `x ↦ x_{i,t} + x_{i',t}`. -/
def pairBitLiteral {m ℓ : ℕ} (i i' : Fin m) (t : Fin ℓ) :
    (BitVar m ℓ → ZMod 2) →ᵃ[ZMod 2] ZMod 2 := bitAffine m ℓ i t + bitAffine m ℓ i' t

/-- The compact pair clause: the pigeons `i, i'` have different codes. -/
def compactPairClause {m ℓ : ℕ} (i i' : Fin m) : FiniteParityClause (BitVar m ℓ) :=
  Finset.univ.image (pairBitLiteral (ℓ := ℓ) i i')

private theorem binary_add_self (x : ZMod 2) : x + x = 0 := by fin_cases x <;> decide

@[simp] theorem bitAffine_apply (m ℓ : ℕ) (i : Fin m) (t : Fin ℓ) (x : BitVar m ℓ → ZMod 2) :
    bitAffine m ℓ i t x = x (i, t) := rfl

@[simp] theorem pairBitLiteral_apply {m ℓ : ℕ} (i i' : Fin m) (t : Fin ℓ)
    (x : BitVar m ℓ → ZMod 2) : pairBitLiteral i i' t x = x (i, t) + x (i', t) := rfl

@[simp] theorem labelBitLiteral_apply {m ℓ : ℕ} (i : Fin m) (z : BitLabel ℓ) (t : Fin ℓ)
    (x : BitVar m ℓ → ZMod 2) : labelBitLiteral i z t x = x (i, t) + z t := rfl

theorem compact_clause_entails_CNF {m ℓ : ℕ} (i i' : Fin m) (z : BitLabel ℓ) :
    clauseEntails (compactPairClause (ℓ := ℓ) i i') (usualCNFClause i i' z) := by
  intro x hx
  by_contra hn
  have hz := (clause_not_holds (usualCNFClause i i' z) x).mp hn
  obtain ⟨g, hg, hgx⟩ := hx
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hg
  have ha : x (i, t) + z t = 0 := hz (labelBitLiteral i z t)
    (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩))
  have hb : x (i', t) + z t = 0 := hz (labelBitLiteral i' z t)
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩))
  have he : x (i, t) = x (i', t) := add_right_cancel (ha.trans hb.symm)
  have hzero : pairBitLiteral i i' t x = 0 := by rw [pairBitLiteral_apply, he, binary_add_self]
  exact zero_ne_one (hzero.symm.trans hgx)

private theorem bitAffine_polynomial (m ℓ : ℕ) (i : Fin m) (t : Fin ℓ) :
    finiteAffinePolynomial (bitAffine m ℓ i t) = X (i, t) := by
  classical
  simp [finiteAffinePolynomial, RL.Braun.bitAffine, LinearMap.proj_apply, ite_smul]

private theorem pairBitLiteral_polynomial {m ℓ : ℕ} (i i' : Fin m) (t : Fin ℓ) :
    finiteAffinePolynomial (pairBitLiteral i i' t) = X (i, t) + X (i', t) := by
  rw [pairBitLiteral, map_add, bitAffine_polynomial, bitAffine_polynomial]

theorem registry_compact_initial {m ℓ N : ℕ}
    (C : Fin N → FiniteParityClause (BitVar m ℓ)) (h : ℕ) (c : Fin N)
    (i i' : Fin m) (hii : i < i') (hc : C c = compactPairClause (ℓ := ℓ) i i') :
    Derives (registrySystem C h (compactBitBase m ℓ)) (2 * h + ℓ) (registryValue C h c) := by
  classical
  let E : Poly (ZMod 2) (BitVar m ℓ) := ∏ t : Fin ℓ, (1 + X (i, t) + X (i', t))
  let g (t : Fin ℓ) := registryOld C h (finiteAffinePolynomial (pairBitLiteral i i' t))
  let lit (t : Fin ℓ) : C c := ⟨pairBitLiteral i i' t, by
    rw [hc]
    exact Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩⟩
  have hg (t : Fin ℓ) : (g t).totalDegree ≤ 1 := registry_input_degree C h c (lit t)
  obtain ⟨U, hU, hUd⟩ := affine_literal_product_prefix ℓ g hg
  have hE : (∏ t : Fin ℓ, (1 - g t)) = registryOld C h E := by
    simp [E, g, pairBitLiteral_polynomial, map_prod, CharTwo.sub_eq_add, add_assoc]
  have hEd : (∏ t : Fin ℓ, (1 - g t)).totalDegree ≤ ℓ := by
    apply (totalDegree_finset_prod _ _).trans
    calc
      _ ≤ ∑ _t : Fin ℓ, 1 := Finset.sum_le_sum (fun t _ =>
        (totalDegree_sub _ _).trans (max_le (by simp) (hg t)))
      _ = ℓ := by simp
  have hEa : (∏ t : Fin ℓ, (1 - g t)) ∈ registrySystem C h (compactBitBase m ℓ) := by
    rw [hE]
    exact Or.inl (Or.inl ⟨E, Or.inr ⟨i, i', hii, rfl⟩, rfl⟩)
  have hEP : Derives (registrySystem C h (compactBitBase m ℓ)) (2 * h + ℓ)
      ((∏ t : Fin ℓ, (1 - g t)) * registryValue C h c) := by
    have hp := registry_value_degree C h c
    have hh := ((Derives.hyp hEa hEd).mul_polynomial (registryValue C h c)).mono
      (fun _ h => h) (show max ℓ ((registryValue C h c).totalDegree +
        (∏ t : Fin ℓ, (1 - g t)).totalDegree) ≤ 2 * h + ℓ by omega)
    simpa only [mul_comm] using hh
  have hsum : (∑ t : Fin ℓ, U t * (g t * registryValue C h c)) ∈
      pcSpace (registrySystem C h (compactBitBase m ℓ)) (2 * h + ℓ) := by
    apply Submodule.sum_mem
    intro t _
    have ht := t.isLt
    have hcomp : Derives (registrySystem C h (compactBitBase m ℓ)) (2 * h + 1)
        (g t * registryValue C h c) :=
      Derives.hyp (Or.inr ⟨c, lit t, rfl⟩) (registry_companion_degree C h c (lit t))
    have hcd := hcomp.degree_le
    have hud := hUd t
    exact (hcomp.mul_polynomial (U t)).mono (fun _ h => h) (by omega)
  have heq : registryValue C h c =
      (∏ t : Fin ℓ, (1 - g t)) * registryValue C h c +
        ∑ t : Fin ℓ, U t * (g t * registryValue C h c) := by
    have hx := congrArg (fun p => p * registryValue C h c) hU
    beta_reduce at hx
    rw [sub_mul, one_mul, Finset.sum_mul] at hx
    simp only [mul_assoc] at hx
    linear_combination hx
  rw [heq]
  exact Derives.add hEP hsum

theorem usual_CNF_zero_iff {m ℓ : ℕ} (i i' : Fin m) (z : BitLabel ℓ)
    (x : BitVar m ℓ → ZMod 2) :
    clauseZero (usualCNFClause i i' z) x ↔
      (∀ t, x (i, t) = z t) ∧ (∀ t, x (i', t) = z t) := by
  constructor
  · intro hz
    constructor
    · intro t
      have ha : x (i, t) + z t = 0 := hz (labelBitLiteral i z t)
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩))
      exact add_right_cancel (ha.trans (binary_add_self (z t)).symm)
    · intro t
      have ha : x (i', t) + z t = 0 := hz (labelBitLiteral i' z t)
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩))
      exact add_right_cancel (ha.trans (binary_add_self (z t)).symm)
  · rintro ⟨ha, hb⟩ f hf
    rcases Finset.mem_union.mp hf with hf | hf
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hf
      simp only [labelBitLiteral_apply, ha, binary_add_self]
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hf
      simp only [labelBitLiteral_apply, hb, binary_add_self]

theorem compact_pair_zero_iff {m ℓ : ℕ} (i i' : Fin m) (x : BitVar m ℓ → ZMod 2) :
    clauseZero (compactPairClause (ℓ := ℓ) i i') x ↔ ∀ t, x (i, t) = x (i', t) := by
  constructor
  · intro hz t
    have ha : x (i, t) + x (i', t) = 0 := hz (pairBitLiteral i i' t)
      (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩)
    exact add_right_cancel (ha.trans (binary_add_self (x (i', t))).symm)
  · intro hx f hf
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hf
    simp only [pairBitLiteral_apply, hx, binary_add_self]

end

end SATurday.ProofComplexity.BraunPC
