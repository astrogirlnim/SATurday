import Theory.ProofComplexity.ResLinBPHP
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Braun's affine clause DAG calculus and the bridge to `RL.DagRefutes` (Ladder Rung R4, Phase 2.1)

Credit. The definitions `PClause`, `PStep`, `PDag`, `usualCNFClause`, `usualInitials` are a port
of the finite affine DAG calculus of K. Braun, bit pigeonhole lower bound for dag like resolution
over parities (arXiv 2609.23015), as formalized in the author's Lean development
(`AffineDAGRegistry.lean`, `BitPHPInitialBridge.lean`, `BitPHPClauseTransfer.lean`,
`BitPHPSuperpolynomial.lean`). The proofs here are our own. Differences: `PStep` is `Prop` valued
(his is `Type` valued; a hypothesis "a dag exists" is equivalent), and clause variables are
`BitVar m l = Fin m × Fin l` as there.

Truth convention (his): an affine map `g` is a true literal at `x` when `g x = 1`; a clause holds
when some literal is true. Our `LClause` line `(S, a)` is true when `∑_{w∈S} x_w = a`, which is
the literal `x ↦ ∑_{w∈S} x_w + a + 1`.

Content.
* `toP`: our linear clauses over `ℕ` become affine clauses over `BitVar m l` by extending an
  assignment of `BitVar m l` by zero to `ℕ` (`holds_toP`).
* `dag_to_pdag`: a dag like `Res(⊕)` refutation with `s` lines becomes a `PDag` with at most `s`
  nodes ending in the empty clause, over the clauses obtained from the axioms.
* `bphp_dag_to_pdag`: for `bphpCNF l m` the initial clauses are exactly `usualInitials m l`.
* `BraunBitPHP`: Braun's theorem as a `Prop` (not assumed anywhere) and
  `braun_implies_dag_lb`: it gives the super polynomial lower bound for `DagRefutes` on
  `bphpCNF ℓ (2^ℓ+1)`.

LOG: R4 BraunDag module (Phase 2.1 layer 0 bridge)
-/

namespace SATurday.ProofComplexity

namespace RL

noncomputable section

open Finset

namespace Braun

open Classical

/-- Affine clauses over a finite variable type (Braun's `FiniteParityClause`). -/
abbrev PClause (σ : Type) := Finset ((σ → ZMod 2) →ᵃ[ZMod 2] ZMod 2)

/-- A clause holds at `x` when some literal has value `1`. -/
def holds {σ : Type} (C : PClause σ) (x : σ → ZMod 2) : Prop := ∃ g ∈ C, g x = 1

/-- Semantic entailment between affine clauses. -/
def entails {σ : Type} (C D : PClause σ) : Prop := ∀ x, holds C x → holds D x

/-- The complementary literal `1 - u`. -/
def opp {σ : Type} (u : (σ → ZMod 2) →ᵃ[ZMod 2] ZMod 2) : (σ → ZMod 2) →ᵃ[ZMod 2] ZMod 2 :=
  AffineMap.const (ZMod 2) (σ → ZMod 2) 1 - u

/-- Braun's finite affine DAG step: node `i` is an initial clause, a semantic weakening of an
earlier node, a resolution of two earlier nodes on `u`, or a binary semantic consequence of two
earlier nodes. -/
inductive PStep {σ : Type} {S : ℕ} (I : Set (PClause σ)) (C : Fin S → PClause σ) (i : Fin S) :
    Prop
  | initial : C i ∈ I → PStep I C i
  | weaken (a : Fin S) : a < i → entails (C a) (C i) → PStep I C i
  | resolve (a b : Fin S) (A B : PClause σ) (u : (σ → ZMod 2) →ᵃ[ZMod 2] ZMod 2) :
      a < i → b < i → C a = insert u A → C b = insert (opp u) B → C i = A ∪ B → PStep I C i
  | binary (a b : Fin S) : a < i → b < i →
      (∀ x, holds (C a) x → holds (C b) x → holds (C i) x) → PStep I C i

/-- A finite affine DAG: every node is justified. -/
def PDag {σ : Type} {S : ℕ} (I : Set (PClause σ)) (C : Fin S → PClause σ) : Prop :=
  ∀ i, PStep I C i

/-! ## The bit pigeonhole clauses (Braun's `usualCNFClause`) -/

abbrev BitVar (m l : ℕ) := Fin m × Fin l

/-- The affine literal `x ↦ x_{i,t}`. -/
def bitAffine (m l : ℕ) (i : Fin m) (t : Fin l) :
    (BitVar m l → ZMod 2) →ᵃ[ZMod 2] ZMod 2 :=
  (LinearMap.proj (i, t)).toAffineMap

/-- `x ↦ x_{i,t} + z_t`. -/
def labelBitLiteral {m l : ℕ} (i : Fin m) (z : Fin l → ZMod 2) (t : Fin l) :
    (BitVar m l → ZMod 2) →ᵃ[ZMod 2] ZMod 2 :=
  bitAffine m l i t + AffineMap.const (ZMod 2) (BitVar m l → ZMod 2) (z t)

/-- The usual bit PHP clause for pigeons `i, i'` and the hole label `z`. -/
def usualCNFClause {m l : ℕ} (i i' : Fin m) (z : Fin l → ZMod 2) : PClause (BitVar m l) :=
  Finset.univ.image (labelBitLiteral i z) ∪ Finset.univ.image (labelBitLiteral i' z)

/-- Initial clauses of the usual bit PHP CNF. -/
def usualInitials (m l : ℕ) : Set (PClause (BitVar m l)) :=
  {C | ∃ i i' : Fin m, i < i' ∧ ∃ z : Fin l → ZMod 2, C = usualCNFClause i i' z}

/-- Braun's theorem (`bitPHP_superpolynomial`) as a statement. Not proved here. -/
def BraunBitPHP : Prop :=
  ∀ K : ℝ, 0 < K → ∃ L : ℕ, ∀ l ≥ L, ∀ {S : ℕ} (C : Fin S → PClause (BitVar (2 ^ l + 1) l)),
    PDag (usualInitials (2 ^ l + 1) l) C → ∀ f : Fin S, C f = ∅ → ((2 ^ l : ℕ) : ℝ) ^ K < (S : ℝ)

/-! ## From `ℕ` indexed linear clauses to affine clauses -/

section Convert

variable (m l : ℕ)

/-- Extend an assignment of `BitVar m l` by zero to all of `ℕ`, via `(i, j) ↦ j + l * i`. -/
def ext (y : BitVar m l → ZMod 2) : ℕ → ZMod 2 := fun w =>
  if h : w < m * l then y ((finProdFinEquiv (m := m) (n := l)).symm ⟨w, h⟩) else 0

/-- The coordinate functional `y ↦ ext y w`. -/
def extL (w : ℕ) : (BitVar m l → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  if h : w < m * l then LinearMap.proj ((finProdFinEquiv (m := m) (n := l)).symm ⟨w, h⟩) else 0

theorem extL_apply (w : ℕ) (y : BitVar m l → ZMod 2) : extL m l w y = ext m l y w := by
  unfold extL ext
  split_ifs <;> simp

/-- The affine literal for the equation `∑_{w∈S} x_w = a` (true iff its value is `1`). -/
def formAff (e : Finset ℕ × ZMod 2) : (BitVar m l → ZMod 2) →ᵃ[ZMod 2] ZMod 2 :=
  (∑ w ∈ e.1, extL m l w).toAffineMap + AffineMap.const (ZMod 2) (BitVar m l → ZMod 2) (e.2 + 1)

theorem formAff_apply (e : Finset ℕ × ZMod 2) (y : BitVar m l → ZMod 2) :
    formAff m l e y = lf e.1 (ext m l y) + e.2 + 1 := by
  unfold formAff lf
  simp [extL_apply, add_assoc]

/-- A linear clause as an affine clause. -/
def toP (L : LClause) : PClause (BitVar m l) := L.image (formAff m l)

theorem z2_iff (u v : ZMod 2) : u + v + 1 = 1 ↔ u = v := by revert u v; decide

theorem holds_toP (L : LClause) (y : BitVar m l → ZMod 2) :
    holds (toP m l L) y ↔ lsatL (ext m l y) L := by
  unfold holds toP lsatL
  constructor
  · rintro ⟨g, hg, hv⟩
    obtain ⟨e, he, rfl⟩ := mem_image.1 hg
    exact ⟨e, he, (z2_iff _ _).1 (by rw [← formAff_apply]; exact hv)⟩
  · rintro ⟨e, he, hv⟩
    exact ⟨_, mem_image_of_mem _ he, by rw [formAff_apply]; exact (z2_iff _ _).2 hv⟩

theorem toP_empty : toP m l ∅ = ∅ := by simp [toP]

end Convert

/-! ## The conversion of derivations -/

section Derivations

variable {m l : ℕ} {Ax : Set Clause}

/-- Extending a dag by a node at the end. -/
theorem pdag_snoc {σ : Type} {S : ℕ} {I : Set (PClause σ)} {C : Fin S → PClause σ}
    (hd : PDag I C) (D : PClause σ)
    (hnew : PStep I (Fin.snoc C D : Fin (S + 1) → PClause σ) (Fin.last S)) :
    PDag I (Fin.snoc C D : Fin (S + 1) → PClause σ) := by
  intro i
  refine Fin.lastCases hnew (fun j => ?_) i
  have hs : ∀ a : Fin S, (Fin.snoc C D : Fin (S + 1) → PClause σ) (Fin.castSucc a) = C a :=
    fun a => Fin.snoc_castSucc (α := fun _ => PClause σ) D C a
  have hlt : ∀ a : Fin S, a < j → Fin.castSucc a < Fin.castSucc j := fun a h => by simpa using h
  rcases hd j with h | ⟨a, ha, he⟩ | ⟨a, b, A, B, u, ha, hb, h1, h2, h3⟩ | ⟨a, b, ha, hb, hs'⟩
  · exact PStep.initial (by rw [hs]; exact h)
  · exact PStep.weaken (Fin.castSucc a) (hlt a ha) (by rw [hs, hs]; exact he)
  · exact PStep.resolve (Fin.castSucc a) (Fin.castSucc b) A B u (hlt a ha) (hlt b hb)
      (by rw [hs]; exact h1) (by rw [hs]; exact h2) (by rw [hs]; exact h3)
  · exact PStep.binary (Fin.castSucc a) (Fin.castSucc b) (hlt a ha) (hlt b hb)
      (by rw [hs, hs, hs]; exact hs')

/-- Semantic classification of a non axiom step. -/
theorem step_cases {P : Finset LClause} {L : LClause} (h : Step Ax P L) :
    (∃ C ∈ Ax, L = ofClause C) ∨ (∃ L0 ∈ P, Imp L0 L) ∨
      (∃ L1 ∈ P, ∃ L2 ∈ P, ∀ x, lsatL x L1 → lsatL x L2 → lsatL x L) := by
  cases h with
  | ax hC => exact Or.inl ⟨_, hC, rfl⟩
  | weak h0 hi => exact Or.inr (Or.inl ⟨_, h0, hi⟩)
  | @res L1 L2 C D f a h1 h2 i1 i2 =>
    refine Or.inr (Or.inr ⟨L1, h1, L2, h2, fun x hx1 hx2 => ?_⟩)
    have hs : Step (∅ : Set Clause) ({L1, L2} : Finset LClause) (C ∪ D) :=
      Step.res (by simp) (by simp) i1 i2
    exact step_sound x (fun C hC => absurd hC (Set.notMem_empty C))
      (by intro L' hL'; simp only [mem_insert, mem_singleton] at hL'
          rcases hL' with rfl | rfl <;> assumption) hs

/-- Invariant relating a finite set of lines to a `PDag`. -/
theorem der_to_pdag {P : Finset LClause} (h : Der Ax P) :
    ∃ (S : ℕ) (C : Fin S → PClause (BitVar m l)), S ≤ P.card ∧
      PDag {D | ∃ c ∈ Ax, D = toP m l (ofClause c)} C ∧ ∀ L ∈ P, ∃ i, C i = toP m l L := by
  induction h with
  | empty => exact ⟨0, Fin.elim0, le_rfl, fun i => i.elim0, by simp⟩
  | @add P L hP hs ih =>
    obtain ⟨S, C, hS, hd, hcov⟩ := ih
    by_cases hL : ∃ i, C i = toP m l L
    · refine ⟨S, C, hS.trans (card_le_card (subset_insert _ _)), hd, ?_⟩
      intro L' hL'
      rcases mem_insert.1 hL' with rfl | hL'
      · exact hL
      · exact hcov L' hL'
    · have hLP : L ∉ P := fun hm => hL (hcov L hm)
      have hsn : ∀ a : Fin S, (Fin.snoc C (toP m l L) : Fin (S + 1) → PClause (BitVar m l))
          (Fin.castSucc a) = C a := fun a => Fin.snoc_castSucc (α := fun _ => PClause _) _ C a
      have hlast : (Fin.snoc C (toP m l L) : Fin (S + 1) → PClause (BitVar m l)) (Fin.last S) =
          toP m l L := Fin.snoc_last (α := fun _ => PClause _) _ C
      refine ⟨S + 1, Fin.snoc C (toP m l L), ?_, ?_, ?_⟩
      · rw [card_insert_of_notMem hLP]; omega
      · apply pdag_snoc hd
        rcases step_cases hs with ⟨c, hc, rfl⟩ | ⟨L0, h0, hi⟩ | ⟨L1, h1, L2, h2, hsem⟩
        · exact PStep.initial (by rw [hlast]; exact ⟨c, hc, rfl⟩)
        · obtain ⟨a, ha⟩ := hcov L0 h0
          refine PStep.weaken (Fin.castSucc a) (Fin.castSucc_lt_last a) ?_
          rw [hsn, ha, hlast]
          intro y hy
          exact (holds_toP m l L y).2 (hi _ ((holds_toP m l L0 y).1 hy))
        · obtain ⟨a, ha⟩ := hcov L1 h1
          obtain ⟨b, hb⟩ := hcov L2 h2
          refine PStep.binary (Fin.castSucc a) (Fin.castSucc b) (Fin.castSucc_lt_last a)
            (Fin.castSucc_lt_last b) ?_
          rw [hsn, hsn, ha, hb, hlast]
          intro y hy1 hy2
          exact (holds_toP m l L y).2 (hsem _ ((holds_toP m l L1 y).1 hy1)
            ((holds_toP m l L2 y).1 hy2))
      · intro L' hL'
        rcases mem_insert.1 hL' with rfl | hL'
        · exact ⟨Fin.last S, hlast⟩
        · obtain ⟨i, hi⟩ := hcov L' hL'
          exact ⟨Fin.castSucc i, by rw [hsn]; exact hi⟩

/-- A dag like `Res(⊕)` refutation with `s` lines gives a `PDag` with at most `s` nodes ending in
the empty clause, with initial clauses coming from the axioms. -/
theorem dag_to_pdag {s : ℕ} (h : DagRefutes Ax s) :
    ∃ (S : ℕ) (C : Fin S → PClause (BitVar m l)), S ≤ s ∧
      PDag {D | ∃ c ∈ Ax, D = toP m l (ofClause c)} C ∧ ∃ f, C f = ∅ := by
  obtain ⟨P, hD, h0, hc⟩ := h
  obtain ⟨S, C, hS, hd, hcov⟩ := der_to_pdag (m := m) (l := l) hD
  obtain ⟨i, hi⟩ := hcov ∅ h0
  exact ⟨S, C, hS.trans hc, hd, i, by rw [hi, toP_empty]⟩

end Derivations

/-! ## The bit pigeonhole CNF -/

theorem toP_bphp_clause (m l : ℕ) (i k : Fin m) (t : Fin l → Bool) :
    toP m l (ofClause
      ((univ : Finset (Fin l)).image (fun j => (⟨i.val * l + j.val, !(t j)⟩ : Literal)) ∪
       (univ : Finset (Fin l)).image (fun j => (⟨k.val * l + j.val, !(t j)⟩ : Literal)))) =
    usualCNFClause i k (fun j => bv (t j)) := by
  have key : ∀ (p : Fin m) (j : Fin l),
      formAff m l (({(⟨p.val * l + j.val, !(t j)⟩ : Literal).var} : Finset ℕ),
        bv (⟨p.val * l + j.val, !(t j)⟩ : Literal).pos) =
      labelBitLiteral p (fun j => bv (t j)) j := by
    intro p j
    apply AffineMap.ext
    intro y
    have hlt : p.val * l + j.val < m * l := by
      have := p.isLt
      have := j.isLt
      nlinarith
    have hidx : (finProdFinEquiv (m := m) (n := l)).symm ⟨p.val * l + j.val, hlt⟩ = (p, j) := by
      rw [Equiv.symm_apply_eq]
      apply Fin.ext
      simp [finProdFinEquiv]
      ring
    rw [formAff_apply]
    simp only [lf, sum_singleton, ext, hlt, dite_true, hidx]
    simp only [labelBitLiteral, bitAffine]
    simp
    generalize y (p, j) = v
    cases t j <;> simp [bv] <;> revert v <;> decide
  unfold toP ofClause usualCNFClause
  rw [image_union, image_union, image_image, image_image, image_image, image_image]
  congr 1
  · apply image_congr
    intro j _
    exact key i j
  · apply image_congr
    intro j _
    exact key k j

/-- The initial clauses of `bphpCNF l m`, converted, are exactly Braun's usual initial clauses. -/
theorem init_subset (m l : ℕ) :
    {D | ∃ c ∈ (↑(bphpCNF l m) : Set Clause), D = toP m l (ofClause c)} ⊆ usualInitials m l := by
  rintro D ⟨c, hc, rfl⟩
  have hc' : c ∈ bphpCNF l m := hc
  unfold bphpCNF at hc'
  obtain ⟨⟨i, k, t⟩, ht, rfl⟩ := mem_image.1 hc'
  simp only [mem_filter, mem_univ, true_and] at ht
  exact ⟨i, k, ht, fun j => bv (t j), toP_bphp_clause m l i k t⟩

theorem pdag_mono {σ : Type} {S : ℕ} {I J : Set (PClause σ)} {C : Fin S → PClause σ}
    (hIJ : I ⊆ J) (h : PDag I C) : PDag J C := by
  intro i
  rcases h i with h | ⟨a, ha, he⟩ | ⟨a, b, A, B, u, ha, hb, h1, h2, h3⟩ | ⟨a, b, ha, hb, hs⟩
  · exact PStep.initial (hIJ h)
  · exact PStep.weaken a ha he
  · exact PStep.resolve a b A B u ha hb h1 h2 h3
  · exact PStep.binary a b ha hb hs

/-- A dag like `Res(⊕)` refutation of the bit PHP CNF with `s` lines is a `PDag` for Braun's
calculus with at most `s` nodes and initial clauses `usualInitials`. -/
theorem bphp_dag_to_pdag (l m s : ℕ) (h : DagRefutes (↑(bphpCNF l m) : Set Clause) s) :
    ∃ (S : ℕ) (C : Fin S → PClause (BitVar m l)), S ≤ s ∧ PDag (usualInitials m l) C ∧
      ∃ f, C f = ∅ := by
  obtain ⟨S, C, hS, hd, hf⟩ := dag_to_pdag (m := m) (l := l) h
  exact ⟨S, C, hS, pdag_mono (init_subset m l) hd, hf⟩

/-- Braun's bound transfers to our `DagRefutes`: every dag like `Res(⊕)` refutation of the bit PHP
CNF with `2^ℓ + 1` pigeons has more than `(2^ℓ)^K` lines, for each `K > 0` and large `ℓ`. -/
theorem braun_implies_dag_lb (hB : BraunBitPHP) (K : ℝ) (hK : 0 < K) :
    ∃ L : ℕ, ∀ l ≥ L, ∀ s : ℕ, DagRefutes (↑(bphpCNF l (2 ^ l + 1)) : Set Clause) s →
      ((2 ^ l : ℕ) : ℝ) ^ K < (s : ℝ) := by
  obtain ⟨L, hL⟩ := hB K hK
  refine ⟨L, fun l hl s hs => ?_⟩
  obtain ⟨S, C, hS, hd, f, hf⟩ := bphp_dag_to_pdag l (2 ^ l + 1) s hs
  exact (hL l hl C hd f hf).trans_le (by exact_mod_cast hS)

end Braun

end

end RL

end SATurday.ProofComplexity
