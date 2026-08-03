import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Resolution: Syntax, Semantics, Soundness, Completeness (Ladder Rung R0)

This module is the foundation of the proof complexity ladder
(docs/ladder/ladder.md). It defines:

1. Literals, clauses (finite sets of literals), CNF formulas (finite sets of
   clauses), assignments, and satisfaction.
2. Size-counted resolution derivations (`Derivation`, `Derivation.size`), so that
   later rungs (R1: the Haken lower bound for pigeonhole formulas) can state
   size bounds.
3. Soundness: a CNF with a resolution refutation is unsatisfiable.
4. Refutational completeness: an unsatisfiable CNF has a resolution refutation.

The completeness proof is Davis-Putnam variable elimination, by induction on the
number of variables. Tautological clauses need no special treatment because the
clause split is strict about polarity: a clause containing both polarities of the
eliminated variable joins neither side of the split and never blocks the argument
(such a clause is satisfied by every assignment that decides that variable).

Acceptance bar (docs/p-vs-np-proof-standards.md): zero sorries, axioms within
propext, Classical.choice, Quot.sound. Verified by scripts/check_axioms.sh.

LOG: R0 resolution foundations module
-/

namespace SATurday.ProofComplexity

/-! ## Syntax -/

/-- A literal is a propositional variable index together with a polarity.
`pos = true` is the positive literal, `pos = false` the negated one. -/
structure Literal where
  var : ℕ
  pos : Bool
deriving DecidableEq, Repr

/-- A clause is a finite set of literals, read as their disjunction. -/
abbrev Clause := Finset Literal

/-- A CNF formula is a finite set of clauses, read as their conjunction. -/
abbrev CNF := Finset Clause

/-- A (total) truth assignment to the propositional variables. -/
abbrev Assignment := ℕ → Bool

/-! ## Semantics -/

/-- A literal is satisfied when the assignment gives its variable its polarity. -/
def litSat (a : Assignment) (l : Literal) : Prop := a l.var = l.pos

/-- A clause is satisfied when some literal in it is satisfied (disjunction). -/
def clauseSat (a : Assignment) (C : Clause) : Prop := ∃ l ∈ C, litSat a l

/-- A CNF is satisfied when every clause in it is satisfied (conjunction). -/
def cnfSat (a : Assignment) (F : CNF) : Prop := ∀ C ∈ F, clauseSat a C

/-- Satisfiability of a CNF formula. -/
def Satisfiable (F : CNF) : Prop := ∃ a, cnfSat a F

/-- A literal whose variable is `x` is one of the two polarities of `x`.
Used throughout to convert variable talk into literal talk. -/
theorem Literal.eq_pos_or_neg_of_var_eq {l : Literal} {x : ℕ} (h : l.var = x) :
    l = ⟨x, true⟩ ∨ l = ⟨x, false⟩ := by
  rcases l with ⟨v, b⟩
  cases b <;> simp_all

/-! ## Resolution derivations -/

/-- The resolvent of `C` and `D` on variable `x`: remove the positive literal
from `C` and the negative literal from `D`, then take the union. -/
def resolvent (C D : Clause) (x : ℕ) : Clause :=
  (C.erase ⟨x, true⟩) ∪ (D.erase ⟨x, false⟩)

/-- Size-counted resolution derivations from hypothesis set `F`.
`hyp` uses a clause of `F`; `res` resolves two derived clauses on a variable
that occurs positively in the first and negatively in the second. -/
inductive Derivation (F : CNF) : Clause → Type where
  | hyp (C : Clause) (hC : C ∈ F) : Derivation F C
  | res (x : ℕ) {C D : Clause}
      (dC : Derivation F C) (dD : Derivation F D)
      (hx : (⟨x, true⟩ : Literal) ∈ C) (hnx : (⟨x, false⟩ : Literal) ∈ D) :
      Derivation F (resolvent C D x)

/-- The size of a derivation: the number of clause occurrences in the proof tree.
R1 states lower bounds against this measure. -/
def Derivation.size {F : CNF} : {C : Clause} → Derivation F C → ℕ
  | _, .hyp _ _ => 1
  | _, .res _ dC dD _ _ => dC.size + dD.size + 1

/-- The conclusion clause of a derivation (the type index, made term-level). -/
def Derivation.conclusion {F : CNF} {C : Clause} (_ : Derivation F C) : Clause := C

/-- Derivability as a proposition. -/
def Derives (F : CNF) (C : Clause) : Prop := Nonempty (Derivation F C)

/-- A refutation is a derivation of the empty clause. -/
def Refutable (F : CNF) : Prop := Derives F ∅

/-! ## Soundness -/

/-- Every derived clause is entailed: an assignment satisfying the hypotheses
satisfies every derivable clause. The resolution step is the only interesting
case and splits on the value of the resolved variable. -/
theorem derivation_entails {F : CNF} {a : Assignment} (ha : cnfSat a F) :
    ∀ {C : Clause}, Derivation F C → clauseSat a C := by
  intro C d
  induction d with
  | hyp C hC =>
    exact ha C hC
  | res x dC dD hx hnx ihC ihD =>
    by_cases hax : a x = true
    · -- The negative literal of x is false, so D's witness survives into the
      -- resolvent through D.erase.
      obtain ⟨l, hl, hla⟩ := ihD
      have hlne : l ≠ ⟨x, false⟩ := by
        rintro rfl
        simp only [litSat] at hla
        rw [hax] at hla
        exact Bool.noConfusion hla
      exact ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hlne, hl⟩), hla⟩
    · -- The positive literal of x is false, so C's witness survives.
      have hax' : a x = false := by
        cases h : a x
        · rfl
        · exact absurd h hax
      obtain ⟨l, hl, hla⟩ := ihC
      have hlne : l ≠ ⟨x, true⟩ := by
        rintro rfl
        simp only [litSat] at hla
        rw [hax'] at hla
        exact Bool.noConfusion hla
      exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hlne, hl⟩), hla⟩

/-- Soundness: a refutable CNF is unsatisfiable. The empty clause is entailed
but no assignment satisfies it. -/
theorem resolution_sound {F : CNF} (h : Refutable F) : ¬Satisfiable F := by
  rintro ⟨a, ha⟩
  obtain ⟨d⟩ := h
  obtain ⟨l, hl, _⟩ := derivation_entails ha d
  exact absurd hl (Finset.notMem_empty l)

/-! ## Variables of a formula -/

/-- The set of variables occurring in a clause. -/
def clauseVars (C : Clause) : Finset ℕ := C.image Literal.var

/-- The set of variables occurring in a CNF formula. -/
def cnfVars (F : CNF) : Finset ℕ := F.biUnion clauseVars

theorem mem_cnfVars {F : CNF} {v : ℕ} :
    v ∈ cnfVars F ↔ ∃ C ∈ F, ∃ l ∈ C, l.var = v := by
  simp [cnfVars, clauseVars]

/-! ## Davis-Putnam elimination of one variable

For a variable `x`, split `F` into clauses using `x` strictly positively,
strictly negatively, and not at all; replace the `x`-clauses by all resolvents
of a strictly positive with a strictly negative clause. Clauses containing both
polarities of `x` are dropped: they are satisfied by any assignment that
decides `x`, so they never matter for satisfiability under an extension. -/

/-- Clauses of `F` containing `x` positively and not negatively. -/
def posClauses (F : CNF) (x : ℕ) : CNF :=
  F.filter fun C => (⟨x, true⟩ : Literal) ∈ C ∧ (⟨x, false⟩ : Literal) ∉ C

/-- Clauses of `F` containing `x` negatively and not positively. -/
def negClauses (F : CNF) (x : ℕ) : CNF :=
  F.filter fun C => (⟨x, false⟩ : Literal) ∈ C ∧ (⟨x, true⟩ : Literal) ∉ C

/-- Clauses of `F` not mentioning `x` at all. -/
def freeClauses (F : CNF) (x : ℕ) : CNF :=
  F.filter fun C => (⟨x, true⟩ : Literal) ∉ C ∧ (⟨x, false⟩ : Literal) ∉ C

/-- All resolvents on `x` of a strictly positive with a strictly negative clause. -/
def resolvents (F : CNF) (x : ℕ) : CNF :=
  (posClauses F x).biUnion fun C => (negClauses F x).image fun D => resolvent C D x

/-- The Davis-Putnam elimination of `x` from `F`. -/
def elimOn (F : CNF) (x : ℕ) : CNF := freeClauses F x ∪ resolvents F x

/-- Point override of an assignment. Self-contained to keep the proofs free of
library name drift; all facts about it are definitional `if` computations. -/
def override (a : Assignment) (x : ℕ) (b : Bool) : Assignment :=
  fun v => if v = x then b else a v

theorem override_self (a : Assignment) (x : ℕ) (b : Bool) : override a x b x = b := by
  simp [override]

theorem override_ne (a : Assignment) {x v : ℕ} (b : Bool) (h : v ≠ x) :
    override a x b v = a v := by
  simp [override, h]

/-- Satisfaction of a literal not mentioning `x` is unchanged by overriding `x`. -/
theorem litSat_override_of_var_ne {a : Assignment} {l : Literal} {x : ℕ} (b : Bool)
    (h : l.var ≠ x) : litSat (override a x b) l ↔ litSat a l := by
  simp [litSat, override_ne a b h]

/-! ### Elimination shrinks the variable set -/

/-- Every clause produced by elimination avoids `x` and introduces no new
variables, so the variable set is contained in the old one minus `x`. -/
theorem cnfVars_elimOn_subset {F : CNF} {x : ℕ} :
    cnfVars (elimOn F x) ⊆ (cnfVars F).erase x := by
  intro v hv
  obtain ⟨E, hE, ⟨l, hl, rfl⟩⟩ := by
    simpa [cnfVars, clauseVars] using hv
  rw [Finset.mem_erase]
  rcases Finset.mem_union.mp hE with hfree | hres
  · -- Free clauses of F: they avoid x and their variables are variables of F.
    obtain ⟨hEF, hnt, hnf⟩ := Finset.mem_filter.mp hfree
    refine ⟨?_, mem_cnfVars.mpr ⟨E, hEF, l, hl, rfl⟩⟩
    intro hveq
    rcases Literal.eq_pos_or_neg_of_var_eq hveq with rfl | rfl
    · exact hnt hl
    · exact hnf hl
  · -- Resolvents: both parents are in F, and both x-literals are gone
    -- (one erased, the other absent by polarity strictness).
    obtain ⟨C, hCpos, hEimg⟩ := Finset.mem_biUnion.mp hres
    obtain ⟨D, hDneg, rfl⟩ := Finset.mem_image.mp hEimg
    obtain ⟨hCF, hCt, hCf⟩ := Finset.mem_filter.mp hCpos
    obtain ⟨hDF, hDf, hDt⟩ := Finset.mem_filter.mp hDneg
    rcases Finset.mem_union.mp hl with hlC | hlD
    · obtain ⟨hlne, hlC⟩ := Finset.mem_erase.mp hlC
      refine ⟨?_, mem_cnfVars.mpr ⟨C, hCF, l, hlC, rfl⟩⟩
      intro hveq
      rcases Literal.eq_pos_or_neg_of_var_eq hveq with rfl | rfl
      · exact hlne rfl
      · exact hCf hlC
    · obtain ⟨hlne, hlD⟩ := Finset.mem_erase.mp hlD
      refine ⟨?_, mem_cnfVars.mpr ⟨D, hDF, l, hlD, rfl⟩⟩
      intro hveq
      rcases Literal.eq_pos_or_neg_of_var_eq hveq with rfl | rfl
      · exact hDt hlD
      · exact hlne rfl

/-! ### Elimination preserves unsatisfiability -/

/-- The heart of Davis-Putnam: a model of the eliminated formula extends to a
model of the original formula by choosing a value for `x`. Contrapositively,
elimination preserves unsatisfiability.

Proof sketch: if neither extension works, some clause `C1` of `F` fails under
`x := true` and some clause `C0` fails under `x := false`. Analysis shows `C1`
must contain the negative literal of `x` strictly and `C0` the positive literal
strictly, so their resolvent is in the eliminated formula and is satisfied by
the base assignment; its satisfied literal does not mention `x`, so it already
satisfied `C0` or `C1` under the corresponding extension. Contradiction. -/
theorem satisfiable_of_elimOn_sat {F : CNF} {x : ℕ} {a : Assignment}
    (haG : cnfSat a (elimOn F x)) : Satisfiable F := by
  by_contra hun
  have h1 : ¬ cnfSat (override a x true) F := fun h => hun ⟨_, h⟩
  have h0 : ¬ cnfSat (override a x false) F := fun h => hun ⟨_, h⟩
  simp only [cnfSat, not_forall] at h1 h0
  obtain ⟨C1, hC1F, hC1⟩ := h1
  obtain ⟨C0, hC0F, hC0⟩ := h0
  -- C1 fails under x := true, so it cannot contain the positive x-literal.
  have hxt1 : (⟨x, true⟩ : Literal) ∉ C1 := by
    intro hmem
    exact hC1 ⟨⟨x, true⟩, hmem, by simp [litSat, override_self]⟩
  -- C0 fails under x := false, so it cannot contain the negative x-literal.
  have hxf0 : (⟨x, false⟩ : Literal) ∉ C0 := by
    intro hmem
    exact hC0 ⟨⟨x, false⟩, hmem, by simp [litSat, override_self]⟩
  -- A clause of F avoiding x entirely sits in the eliminated formula, is
  -- satisfied by the base assignment, and that survives any override of x.
  have free_absurd : ∀ (C : Clause), C ∈ F → (⟨x, true⟩ : Literal) ∉ C →
      (⟨x, false⟩ : Literal) ∉ C → ∀ b : Bool, clauseSat (override a x b) C := by
    intro C hCF hnt hnf b
    have hCfree : C ∈ elimOn F x :=
      Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hCF, hnt, hnf⟩)
    obtain ⟨l, hl, hla⟩ := haG C hCfree
    have hvar : l.var ≠ x := by
      intro hv
      rcases Literal.eq_pos_or_neg_of_var_eq hv with rfl | rfl
      · exact hnt hl
      · exact hnf hl
    exact ⟨l, hl, (litSat_override_of_var_ne b hvar).mpr hla⟩
  -- Hence C1 must contain the negative x-literal (strictly), C0 the positive.
  have hxf1 : (⟨x, false⟩ : Literal) ∈ C1 := by
    by_contra hnf
    exact hC1 (free_absurd C1 hC1F hxt1 hnf true)
  have hxt0 : (⟨x, true⟩ : Literal) ∈ C0 := by
    by_contra hnt
    exact hC0 (free_absurd C0 hC0F hnt hxf0 false)
  -- Their resolvent on x lives in the eliminated formula.
  have hres : resolvent C0 C1 x ∈ elimOn F x := by
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨C0, ?_, ?_⟩)
    · exact Finset.mem_filter.mpr ⟨hC0F, hxt0, hxf0⟩
    · exact Finset.mem_image.mpr ⟨C1, Finset.mem_filter.mpr ⟨hC1F, hxf1, hxt1⟩, rfl⟩
  obtain ⟨l, hl, hla⟩ := haG _ hres
  -- The satisfied literal avoids x, so it satisfied a parent under its override.
  rcases Finset.mem_union.mp hl with hlC | hlD
  · obtain ⟨hlne, hlC0⟩ := Finset.mem_erase.mp hlC
    have hvar : l.var ≠ x := by
      intro hv
      rcases Literal.eq_pos_or_neg_of_var_eq hv with rfl | rfl
      · exact hlne rfl
      · exact hxf0 hlC0
    exact hC0 ⟨l, hlC0, (litSat_override_of_var_ne false hvar).mpr hla⟩
  · obtain ⟨hlne, hlC1⟩ := Finset.mem_erase.mp hlD
    have hvar : l.var ≠ x := by
      intro hv
      rcases Literal.eq_pos_or_neg_of_var_eq hv with rfl | rfl
      · exact hxt1 hlC1
      · exact hlne rfl
    exact hC1 ⟨l, hlC1, (litSat_override_of_var_ne true hvar).mpr hla⟩

/-- Elimination preserves unsatisfiability (the direction the induction uses). -/
theorem elimOn_unsat {F : CNF} {x : ℕ} (hun : ¬Satisfiable F) :
    ¬Satisfiable (elimOn F x) := by
  rintro ⟨a, ha⟩
  exact hun (satisfiable_of_elimOn_sat ha)

/-! ### Every eliminated clause is derivable -/

/-- Clauses of the eliminated formula are derivable from `F`: free clauses are
hypotheses, resolvents are one resolution step between two hypotheses. -/
theorem derives_elimOn_clauses {F : CNF} {x : ℕ} :
    ∀ E ∈ elimOn F x, Derives F E := by
  intro E hE
  rcases Finset.mem_union.mp hE with hfree | hres
  · exact ⟨Derivation.hyp E (Finset.mem_filter.mp hfree).1⟩
  · obtain ⟨C, hCpos, hEimg⟩ := Finset.mem_biUnion.mp hres
    obtain ⟨D, hDneg, rfl⟩ := Finset.mem_image.mp hEimg
    obtain ⟨hCF, hCt, _⟩ := Finset.mem_filter.mp hCpos
    obtain ⟨hDF, hDf, _⟩ := Finset.mem_filter.mp hDneg
    exact ⟨Derivation.res x (Derivation.hyp C hCF) (Derivation.hyp D hDF) hCt hDf⟩

/-- Derivability composes: if everything in `G` is derivable from `F`, then
everything derivable from `G` is derivable from `F`. -/
theorem derives_trans {F G : CNF} (hAll : ∀ C ∈ G, Derives F C) {E : Clause}
    (hE : Derives G E) : Derives F E := by
  obtain ⟨d⟩ := hE
  induction d with
  | hyp C hC => exact hAll C hC
  | res x dC dD hx hnx ihC ihD =>
    obtain ⟨eC⟩ := ihC
    obtain ⟨eD⟩ := ihD
    exact ⟨Derivation.res x eC eD hx hnx⟩

/-! ## Completeness -/

/-- Degenerate case: a formula with no variables is unsatisfiable only by
containing the empty clause, which is a one-step refutation. -/
theorem refutable_of_no_vars {F : CNF} (h : cnfVars F = ∅) (hun : ¬Satisfiable F) :
    Refutable F := by
  have hne : F.Nonempty := by
    rcases Finset.eq_empty_or_nonempty F with rfl | hne
    · exact absurd ⟨fun _ => true, fun C hC => absurd hC (Finset.notMem_empty C)⟩ hun
    · exact hne
  obtain ⟨C, hC⟩ := hne
  have hCempty : C = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro l hl
    have : l.var ∈ cnfVars F := mem_cnfVars.mpr ⟨C, hC, l, hl, rfl⟩
    simp [h] at this
  exact ⟨Derivation.hyp ∅ (hCempty ▸ hC)⟩

/-- Completeness, bounded form: induction on the number of variables. Each step
eliminates one variable by Davis-Putnam, keeps unsatisfiability, and pulls the
smaller refutation back through one layer of resolution steps. -/
theorem completeness_aux :
    ∀ (n : ℕ) (F : CNF), (cnfVars F).card ≤ n → ¬Satisfiable F → Refutable F := by
  intro n
  induction n with
  | zero =>
    intro F hcard hun
    exact refutable_of_no_vars (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)) hun
  | succ n ih =>
    intro F hcard hun
    by_cases hvars : cnfVars F = ∅
    · exact refutable_of_no_vars hvars hun
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hvars
      have hGcard : (cnfVars (elimOn F x)).card ≤ n := by
        have hsub : (cnfVars (elimOn F x)).card ≤ ((cnfVars F).erase x).card :=
          Finset.card_le_card cnfVars_elimOn_subset
        have herase : ((cnfVars F).erase x).card = (cnfVars F).card - 1 :=
          Finset.card_erase_of_mem hx
        omega
      have hGun : ¬Satisfiable (elimOn F x) := elimOn_unsat hun
      have hGref : Refutable (elimOn F x) := ih (elimOn F x) hGcard hGun
      exact derives_trans derives_elimOn_clauses hGref

/-- Refutational completeness: every unsatisfiable CNF has a resolution
refutation. -/
theorem resolution_complete {F : CNF} (h : ¬Satisfiable F) : Refutable F :=
  completeness_aux (cnfVars F).card F le_rfl h

/-- R0 summary theorem: refutability characterizes unsatisfiability. -/
theorem resolution_refutable_iff (F : CNF) : Refutable F ↔ ¬Satisfiable F :=
  ⟨resolution_sound, resolution_complete⟩

end SATurday.ProofComplexity
