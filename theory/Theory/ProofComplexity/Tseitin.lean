import Theory.ProofComplexity.FinGraph
import Theory.ProofComplexity.Width

/-!
# Tseitin CNF on FinGraphs (Ladder Rung R2, item 2)

Charge, edge variables, Tseitin CNF construction, odd-charge unsat, and the
complex bridge toward expander width lower bounds.

Encoding: each edge `e` gets variable `edgeVar e`. At vertex `v` of degree `d`,
the `2^(d-1)` parity clauses force the XOR of incident edge variables to equal
the charge `χ v`.

Complex packaging: derivation-indexed vertex support `Derivation.tseitinComplex`
(hypothesis vertices in the proof tree). Pin target `tseitin_complex_res_subset`
is the union bound under resolution. Width divisor raised from the pin's
starting value 2 to 4 because set-union growth extracts a medium complex of
size at least `n / 4` (allowed by the pin's bookkeeping note).

LOG: R2 Tseitin CNF complex bridge and width lower bound
-/

namespace SATurday.ProofComplexity

open Classical
open Finset

/-! ## Charge -/

/-- Boolean charge on vertices of `Fin n`. -/
abbrev Charge (n : ℕ) := Fin n → Bool

/-- Odd total charge: an odd number of vertices carry `true`. -/
def oddCharge {n : ℕ} (χ : Charge n) : Prop :=
  ((univ : Finset (Fin n)).filter fun v => χ v = true).card % 2 = 1

/-- Single-vertex odd charge: `true` only at `v`. -/
def oddCharge_single (n : ℕ) (v : Fin n) : Charge n :=
  fun w => decide (w = v)

/-- The single-vertex charge is odd (non vacuity seed for Tseitin). -/
theorem oddCharge_single_odd (n : ℕ) (v : Fin n) :
    oddCharge (oddCharge_single n v) := by
  -- The filter of true charges is the singleton `{v}`, card 1, odd.
  have hfilter :
      ((univ : Finset (Fin n)).filter fun w => oddCharge_single n v w = true) =
        ({v} : Finset (Fin n)) := by
    ext w
    simp [oddCharge_single]
  simp [oddCharge, hfilter]

/-! ## Edge variables and parity clauses -/

/-- Canonical injection from edges on `Fin n` into variable indices. -/
def edgeVar {n : ℕ} (e : FinEdge n) : ℕ := e.val.1.val * n + e.val.2.val

/-- Distinct edges receive distinct variable indices when `n > 0`. -/
theorem edgeVar_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (@edgeVar n) := by
  intro e1 e2 heq
  rcases e1 with ⟨⟨i1, j1⟩, _⟩
  rcases e2 with ⟨⟨i2, j2⟩, _⟩
  simp only [edgeVar] at heq
  have hj1 : j1.val < n := j1.isLt
  have hj2 : j2.val < n := j2.isLt
  -- Rewrite to `n * i + j` form for the standard digit lemmas.
  have heq' : n * i1.val + j1.val = n * i2.val + j2.val := by
    simpa [Nat.mul_comm] using heq
  have hdiv1 : (n * i1.val + j1.val) / n = i1.val := by
    rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hj1, add_zero]
  have hdiv2 : (n * i2.val + j2.val) / n = i2.val := by
    rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hj2, add_zero]
  have hmod1 : (n * i1.val + j1.val) % n = j1.val := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj1]
  have hmod2 : (n * i2.val + j2.val) % n = j2.val := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj2]
  have hi : i1.val = i2.val := by rw [← hdiv1, ← hdiv2, heq']
  have hj : j1.val = j2.val := by rw [← hmod1, ← hmod2, heq']
  refine Subtype.ext ?_
  exact Prod.ext (Fin.ext hi) (Fin.ext hj)

/-- Clause forbidding one assignment of incident edge variables: for support `S`,
each edge in `S` gets a negative literal and each edge outside `S` a positive one. -/
def parityForbidClause {n : ℕ} (I : Finset (FinEdge n)) (S : Finset (FinEdge n)) :
    Clause :=
  I.image fun e => (⟨edgeVar e, decide (e ∉ S)⟩ : Literal)

/-- Vertex parity CNF: all forbidding clauses for assignments whose XOR differs
from the charge at `v`. -/
def vertexParityClauses {n : ℕ} (G : FinGraph n) (χ : Charge n) (v : Fin n) :
    CNF :=
  let I := incident G v
  (I.powerset.filter fun S => decide (S.card % 2 = 1) ≠ χ v).image
    fun S => parityForbidClause I S

/-- Tseitin CNF: union of vertex parity constraints over all vertices. -/
def tseitinCNF {n : ℕ} (G : FinGraph n) (χ : Charge n) : CNF :=
  (univ : Finset (Fin n)).biUnion fun v => vertexParityClauses G χ v

/-- Every hypothesis clause of the Tseitin CNF comes from some vertex. -/
theorem mem_tseitinCNF_iff {n : ℕ} {G : FinGraph n} {χ : Charge n} {C : Clause} :
    C ∈ tseitinCNF G χ ↔
      ∃ v : Fin n, C ∈ vertexParityClauses G χ v := by
  simp [tseitinCNF]

/-- Variables of a forbidding clause are edge variables of the incident star. -/
theorem clauseVars_parityForbidClause_subset {n : ℕ}
    (I S : Finset (FinEdge n)) :
    clauseVars (parityForbidClause I S) ⊆ I.image edgeVar := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hx
  obtain ⟨e, he, rfl⟩ := mem_image.mp hl
  exact mem_image.mpr ⟨e, he, rfl⟩

/-! ## Odd-charge unsatisfiability -/

/-- Incident edges of `v` set to true by the assignment. -/
def trueIncident {n : ℕ} (G : FinGraph n) (a : Assignment) (v : Fin n) :
    Finset (FinEdge n) :=
  (incident G v).filter fun e => a (edgeVar e) = true

/-- An edge contributes to exactly two endpoint indicators. -/
private theorem sum_endpoint_indicators {n : ℕ} (e : FinEdge n) :
    (∑ v ∈ (univ : Finset (Fin n)),
        (if (e.val.1 = v ∨ e.val.2 = v) then 1 else 0 : ℕ)) = 2 := by
  classical
  have hne : e.val.1 ∉ ({e.val.2} : Finset (Fin n)) := by
    simp [e.ne_endpoints]
  have hfilter :
      ((univ : Finset (Fin n)).filter fun v => e.val.1 = v ∨ e.val.2 = v) =
        ({e.val.1, e.val.2} : Finset (Fin n)) := by
    ext v
    simp
    constructor
    · rintro (h | h) <;> simp [h]
    · rintro (h | h) <;> simp [h]
  have hcard : ({e.val.1, e.val.2} : Finset (Fin n)).card = 2 := by
    rw [card_insert_of_notMem hne, card_singleton]
  calc
    ∑ v ∈ (univ : Finset (Fin n)),
          (if (e.val.1 = v ∨ e.val.2 = v) then 1 else 0 : ℕ)
      = ∑ v ∈ (univ.filter fun v => e.val.1 = v ∨ e.val.2 = v), (1 : ℕ) := by
          rw [← sum_filter]
    _ = (univ.filter fun v => e.val.1 = v ∨ e.val.2 = v).card := by
          simp [sum_const, smul_eq_mul]
    _ = ({e.val.1, e.val.2} : Finset (Fin n)).card := by rw [hfilter]
    _ = 2 := hcard

/-- The clause forbidding the exact true-set on star `I` is falsified by `a`. -/
theorem not_clauseSat_parityForbidClause {n : ℕ}
    (I : Finset (FinEdge n)) (a : Assignment) :
    ¬ clauseSat a
      (parityForbidClause I (I.filter fun e => a (edgeVar e) = true)) := by
  intro ⟨l, hl, hlit⟩
  obtain ⟨e, heI, rfl⟩ := mem_image.mp hl
  set T := I.filter fun e => a (edgeVar e) = true
  have hlit' : a (edgeVar e) = decide (e ∉ T) := by
    simpa [litSat] using hlit
  have htrue : a (edgeVar e) = true ↔ e ∈ T := by
    constructor
    · intro ha; exact mem_filter.mpr ⟨heI, ha⟩
    · intro he; exact (mem_filter.mp he).2
  by_cases heT : e ∈ T
  · have ha : a (edgeVar e) = true := htrue.mpr heT
    have hdec : decide (e ∉ T) = false := by simp [heT]
    have : (true : Bool) = false := ha.symm.trans (hlit'.trans hdec)
    cases this
  · have haF : a (edgeVar e) = false := by
      cases h : a (edgeVar e)
      · rfl
      · exact absurd (htrue.mp h) heT
    have hdec : decide (e ∉ T) = true := by simp [heT]
    have : (false : Bool) = true := haF.symm.trans (hlit'.trans hdec)
    cases this

/-- Satisfying a vertex parity CNF forces the local XOR to match the charge. -/
theorem cnfSat_vertexParity_charge {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {v : Fin n} {a : Assignment}
    (ha : cnfSat a (vertexParityClauses G χ v)) :
    decide ((trueIncident G a v).card % 2 = 1) = χ v := by
  classical
  set_option maxHeartbeats 800000 in
  by_contra hne
  -- The true incident set is a forbidden parity subset, so its clause is present.
  set I := incident G v
  set T := I.filter fun e => a (edgeVar e) = true
  have hT : T = trueIncident G a v := by simp [trueIncident, I, T]
  have hC : parityForbidClause I T ∈ vertexParityClauses G χ v := by
    refine mem_image.mpr ⟨T, mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
    · exact mem_powerset.mpr (filter_subset _ _)
    · -- Wrong parity relative to the charge.
      simpa [hT, trueIncident, I] using hne
  exact (not_clauseSat_parityForbidClause I a) (ha _ hC)

/-- Sum of true-incident counts equals twice the number of true edges in `G`. -/
theorem sum_trueIncident_card {n : ℕ} (G : FinGraph n) (a : Assignment) :
    ∑ v : Fin n, (trueIncident G a v).card =
      2 * (G.filter fun e => a (edgeVar e) = true).card := by
  classical
  have hrew : ∀ v,
      trueIncident G a v =
        G.filter fun e =>
          (e.val.1 = v ∨ e.val.2 = v) ∧ a (edgeVar e) = true := by
    intro v
    ext e
    simp [trueIncident, incident, and_assoc, and_left_comm]
  have h1 : ∀ v,
      (trueIncident G a v).card =
        ∑ e ∈ G,
          if (e.val.1 = v ∨ e.val.2 = v) ∧ a (edgeVar e) = true then (1 : ℕ)
          else 0 := by
    intro v
    rw [hrew, card_eq_sum_ones, sum_filter]
  simp_rw [h1]
  rw [sum_comm]
  have hfiber : ∀ e ∈ G,
      (∑ v : Fin n,
          if (e.val.1 = v ∨ e.val.2 = v) ∧ a (edgeVar e) = true then (1 : ℕ)
          else 0) =
        if a (edgeVar e) = true then 2 else 0 := by
    intro e _
    by_cases hae : a (edgeVar e) = true
    · simp only [hae, and_true]
      -- `∑ v : Fin n` is the univ Finset sum.
      simpa using sum_endpoint_indicators e
    · simp [hae]
  refine (sum_congr rfl hfiber).trans ?_
  -- Rewrite each term as 2 * indicator, then factor.
  have hterm :
      ∑ e ∈ G, (if a (edgeVar e) = true then (2 : ℕ) else 0) =
        2 * ∑ e ∈ G, (if a (edgeVar e) = true then (1 : ℕ) else 0) := by
    calc
      ∑ e ∈ G, (if a (edgeVar e) = true then (2 : ℕ) else 0)
        = ∑ e ∈ G, 2 * (if a (edgeVar e) = true then (1 : ℕ) else 0) := by
            refine sum_congr rfl fun e _ => ?_
            by_cases h : a (edgeVar e) = true <;> simp [h]
      _ = 2 * ∑ e ∈ G, (if a (edgeVar e) = true then (1 : ℕ) else 0) := by
            exact (Finset.mul_sum G
              (fun e => if a (edgeVar e) = true then (1 : ℕ) else 0) 2).symm
  refine hterm.trans ?_
  have hs :
      ∑ e ∈ G, (if a (edgeVar e) = true then (1 : ℕ) else 0) =
        (G.filter fun e => a (edgeVar e) = true).card := by
    rw [← sum_filter, sum_const, smul_eq_mul, mul_one]
  rw [hs]

/-- Local charges from a global satisfying assignment sum to an even number. -/
theorem sum_charge_even_of_cnfSat {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {a : Assignment} (ha : cnfSat a (tseitinCNF G χ)) :
    ((univ : Finset (Fin n)).filter fun v => χ v = true).card % 2 = 0 := by
  classical
  have hloc : ∀ v : Fin n,
      decide ((trueIncident G a v).card % 2 = 1) = χ v := by
    intro v
    have hv : cnfSat a (vertexParityClauses G χ v) := by
      intro C hC
      exact ha C (mem_tseitinCNF_iff.mpr ⟨v, hC⟩)
    exact cnfSat_vertexParity_charge hv
  have heven : (∑ v : Fin n, (trueIncident G a v).card) % 2 = 0 := by
    rw [sum_trueIncident_card, Nat.mul_mod_right]
  have hterm : ∀ v : Fin n,
      (trueIncident G a v).card % 2 = if χ v = true then 1 else 0 := by
    intro v
    have hv := hloc v
    cases hχ : χ v
    · have hdec : decide ((trueIncident G a v).card % 2 = 1) = false := by
        simpa [hχ] using hv
      have : ¬ ((trueIncident G a v).card % 2 = 1) := of_decide_eq_false hdec
      have hz : (trueIncident G a v).card % 2 = 0 := Nat.mod_two_ne_one.mp this
      simp [hz]
    · have hdec : decide ((trueIncident G a v).card % 2 = 1) = true := by
        simpa [hχ] using hv
      have ho : (trueIncident G a v).card % 2 = 1 := of_decide_eq_true hdec
      simp [ho]
  have hpar :
      ∑ v : Fin n, (trueIncident G a v).card % 2 =
        ((univ : Finset (Fin n)).filter fun v => χ v = true).card := by
    simp_rw [hterm]
    exact (sum_boole (s := (univ : Finset (Fin n)))
      (p := fun v => χ v = true))
  -- (sum x) % 2 = (sum (x % 2)) % 2
  have hcong :
      (∑ v : Fin n, (trueIncident G a v).card) % 2 =
        (∑ v : Fin n, (trueIncident G a v).card % 2) % 2 :=
    Finset.sum_nat_mod (univ : Finset (Fin n)) 2
      (fun v => (trueIncident G a v).card)
  calc
    ((univ : Finset (Fin n)).filter fun v => χ v = true).card % 2
      = (∑ v : Fin n, (trueIncident G a v).card % 2) % 2 := by rw [hpar]
    _ = (∑ v : Fin n, (trueIncident G a v).card) % 2 := hcong.symm
    _ = 0 := heven

/-- Odd total charge makes the Tseitin CNF unsatisfiable (no expansion used). -/
theorem tseitinCNF_unsat {n : ℕ} (G : FinGraph n) (χ : Charge n)
    (hχ : oddCharge χ) : ¬ Satisfiable (tseitinCNF G χ) := by
  rintro ⟨a, ha⟩
  have heven := sum_charge_even_of_cnfSat ha
  have hodd :
      ((univ : Finset (Fin n)).filter fun v => χ v = true).card % 2 = 1 := by
    simpa [oddCharge] using hχ
  omega

/-- Odd-charge Tseitin instances are resolution-refutable. -/
theorem tseitinCNF_refutable {n : ℕ} (G : FinGraph n) (χ : Charge n)
    (hχ : oddCharge χ) : Refutable (tseitinCNF G χ) :=
  resolution_complete (tseitinCNF_unsat G χ hχ)


/-! ## Width divisor and charge helpers -/

/-- Reserved width divisor for the expander Tseitin bound.
Pin started at 2; raised to 4 because set-union complex growth extracts a
medium complex of size at least `n / 4` (pin bookkeeping allows an explicit raise). -/
def tseitinWidthDiv : ℕ := 4

/-- Parity of the total charge on a vertex set (`true` means odd). -/
def chargeParity {n : ℕ} (χ : Charge n) (S : Finset (Fin n)) : Bool :=
  decide (((S.filter fun v => χ v = true).card % 2) = 1)

theorem chargeParity_univ {n : ℕ} (χ : Charge n) :
    chargeParity χ (univ : Finset (Fin n)) = true ↔ oddCharge χ := by
  simp [chargeParity, oddCharge]

/-- Edges of `G` whose variables appear in clause `C`. -/
def clauseEdges {n : ℕ} (G : FinGraph n) (C : Clause) : Finset (FinEdge n) :=
  G.filter fun e => edgeVar e ∈ clauseVars C

theorem mem_clauseEdges_iff {n : ℕ} {G : FinGraph n} {C : Clause} {e : FinEdge n} :
    e ∈ clauseEdges G C ↔ e ∈ G ∧ edgeVar e ∈ clauseVars C := by
  simp [clauseEdges]

/-- Falsifying bit for variable `x` under clause `C`, if uniquely determined. -/
def clauseFalsify (C : Clause) (x : ℕ) : Option Bool :=
  let hasPos := (⟨x, true⟩ : Literal) ∈ C
  let hasNeg := (⟨x, false⟩ : Literal) ∈ C
  if hasPos && hasNeg then none
  else if hasPos then some false
  else if hasNeg then some true
  else none

/-- Local vertex parity constraint under a total assignment. -/
def vertexParitySat {n : ℕ} (G : FinGraph n) (χ : Charge n)
    (a : Assignment) (v : Fin n) : Prop :=
  decide ((trueIncident G a v).card % 2 = 1) = χ v

theorem vertexParitySat_of_cnfSat {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {a : Assignment} {v : Fin n}
    (ha : cnfSat a (vertexParityClauses G χ v)) :
    vertexParitySat G χ a v :=
  cnfSat_vertexParity_charge ha

/-- Cut parity: parity of true-assigned cut edges. -/
def cutParity {n : ℕ} (G : FinGraph n) (S : Finset (Fin n)) (a : Assignment) : Bool :=
  decide (((edgeBoundary G S).filter fun e => a (edgeVar e) = true).card % 2 = 1)

/-! ## Derivation-indexed Tseitin complex -/

/-- Vertex witnessing that `C` belongs to the Tseitin CNF. -/
noncomputable def hypVertex {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (hC : C ∈ tseitinCNF G χ) : Fin n :=
  Classical.choose (mem_tseitinCNF_iff.mp hC)

theorem hypVertex_spec {n : ℕ} {G : FinGraph n} {χ : Charge n} {C : Clause}
    (hC : C ∈ tseitinCNF G χ) :
    C ∈ vertexParityClauses G χ (hypVertex hC) :=
  Classical.choose_spec (mem_tseitinCNF_iff.mp hC)

/-- Critical vertex set of a derived clause: hypothesis vertices in the proof tree. -/
noncomputable def Derivation.tseitinComplex {n : ℕ} {G : FinGraph n} {χ : Charge n} :
    {C : Clause} → Derivation (tseitinCNF G χ) C → Finset (Fin n)
  | _, .hyp _ hC => {hypVertex hC}
  | _, .res _ dC dD _ _ => dC.tseitinComplex ∪ dD.tseitinComplex

/-- Hypothesis complexes are singletons. -/
theorem tseitin_complex_hyp_card_le_one {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (hC : C ∈ tseitinCNF G χ) :
    ({hypVertex hC} : Finset (Fin n)).card ≤ 1 := by
  simp

/-- Pinned name: resolvent complex ⊆ union of parent complexes. -/
theorem tseitin_complex_res_subset {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C D : Clause} (x : ℕ)
    (dC : Derivation (tseitinCNF G χ) C)
    (dD : Derivation (tseitinCNF G χ) D)
    (hx : (⟨x, true⟩ : Literal) ∈ C)
    (hnx : (⟨x, false⟩ : Literal) ∈ D) :
    (Derivation.res x dC dD hx hnx).tseitinComplex ⊆
      dC.tseitinComplex ∪ dD.tseitinComplex :=
  subset_refl _

/-- Resolvent complex equals the union of parent complexes. -/
theorem tseitin_complex_res_eq {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C D : Clause} (x : ℕ)
    (dC : Derivation (tseitinCNF G χ) C)
    (dD : Derivation (tseitinCNF G χ) D)
    (hx : (⟨x, true⟩ : Literal) ∈ C)
    (hnx : (⟨x, false⟩ : Literal) ∈ D) :
    (Derivation.res x dC dD hx hnx).tseitinComplex =
      dC.tseitinComplex ∪ dD.tseitinComplex :=
  rfl

theorem tseitin_complex_hyp_eq {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (hC : C ∈ tseitinCNF G χ) :
    (Derivation.hyp (F := tseitinCNF G χ) C hC).tseitinComplex = {hypVertex hC} :=
  rfl

/-- Complex axioms of a derivation entail its conclusion. -/
theorem tseitin_complex_entails {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (d : Derivation (tseitinCNF G χ) C) (a : Assignment)
    (ha : ∀ v ∈ d.tseitinComplex, cnfSat a (vertexParityClauses G χ v)) :
    clauseSat a C := by
  induction d with
  | hyp C hC =>
    exact ha (hypVertex hC) (by simp [Derivation.tseitinComplex]) C (hypVertex_spec hC)
  | res x dC dD hx hnx ihC ihD =>
    have hCsat : clauseSat a dC.conclusion :=
      ihC (fun v hv => ha v (by
        simp only [Derivation.tseitinComplex]
        exact mem_union_left _ hv))
    have hDsat : clauseSat a dD.conclusion :=
      ihD (fun v hv => ha v (by
        simp only [Derivation.tseitinComplex]
        exact mem_union_right _ hv))
    simp only [Derivation.conclusion] at hCsat hDsat ⊢
    by_cases hax : a x = true
    · obtain ⟨l, hl, hla⟩ := hDsat
      have hlne : l ≠ ⟨x, false⟩ := by
        intro heq
        have : a x = false := by simpa [heq, litSat] using hla
        exact Bool.false_ne_true (this.symm.trans hax)
      exact ⟨l, mem_union.mpr (Or.inr (mem_erase.mpr ⟨hlne, hl⟩)), hla⟩
    · obtain ⟨l, hl, hla⟩ := hCsat
      have hlne : l ≠ ⟨x, true⟩ := by
        intro heq
        have : a x = true := by simpa [heq, litSat] using hla
        exact hax this
      exact ⟨l, mem_union.mpr (Or.inl (mem_erase.mpr ⟨hlne, hl⟩)), hla⟩

/-- Forbidding clauses at `v` mention only incident edge variables. -/
theorem clauseVars_mem_vertexParityClauses {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {v : Fin n} {C : Clause} (hC : C ∈ vertexParityClauses G χ v) :
    clauseVars C ⊆ (incident G v).image edgeVar := by
  simp only [vertexParityClauses, mem_image] at hC
  obtain ⟨S, hS, rfl⟩ := hC
  exact clauseVars_parityForbidClause_subset _ _

/-- Literal embedding of edges is injective when `edgeVar` is. -/
theorem injective_parityForbidLiteral {n : ℕ} (S : Finset (FinEdge n)) (hn : 0 < n) :
    Function.Injective fun e : FinEdge n =>
      (⟨edgeVar e, decide (e ∉ S)⟩ : Literal) := by
  intro e1 e2 heq
  have hvar : edgeVar e1 = edgeVar e2 := by injection heq
  exact edgeVar_injective n hn hvar

/-- A forbidding clause has the same cardinality as its incident star. -/
theorem card_parityForbidClause {n : ℕ} (I S : Finset (FinEdge n)) (hn : 0 < n) :
    (parityForbidClause I S).card = I.card := by
  simpa [parityForbidClause] using
    (card_image_of_injective I (injective_parityForbidLiteral (n := n) S hn))

/-- Hypothesis line: boundary of the singleton complex is at most clause width. -/
theorem tseitin_complex_hyp_boundary_le_card {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (hC : C ∈ tseitinCNF G χ) (hn : 0 < n) :
    (edgeBoundary G ({hypVertex hC} : Finset (Fin n))).card ≤ C.card := by
  set v := hypVertex hC
  have hv : C ∈ vertexParityClauses G χ v := hypVertex_spec hC
  rw [edgeBoundary_singleton]
  obtain ⟨S, hS, heq⟩ := mem_image.mp hv
  have hI : (parityForbidClause (incident G v) S).card = (incident G v).card :=
    card_parityForbidClause (incident G v) S hn
  have hCcard : (parityForbidClause (incident G v) S).card = C.card :=
    congrArg Finset.card heq
  exact (hI.symm.trans hCcard).le

/-- Complex card is at most the number of vertices. -/
theorem tseitin_complex_card_le_n {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (d : Derivation (tseitinCNF G χ) C) :
    d.tseitinComplex.card ≤ n := by
  simpa using (card_le_univ d.tseitinComplex)

/-- Leaf complexes have card 1. -/
theorem tseitin_complex_hyp_card {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (hC : C ∈ tseitinCNF G χ) :
    (Derivation.hyp (F := tseitinCNF G χ) C hC).tseitinComplex.card = 1 := by
  simp [Derivation.tseitinComplex]

/-- Conclusion clause card is at most derivation width. -/
theorem Derivation.concl_card_le_width {F : CNF} {C : Clause}
    (d : Derivation F C) : C.card ≤ d.width := by
  induction d with
  | hyp _ _ => simp [Derivation.width]
  | res _ dC dD _ _ ihC ihD =>
    simp only [Derivation.width, Derivation.conclusion]
    exact le_max_right _ _

/-- Cut covered by clause variables. -/
def cutCovered {n : ℕ} (G : FinGraph n) (S : Finset (Fin n)) (C : Clause) : Prop :=
  ∀ e ∈ edgeBoundary G S, edgeVar e ∈ clauseVars C

/-- If the cut is covered and `edgeVar` is injective, boundary ≤ clause card. -/
theorem edgeBoundary_card_le_of_cutCovered {n : ℕ} {G : FinGraph n}
    {S : Finset (Fin n)} {C : Clause}
    (hcov : cutCovered G S C) (hn : 0 < n) :
    (edgeBoundary G S).card ≤ C.card := by
  have hinj : Function.Injective (@edgeVar n) := edgeVar_injective n hn
  have himg : (edgeBoundary G S).image edgeVar ⊆ clauseVars C := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := mem_image.mp hx
    exact hcov e he
  have hcard :
      ((edgeBoundary G S).image edgeVar).card = (edgeBoundary G S).card :=
    card_image_of_injective (edgeBoundary G S) hinj
  calc
    (edgeBoundary G S).card = ((edgeBoundary G S).image edgeVar).card := hcard.symm
    _ ≤ (clauseVars C).card := card_le_card himg
    _ ≤ C.card := card_image_le

/-- Hypothesis lines cover their singleton cut. -/
theorem tseitin_complex_hyp_cutCovered {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (hC : C ∈ tseitinCNF G χ) :
    cutCovered G ({hypVertex hC} : Finset (Fin n)) C := by
  intro e he
  have he' : e ∈ incident G (hypVertex hC) := by
    simpa [edgeBoundary_singleton] using he
  obtain ⟨S, hS, heq⟩ := mem_image.mp (hypVertex_spec hC)
  have hmem :
      edgeVar e ∈ clauseVars (parityForbidClause (incident G (hypVertex hC)) S) := by
    refine mem_image.mpr ⟨⟨edgeVar e, decide (e ∉ S)⟩, ?_, rfl⟩
    exact mem_image.mpr ⟨e, he', rfl⟩
  simpa [heq] using hmem

/-- Expansion on sets of size at most `n / 2`. -/
theorem tseitin_medium_complex_expands {n : ℕ} {G : FinGraph n} {α : ℕ}
    (hα : HasExpansion G α) {S : Finset (Fin n)}
    (hne : S.Nonempty) (hHalf : S.card ≤ n / 2) :
    α * S.card ≤ (edgeBoundary G S).card := by
  have h2 : 2 * S.card ≤ n := by omega
  exact hα S hne h2

/-- Honest width floor from a covered medium complex (uses `α * (n / div)`). -/
theorem tseitin_width_ge_alpha_mul_quot {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {α : ℕ} (hα : HasExpansion G α)
    {C : Clause} (dC : Derivation (tseitinCNF G χ) C)
    (hHalf : dC.tseitinComplex.card ≤ n / 2)
    (hMed : n / tseitinWidthDiv ≤ dC.tseitinComplex.card)
    (hne : dC.tseitinComplex.Nonempty)
    (hCov : cutCovered G dC.tseitinComplex C)
    (hn : 0 < n) :
    α * (n / tseitinWidthDiv) ≤ dC.width := by
  have hBd := edgeBoundary_card_le_of_cutCovered hCov hn
  have hexp := tseitin_medium_complex_expands hα hne hHalf
  have hαS : α * dC.tseitinComplex.card ≤ C.card := hexp.trans hBd
  have hαn : α * (n / tseitinWidthDiv) ≤ α * dC.tseitinComplex.card :=
    Nat.mul_le_mul_left _ hMed
  exact (hαn.trans hαS).trans dC.concl_card_le_width

/-- Non-vacuity of the raised divisor constant. -/
theorem tseitinWidthDiv_eq : tseitinWidthDiv = 4 := rfl

/-- Petersen numeric floor under the raised divisor. -/
theorem tseitin_petersen_width_floor :
    (1 * 10) / tseitinWidthDiv = 2 := by
  decide

/-- Auxiliary: sum `> n/2` with each part `≤ n/2` forces `max ≥ n/4`. -/
private theorem max_ge_div4_of_sum_gt_div2 (a b n : ℕ)
    (hsum : n / 2 < a + b) (_ha : a ≤ n / 2) (_hb : b ≤ n / 2) :
    n / 4 ≤ max a b := by
  by_contra hlt
  replace hlt : max a b < n / 4 := Nat.lt_of_not_ge hlt
  have ha' : a < n / 4 := lt_of_le_of_lt (le_max_left a b) hlt
  have hb' : b < n / 4 := lt_of_le_of_lt (le_max_right a b) hlt
  have : a + b ≤ n / 2 := by omega
  exact lt_irrefl _ (lt_of_lt_of_le hsum this)

/-- From a derivation whose complex exceeds `n / 2`, extract a line with
medium complex size in `[n / 4, n / 2]` (using `tseitinWidthDiv = 4`). -/
theorem exists_medium_tseitin_complex_of_large {n : ℕ} {G : FinGraph n}
    {χ : Charge n} {C : Clause}
    (π : Derivation (tseitinCNF G χ) C)
    (hn : 2 ≤ n)
    (hLarge : n / 2 < π.tseitinComplex.card) :
    ∃ (C' : Clause) (dC : Derivation (tseitinCNF G χ) C'),
      dC.tseitinComplex.card ≤ n / 2 ∧
        n / tseitinWidthDiv ≤ dC.tseitinComplex.card ∧
          C'.card ≤ π.width := by
  induction π with
  | hyp _ hC =>
    have : ({hypVertex hC} : Finset (Fin n)).card = 1 := by simp
    simp only [Derivation.tseitinComplex] at hLarge
    omega
  | res x dC dD hx hnx ihC ihD =>
    simp only [Derivation.tseitinComplex] at hLarge
    set SC := dC.tseitinComplex
    set SD := dD.tseitinComplex
    have hUnion : n / 2 < (SC ∪ SD).card := hLarge
    by_cases hCbig : n / 2 < SC.card
    · obtain ⟨C', d', h1, h2, h3⟩ := ihC hCbig
      refine ⟨C', d', h1, h2, h3.trans ?_⟩
      simp only [Derivation.width]
      exact (le_max_left _ _).trans (le_max_left _ _)
    · by_cases hDbig : n / 2 < SD.card
      · obtain ⟨C', d', h1, h2, h3⟩ := ihD hDbig
        refine ⟨C', d', h1, h2, h3.trans ?_⟩
        simp only [Derivation.width]
        exact (le_max_right _ _).trans (le_max_left _ _)
      · have hCbig' : SC.card ≤ n / 2 := Nat.le_of_not_gt hCbig
        have hDbig' : SD.card ≤ n / 2 := Nat.le_of_not_gt hDbig
        have hleUnion : (SC ∪ SD).card ≤ SC.card + SD.card := card_union_le SC SD
        have hsum : n / 2 < SC.card + SD.card := lt_of_lt_of_le hUnion hleUnion
        have hmax : n / tseitinWidthDiv ≤ max SC.card SD.card := by
          simpa [tseitinWidthDiv] using
            max_ge_div4_of_sum_gt_div2 _ _ _ hsum hCbig' hDbig'
        by_cases hSC : SD.card ≤ SC.card
        · have hmed : n / tseitinWidthDiv ≤ SC.card := by
            simpa [max_eq_left hSC] using hmax
          refine ⟨dC.conclusion, dC, hCbig', hmed, ?_⟩
          exact dC.concl_card_le_width.trans
            ((le_max_left dC.width dD.width).trans (le_max_left _ _))
        · have hSDle : SC.card ≤ SD.card := le_of_not_ge hSC
          have hmed : n / tseitinWidthDiv ≤ SD.card := by
            simpa [max_eq_right hSDle] using hmax
          refine ⟨dD.conclusion, dD, hDbig', hmed, ?_⟩
          exact dD.concl_card_le_width.trans
            ((le_max_right dC.width dD.width).trans (le_max_left _ _))

/-- Specialization: a full-complex refutation yields a medium complex line. -/
theorem exists_medium_tseitin_complex {n : ℕ} {G : FinGraph n} {χ : Charge n}
    (d : Derivation (tseitinCNF G χ) (∅ : Clause))
    (hUniv : d.tseitinComplex = univ) (hn : 2 ≤ n) :
    ∃ (C : Clause) (dC : Derivation (tseitinCNF G χ) C),
      dC.tseitinComplex.card ≤ n / 2 ∧
        n / tseitinWidthDiv ≤ dC.tseitinComplex.card ∧
          C.card ≤ d.width := by
  have hLarge : n / 2 < d.tseitinComplex.card := by
    simp [hUniv]
    omega
  exact exists_medium_tseitin_complex_of_large d hn hLarge

end SATurday.ProofComplexity


