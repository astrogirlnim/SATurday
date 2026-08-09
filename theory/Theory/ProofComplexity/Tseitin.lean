import Theory.ProofComplexity.FinGraph
import Theory.ProofComplexity.Width
import Theory.ProofComplexity.SizeWidth

/-!
# Tseitin CNF on FinGraphs (Ladder Rung R2, item 2)

Charge, edge variables, Tseitin CNF construction, odd-charge unsat, and the
complex bridge toward expander width lower bounds.

Encoding: each edge `e` gets variable `edgeVar e`. At vertex `v` of degree `d`,
the `2^(d-1)` parity clauses force the XOR of incident edge variables to equal
the charge `χ v`.

Complex packaging: derivation-indexed semantic erase-minimal vertex sets
`Derivation.tseitinComplex` (minimal `S` such that parity axioms on `S` imply
the conclusion, chosen inside the parent union at resolution steps). Pin target
`tseitin_complex_res_subset` holds by that choice. Coarse divisor
`tseitinWidthDiv = 4` remains; sharp medium floor is
`tseitinMediumFloor n = (n / 2 + 2) / 2` (Nat form of ceil of half the
exceeding half-size union). Width LB uses the sharp floor. Coarse form
`α * (n / tseitinWidthDiv)` is a weaker corollary. Petersen coarse floor 2 and
sharp floor 3 do not beat `cnfWidth = 3`. Heawood has `HasExpansion _ 1` and
unconditional width ≥ 4 (sharp floor beats regular axiom width 3).

LOG: R2 Tseitin Heawood unconditional expander width LB
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

/-- Reserved coarse width divisor for the expander Tseitin bound.
Pin started at 2; raised to 4 for the weak `n / 4` packaging. The certified
width theorem uses the sharper `tseitinMediumFloor`. -/
def tseitinWidthDiv : ℕ := 4

/-- Sharp medium-complex cardinality floor from BSW union arithmetic:
if `n/2 < a + b` then `(n/2 + 2) / 2 ≤ max a b`, since
`max ≥ ceil((a+b)/2)` and `a+b ≥ n/2 + 1`. -/
def tseitinMediumFloor (n : ℕ) : ℕ := (n / 2 + 2) / 2

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

/-! ## Cut coverage -/

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

/-! ## Semantic implication and edge flips -/

/-- Parity axioms on vertex set `S` semantically imply clause `C`. -/
def tseitinImplies {n : ℕ} (G : FinGraph n) (χ : Charge n)
    (S : Finset (Fin n)) (C : Clause) : Prop :=
  ∀ a : Assignment, (∀ v ∈ S, vertexParitySat G χ a v) → clauseSat a C

/-- Flip one propositional variable. -/
def flipVar (a : Assignment) (x : ℕ) : Assignment :=
  fun y => if y = x then !a y else a y

/-- Flip the edge variable of `e`. -/
def flipEdge {n : ℕ} (a : Assignment) (e : FinEdge n) : Assignment :=
  flipVar a (edgeVar e)

/-- Membership after flipping an incident edge. -/
theorem mem_trueIncident_flipEdge {n : ℕ} (hn : 0 < n) (G : FinGraph n)
    (a : Assignment) {e : FinEdge n} {v : Fin n}
    (hinc : e ∈ incident G v) (e' : FinEdge n) :
    e' ∈ trueIncident G (flipEdge a e) v ↔
      (e' = e ∧ a (edgeVar e) ≠ true) ∨
        (e' ≠ e ∧ e' ∈ trueIncident G a v) := by
  classical
  have hinj := edgeVar_injective n hn
  simp only [trueIncident, flipEdge, flipVar, mem_filter]
  by_cases he'e : e' = e
  · cases ha : a (edgeVar e) <;> simp [hinc, ha, he'e]
  · have hvar : edgeVar e' ≠ edgeVar e := fun h => he'e (hinj h)
    simp [he'e, hvar]

/-- Flipping an incident edge toggles membership of that edge in `trueIncident`. -/
theorem trueIncident_flipEdge_eq {n : ℕ} (hn : 0 < n) (G : FinGraph n)
    (a : Assignment) {e : FinEdge n} {v : Fin n}
    (hinc : e ∈ incident G v) :
    trueIncident G (flipEdge a e) v =
      if e ∈ trueIncident G a v then
        (trueIncident G a v).erase e
      else
        insert e (trueIncident G a v) := by
  classical
  ext e'
  rw [mem_trueIncident_flipEdge hn G a hinc]
  by_cases heT : e ∈ trueIncident G a v
  · have ha : a (edgeVar e) = true := (mem_filter.mp heT).2
    simp [heT, mem_erase, ha]
  · have ha : a (edgeVar e) ≠ true := by
      intro ht
      exact heT (mem_filter.mpr ⟨hinc, ht⟩)
    by_cases he'e : e' = e
    · subst he'e
      simp [heT, ha]
    · simp [heT, he'e, mem_insert]

/-- Flipping an incident edge flips the local trueIncident parity bit. -/
theorem trueIncident_card_mod_flipEdge {n : ℕ} (hn : 0 < n) (G : FinGraph n)
    (a : Assignment) {e : FinEdge n} {v : Fin n}
    (hinc : e ∈ incident G v) :
    (trueIncident G (flipEdge a e) v).card % 2 =
      ((trueIncident G a v).card + 1) % 2 := by
  classical
  rw [trueIncident_flipEdge_eq hn G a hinc]
  by_cases heT : e ∈ trueIncident G a v
  · have hcard : ((trueIncident G a v).erase e).card =
        (trueIncident G a v).card - 1 := card_erase_of_mem heT
    have hpos : 0 < (trueIncident G a v).card := card_pos.mpr ⟨e, heT⟩
    simp [heT, hcard]
    omega
  · have hcard : (insert e (trueIncident G a v)).card =
        (trueIncident G a v).card + 1 := card_insert_of_notMem heT
    simp [heT, hcard]

/-- Flipping an incident edge negates local parity satisfaction. -/
theorem vertexParitySat_flipEdge {n : ℕ} (hn : 0 < n) {G : FinGraph n} {χ : Charge n}
    {a : Assignment} {e : FinEdge n} {v : Fin n}
    (hinc : e ∈ incident G v) :
    vertexParitySat G χ (flipEdge a e) v ↔ ¬ vertexParitySat G χ a v := by
  have hmod := trueIncident_card_mod_flipEdge hn G a hinc
  simp only [vertexParitySat]
  have hbit : (trueIncident G a v).card % 2 = 0 ∨
      (trueIncident G a v).card % 2 = 1 := Nat.mod_two_eq_zero_or_one _
  rcases hbit with h0 | h1
  · have hflip : (trueIncident G (flipEdge a e) v).card % 2 = 1 := by
      have : ((trueIncident G a v).card + 1) % 2 = 1 := by omega
      exact hmod.trans this
    cases χ v <;> simp [h0, hflip]
  · have hflip : (trueIncident G (flipEdge a e) v).card % 2 = 0 := by
      have : ((trueIncident G a v).card + 1) % 2 = 0 := by omega
      exact hmod.trans this
    cases χ v <;> simp [h1, hflip]

/-- Flipping a non-incident edge preserves local parity satisfaction. -/
theorem vertexParitySat_flipEdge_of_not_mem {n : ℕ} (hn : 0 < n) {G : FinGraph n}
    {χ : Charge n} {a : Assignment} {e : FinEdge n} {v : Fin n}
    (hinc : e ∉ incident G v) :
    vertexParitySat G χ (flipEdge a e) v ↔ vertexParitySat G χ a v := by
  classical
  have hinj := edgeVar_injective n hn
  have hEq : trueIncident G (flipEdge a e) v = trueIncident G a v := by
    ext e'
    simp only [trueIncident, flipEdge, flipVar, mem_filter]
    by_cases heq : edgeVar e' = edgeVar e
    · have he'e : e' = e := hinj heq
      subst he'e
      simp [hinc]
    · simp [heq]
  simp [vertexParitySat, hEq]

/-- Flipping a variable absent from `C` preserves clause satisfaction. -/
theorem clauseSat_flipVar_of_not_mem (a : Assignment) (C : Clause) (x : ℕ)
    (hx : x ∉ clauseVars C) :
    clauseSat (flipVar a x) C ↔ clauseSat a C := by
  classical
  constructor
  · rintro ⟨l, hl, hlit⟩
    refine ⟨l, hl, ?_⟩
    have hvar : l.var ≠ x := by
      intro heq
      exact hx (mem_image.mpr ⟨l, hl, heq⟩)
    simpa [litSat, flipVar, hvar] using hlit
  · rintro ⟨l, hl, hlit⟩
    refine ⟨l, hl, ?_⟩
    have hvar : l.var ≠ x := by
      intro heq
      exact hx (mem_image.mpr ⟨l, hl, heq⟩)
    simpa [litSat, flipVar, hvar] using hlit

theorem clauseSat_flipEdge_of_not_mem {n : ℕ} (a : Assignment) (C : Clause)
    (e : FinEdge n) (hx : edgeVar e ∉ clauseVars C) :
    clauseSat (flipEdge a e) C ↔ clauseSat a C :=
  clauseSat_flipVar_of_not_mem a C (edgeVar e) hx

/-- `S` is erase-minimal among vertex sets that imply `C`. -/
def IsEraseMinimalComplex {n : ℕ} (G : FinGraph n) (χ : Charge n)
    (S : Finset (Fin n)) (C : Clause) : Prop :=
  tseitinImplies G χ S C ∧
    ∀ v ∈ S, ¬ tseitinImplies G χ (S.erase v) C

/-- Every implying set has an erase-minimal subset. -/
theorem exists_eraseMinimalComplex {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (S : Finset (Fin n)) (h : tseitinImplies G χ S C) :
    ∃ T ⊆ S, IsEraseMinimalComplex G χ T C := by
  classical
  revert h
  refine Finset.strongInductionOn S ?_
  intro S IH h
  by_cases hmin : ∀ v ∈ S, ¬ tseitinImplies G χ (S.erase v) C
  · exact ⟨S, subset_rfl, h, hmin⟩
  · simp only [not_forall, Classical.not_imp, not_not] at hmin
    obtain ⟨v, hv, hvimp⟩ := hmin
    obtain ⟨T, hTsub, hTmin⟩ := IH (S.erase v) (erase_ssubset hv) hvimp
    exact ⟨T, hTsub.trans (erase_subset v S), hTmin⟩

/-- Choose an erase-minimal complex inside an implying set. -/
noncomputable def chooseEraseMinimalComplex {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (S : Finset (Fin n)) (h : tseitinImplies G χ S C) :
    Finset (Fin n) :=
  Classical.choose (exists_eraseMinimalComplex S h)

theorem chooseEraseMinimalComplex_subset {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (S : Finset (Fin n)) (h : tseitinImplies G χ S C) :
    chooseEraseMinimalComplex S h ⊆ S :=
  (Classical.choose_spec (exists_eraseMinimalComplex S h)).1

theorem chooseEraseMinimalComplex_isMinimal {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (S : Finset (Fin n)) (h : tseitinImplies G χ S C) :
    IsEraseMinimalComplex G χ (chooseEraseMinimalComplex S h) C :=
  (Classical.choose_spec (exists_eraseMinimalComplex S h)).2

/-- Endpoint of a cut edge that lies in `S`. -/
noncomputable def cutEndpointIn {n : ℕ} {G : FinGraph n} {S : Finset (Fin n)}
    {e : FinEdge n} (_he : e ∈ edgeBoundary G S) : Fin n :=
  if e.val.1 ∈ S then e.val.1 else e.val.2

theorem cutEndpointIn_mem {n : ℕ} {G : FinGraph n} {S : Finset (Fin n)}
    {e : FinEdge n} (he : e ∈ edgeBoundary G S) :
    cutEndpointIn (S := S) he ∈ S := by
  simp only [cutEndpointIn]
  have he' := (mem_edgeBoundary_iff.mp he).2
  by_cases h1 : e.val.1 ∈ S
  · simp [h1]
  · simp [h1]
    rcases he' with ⟨h1', _⟩ | ⟨_, h2⟩
    · exact absurd h1' h1
    · exact h2

theorem cutEndpointIn_incident {n : ℕ} {G : FinGraph n} {S : Finset (Fin n)}
    {e : FinEdge n} (he : e ∈ edgeBoundary G S) :
    e ∈ incident G (cutEndpointIn (S := S) he) := by
  have heG := (mem_edgeBoundary_iff.mp he).1
  have he' := (mem_edgeBoundary_iff.mp he).2
  unfold cutEndpointIn
  by_cases h1 : e.val.1 ∈ S
  · simp [h1, mem_incident_iff, heG]
  · have h2 : e.val.2 ∈ S := by
      rcases he' with ⟨h1', _⟩ | ⟨_, h2⟩
      · exact absurd h1' h1
      · exact h2
    simp [h1, mem_incident_iff, heG]

/-- A cut edge is incident in `S` only at `cutEndpointIn`. -/
theorem not_mem_incident_of_cut_other {n : ℕ} {G : FinGraph n} {S : Finset (Fin n)}
    {e : FinEdge n} (he : e ∈ edgeBoundary G S) {u : Fin n}
    (huS : u ∈ S) (hne : u ≠ cutEndpointIn (S := S) he) :
    e ∉ incident G u := by
  intro hinc
  have hcut := (mem_edgeBoundary_iff.mp he).2
  have hends : u = e.val.1 ∨ u = e.val.2 := by
    rcases (mem_incident_iff.mp hinc).2 with h1 | h2
    · exact Or.inl h1.symm
    · exact Or.inr h2.symm
  by_cases h1 : e.val.1 ∈ S
  · have hv : cutEndpointIn (S := S) he = e.val.1 := by simp [cutEndpointIn, h1]
    have h2out : e.val.2 ∉ S := by
      rcases hcut with ⟨_, h2out⟩ | ⟨h1out, _⟩
      · exact h2out
      · exact absurd h1 h1out
    rcases hends with hu1 | hu2
    · exact hne (hu1.trans hv.symm)
    · exact h2out (hu2 ▸ huS)
  · have hv : cutEndpointIn (S := S) he = e.val.2 := by simp [cutEndpointIn, h1]
    rcases hends with hu1 | hu2
    · exact h1 (hu1 ▸ huS)
    · exact hne (hu2.trans hv.symm)

/-- Erase-minimal complexes cut-cover their clause (BSW flip argument). -/
theorem cutCovered_of_eraseMinimal {n : ℕ} (hn : 0 < n) {G : FinGraph n}
    {χ : Charge n} {S : Finset (Fin n)} {C : Clause}
    (hmin : IsEraseMinimalComplex G χ S C) : cutCovered G S C := by
  classical
  intro e he
  by_contra hx
  set v := cutEndpointIn (S := S) he
  have hvS : v ∈ S := cutEndpointIn_mem he
  have hinc : e ∈ incident G v := cutEndpointIn_incident he
  have hImp := hmin.1
  have hNot := hmin.2 v hvS
  have hEx : ∃ a, (∀ u ∈ S.erase v, vertexParitySat G χ a u) ∧ ¬ clauseSat a C := by
    simpa [tseitinImplies, not_forall, Classical.not_imp] using hNot
  obtain ⟨a, haS, haC⟩ := hEx
  have haVfalse : ¬ vertexParitySat G χ a v := by
    intro hav
    have haAll : ∀ u ∈ S, vertexParitySat G χ a u := by
      intro u hu
      by_cases huv : u = v
      · simpa [huv] using hav
      · exact haS u (mem_erase.mpr ⟨huv, hu⟩)
    exact haC (hImp a haAll)
  set a' := flipEdge a e
  have ha'C : ¬ clauseSat a' C := by
    simpa [a', clauseSat_flipEdge_of_not_mem a C e hx] using haC
  have ha'S : ∀ u ∈ S.erase v, vertexParitySat G χ a' u := by
    intro u hu
    have huS : u ∈ S := (mem_erase.mp hu).2
    have hune : u ≠ v := (mem_erase.mp hu).1
    have hnot := not_mem_incident_of_cut_other he huS hune
    exact (vertexParitySat_flipEdge_of_not_mem hn (e := e) (v := u) hnot).mpr (haS u hu)
  have ha'V : vertexParitySat G χ a' v :=
    (vertexParitySat_flipEdge hn (e := e) (v := v) hinc).mpr haVfalse
  have ha'All : ∀ u ∈ S, vertexParitySat G χ a' u := by
    intro u hu
    by_cases huv : u = v
    · simpa [huv] using ha'V
    · exact ha'S u (mem_erase.mpr ⟨huv, hu⟩)
  exact ha'C (hImp a' ha'All)

/-! ## Implication bridges -/

/-- Falsifying a forbidding clause forces the true star to equal the forbidden set. -/
theorem trueIncident_eq_of_not_clauseSat_parityForbid {n : ℕ}
    (G : FinGraph n) (v : Fin n) (S : Finset (FinEdge n)) (a : Assignment)
    (hS : S ⊆ incident G v)
    (hfalse : ¬ clauseSat a (parityForbidClause (incident G v) S)) :
    trueIncident G a v = S := by
  classical
  set I := incident G v
  ext e
  simp only [trueIncident, mem_filter]
  constructor
  · intro ⟨heI, ha⟩
    by_contra hne
    -- build a satisfied literal from e ∉ S with positive polarity expectation
    have hlit : (⟨edgeVar e, decide (e ∉ S)⟩ : Literal) ∈ parityForbidClause I S := by
      refine mem_image.mpr ⟨e, heI, rfl⟩
    have : clauseSat a (parityForbidClause I S) := by
      refine ⟨⟨edgeVar e, decide (e ∉ S)⟩, hlit, ?_⟩
      simp [litSat, ha, hne]
    exact hfalse this
  · intro heS
    have heI : e ∈ I := hS heS
    refine ⟨heI, ?_⟩
    by_contra haF
    have ha : a (edgeVar e) = false := eq_false_of_ne_true haF
    have hlit : (⟨edgeVar e, decide (e ∉ S)⟩ : Literal) ∈ parityForbidClause I S := by
      refine mem_image.mpr ⟨e, heI, rfl⟩
    have : clauseSat a (parityForbidClause I S) := by
      refine ⟨⟨edgeVar e, decide (e ∉ S)⟩, hlit, ?_⟩
      simp [litSat, ha, heS]
    exact hfalse this

/-- Local parity satisfaction implies the vertex parity CNF. -/
theorem cnfSat_of_vertexParitySat {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {a : Assignment} {v : Fin n}
    (ha : vertexParitySat G χ a v) :
    cnfSat a (vertexParityClauses G χ v) := by
  classical
  intro C hC
  simp only [vertexParityClauses, mem_image] at hC
  obtain ⟨S, hS, rfl⟩ := hC
  have hSsub : S ⊆ incident G v := mem_powerset.mp (mem_filter.mp hS).1
  have hSpar : decide (S.card % 2 = 1) ≠ χ v := (mem_filter.mp hS).2
  by_contra hfalse
  have hEq := trueIncident_eq_of_not_clauseSat_parityForbid G v S a hSsub hfalse
  have : decide ((trueIncident G a v).card % 2 = 1) ≠ χ v := by
    simpa [hEq] using hSpar
  exact this (by simpa [vertexParitySat] using ha)

/-- A hypothesis clause is implied by its vertex singleton. -/
theorem tseitinImplies_hyp {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (hC : C ∈ tseitinCNF G χ) :
    tseitinImplies G χ ({hypVertex hC} : Finset (Fin n)) C := by
  intro a ha
  have hv := ha (hypVertex hC) (mem_singleton_self _)
  exact cnfSat_of_vertexParitySat hv C (hypVertex_spec hC)

/-- Empty set does not imply a Tseitin axiom clause. -/
theorem not_tseitinImplies_empty_hyp {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (hC : C ∈ tseitinCNF G χ) :
    ¬ tseitinImplies G χ (∅ : Finset (Fin n)) C := by
  classical
  intro himp
  have hv := hypVertex_spec hC
  simp only [vertexParityClauses, mem_image] at hv
  obtain ⟨S, hS, heqC⟩ := hv
  set I := incident G (hypVertex hC)
  set a : Assignment := fun x => decide (∃ e ∈ S, edgeVar e = x)
  have hSsub : S ⊆ I := mem_powerset.mp (mem_filter.mp hS).1
  have hT : I.filter (fun e => a (edgeVar e) = true) = S := by
    ext e
    simp only [mem_filter, a, decide_eq_true_iff]
    constructor
    · intro ⟨heI, ⟨e', he'S, heq⟩⟩
      have hn0 : n ≠ 0 := by
        intro hn0
        have : e.val.1.val < n := e.val.1.isLt
        omega
      have hinj := edgeVar_injective n (Nat.pos_of_ne_zero hn0)
      exact (hinj heq) ▸ he'S
    · intro heS
      exact ⟨hSsub heS, ⟨e, heS, rfl⟩⟩
  have hfalse : ¬ clauseSat a (parityForbidClause I S) := by
    simpa [hT] using not_clauseSat_parityForbidClause I a
  have hsat : clauseSat a C := himp a (by intro v hv; simp at hv)
  exact hfalse (heqC ▸ hsat)

/-- Hypothesis singleton is erase-minimal. -/
theorem isEraseMinimalComplex_hyp {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (hC : C ∈ tseitinCNF G χ) :
    IsEraseMinimalComplex G χ ({hypVertex hC} : Finset (Fin n)) C := by
  refine ⟨tseitinImplies_hyp hC, ?_⟩
  intro v hv
  have hv' : v = hypVertex hC := mem_singleton.mp hv
  simpa [hv', erase_singleton] using not_tseitinImplies_empty_hyp hC

/-- Implication is preserved by resolution (union of supports). -/
theorem tseitinImplies_resolvent {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C D : Clause} (x : ℕ) {S T : Finset (Fin n)}
    (hC : tseitinImplies G χ S C) (hD : tseitinImplies G χ T D)
    (hx : (⟨x, true⟩ : Literal) ∈ C)
    (hnx : (⟨x, false⟩ : Literal) ∈ D) :
    tseitinImplies G χ (S ∪ T) (resolvent C D x) := by
  intro a ha
  have hCs : clauseSat a C := hC a (fun v hv => ha v (mem_union_left T hv))
  have hDs : clauseSat a D := hD a (fun v hv => ha v (mem_union_right S hv))
  by_cases hax : a x = true
  · obtain ⟨l, hl, hla⟩ := hDs
    have hlne : l ≠ ⟨x, false⟩ := by
      intro heq
      have : a x = false := by simpa [heq, litSat] using hla
      exact Bool.false_ne_true (this.symm.trans hax)
    exact ⟨l, mem_union.mpr (Or.inr (mem_erase.mpr ⟨hlne, hl⟩)), hla⟩
  · obtain ⟨l, hl, hla⟩ := hCs
    have hlne : l ≠ ⟨x, true⟩ := by
      intro heq
      have : a x = true := by simpa [heq, litSat] using hla
      exact hax this
    exact ⟨l, mem_union.mpr (Or.inl (mem_erase.mpr ⟨hlne, hl⟩)), hla⟩

/-! ## Derivation-indexed semantic complexes -/

/-- Proof-carrying erase-minimal complex for a derived clause. -/
structure Derivation.TseitinComplexData {n : ℕ} (G : FinGraph n) (χ : Charge n)
    {C : Clause} (d : Derivation (tseitinCNF G χ) C) where
  S : Finset (Fin n)
  isMinimal : IsEraseMinimalComplex G χ S C

/-- Critical vertex set: erase-minimal semantic complex inside parent union. -/
noncomputable def Derivation.tseitinComplexData {n : ℕ} {G : FinGraph n} {χ : Charge n} :
    {C : Clause} → (d : Derivation (tseitinCNF G χ) C) →
      Derivation.TseitinComplexData G χ d
  | _, .hyp _ hC => ⟨{hypVertex hC}, isEraseMinimalComplex_hyp hC⟩
  | _, .res x dC dD hx hnx =>
    let pC := dC.tseitinComplexData
    let pD := dD.tseitinComplexData
    let hU := tseitinImplies_resolvent x pC.isMinimal.1 pD.isMinimal.1 hx hnx
    ⟨chooseEraseMinimalComplex (pC.S ∪ pD.S) hU,
      chooseEraseMinimalComplex_isMinimal (pC.S ∪ pD.S) hU⟩

/-- Critical vertex set of a derived clause (semantic erase-minimal complex). -/
noncomputable def Derivation.tseitinComplex {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (d : Derivation (tseitinCNF G χ) C) : Finset (Fin n) :=
  d.tseitinComplexData.S

theorem tseitinComplex_isMinimal {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (d : Derivation (tseitinCNF G χ) C) :
    IsEraseMinimalComplex G χ d.tseitinComplex C :=
  d.tseitinComplexData.isMinimal

theorem tseitinComplex_implies {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (d : Derivation (tseitinCNF G χ) C) :
    tseitinImplies G χ d.tseitinComplex C :=
  (tseitinComplex_isMinimal d).1

/-- Every derived line is cut-covered by its semantic complex. -/
theorem tseitin_complex_cutCovered {n : ℕ} (hn : 0 < n) {G : FinGraph n} {χ : Charge n}
    {C : Clause} (d : Derivation (tseitinCNF G χ) C) :
    cutCovered G d.tseitinComplex C :=
  cutCovered_of_eraseMinimal hn (tseitinComplex_isMinimal d)

/-- Hypothesis complexes are singletons. -/
theorem tseitin_complex_hyp_card_le_one {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (hC : C ∈ tseitinCNF G χ) :
    ({hypVertex hC} : Finset (Fin n)).card ≤ 1 := by
  simp

theorem tseitin_complex_hyp_eq {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (hC : C ∈ tseitinCNF G χ) :
    (Derivation.hyp (F := tseitinCNF G χ) C hC).tseitinComplex = {hypVertex hC} :=
  rfl

/-- Pinned name: resolvent complex ⊆ union of parent complexes. -/
theorem tseitin_complex_res_subset {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C D : Clause} (x : ℕ)
    (dC : Derivation (tseitinCNF G χ) C)
    (dD : Derivation (tseitinCNF G χ) D)
    (hx : (⟨x, true⟩ : Literal) ∈ C)
    (hnx : (⟨x, false⟩ : Literal) ∈ D) :
    (Derivation.res x dC dD hx hnx).tseitinComplex ⊆
      dC.tseitinComplex ∪ dD.tseitinComplex := by
  have hU :=
    tseitinImplies_resolvent x dC.tseitinComplexData.isMinimal.1
      dD.tseitinComplexData.isMinimal.1 hx hnx
  simpa [Derivation.tseitinComplex] using
    (chooseEraseMinimalComplex_subset (dC.tseitinComplexData.S ∪ dD.tseitinComplexData.S) hU)

theorem tseitin_complex_hyp_card {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (hC : C ∈ tseitinCNF G χ) :
    (Derivation.hyp (F := tseitinCNF G χ) C hC).tseitinComplex.card = 1 := by
  simp [Derivation.tseitinComplex, Derivation.tseitinComplexData]

theorem tseitin_complex_card_le_n {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (d : Derivation (tseitinCNF G χ) C) :
    d.tseitinComplex.card ≤ n := by
  simpa using (card_le_univ d.tseitinComplex)

/-- Conclusion clause card is at most derivation width. -/
theorem Derivation.concl_card_le_width {F : CNF} {C : Clause}
    (d : Derivation F C) : C.card ≤ d.width := by
  induction d with
  | hyp _ _ => simp [Derivation.width]
  | res _ dC dD _ _ ihC ihD =>
    simp only [Derivation.width, Derivation.conclusion]
    exact le_max_right _ _

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

/-- Complex axioms of a derivation entail its conclusion (semantic packaging). -/
theorem tseitin_complex_entails {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (d : Derivation (tseitinCNF G χ) C) (a : Assignment)
    (ha : ∀ v ∈ d.tseitinComplex, cnfSat a (vertexParityClauses G χ v)) :
    clauseSat a C := by
  have himp := tseitinComplex_implies d
  exact himp a (fun v hv => vertexParitySat_of_cnfSat (ha v hv))

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

/-- Width floor from a covered medium complex at the sharp medium threshold. -/
theorem tseitin_width_ge_alpha_mul_quot {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {α : ℕ} (hα : HasExpansion G α)
    {C : Clause} (dC : Derivation (tseitinCNF G χ) C)
    (hHalf : dC.tseitinComplex.card ≤ n / 2)
    (hMed : tseitinMediumFloor n ≤ dC.tseitinComplex.card)
    (hne : dC.tseitinComplex.Nonempty)
    (hCov : cutCovered G dC.tseitinComplex C)
    (hn : 0 < n) :
    α * tseitinMediumFloor n ≤ dC.width := by
  have hBd := edgeBoundary_card_le_of_cutCovered hCov hn
  have hexp := tseitin_medium_complex_expands hα hne hHalf
  have hαS : α * dC.tseitinComplex.card ≤ C.card := hexp.trans hBd
  have hαn : α * tseitinMediumFloor n ≤ α * dC.tseitinComplex.card :=
    Nat.mul_le_mul_left _ hMed
  exact (hαn.trans hαS).trans dC.concl_card_le_width

/-- Non-vacuity of the raised divisor constant. -/
theorem tseitinWidthDiv_eq : tseitinWidthDiv = 4 := rfl

/-- Coarse quotient is at most the sharp medium floor. -/
theorem tseitin_div_quot_le_mediumFloor (n : ℕ) :
    n / tseitinWidthDiv ≤ tseitinMediumFloor n := by
  simp only [tseitinWidthDiv, tseitinMediumFloor]
  omega

/-- Petersen numeric floor under the coarse divisor. -/
theorem tseitin_petersen_width_floor :
    (1 * 10) / tseitinWidthDiv = 2 := by
  decide

/-- Honest: with coarse divisor 4, Petersen floor does not beat width 3. -/
theorem tseitin_petersen_floor_le_cnfWidth3 :
    (1 * 10) / tseitinWidthDiv ≤ 3 := by
  decide

/-- Sharp medium floor on Petersen equals 3 (still not strictly above width 3). -/
theorem tseitin_petersen_mediumFloor :
    tseitinMediumFloor 10 = 3 := by
  decide

/-- Auxiliary: sum `> n/2` forces `max ≥ tseitinMediumFloor n`. -/
private theorem max_ge_mediumFloor_of_sum_gt_div2 (a b n : ℕ)
    (hsum : n / 2 < a + b) : tseitinMediumFloor n ≤ max a b := by
  have hab : n / 2 + 1 ≤ a + b := Nat.succ_le_of_lt hsum
  have hceil : (a + b + 1) / 2 ≤ max a b := by
    have h2 : a + b ≤ 2 * max a b := by
      cases le_total a b with
      | inl hab =>
        have : max a b = b := max_eq_right hab
        simp [this]; omega
      | inr hba =>
        have : max a b = a := max_eq_left hba
        simp [this]; omega
    omega
  have hfl : tseitinMediumFloor n ≤ (a + b + 1) / 2 := by
    simp only [tseitinMediumFloor]
    omega
  exact hfl.trans hceil

/-- From a derivation whose complex exceeds `n / 2`, extract a medium line. -/
theorem exists_medium_tseitin_complex_of_large {n : ℕ} {G : FinGraph n}
    {χ : Charge n} {C : Clause}
    (π : Derivation (tseitinCNF G χ) C)
    (hn : 2 ≤ n)
    (hLarge : n / 2 < π.tseitinComplex.card) :
    ∃ (C' : Clause) (dC : Derivation (tseitinCNF G χ) C'),
      dC.tseitinComplex.card ≤ n / 2 ∧
        tseitinMediumFloor n ≤ dC.tseitinComplex.card ∧
          dC.width ≤ π.width ∧
            cutCovered G dC.tseitinComplex C' := by
  induction π with
  | hyp _ hC =>
    simp only [tseitin_complex_hyp_eq, card_singleton] at hLarge
    omega
  | res x dC dD hx hnx ihC ihD =>
    have hsub := tseitin_complex_res_subset x dC dD hx hnx
    have hle : (Derivation.res x dC dD hx hnx).tseitinComplex.card ≤
        (dC.tseitinComplex ∪ dD.tseitinComplex).card := card_le_card hsub
    set SC := dC.tseitinComplex
    set SD := dD.tseitinComplex
    have hUnion : n / 2 < (SC ∪ SD).card := lt_of_lt_of_le hLarge hle
    by_cases hCbig : n / 2 < SC.card
    · obtain ⟨C', d', h1, h2, h3, h4⟩ := ihC hCbig
      refine ⟨C', d', h1, h2, h3.trans ?_, h4⟩
      simp only [Derivation.width]
      exact (le_max_left _ _).trans (le_max_left _ _)
    · by_cases hDbig : n / 2 < SD.card
      · obtain ⟨C', d', h1, h2, h3, h4⟩ := ihD hDbig
        refine ⟨C', d', h1, h2, h3.trans ?_, h4⟩
        simp only [Derivation.width]
        exact (le_max_right _ _).trans (le_max_left _ _)
      · have hCbig' : SC.card ≤ n / 2 := Nat.le_of_not_gt hCbig
        have hDbig' : SD.card ≤ n / 2 := Nat.le_of_not_gt hDbig
        have hleUnion : (SC ∪ SD).card ≤ SC.card + SD.card := card_union_le SC SD
        have hsum : n / 2 < SC.card + SD.card := lt_of_lt_of_le hUnion hleUnion
        have hmax : tseitinMediumFloor n ≤ max SC.card SD.card :=
          max_ge_mediumFloor_of_sum_gt_div2 _ _ _ hsum
        have hn0 : 0 < n := by omega
        by_cases hSC : SD.card ≤ SC.card
        · have hmed : tseitinMediumFloor n ≤ SC.card := by
            simpa [max_eq_left hSC] using hmax
          refine ⟨dC.conclusion, dC, hCbig', hmed, ?_, tseitin_complex_cutCovered hn0 dC⟩
          exact (le_max_left dC.width dD.width).trans (le_max_left _ _)
        · have hSDle : SC.card ≤ SD.card := le_of_not_ge hSC
          have hmed : tseitinMediumFloor n ≤ SD.card := by
            simpa [max_eq_right hSDle] using hmax
          refine ⟨dD.conclusion, dD, hDbig', hmed, ?_, tseitin_complex_cutCovered hn0 dD⟩
          exact (le_max_right dC.width dD.width).trans (le_max_left _ _)

/-- Full-complex refutation yields a medium cut-covered line. -/
theorem exists_medium_tseitin_complex {n : ℕ} {G : FinGraph n} {χ : Charge n}
    (d : Derivation (tseitinCNF G χ) (∅ : Clause))
    (hUniv : d.tseitinComplex = univ) (hn : 2 ≤ n) :
    ∃ (C : Clause) (dC : Derivation (tseitinCNF G χ) C),
      dC.tseitinComplex.card ≤ n / 2 ∧
        tseitinMediumFloor n ≤ dC.tseitinComplex.card ∧
          dC.width ≤ d.width ∧
            cutCovered G dC.tseitinComplex C := by
  have hLarge : n / 2 < d.tseitinComplex.card := by
    simp [hUniv]
    omega
  exact exists_medium_tseitin_complex_of_large d hn hLarge


/-! ## Connectivity bridge: complex = univ -/

/-- Full vertex set implies the empty clause under odd charge. -/
theorem tseitinImplies_univ_empty {n : ℕ} {G : FinGraph n} {χ : Charge n}
    (hχ : oddCharge χ) :
    tseitinImplies G χ (univ : Finset (Fin n)) (∅ : Clause) := by
  intro a ha
  have hcnf : cnfSat a (tseitinCNF G χ) := by
    intro C hC
    obtain ⟨v, hv⟩ := mem_tseitinCNF_iff.mp hC
    exact cnfSat_of_vertexParitySat (ha v (mem_univ v)) C hv
  exact absurd ⟨a, hcnf⟩ (tseitinCNF_unsat G χ hχ)

/-- An edge is incident only at its two endpoints. -/
theorem not_mem_incident_of_ne_endpoints {n : ℕ} {G : FinGraph n}
    {e : FinEdge n} {w : Fin n}
    (h1 : w ≠ e.val.1) (h2 : w ≠ e.val.2) : e ∉ incident G w := by
  intro hinc
  rcases (mem_incident_iff.mp hinc).2 with hw | hw
  · exact h1 hw.symm
  · exact h2 hw.symm

/-- Chosen adjacency edge is incident only at the two adjacent vertices. -/
theorem not_mem_incident_adjEdge {n : ℕ} (G : FinGraph n) {u v w : Fin n}
    (h : G.Adj u v) (hwu : w ≠ u) (hwv : w ≠ v) :
    G.adjEdge h ∉ incident G w := by
  intro hinc
  rcases (mem_incident_iff.mp hinc).2 with hw | hw
  · rcases (G.adjEdge_spec h).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hwu (hw.symm.trans h1)
    · exact hwv (hw.symm.trans h1)
  · rcases (G.adjEdge_spec h).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hwv (hw.symm.trans h2)
    · exact hwu (hw.symm.trans h2)

/-- Flip preserves `trueIncident` at vertices not incident to the flipped edge. -/
theorem trueIncident_flipEdge_of_not_mem {n : ℕ} (hn : 0 < n) (G : FinGraph n)
    (a : Assignment) {e : FinEdge n} {w : Fin n}
    (hinc : e ∉ incident G w) :
    trueIncident G (flipEdge a e) w = trueIncident G a w := by
  ext e'
  have hinj := edgeVar_injective n hn
  simp only [trueIncident, flipEdge, flipVar, mem_filter]
  by_cases heq : edgeVar e' = edgeVar e
  · have he'e : e' = e := hinj heq
    subst he'e
    simp [hinc]
  · simp [heq]

/-- Reachability cannot leave a set with empty edge boundary. -/
theorem reachable_mem_of_edgeBoundary_empty {n : ℕ} {G : FinGraph n}
    {S : Finset (Fin n)} (hbd : edgeBoundary G S = ∅) {u v : Fin n}
    (hu : u ∈ S) (h : G.Reachable u v) : v ∈ S := by
  induction h with
  | refl => exact hu
  | tail hreach hadj ih =>
    have heG := (G.adjEdge_spec hadj).1
    have hmid := ih
    by_contra hv
    have hcut : G.adjEdge hadj ∈ edgeBoundary G S := by
      refine mem_edgeBoundary_iff.mpr ⟨heG, ?_⟩
      rcases (G.adjEdge_spec hadj).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by simpa [h1] using hmid,
          fun hin => hv (by simpa [h2] using hin)⟩
      · exact Or.inr ⟨fun hin => hv (by simpa [h1] using hin),
          by simpa [h2] using hmid⟩
    simp [hbd] at hcut

/-- Proper nonempty subsets of a connected graph have nonempty cut. -/
theorem edgeBoundary_nonempty_of_connected_proper {n : ℕ} {G : FinGraph n}
    (hG : G.IsConnected) {S : Finset (Fin n)}
    (hne : S.Nonempty) (hS : S ≠ univ) :
    (edgeBoundary G S).Nonempty := by
  classical
  obtain ⟨u, hu⟩ := hne
  obtain ⟨v, hv⟩ : ∃ v : Fin n, v ∉ S := by
    by_contra h
    push Not at h
    exact hS (eq_univ_of_forall h)
  by_contra hbd
  have hbd' : edgeBoundary G S = ∅ := by
    simpa [Finset.not_nonempty_iff_eq_empty] using hbd
  have hvS : v ∈ S := reachable_mem_of_edgeBoundary_empty hbd' hu (hG u v)
  exact hv hvS

/-- On a connected graph, parity constraints on any proper vertex set are sat. -/
theorem exists_vertexParitySat_of_ne_univ {n : ℕ} (hn : 0 < n) {G : FinGraph n}
    {χ : Charge n} (hG : G.IsConnected) {S : Finset (Fin n)} (hS : S ≠ univ) :
    ∃ a : Assignment, ∀ v ∈ S, vertexParitySat G χ a v := by
  classical
  revert hS
  refine Finset.strongInductionOn S ?_
  intro S IH hS
  by_cases hempty : S = ∅
  · subst hempty
    exact ⟨fun _ => false, by simp⟩
  · have hne : S.Nonempty := nonempty_iff_ne_empty.mpr hempty
    obtain ⟨e, he⟩ := edgeBoundary_nonempty_of_connected_proper hG hne hS
    set x := cutEndpointIn (S := S) he
    have hx : x ∈ S := cutEndpointIn_mem he
    have hinc : e ∈ incident G x := cutEndpointIn_incident he
    have hEraseNe : S.erase x ≠ univ := by
      intro hEu
      exact (mem_erase.mp (hEu ▸ mem_univ x)).1 rfl
    obtain ⟨a, ha⟩ := IH (S.erase x) (erase_ssubset hx) hEraseNe
    by_cases hsat : vertexParitySat G χ a x
    · refine ⟨a, ?_⟩
      intro v hv
      by_cases hvx : v = x
      · simpa [hvx] using hsat
      · exact ha v (mem_erase.mpr ⟨hvx, hv⟩)
    · set a' := flipEdge a e
      refine ⟨a', ?_⟩
      intro v hv
      by_cases hvx : v = x
      · subst hvx
        exact (vertexParitySat_flipEdge hn (e := e) (v := x) hinc).mpr hsat
      · have hnot := not_mem_incident_of_cut_other he hv hvx
        exact (vertexParitySat_flipEdge_of_not_mem hn (e := e) (v := v) hnot).mpr
          (ha v (mem_erase.mpr ⟨hvx, hv⟩))

/-- Empty clause is never satisfied. -/
theorem not_clauseSat_empty (a : Assignment) : ¬ clauseSat a (∅ : Clause) := by
  simp [clauseSat]

/-- Under connectivity, the only set implying `∅` is `univ`. -/
theorem tseitinImplies_empty_eq_univ {n : ℕ} (hn : 0 < n) {G : FinGraph n}
    {χ : Charge n} (hG : G.IsConnected) {S : Finset (Fin n)}
    (h : tseitinImplies G χ S (∅ : Clause)) : S = univ := by
  by_contra hS
  obtain ⟨a, ha⟩ := exists_vertexParitySat_of_ne_univ hn hG hS
  exact not_clauseSat_empty a (h a ha)

/-- Semantic complex of any refutation is the full vertex set on a connected graph. -/
theorem tseitin_complex_eq_univ {n : ℕ} (hn : 0 < n) {G : FinGraph n} {χ : Charge n}
    (hG : G.IsConnected) (d : Derivation (tseitinCNF G χ) (∅ : Clause)) :
    d.tseitinComplex = univ :=
  tseitinImplies_empty_eq_univ hn hG (tseitinComplex_implies d)

/-! ## Width assembly -/

/-- Semantic complex of a refutation is univ when implying sets for `∅` are unique. -/
theorem tseitin_complex_eq_univ_of_unique {n : ℕ} {G : FinGraph n} {χ : Charge n}
    (d : Derivation (tseitinCNF G χ) (∅ : Clause))
    (hunique : ∀ S : Finset (Fin n), tseitinImplies G χ S (∅ : Clause) → S = univ) :
    d.tseitinComplex = univ :=
  hunique _ (tseitinComplex_implies d)

/-- Width lower bound from full complex + medium extraction + cut coverage. -/
theorem tseitin_expander_width_lower_bound_of_univ {n : ℕ} {G : FinGraph n}
    {χ : Charge n} {α : ℕ}
    (hα : HasExpansion G α)
    (d : Derivation (tseitinCNF G χ) (∅ : Clause))
    (hUniv : d.tseitinComplex = univ) (hn : 2 ≤ n) :
    α * tseitinMediumFloor n ≤ d.width := by
  obtain ⟨C, dC, hHalf, hMed, hw, hCov⟩ := exists_medium_tseitin_complex d hUniv hn
  have hn0 : 0 < n := by omega
  by_cases hdiv : tseitinMediumFloor n = 0
  · simp [hdiv]
  · have hne : dC.tseitinComplex.Nonempty := by
      have hpos : 0 < tseitinMediumFloor n := Nat.pos_of_ne_zero hdiv
      exact card_pos.mp (lt_of_lt_of_le hpos hMed)
    have hge := tseitin_width_ge_alpha_mul_quot hα dC hHalf hMed hne hCov hn0
    exact hge.trans hw

/-- Coarse corollary: `α * (n / tseitinWidthDiv)` via `tseitin_div_quot_le_mediumFloor`. -/
theorem tseitin_expander_width_lower_bound_coarse_of_univ {n : ℕ} {G : FinGraph n}
    {χ : Charge n} {α : ℕ}
    (hα : HasExpansion G α)
    (d : Derivation (tseitinCNF G χ) (∅ : Clause))
    (hUniv : d.tseitinComplex = univ) (hn : 2 ≤ n) :
    α * (n / tseitinWidthDiv) ≤ d.width := by
  have hsharp := tseitin_expander_width_lower_bound_of_univ hα d hUniv hn
  exact (Nat.mul_le_mul_left α (tseitin_div_quot_le_mediumFloor n)).trans hsharp

/-- Expander width lower bound for Tseitin (semantic complex = univ via connectivity). -/
theorem tseitin_expander_width_lower_bound {n : ℕ} {G : FinGraph n}
    {χ : Charge n} {α : ℕ}
    (hα : HasExpansion G α) (hα1 : 1 ≤ α)
    (d : Derivation (tseitinCNF G χ) (∅ : Clause)) (hn : 2 ≤ n) :
    α * tseitinMediumFloor n ≤ d.width := by
  have hn0 : 0 < n := by omega
  have hG := hα.isConnected hα1
  exact tseitin_expander_width_lower_bound_of_univ hα d
    (tseitin_complex_eq_univ hn0 hG d) hn

/-- Coarse form of the expander width lower bound. -/
theorem tseitin_expander_width_lower_bound_coarse {n : ℕ} {G : FinGraph n}
    {χ : Charge n} {α : ℕ}
    (hα : HasExpansion G α) (hα1 : 1 ≤ α)
    (d : Derivation (tseitinCNF G χ) (∅ : Clause)) (hn : 2 ≤ n) :
    α * (n / tseitinWidthDiv) ≤ d.width := by
  have hn0 : 0 < n := by omega
  have hG := hα.isConnected hα1
  exact tseitin_expander_width_lower_bound_coarse_of_univ hα d
    (tseitin_complex_eq_univ hn0 hG d) hn

/-- Size corollary under a full-complex hypothesis (BSW reuse). -/
theorem tseitin_expander_size_lower_bound_of_univ {n : ℕ} {G : FinGraph n}
    {χ : Charge n} {α : ℕ}
    (hα : HasExpansion G α) (_hχ : oddCharge χ)
    (hUnivAll : ∀ d : Derivation (tseitinCNF G χ) (∅ : Clause),
      d.tseitinComplex = univ)
    (d : Derivation (tseitinCNF G χ) (∅ : Clause))
    (hn : 2 ≤ n) :
    let W := α * tseitinMediumFloor n
    2 ^ ((W - cnfWidth (tseitinCNF G χ)) * (W - cnfWidth (tseitinCNF G χ)) /
          (bswRateConst * (cnfVars (tseitinCNF G χ)).card)) ≤ d.size := by
  intro W
  refine bsw_size_lower_bound (tseitinCNF G χ) W ?_ d
  intro d'
  exact tseitin_expander_width_lower_bound_of_univ hα d' (hUnivAll d') hn

/-- Size corollary from expansion (connectivity supplies complex = univ). -/
theorem tseitin_expander_size_lower_bound {n : ℕ} {G : FinGraph n}
    {χ : Charge n} {α : ℕ}
    (hα : HasExpansion G α) (hα1 : 1 ≤ α) (hχ : oddCharge χ)
    (d : Derivation (tseitinCNF G χ) (∅ : Clause)) (hn : 2 ≤ n) :
    let W := α * tseitinMediumFloor n
    2 ^ ((W - cnfWidth (tseitinCNF G χ)) * (W - cnfWidth (tseitinCNF G χ)) /
          (bswRateConst * (cnfVars (tseitinCNF G χ)).card)) ≤ d.size := by
  intro W
  have hn0 : 0 < n := by omega
  have hG := hα.isConnected hα1
  exact tseitin_expander_size_lower_bound_of_univ hα hχ
    (fun d' => tseitin_complex_eq_univ hn0 hG d') d hn

/-- Honest Petersen non-vacuity status: coarse divisor 4 gives floor 2, not above width 3. -/
theorem tseitin_petersen_floor_not_gt_cnfWidth3 :
    ¬ (3 < (1 * 10) / tseitinWidthDiv) := by
  decide

/-- Honest: coarse Heawood floor equals 3, not strictly above width 3. -/
theorem tseitin_heawood_coarse_floor_not_gt_cnfWidth3 :
    ¬ (3 < 1 * (14 / tseitinWidthDiv)) := by
  decide

/-! ## Regular degree implies Tseitin axiom width; Heawood beats -/

/-- Every vertex-parity clause has cardinality equal to the vertex degree. -/
theorem card_mem_vertexParityClauses {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {v : Fin n} {C : Clause} (hC : C ∈ vertexParityClauses G χ v) (hn : 0 < n) :
    C.card = degree G v := by
  obtain ⟨S, hS, rfl⟩ := mem_image.mp hC
  simpa [degree] using card_parityForbidClause (incident G v) S hn

/-- Every Tseitin hypothesis clause has cardinality equal to some vertex degree. -/
theorem exists_degree_eq_card_mem_tseitinCNF {n : ℕ} {G : FinGraph n} {χ : Charge n}
    {C : Clause} (hC : C ∈ tseitinCNF G χ) (hn : 0 < n) :
    ∃ v : Fin n, C.card = degree G v := by
  obtain ⟨v, hv⟩ := mem_tseitinCNF_iff.mp hC
  exact ⟨v, card_mem_vertexParityClauses hv hn⟩

/-- Under `d`-regularity, every Tseitin clause has card `d`. -/
theorem card_mem_tseitinCNF_of_regular {n d : ℕ} {G : FinGraph n} {χ : Charge n}
    (hreg : IsRegular G d) {C : Clause} (hC : C ∈ tseitinCNF G χ) (hn : 0 < n) :
    C.card = d := by
  obtain ⟨v, hv⟩ := exists_degree_eq_card_mem_tseitinCNF hC hn
  exact hv.trans (hreg v)

/-- Positive-degree regular graphs have a nonempty Tseitin CNF. -/
theorem tseitinCNF_nonempty_of_regular {n d : ℕ} {G : FinGraph n} {χ : Charge n}
    (hreg : IsRegular G d) (hn : 0 < n) (hd : 0 < d) :
    (tseitinCNF G χ).Nonempty := by
  let v : Fin n := ⟨0, hn⟩
  have hdeg : degree G v = d := hreg v
  have hIcard : (incident G v).card = d := hdeg
  have hIpos : (incident G v).Nonempty := by
    exact card_pos.mp (by omega)
  obtain ⟨e, he⟩ := hIpos
  -- At least one wrong-parity subset of the star exists when d > 0.
  -- Take empty if χ v = true (even parity empty mismatches odd charge), else {e}.
  classical
  by_cases hχ : χ v = true
  · refine ⟨parityForbidClause (incident G v) ∅, ?_⟩
    refine mem_tseitinCNF_iff.mpr ⟨v, ?_⟩
    refine mem_image.mpr ⟨∅, ?_, rfl⟩
    refine mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), ?_⟩
    simp [hχ]
  · refine ⟨parityForbidClause (incident G v) ({e} : Finset (FinEdge n)), ?_⟩
    refine mem_tseitinCNF_iff.mpr ⟨v, ?_⟩
    refine mem_image.mpr ⟨{e}, ?_, rfl⟩
    refine mem_filter.mpr ⟨mem_powerset.mpr (singleton_subset_iff.mpr he), ?_⟩
    have hχf : χ v = false := eq_false_of_ne_true hχ
    simp [hχf, card_singleton]

/-- Tseitin CNF width equals the regular degree. -/
theorem cnfWidth_tseitinCNF_of_regular {n d : ℕ} {G : FinGraph n} {χ : Charge n}
    (hreg : IsRegular G d) (hn : 0 < n) (hd : 0 < d) :
    cnfWidth (tseitinCNF G χ) = d := by
  have hF := tseitinCNF_nonempty_of_regular (χ := χ) hreg hn hd
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro C hC
    exact (card_mem_tseitinCNF_of_regular hreg hC hn).le
  · obtain ⟨C, hC⟩ := hF
    have hCd : C.card = d := card_mem_tseitinCNF_of_regular hreg hC hn
    have : C.card ≤ cnfWidth (tseitinCNF G χ) := Finset.le_sup hC
    omega

/-- Heawood sharp medium floor is 4. -/
theorem tseitin_heawood_mediumFloor :
    tseitinMediumFloor 14 = 4 := by
  decide

/-- Numeric non-vacuity seed: Heawood sharp floor strictly beats 3-regular axiom
width (4 > 3). -/
theorem tseitin_heawood_width_beats_cnfWidth
    (χ : Charge 14) (_hχ : oddCharge χ) :
    cnfWidth (tseitinCNF heawoodGraph χ) < 1 * tseitinMediumFloor 14 := by
  have hn : 0 < 14 := by omega
  have hW : cnfWidth (tseitinCNF heawoodGraph χ) = 3 :=
    cnfWidth_tseitinCNF_of_regular heawoodGraph_regular hn (by omega)
  simp [hW, tseitin_heawood_mediumFloor]

/-- Conditional packaging kept for pin compatibility; unconditional form below. -/
theorem tseitin_heawood_width_ge_four_of_expansion
    (hα : HasExpansion heawoodGraph 1)
    (χ : Charge 14) (_hχ : oddCharge χ)
    (d : Derivation (tseitinCNF heawoodGraph χ) (∅ : Clause)) :
    4 ≤ d.width := by
  have h := tseitin_expander_width_lower_bound hα (by omega : 1 ≤ 1) d
    (by omega : 2 ≤ 14)
  simpa [tseitin_heawood_mediumFloor, one_mul] using h

/-- Unconditional Heawood width LB: every refutation has width at least 4. -/
theorem tseitin_heawood_width_ge_four
    (χ : Charge 14) (hχ : oddCharge χ)
    (d : Derivation (tseitinCNF heawoodGraph χ) (∅ : Clause)) :
    4 ≤ d.width :=
  tseitin_heawood_width_ge_four_of_expansion heawoodGraph_expansion χ hχ d

/-- Unconditional Heawood size LB via BSW at width floor 4. -/
theorem tseitin_heawood_size_lower_bound
    (χ : Charge 14) (hχ : oddCharge χ)
    (d : Derivation (tseitinCNF heawoodGraph χ) (∅ : Clause)) :
    let W := 1 * tseitinMediumFloor 14
    2 ^ ((W - cnfWidth (tseitinCNF heawoodGraph χ)) *
          (W - cnfWidth (tseitinCNF heawoodGraph χ)) /
          (bswRateConst * (cnfVars (tseitinCNF heawoodGraph χ)).card)) ≤ d.size := by
  exact tseitin_expander_size_lower_bound heawoodGraph_expansion (by omega : 1 ≤ 1)
    hχ d (by omega : 2 ≤ 14)

/-- Concrete non-vacuity with the standard single-vertex odd charge. -/
theorem tseitin_heawood_width_floor_gt_cnfWidth :
    cnfWidth (tseitinCNF heawoodGraph (oddCharge_single 14 ⟨0, by omega⟩)) <
      1 * tseitinMediumFloor 14 :=
  tseitin_heawood_width_beats_cnfWidth _ (oddCharge_single_odd 14 ⟨0, by omega⟩)

end SATurday.ProofComplexity
