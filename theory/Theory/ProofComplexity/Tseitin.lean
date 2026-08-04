import Theory.ProofComplexity.FinGraph
import Theory.ProofComplexity.Width

/-!
# Tseitin CNF on FinGraphs (Ladder Rung R2, item 2 cluster 2 start)

Charge, edge variables, and the Tseitin CNF construction over the FinGraph API.
Unsatisfiability (`tseitinCNF_unsat`) is certified here by double counting.
Expander width lower bounds remain later clusters.

Encoding: each edge `e` gets variable `edgeVar e`. At vertex `v` of degree `d`,
the `2^(d-1)` parity clauses force the XOR of incident edge variables to equal
the charge `χ v`.

LOG: R2 Tseitin CNF construction and odd-charge unsat
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

end SATurday.ProofComplexity
