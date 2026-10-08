import Theory.ProofComplexity.PCSizeDegree

/-!
# Exponential polynomial calculus size for Tseitin mod q (Ladder Rung R4, 1C.3)

Combining the linear degree lower bound for the one hot Tseitin mod `q` CNF over `F_p`
(`TseitinPC.tseitin_bool_degree_Fp`) with the size–degree tradeoff (`MLPC.size_degree`) and
the translation of multilinear derivations (`MLPC.translate`): every multilinear polynomial
calculus refutation over `ZMod p` has size at least `2^m` with `m` linear in the number of
vertices (`tseitin_ml_size`).

LOG: R4 TseitinSize module (PC size lower bound)
-/

namespace SATurday.ProofComplexity

open Finset MvPolynomial

noncomputable section

open Classical

namespace MLPC

variable {F : Type} [Field F]

/-- Multilinear axioms of a CNF: multilinear polynomials whose polynomial is a clause. -/
def AxML (Φ : CNF) : Set (ML F) := {a | toPoly a ∈ cnfAx (F := F) Φ}

/-- The exponent vector of a variable set. -/
def ms (S : Finset ℕ) : ℕ →₀ ℕ := ∑ i ∈ S, Finsupp.single i 1

theorem ms_apply (S : Finset ℕ) (i : ℕ) : ms S i = if i ∈ S then 1 else 0 := by
  unfold ms; rw [Finsupp.finset_sum_apply]; simp [Finsupp.single_apply]

theorem ms_inj {S T : Finset ℕ} (h : ms S = ms T) : S = T := by
  ext i; have := congrArg (fun f => f i) h; simp only [ms_apply] at this
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

theorem toPoly_eq_sum (f : ML F) : toPoly f = ∑ T ∈ f.support, monomial (ms T) (f T) := by
  unfold toPoly Finsupp.sum
  refine sum_congr rfl fun T _ => ?_
  show C (f T) * ∏ i ∈ T, X i = _
  rw [show (∏ i ∈ T, (X i : MvPolynomial ℕ F)) = monomial (∑ i ∈ T, Finsupp.single i 1) 1 by
    rw [monomial_sum_one]; rfl, C_mul_monomial, mul_one]; rfl

theorem coeff_toPoly (f : ML F) (S : Finset ℕ) : coeff (ms S) (toPoly f) = f S := by
  rw [toPoly_eq_sum, coeff_sum]
  by_cases hS : S ∈ f.support
  · rw [sum_eq_single S]
    · simp [coeff_monomial]
    · intro T _ hne; rw [coeff_monomial, if_neg (fun h => hne (ms_inj h))]
    · intro h; exact absurd hS h
  · rw [sum_eq_zero]
    · exact (Finsupp.notMem_support_iff.1 hS).symm
    · intro T hT; rw [coeff_monomial, if_neg]; intro h; rw [ms_inj h] at hT; exact hS hT

theorem degree_ms (S : Finset ℕ) : Finsupp.degree (ms S) = S.card := by
  unfold ms; rw [map_sum]; simp

theorem vars_litPoly (l : Literal) : (litPoly (F := F) l).vars ⊆ {l.var} := by
  unfold litPoly
  split_ifs
  · refine (vars_sub_subset (p := (1 : MvPolynomial ℕ F)) (q := X l.var)).trans ?_
    simp [vars_one, vars_X]
  · simp [vars_X]

theorem totalDegree_litPoly (l : Literal) : (litPoly (F := F) l).totalDegree ≤ 1 := by
  unfold litPoly
  split_ifs
  · refine (totalDegree_sub _ _).trans ?_; simp
  · simp

/-- Monomials of a clause axiom use the clause variables, at most `|C|` of them. -/
theorem axML_props {Φ : CNF} {a : ML F} (ha : a ∈ AxML Φ) :
    ∃ C ∈ Φ, ∀ S ∈ a.support, S ⊆ C.image Literal.var ∧ S.card ≤ C.card := by
  obtain ⟨C, hC, hEq⟩ := ha
  refine ⟨C, hC, fun S hS => ?_⟩
  have hmem : ms S ∈ (clausePoly (F := F) C).support := by
    rw [mem_support_iff, ← hEq, coeff_toPoly]; exact Finsupp.mem_support_iff.1 hS
  constructor
  · intro i hi
    have hv : i ∈ (clausePoly (F := F) C).vars :=
      (mem_vars i).2 ⟨ms S, hmem, by rw [Finsupp.mem_support_iff, ms_apply, if_pos hi]; simp⟩
    unfold clausePoly at hv
    have := vars_prod (s := C) (fun l => litPoly (F := F) l) hv
    obtain ⟨l, hl, hil⟩ := mem_biUnion.1 this
    have := vars_litPoly l hil
    rw [mem_singleton] at this
    exact mem_image.2 ⟨l, hl, this.symm⟩
  · have := le_totalDegree hmem
    have h2 : (clausePoly (F := F) C).totalDegree ≤ C.card := by
      unfold clausePoly
      refine (totalDegree_finset_prod _ _).trans ?_
      calc ∑ l ∈ C, (litPoly (F := F) l).totalDegree ≤ ∑ l ∈ C, 1 := sum_le_sum fun l _ => totalDegree_litPoly l
        _ = C.card := by simp
    have h3 : (ms S).sum (fun _ e => e) = S.card := degree_ms S
    omega

end MLPC

theorem pcd_mono {F : Type} [Field F] {Ax : Set (MvPolynomial ℕ F)} {d d' : ℕ} (hdd : d ≤ d')
    {f : MvPolynomial ℕ F} (h : PCD Ax d f) : PCD Ax d' f := by
  induction h with
  | ax hf hd => exact PCD.ax hf (hd.trans hdd)
  | bool i h2 => exact PCD.bool i (h2.trans hdd)
  | lin a b _ _ ihf ihg => exact PCD.lin a b ihf ihg
  | mul i _ hd ih => exact PCD.mul i ih (hd.trans hdd)

namespace TseitinPC

open MLPC

variable {q : ℕ} [NeZero q]

/-- The variables of the one hot encoding. -/
def tVars {n : ℕ} (G : FinGraph n) (q : ℕ) : Finset ℕ :=
  (univ ×ˢ range q).image fun x : G × ℕ => xv x.1.1 x.2

theorem tcnf_clause_props {n : ℕ} {G : FinGraph n} {b : Fin n → ZMod q} (hreg : IsRegular G 3)
    {C : Clause} (hC : C ∈ tcnf G q b) :
    C.image Literal.var ⊆ tVars G q ∧ C.card ≤ q + 3 := by
  rcases mem_tcnf hC with ⟨e, rfl⟩ | ⟨e, j, j', hj, hj', -, rfl⟩ | ⟨v, α, -, rfl⟩
  · refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨l, hl, rfl⟩ := mem_image.1 hi
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hl
      exact mem_image.2 ⟨(e, j), mem_product.2 ⟨mem_univ _, hj⟩, rfl⟩
    · unfold aloC; exact card_image_le.trans (by simp)
  · refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨l, hl, rfl⟩ := mem_image.1 hi
      simp only [amoC, mem_insert, mem_singleton] at hl
      rcases hl with rfl | rfl
      · exact mem_image.2 ⟨(e, j), mem_product.2 ⟨mem_univ _, mem_range.2 hj⟩, rfl⟩
      · exact mem_image.2 ⟨(e, j'), mem_product.2 ⟨mem_univ _, mem_range.2 hj'⟩, rfl⟩
    · unfold amoC; exact (card_insert_le _ _).trans (by simp)
  · refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨l, hl, rfl⟩ := mem_image.1 hi
      obtain ⟨e, -, rfl⟩ := mem_image.1 hl
      exact mem_image.2 ⟨(e, (α e).val), mem_product.2 ⟨mem_univ _, mem_range.2 (ZMod.val_lt _)⟩, rfl⟩
    · unfold vC
      refine card_image_le.trans ((card_incE_le v).trans ?_)
      rw [hreg v]; omega

theorem card_G_ge {n : ℕ} {G : FinGraph n} (hreg : IsRegular G 3) : n ≤ 2 * G.card := by
  have hsub : (univ : Finset (Fin n)) ⊆ G.biUnion fun e => ({e.val.1, e.val.2} : Finset (Fin n)) := by
    intro v _
    have hd := hreg v
    obtain ⟨e, he⟩ : (incident G v).Nonempty := by rw [← card_pos]; unfold degree at hd; omega
    obtain ⟨heG, hev⟩ := mem_incident_iff.1 he
    refine mem_biUnion.2 ⟨e, heG, ?_⟩
    rcases hev with h | h <;> simp [h]
  have := (card_le_card hsub).trans card_biUnion_le
  simp only [card_univ, Fintype.card_fin] at this
  refine this.trans ?_
  calc ∑ e ∈ G, ({e.val.1, e.val.2} : Finset (Fin n)).card ≤ ∑ e ∈ G, 2 :=
        sum_le_sum fun e _ => card_le_two
    _ = 2 * G.card := by rw [sum_const, smul_eq_mul, mul_comm]

theorem card_tVars_ge {n : ℕ} (hn : 0 < n) (G : FinGraph n) : G.card ≤ (tVars G q).card := by
  refine card_le_card_of_injOn (fun e => xv e 0) (fun e he => ?_) (fun e he e' he' h => ?_)
  · exact mem_image.2 ⟨(⟨e, he⟩, 0), mem_product.2 ⟨mem_univ _, mem_range.2 (Nat.pos_of_ne_zero (NeZero.ne q))⟩, rfl⟩
  · exact (xv_inj hn h).1

/-- **Exponential size for Tseitin mod `q` over `F_p`**: for primes `p ∤ q` and every `N` there
is a cubic graph on `n ≥ N` vertices such that every multilinear polynomial calculus
refutation over `ZMod p` of the one hot Tseitin mod `q` CNF (any charge) has size at least
`2^m`, where `m = E / (2 (|V| / E + 1))`, `|V| = |G| q` is the number of variables,
`E = d / 3` and `d = ((n - 2) / 1312 - q (q + 3)) / (q - 1)` is the degree bound. For fixed
`q`, `d` and `E` are linear in `n` and `|V| = 3 n q / 2`, so `m` is linear in `n`. -/
theorem tseitin_ml_size (p : ℕ) [Fact p.Prime] (hq : 2 ≤ q) (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ ∀ b : Fin n → ZMod q,
      ∀ L : List (ML (ZMod p)), MLProof (AxML (tcnf G q b)) L → one ∈ L →
        2 ^ ((((n - 2) / 1312 - q * (q + 3)) / (q - 1) / 3) /
          (2 * ((tVars G q).card / (((n - 2) / 1312 - q * (q + 3)) / (q - 1) / 3) + 1)))
          ≤ sizeL L := by
  obtain ⟨n, G, hN, hreg, hdeg⟩ := tseitin_bool_degree_Fp (q := q) p hq hpq
    (max N (1312 * (q * (q + 3) + 3 * (q + 5) * q) + 2))
  refine ⟨n, G, le_trans (le_max_left _ _) hN, hreg, fun b L hL h1 => ?_⟩
  have hn : 1312 * (q * (q + 3) + 3 * (q + 5) * q) + 2 ≤ n := le_trans (le_max_right _ _) hN
  set dT := ((n - 2) / 1312 - q * (q + 3)) / (q - 1) with hdTdef
  set E := dT / 3 with hEdef
  set NV := (tVars G q).card with hNV
  set r := NV / E + 1 with hr
  set m := E / (2 * r) with hm
  have hX : q * (q + 3) + 3 * (q + 5) * q ≤ (n - 2) / 1312 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 1312), mul_comm]; omega
  have hdT : 3 * (q + 5) ≤ dT := by
    rw [hdTdef, Nat.le_div_iff_mul_le (by omega)]
    have : 3 * (q + 5) * (q - 1) ≤ 3 * (q + 5) * q := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    omega
  have hE : q + 5 ≤ E := by rw [hEdef, Nat.le_div_iff_mul_le (by norm_num)]; omega
  have h3E : 3 * E ≤ dT := by rw [hEdef]; omega
  have hdTn : dT ≤ n / 2 := by
    have h1 : dT ≤ (n - 2) / 1312 - q * (q + 3) := Nat.div_le_self _ _
    have h2 : (n - 2) / 1312 ≤ n / 2 := Nat.div_le_div (by omega) (by norm_num) (by norm_num)
    omega
  have hGc := card_G_ge hreg
  have hNVG := card_tVars_ge (q := q) (by omega) G
  have hENV : E ≤ NV := by omega
  by_contra hlt
  push Not at hlt
  have hw : ∀ a ∈ AxML (F := ZMod p) (tcnf G q b), mdeg a ≤ q + 3 := by
    intro a ha
    obtain ⟨C, hC, hS⟩ := axML_props ha
    rw [mdeg_le]; intro S hSa; exact (hS S hSa).2.trans (tcnf_clause_props hreg hC).2
  have hAxV : ∀ a ∈ AxML (F := ZMod p) (tcnf G q b), ∀ S ∈ a.support, S ⊆ tVars G q := by
    intro a ha S hSa
    obtain ⟨C, hC, hS⟩ := axML_props ha
    exact (hS S hSa).1.trans (tcnf_clause_props hreg hC).1
  have hEpos : 0 < E := by omega
  have hrE : NV ≤ r * E + E := by
    have := Nat.lt_div_mul_add (a := NV) hEpos
    rw [hr, add_mul, one_mul]; omega
  have hMLD := size_degree (t := E) (r := r) (m := m) hw hAxV hL h1 hlt (by omega) (Nat.le_add_left 1 _)
    hENV hrE
  have hPC := pcd₀_to_pcd (by omega) (translate (Axp := cnfAx (F := ZMod p) (tcnf G q b))
    (fun a ha => ha) hMLD)
  rw [toPoly_one] at hPC
  have h2rm : 2 * (r * m) ≤ E := by
    have := Nat.div_mul_le_self E (2 * r)
    rw [hm]; nlinarith
  refine hdeg b (pcd_mono ?_ hPC)
  have : max (E - 1) (q + 3 + 1) = E - 1 := max_eq_left (by omega)
  rw [this]; omega

end TseitinPC

end

end SATurday.ProofComplexity
