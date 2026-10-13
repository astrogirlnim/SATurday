import Theory.ProofComplexity.ResLinFBack
import Theory.ProofComplexity.ResLinTseitin
import Mathlib.Data.Finsupp.Encodable

/-!
# Dag-like Res(lin F_p) size from polynomial calculus degree (Ladder Rung R4, Phase 2.2, K5-K6)

Khaniki's size-width argument for dag-like `Res(lin F_p)`: a dag refutation of a CNF `Φ` with `L`
lines gives (forward translation, `atom_refutation`) a dag Resolution refutation of the atom
hypotheses with at most `3 L` lines, whose clauses mention at most `K * 3 L` variables
(`K = max w0 3`); by dag-like BSW (`bsw_dag_size_lower_bound`) and the back translation
(`atom_refutation_pcd`: tree Resolution width `w` gives PC degree `(p-1)(w+1)`), a polynomial
calculus degree lower bound `D` for `Φ` forces `W = D / (p - 1)` to satisfy
`(W - K)^2 < 72 K L (log2 (3 L) + 1)` (`reslin_dag_size_of_pc_degree`), i.e. `L (log L)` is at least
`(W-K)^2`: almost quadratic when `D` is linear in the number of variables.
For the certified one hot Tseitin mod `q` CNF on cubic expanders this is `reslin_tseitin_dag_size`.

LOG: R4 Phase 2.2 ResLinDagSize module (Khaniki dag-like size bound)
-/

namespace SATurday.ProofComplexity

namespace RLF

open scoped Classical
open Finset

noncomputable section

theorem leq_countable (p : ℕ) [Fact p.Prime] : Countable (LEq (ZMod p)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Finite (ZMod p) := inferInstance
  unfold LEq
  infer_instance

theorem atomHyp_card_le {F : Type} [Field F] {aid : LEq F → ℕ} (haid : Function.Injective aid)
    {Φ : CNF} {w0 : ℕ} (hΦ : ∀ C ∈ Φ, C.card ≤ w0) {X : Clause} (hX : AtomHyp aid Φ X) :
    X.card ≤ max w0 3 := by
  cases hX with
  | phi C hC =>
    rw [aCl_card haid]
    exact ((ofCl_card_le C).trans (hΦ C hC)).trans (le_max_left _ _)
  | bool i =>
    rw [aCl_card haid, boolCl_card]
    exact (by norm_num : 2 ≤ 3).trans (le_max_right _ _)
  | imp e1 e2 α β _ _ =>
    exact (Finset.card_le_three).trans (le_max_right _ _)
  | unit c _ =>
    simp [uCl]

theorem cnfVars_card_le_mul {Γ : CNF} {K : ℕ} (h : ∀ C ∈ Γ, C.card ≤ K) :
    (cnfVars Γ).card ≤ Γ.card * K := by
  unfold cnfVars
  refine (card_biUnion_le).trans ?_
  calc ∑ C ∈ Γ, (clauseVars C).card ≤ ∑ _C ∈ Γ, K :=
        Finset.sum_le_sum fun C hC => (card_image_le).trans (h C hC)
    _ = Γ.card * K := by simp

/-- **Khaniki's size-width argument for dag-like `Res(lin F_p)`.** If `Φ` has no polynomial
calculus refutation of degree `D` over `F_p`, with `4 ≤ D / (p - 1)`, then every dag-like
`Res(lin F_p)` refutation with `L` lines satisfies, with `W = D / (p - 1)` and
`K = max w0 3` (`w0` the clause width of `Φ`),
`(W - K)^2 < 72 K L (log2 (3 L) + 1)`. -/
theorem reslin_dag_size_of_pc_degree (p : ℕ) [Fact p.Prime] {Φ : CNF} {w0 : ℕ}
    (hΦ : ∀ C ∈ Φ, C.card ≤ w0) {D : ℕ} (hD : 4 ≤ D / (p - 1))
    (hno : ¬ PCD (cnfAx (F := ZMod p) Φ) D 1)
    {𝓛 : Finset (Finset (LEq (ZMod p)))}
    (h : RLDag (((fun C => (ofCl C : Finset (LEq (ZMod p)))) '' Φ) ∪ boolAx) 𝓛)
    (h0 : (∅ : Finset (LEq (ZMod p))) ∈ 𝓛) :
    (D / (p - 1) - max w0 3) * (D / (p - 1) - max w0 3) <
      72 * max w0 3 * 𝓛.card * (Nat.log 2 (3 * 𝓛.card) + 1) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : 0 < p - 1 := by omega
  haveI := leq_countable p
  obtain ⟨aid, haid⟩ := exists_injective_nat (LEq (ZMod p))
  haveI : Nonempty (LEq (ZMod p)) := ⟨((0 : ℕ →₀ ZMod p), 0)⟩
  set dec : ℕ → LEq (ZMod p) := Function.invFun aid with hdec_def
  have hdec : ∀ e, dec (aid e) = e := Function.leftInverse_invFun haid
  set K := max w0 3 with hK
  set W := D / (p - 1) with hW
  obtain ⟨S, hS, hE0, hcard⟩ := atom_refutation haid h h0
  set Γ : CNF := S.filter (AtomHyp aid Φ) with hΓ
  have hΓH : ∀ X ∈ Γ, AtomHyp aid Φ X := fun X hX => (mem_filter.1 hX).2
  have hΓK : ∀ X ∈ Γ, X.card ≤ K := fun X hX => atomHyp_card_le haid hΦ (hΓH X hX)
  have hcw : cnfWidth Γ ≤ K := Finset.sup_le hΓK
  -- every tree refutation of Γ has width at least W
  have hWd : ∀ d : Derivation Γ (∅ : Clause), W ≤ d.width := by
    intro d
    by_contra hlt
    rw [not_le] at hlt
    have hw3 : 3 ≤ max d.width 3 := le_max_right _ _
    have hdw : d.width ≤ max d.width 3 := le_max_left _ _
    have hpc := atom_refutation_pcd (ZMod.pow_card) haid hdec hw3 hΓH d hdw
    refine hno (pcd_mono ?_ hpc)
    -- (p-1) * (max d.width 3 + 1) ≤ D
    have hmax : max d.width 3 + 1 ≤ W := by
      rcases max_cases d.width 3 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    calc (p - 1) * (max d.width 3 + 1) ≤ (p - 1) * W := Nat.mul_le_mul_left _ hmax
      _ ≤ D := Nat.mul_div_le D (p - 1)
  have hbsw := bsw_dag_size_lower_bound Γ W hWd (T := S) (by
    have : DDer Γ S := hS
    exact this) hE0
  -- positivity of the variable count
  have hn : 0 < (cnfVars Γ).card := by
    obtain ⟨d, hd⟩ := hS.to_tree ∅ hE0
    have h1 := hWd d
    have h2 : S.sup Finset.card ≤ (cnfLits Γ).card :=
      Finset.sup_le fun C hC => hS.card_le_lits hC
    rw [cnfLits_card] at h2
    omega
  have hnK : (cnfVars Γ).card ≤ K * S.card := by
    have := cnfVars_card_le_mul hΓK
    have h2 : Γ.card ≤ S.card := card_filter_le _ _
    calc (cnfVars Γ).card ≤ Γ.card * K := this
      _ ≤ S.card * K := Nat.mul_le_mul_right _ h2
      _ = K * S.card := by ring
  -- arrange the exponent
  have hS0 : 0 < S.card := card_pos.2 ⟨∅, hE0⟩
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) (le_max_right w0 3)
  set e := (W - K) * (W - K) / (24 * (K * S.card)) with he
  have hedge : e ≤ (W - cnfWidth Γ) * (W - cnfWidth Γ) / (bswRateConst * (cnfVars Γ).card) := by
    refine Nat.div_le_div (Nat.mul_le_mul (by omega) (by omega)) ?_ (by
      simp only [bswRateConst]; omega)
    simp only [bswRateConst]
    have := Nat.mul_le_mul_left 24 hnK
    omega
  have hpow : 2 ^ e ≤ S.card :=
    (Nat.pow_le_pow_right (by norm_num) hedge).trans hbsw
  have hlog : e ≤ Nat.log 2 S.card :=
    (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 hpow
  have hlt : (W - K) * (W - K) < 24 * (K * S.card) * (e + 1) := by
    have := Nat.lt_mul_div_succ ((W - K) * (W - K)) (show 0 < 24 * (K * S.card) by positivity)
    simpa [he, mul_comm] using this
  -- pass from S.card to 𝓛.card
  have hlog3 : Nat.log 2 S.card ≤ Nat.log 2 (3 * 𝓛.card) := Nat.log_mono_right hcard
  have h1 : 24 * (K * S.card) * (e + 1) ≤ 24 * (K * S.card) * (Nat.log 2 (3 * 𝓛.card) + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : 24 * (K * S.card) * (Nat.log 2 (3 * 𝓛.card) + 1) ≤
      24 * (K * (3 * 𝓛.card)) * (Nat.log 2 (3 * 𝓛.card) + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hcard))
  have h3 : 24 * (K * (3 * 𝓛.card)) = 72 * K * 𝓛.card := by ring
  rw [h3] at h2
  exact lt_of_lt_of_le hlt (h1.trans h2)

/-- From `X < c L (log2 (3 L) + 1)` to the explicit lower bound on `L`. -/
theorem lines_lower_bound (X c L : ℕ) (hc : 0 < c) (h : X < c * L * (Nat.log 2 (3 * L) + 1)) :
    X / (c * (Nat.log 2 (3 * X) + 1)) ≤ L := by
  by_cases hLX : X ≤ L
  · exact (Nat.div_le_self _ _).trans hLX
  · rw [not_le] at hLX
    have hlog : Nat.log 2 (3 * L) ≤ Nat.log 2 (3 * X) :=
      Nat.log_mono_right (Nat.mul_le_mul_left 3 hLX.le)
    have h2 : X < (c * (Nat.log 2 (3 * X) + 1)) * L := by
      calc X < c * L * (Nat.log 2 (3 * L) + 1) := h
        _ ≤ c * L * (Nat.log 2 (3 * X) + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = (c * (Nat.log 2 (3 * X) + 1)) * L := by ring
    exact (Nat.div_lt_of_lt_mul h2).le

end

end RLF

/-- The width scale `W = ((((n-2)/1312 - q(q+3)) / (q-1)) / (p-1)` of the certified polynomial
calculus degree bound for the one hot Tseitin mod `q` CNF on `n`-vertex cubic expanders. -/
def tseitinW (p q n : ℕ) : ℕ := (((n - 2) / 1312 - q * (q + 3)) / (q - 1)) / (p - 1)

open TseitinPC in
/-- **Khaniki's dag-like bound for `Res(lin F_p)` (one hot Tseitin mod `q`)**: for a prime `p`
and `q ≥ 2` with `p ∤ q` there are cubic expanders `G` on `n ≥ N` vertices such that every dag-like
`Res(lin F_p)` refutation of the one hot Tseitin mod `q` CNF `tcnf G q b` with `L` lines satisfies
`X < 72 (q+3) L (log2 (3 L) + 1)` and `X / (72 (q+3) (log2 (3 X) + 1)) ≤ L`, where
`X = (W - (q+3))^2` and `W = tseitinW p q n ≥ q + 5` is linear in `n` (the certified polynomial
calculus degree bound divided by `p-1`). So `L = Ω(n^2 / log n)`: almost quadratic. -/
theorem reslin_tseitin_dag_size (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ q + 5 ≤ tseitinW p q n ∧
      ∀ b : Fin n → ZMod q, ∀ 𝓛 : Finset (Finset (RLF.LEq (ZMod p))),
        RLF.RLDag (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' tcnf G q b) ∪
          RLF.boolAx) 𝓛 → (∅ : Finset (RLF.LEq (ZMod p))) ∈ 𝓛 →
        ((tseitinW p q n - (q + 3)) * (tseitinW p q n - (q + 3)) <
          72 * (q + 3) * 𝓛.card * (Nat.log 2 (3 * 𝓛.card) + 1)) ∧
        (tseitinW p q n - (q + 3)) * (tseitinW p q n - (q + 3)) /
          (72 * (q + 3) * (Nat.log 2 (3 * ((tseitinW p q n - (q + 3)) *
            (tseitinW p q n - (q + 3))) ) + 1)) ≤ 𝓛.card := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  set N0 := 2 + 1312 * (q * (q + 3) + (q - 1) * (p - 1) * (q + 5)) with hN0
  obtain ⟨n, G, hN, hreg, hdeg⟩ := TseitinPC.tseitin_bool_degree_Fp p hq hpq (max N N0)
  have hnN : N ≤ n := (le_max_left _ _).trans hN
  have hn0 : N0 ≤ n := (le_max_right _ _).trans hN
  set D := ((n - 2) / 1312 - q * (q + 3)) / (q - 1) with hD
  have hq1 : 0 < q - 1 := by omega
  have hp1 : 0 < p - 1 := by omega
  have hW : q + 5 ≤ tseitinW p q n := by
    unfold tseitinW
    rw [Nat.le_div_iff_mul_le hp1]
    have hDq : (p - 1) * (q + 5) ≤ D := by
      rw [hD, Nat.le_div_iff_mul_le hq1]
      have h1 : q * (q + 3) + (q - 1) * (p - 1) * (q + 5) ≤ (n - 2) / 1312 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        omega
      have : (p - 1) * (q + 5) * (q - 1) = (q - 1) * (p - 1) * (q + 5) := by ring
      omega
    nlinarith
  refine ⟨n, G, hnN, hreg, hW, fun b 𝓛 h h0 => ?_⟩
  have hmain := RLF.reslin_dag_size_of_pc_degree p (Φ := tcnf G q b) (w0 := q + 3)
    (fun C hC => (tcnf_clause_props hreg hC).2) (D := D) (by have : q + 5 ≤ D / (p - 1) := hW; omega) (hdeg b) h h0
  have hmax : max (q + 3) 3 = q + 3 := max_eq_left (by omega)
  rw [hmax] at hmain
  exact ⟨hmain, RLF.lines_lower_bound _ _ _ (by omega) hmain⟩

end SATurday.ProofComplexity
