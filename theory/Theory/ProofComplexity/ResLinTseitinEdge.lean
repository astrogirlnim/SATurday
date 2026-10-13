import Theory.ProofComplexity.GreenTseitin
import Theory.ProofComplexity.ResLinFSize
import Theory.ProofComplexity.TseitinSize

/-!
# Tree-like `Res(lin F_p)` size for the Boolean-edge Tseitin mod `q` formula (Ladder Rung R4, F)

The CNF `T_q(G, σ)` of Alekhnovich-Razborov Definition 4.3 as a propositional `CNF` (one clause of
width `deg v` for every bad local assignment `α` at every vertex `v`), whose polynomial system is
exactly the clause family `OGraph.Ax` of D1 (`OGraph.cnfAx_eq`).  Combining the polynomial calculus
degree lower bound `ggw_tseitin_pc_degree` (over `F_p`, `p ∤ q`) with Part-Tzameret Theorems 44 and 45
(`RLF.rld_cnf_size`) gives the tree-like size bound for the explicit family `GGW m k`.

LOG: R4 F ResLinTseitinEdge
-/

namespace SATurday.ProofComplexity.TseitinEdge

open Finset MvPolynomial SATurday.ProofComplexity SATurday.ProofComplexity.PCL

noncomputable section
open Classical

variable {V E : Type} [Fintype V] [Fintype E] (G : OGraph V E)

/-- The literal of the edge `e` falsified by the assignment `α`. -/
def OGraph.lit (α : E → Bool) (e : E) : Literal := ⟨G.col e, !α e⟩

/-- The clause excluding the local assignment `α` at `v`. -/
def OGraph.clause (v : V) (α : E → Bool) : Clause := (G.inc v).image (G.lit α)

/-- The Tseitin mod `q` CNF (AR Definition 4.3). -/
def OGraph.cnf (q : ℕ) (σ : V → ZMod q) : CNF :=
  (Finset.univ.filter fun p : V × (E → Bool) => G.lsum q p.1 p.2 ≠ σ p.1).image
    fun p => G.clause p.1 p.2

theorem OGraph.clausePoly_clause (F : Type) [Field F] (v : V) (α : E → Bool) :
    clausePoly (F := F) (G.clause v α) = G.cl F v α := by
  unfold clausePoly OGraph.clause OGraph.cl
  rw [Finset.prod_image (fun e _ e' _ h =>
    G.col_inj (by simpa [OGraph.lit] using congrArg Literal.var h))]
  refine Finset.prod_congr rfl fun e _ => ?_
  unfold litPoly OGraph.lit
  cases h : α e <;> simp [h]

theorem OGraph.cnfAx_eq (F : Type) [Field F] (q : ℕ) (σ : V → ZMod q) :
    cnfAx (F := F) (G.cnf q σ) = G.Ax F q σ := by
  ext f
  constructor
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hC
    exact ⟨p.1, p.2, (Finset.mem_filter.1 hp).2, G.clausePoly_clause F _ _⟩
  · rintro ⟨v, α, hα, rfl⟩
    exact ⟨G.clause v α, Finset.mem_image.2 ⟨(v, α),
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hα⟩, rfl⟩, (G.clausePoly_clause F v α).symm⟩

theorem OGraph.clause_card_le (v : V) (α : E → Bool) : (G.clause v α).card ≤ (G.inc v).card :=
  Finset.card_image_le

open SATurday.ProofComplexity.Expander in
/-- **Tree-like `Res(lin F_p)` size bound** for the Boolean-edge Tseitin mod `q` formula on the
explicit multigraph family `GGW m k` (`p` prime, `p ∤ q`, `q ≥ 2`, `16 q ≤ m`, `k ≥ k0 q`, `σ`
arbitrary): a tree-like refutation with `s` leaves of the formula satisfies
`2^((m² 8^k / (256 q²) - 8^k - p) / (p - 1)) ≤ 2 s`.  With `n = 2 m²` vertices and degree
`d = 8^k` this is `2^{Ω(d n / (p q²))}` once `m² ≥ 512 q²` or so. -/
theorem ggw_tseitin_reslin_size (p : ℕ) [Fact p.Prime] {q : ℕ} (hq2 : 2 ≤ q) (hpq : ¬ p ∣ q)
    {m : ℕ} (hm : 16 * q ≤ m) {k : ℕ} (hk : k0 q ≤ k) (σ : MggTorus m ⊕ MggTorus m → ZMod q)
    {w s : ℕ}
    (h : RLF.RLD (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) ''
      ((ggwGraph m (by omega) k).cnf q σ)) ∪ RLF.boolAx) w ∅ s) :
    2 ^ ((m * m * 8 ^ k / (256 * q ^ 2) - 8 ^ k - p) / (p - 1)) ≤ 2 * s := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hqF : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpq
  have hs1 : 1 ≤ s := RLF.rld_pos h
  have hw0 : 2 ≤ 8 ^ k := by have := four_q_le_pow q hk; omega
  set D := m * m * 8 ^ k / (256 * q ^ 2) with hD
  set kk := Nat.clog 2 s with hkk
  have hlt : D < 8 ^ k + (p - 1) * kk + p := by
    by_contra hcon
    rw [not_lt] at hcon
    have hpc := RLF.rld_cnf_size (p := p) (Φ := (ggwGraph m (by omega) k).cnf q σ) (w0 := 8 ^ k)
      hw0 (fun C hC => by
        obtain ⟨pr, _, rfl⟩ := Finset.mem_image.1 hC
        refine ((ggwGraph m (by omega) k).clause_card_le pr.1 pr.2).trans ?_
        have h2 := ggwGraph_inc_card m (by omega) k pr.1
        exact_mod_cast h2.le) h
    rw [OGraph.cnfAx_eq] at hpc
    refine ggw_tseitin_pc_degree hq2 hqF hm hk σ (d := D) ?_ (pcd_mono hcon hpc)
    have h3 : ((m * m * 8 ^ k / (256 * q ^ 2) : ℕ) : ℝ) ≤
        ((m * m * 8 ^ k : ℕ) : ℝ) / ((256 * q ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
    refine h3.trans (le_of_eq ?_)
    push_cast; ring
  have h1 : (D - 8 ^ k - p) / (p - 1) ≤ kk := Nat.div_le_of_le_mul (by omega)
  refine le_trans (Nat.pow_le_pow_right (by norm_num) h1) ?_
  rcases Nat.lt_or_ge 1 s with hs | hs
  · have h2 : 2 ^ (kk - 1) < s := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hs
    have hk1 : 1 ≤ kk := Nat.clog_pos (by norm_num) hs
    have : 2 ^ kk = 2 * 2 ^ (kk - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  · have : s = 1 := by omega
    subst this
    simp [hkk]

end

end SATurday.ProofComplexity.TseitinEdge
