import Theory.ProofComplexity.TseitinBool

/-!
# Satisfiability criterion for the one hot Tseitin CNF on connected graphs (referee repair, 2a)

For a connected graph `G` and `q ≥ 1`, `tcnf G q b` is satisfiable iff `∑ v, b v = 0` in `ZMod q`
(`tcnf_sat_iff`).  The direction `→` is `tcnf_unsat` (no connectivity needed); the direction `←`
is proved here: on a connected graph every charge of total zero is the net flow of an edge
labelling (`exists_flow`; the net flow map is linear and its image contains `e_u - e_v` for
adjacent hence for all `u, v`), and a flow gives a satisfying one hot assignment (`tcnf_sat_of_flow`).
-/

namespace SATurday.ProofComplexity

namespace TseitinPC

open Finset

noncomputable section

open Classical

variable {n : ℕ} {G : FinGraph n} {q : ℕ} [NeZero q]

theorem netAt_eq (v : Fin n) (α : G → ZMod q) :
    netAt G q v α = ∑ e, ((if e.1.val.1 = v then (1 : ZMod q) else 0) -
      (if e.1.val.2 = v then 1 else 0)) * α e := by
  unfold netAt
  refine sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

/-- The net flow map as a linear map. -/
def netLin (G : FinGraph n) (q : ℕ) [NeZero q] : (G → ZMod q) →ₗ[ZMod q] (Fin n → ZMod q) where
  toFun α := fun v => netAt G q v α
  map_add' α β := by
    funext v
    simp only [netAt_eq, Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' c α := by
    funext v
    simp only [netAt_eq, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact sum_congr rfl fun e _ => by ring

theorem netLin_apply (α : G → ZMod q) (v : Fin n) : netLin G q α v = netAt G q v α := rfl

/-- The dipole `e_u - e_w`. -/
def dip (q : ℕ) (u w : Fin n) : Fin n → ZMod q := Pi.single u 1 - Pi.single w 1

theorem dip_mem_range_of_adj {u w : Fin n} (h : G.Adj u w) :
    dip q u w ∈ LinearMap.range (netLin G q) := by
  obtain ⟨e, he, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ := h
  · refine ⟨Pi.single ⟨e, he⟩ 1, ?_⟩
    funext x
    rw [netLin_apply, netAt_eq, sum_eq_single (⟨e, he⟩ : G)]
    · simp [dip, Pi.single_apply, h1, h2, eq_comm]
    · intro e' _ hne; simp [hne]
    · simp
  · have : dip q w u ∈ LinearMap.range (netLin G q) := by
      refine ⟨Pi.single ⟨e, he⟩ 1, ?_⟩
      funext x
      rw [netLin_apply, netAt_eq, sum_eq_single (⟨e, he⟩ : G)]
      · simp [dip, Pi.single_apply, h1, h2, eq_comm]
      · intro e' _ hne; simp [hne]
      · simp
    have h2 : dip q u w = -dip q w u := by simp [dip]
    rw [h2]; exact Submodule.neg_mem _ this

theorem dip_mem_range {u w : Fin n} (h : G.Reachable u w) :
    dip q u w ∈ LinearMap.range (netLin G q) := by
  induction h with
  | refl => simp [dip]
  | @tail a c _ hadj ih =>
    have : dip q u c = dip q u a + dip q a c := by simp [dip]
    rw [this]
    exact Submodule.add_mem _ ih (dip_mem_range_of_adj hadj)

/-- On a connected graph every charge of total zero is a net flow. -/
theorem exists_flow (hn : 0 < n) (hG : G.IsConnected) {b : Fin n → ZMod q}
    (hb : ∑ v, b v = 0) : ∃ α : G → ZMod q, ∀ v, netAt G q v α = b v := by
  have hmem : b ∈ LinearMap.range (netLin G q) := by
    have : b = ∑ v, b v • dip q v ⟨0, hn⟩ := by
      funext x
      simp only [dip, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub,
        Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, sum_ite_eq,
        mem_univ, if_true, ← Finset.sum_mul]
      by_cases hx : x = ⟨0, hn⟩ <;> simp [hx, hb]
    rw [this]
    exact Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ (dip_mem_range (hG v _))
  obtain ⟨α, hα⟩ := hmem
  exact ⟨α, fun v => by rw [← netLin_apply, hα]⟩

/-- A net flow with values `α` gives a satisfying assignment. -/
theorem tcnf_sat_of_flow (hn : 0 < n) {b : Fin n → ZMod q} (α : G → ZMod q)
    (hα : ∀ v, netAt G q v α = b v) : Satisfiable (tcnf G q b) := by
  let a : Assignment := fun x => decide (∃ e : G, x = xv e.1 (α e).val)
  have ha : ∀ e : G, ∀ j, a (xv e.1 j) = true ↔ j = (α e).val := by
    intro e j
    simp only [a, decide_eq_true_eq]
    constructor
    · rintro ⟨e', he'⟩
      obtain ⟨h1, h2⟩ := xv_inj hn he'
      have : e = e' := Subtype.ext h1
      subst this; exact h2
    · intro h; exact ⟨e, by rw [h]⟩
  refine ⟨a, fun C hC => ?_⟩
  rcases mem_tcnf hC with ⟨e, rfl⟩ | ⟨e, j, j', hj, hj', hne, rfl⟩ | ⟨v, α', hv, rfl⟩
  · refine ⟨⟨xv e.1 (α e).val, true⟩, ?_, ?_⟩
    · exact mem_image.2 ⟨(α e).val, mem_range.2 (ZMod.val_lt _), rfl⟩
    · exact (ha e _).2 rfl
  · by_cases h1 : a (xv e.1 j) = true
    · refine ⟨⟨xv e.1 j', false⟩, by simp [amoC], ?_⟩
      have := (ha e j).1 h1
      have h2 : a (xv e.1 j') ≠ true := fun h => hne (this.trans ((ha e j').1 h).symm)
      simpa [litSat] using h2
    · refine ⟨⟨xv e.1 j, false⟩, by simp [amoC], ?_⟩
      simpa [litSat] using h1
  · by_contra hcon
    have hcon : ∀ l ∈ vC G q v α', ¬ litSat a l := fun l hl hs => hcon ⟨l, hl, hs⟩
    refine hv ?_
    rw [← hα v]
    have hall : ∀ e : G, e.1 ∈ incident G v → α' e = α e := by
      intro e he
      have := hcon ⟨xv e.1 (α' e).val, false⟩ (mem_image.2 ⟨e, mem_filter.2 ⟨mem_univ _, he⟩, rfl⟩)
      have h2 : a (xv e.1 (α' e).val) = true := by
        simpa [litSat] using this
      exact ZMod.val_injective q ((ha e _).1 h2)
    unfold netAt
    refine sum_congr rfl fun e _ => ?_
    by_cases h1 : e.1.val.1 = v
    · rw [hall e (mem_incident_iff.2 ⟨e.2, Or.inl h1⟩)]
    · by_cases h2 : e.1.val.2 = v
      · rw [hall e (mem_incident_iff.2 ⟨e.2, Or.inr h2⟩)]
      · simp [h1, h2]

/-- **Satisfiability criterion (connected graphs)**: `tcnf G q b` is satisfiable iff the total charge
is zero in `ZMod q`. -/
theorem tcnf_sat_iff (hn : 0 < n) (hG : G.IsConnected) {b : Fin n → ZMod q} :
    Satisfiable (tcnf G q b) ↔ ∑ v, b v = 0 := by
  constructor
  · intro h; by_contra hne; exact tcnf_unsat hne h
  · intro hb
    obtain ⟨α, hα⟩ := exists_flow hn hG hb
    exact tcnf_sat_of_flow hn α hα

end

end TseitinPC

end SATurday.ProofComplexity
