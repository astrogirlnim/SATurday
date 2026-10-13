import Theory.ProofComplexity.ARBound
import Theory.ProofComplexity.ExpanderParams
import Theory.ProofComplexity.PolyCalc

/-!
# Boolean-edge Tseitin mod `q` CNF and its root sets (Ladder Rung R4, layer D1)

AR Definition 4.3: a finite oriented graph with one Boolean variable per edge; the vertex `v` demands
`(sum of in-edge variables) - (sum of out-edge variables) = σ v (mod q)`.  Stated through root sets
`Z v` (the Boolean points satisfying the vertex condition, local to the incident columns `J v`) and
the clause polynomials `cl v α` (one per bad local assignment `α`, equal to `1` exactly on points
that restrict to `α` at `v`).  `ev_ml` connects clause polynomials to the semantic form of `PCL`.

LOG: R4 D1 TseitinEdgeCNF
-/

namespace SATurday.ProofComplexity.TseitinEdge

open Finset MvPolynomial SATurday.ProofComplexity SATurday.ProofComplexity.PCL

noncomputable section
open Classical

/-- A finite oriented multigraph with an injective numbering of the edge variables. -/
structure OGraph (V E : Type) where
  src : E → V
  dst : E → V
  col : E → ℕ
  col_inj : Function.Injective col

variable {V E : Type} [Fintype V] [Fintype E] (G : OGraph V E)

/-- Edges incident to `v`. -/
def OGraph.inc (v : V) : Finset E := Finset.univ.filter fun e => G.src e = v ∨ G.dst e = v

/-- The variable columns of the edges at `v` (the row support of AR). -/
def OGraph.J (v : V) : Finset ℕ := (G.inc v).image G.col

/-- Coefficient of the edge `e` in the condition at `v`: `+1` in, `-1` out. -/
def OGraph.coef (q : ℕ) (v : V) (e : E) : ZMod q :=
  (if G.dst e = v then 1 else 0) - (if G.src e = v then 1 else 0)

/-- The vertex sum of a Boolean edge assignment. -/
def OGraph.lsum (q : ℕ) (v : V) (b : E → Bool) : ZMod q :=
  ∑ e, G.coef q v e * (if b e then 1 else 0)

/-- The Boolean edge assignment of a point `a` (set of true variables). -/
def OGraph.asg (a : Set ℕ) (e : E) : Bool := decide (G.col e ∈ a)

/-- Root set of vertex `v`: points satisfying the vertex condition. -/
def OGraph.Z (q : ℕ) (σ : V → ZMod q) (v : V) : Set (Set ℕ) := {a | G.lsum q v (G.asg a) = σ v}

theorem OGraph.coef_eq_zero {q : ℕ} {v : V} {e : E} (h : e ∉ G.inc v) : G.coef q v e = 0 := by
  simp only [OGraph.inc, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at h
  simp [OGraph.coef, h.1, h.2]

theorem OGraph.lsum_congr (q : ℕ) (v : V) {b b' : E → Bool} (h : ∀ e ∈ G.inc v, b e = b' e) :
    G.lsum q v b = G.lsum q v b' := by
  unfold OGraph.lsum
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases he : e ∈ G.inc v
  · rw [h e he]
  · rw [G.coef_eq_zero he]; simp

/-- Locality of the root set: it depends only on the columns `J v`. -/
theorem OGraph.Z_local (q : ℕ) (σ : V → ZMod q) (v : V) (a b : Set ℕ)
    (h : ∀ x ∈ G.J v, (x ∈ a ↔ x ∈ b)) (ha : a ∈ G.Z q σ v) : b ∈ G.Z q σ v := by
  unfold OGraph.Z at *
  simp only [Set.mem_setOf_eq] at *
  rw [← ha]
  refine (G.lsum_congr q v fun e he => ?_)
  have := h (G.col e) (Finset.mem_image_of_mem _ he)
  simp [OGraph.asg, this]

/-- The clause polynomial: `1` exactly on points whose restriction to `inc v` is `α`. -/
def OGraph.cl (F : Type) [Field F] (v : V) (α : E → Bool) : MvPolynomial ℕ F :=
  ∏ e ∈ G.inc v, if α e then X (G.col e) else 1 - X (G.col e)

/-- The CNF `T_q(G, σ)`: clause polynomials of the bad local assignments. -/
def OGraph.Ax (F : Type) [Field F] (q : ℕ) (σ : V → ZMod q) : Set (MvPolynomial ℕ F) :=
  {p | ∃ v α, G.lsum q v α ≠ σ v ∧ p = G.cl F v α}

/-- The point `a` as a 0-1 valuation. -/
def pt (F : Type) [Field F] (a : Set ℕ) (i : ℕ) : F := if i ∈ a then 1 else 0

/-- **Connection lemma**: the evaluation of the multilinearization at a Boolean point is the
polynomial evaluation. -/
theorem ev_ml {F : Type} [Field F] (a : Set ℕ) (p : MvPolynomial ℕ F) :
    ev a (ml p) = MvPolynomial.eval (pt F a) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [ml_monomial, ev_single, MvPolynomial.eval_monomial]
    unfold Finsupp.prod
    by_cases h : (↑m.support : Set ℕ) ⊆ a
    · rw [if_pos h, Finset.prod_eq_one, mul_one]
      intro i hi
      have : i ∈ a := h hi
      simp [pt, this]
    · rw [if_neg h]
      obtain ⟨i, hi, hia⟩ : ∃ i ∈ m.support, i ∉ a := by
        by_contra hc; push Not at hc; exact h fun x hx => hc x hx
      rw [Finset.prod_eq_zero hi]
      · simp
      · have : m i ≠ 0 := Finsupp.mem_support_iff.1 hi
        simp [pt, hia, this]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem OGraph.eval_cl {F : Type} [Field F] (a : Set ℕ) (v : V) (α : E → Bool) :
    MvPolynomial.eval (pt F a) (G.cl F v α) =
      if ∀ e ∈ G.inc v, G.asg a e = α e then 1 else 0 := by
  unfold OGraph.cl
  rw [map_prod]
  have h : ∀ e ∈ G.inc v, MvPolynomial.eval (pt F a)
      (if α e then X (G.col e) else 1 - X (G.col e)) = if G.asg a e = α e then (1 : F) else 0 := by
    intro e _
    by_cases h : α e <;> by_cases h2 : G.col e ∈ a <;> simp [pt, OGraph.asg, h, h2]
  rw [Finset.prod_congr rfl h, Finset.prod_boole]
  congr

theorem OGraph.ev_cl {F : Type} [Field F] (a : Set ℕ) (v : V) (α : E → Bool) :
    ev a (ml (G.cl F v α)) = if ∀ e ∈ G.inc v, G.asg a e = α e then 1 else 0 := by
  rw [ev_ml, G.eval_cl]

/-- Clause polynomials are supported in the row support. -/
theorem OGraph.cl_supp {F : Type} [Field F] (v : V) (α : E → Bool) :
    ∀ T ∈ (ml (G.cl F v α)).support, T ⊆ G.J v := by
  intro T hT
  obtain ⟨m, hm, rfl⟩ := support_ml_subset _ T hT
  intro i hi
  have hv : i ∈ (G.cl F v α).vars := MvPolynomial.mem_vars _ |>.2 ⟨m, hm, hi⟩
  have hsub : (G.cl F v α).vars ⊆ G.J v := by
    unfold OGraph.cl
    intro i hi
    obtain ⟨e, he, hie⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hi)
    have : i = G.col e := by
      by_cases h : α e
      · simp only [h, if_true] at hie
        simpa using hie
      · simp only [h, Bool.false_eq_true, if_false] at hie
        have hs : (1 - X (G.col e) : MvPolynomial ℕ F).vars ⊆
            (1 : MvPolynomial ℕ F).vars ∪ (X (G.col e) : MvPolynomial ℕ F).vars :=
          MvPolynomial.vars_sub_subset _
        have := hs hie
        simpa using this
    exact Finset.mem_image.2 ⟨e, he, this.symm⟩
  exact hsub hv

/-! ## Clause polynomials are PC axioms of the semantic form, and unsatisfiability -/

/-- The clause polynomials are local to the row support and vanish on the root set. -/
theorem OGraph.cl_axiom {F : Type} [Field F] (q : ℕ) (σ : V → ZMod q) {p : MvPolynomial ℕ F}
    (hp : p ∈ G.Ax F q σ) :
    ∃ v, (∀ T ∈ (ml p).support, T ⊆ G.J v) ∧ ml p ∈ vsub (F := F) (G.Z q σ v) := by
  obtain ⟨v, α, hbad, rfl⟩ := hp
  refine ⟨v, G.cl_supp v α, fun a ha => ?_⟩
  rw [G.ev_cl, if_neg]
  intro hall
  apply hbad
  have : G.lsum q v α = G.lsum q v (G.asg a) := G.lsum_congr q v fun e he => (hall e he).symm
  rw [this]; exact ha

/-- A Boolean point is a common root of the clause polynomials iff it satisfies every vertex. -/
theorem OGraph.Ax_root_iff {F : Type} [Field F] (q : ℕ) (σ : V → ZMod q) (a : Set ℕ) :
    (∀ p ∈ G.Ax F q σ, MvPolynomial.eval (pt F a) p = 0) ↔ ∀ v, a ∈ G.Z q σ v := by
  constructor
  · intro h v
    by_contra hv
    have := h (G.cl F v (G.asg a)) ⟨v, G.asg a, hv, rfl⟩
    rw [G.eval_cl, if_pos (fun e _ => rfl)] at this
    exact one_ne_zero this
  · intro h p hp
    obtain ⟨v, α, hbad, rfl⟩ := hp
    rw [G.eval_cl, if_neg]
    intro hall
    apply hbad
    have : G.lsum q v α = G.lsum q v (G.asg a) := G.lsum_congr q v fun e he => (hall e he).symm
    rw [this]; exact h v

/-- Every edge is counted once with `+` and once with `-`: the vertex sums add up to `0`. -/
theorem OGraph.sum_lsum (q : ℕ) (b : E → Bool) : ∑ v, G.lsum q v b = 0 := by
  unfold OGraph.lsum
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [← Finset.sum_mul]
  have : ∑ v, G.coef q v e = 0 := by
    unfold OGraph.coef
    rw [Finset.sum_sub_distrib]
    simp
  rw [this, zero_mul]

/-- Unsatisfiability (AR Def. 4.3): if `∑ σ ≠ 0` there is no point satisfying all vertices. -/
theorem OGraph.Z_inter_empty (q : ℕ) (σ : V → ZMod q) (hσ : ∑ v, σ v ≠ 0) (a : Set ℕ) :
    ¬ ∀ v, a ∈ G.Z q σ v := by
  intro h
  apply hσ
  rw [← G.sum_lsum q (G.asg a)]
  exact (Finset.sum_congr rfl fun v _ => (h v).symm)

/-- The Tseitin CNF has no common Boolean root of its clause polynomials. -/
theorem OGraph.Ax_unsat {F : Type} [Field F] (q : ℕ) (σ : V → ZMod q) (hσ : ∑ v, σ v ≠ 0)
    (a : Set ℕ) : ¬ ∀ p ∈ G.Ax F q σ, MvPolynomial.eval (pt F a) p = 0 :=
  fun h => G.Z_inter_empty q σ hσ a ((G.Ax_root_iff q σ a).1 h)

/-! ## Boundary form -/

/-- Edge cut of a vertex set. -/
def OGraph.cut (I : Finset V) : Finset E := Finset.univ.filter fun e => (G.src e ∈ I) ≠ (G.dst e ∈ I)

theorem OGraph.bdry_eq (hloop : ∀ e, G.src e ≠ G.dst e) (I : Finset V) :
    bdry G.J I = (G.cut I).image G.col := by
  ext j
  simp only [bdry, Finset.mem_filter, Finset.mem_biUnion, OGraph.J, Finset.mem_image,
    OGraph.cut, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨v, hv, e, he, rfl⟩, hcard⟩
    refine ⟨e, ?_, rfl⟩
    have hf : I.filter (fun v => ∃ a ∈ G.inc v, G.col a = G.col e) =
        I.filter (fun v => G.src e = v ∨ G.dst e = v) := by
      refine Finset.filter_congr fun w _ => ?_
      constructor
      · rintro ⟨e', he', hee⟩
        have := G.col_inj hee
        subst this
        simpa [OGraph.inc] using he'
      · intro h
        exact ⟨e, by simpa [OGraph.inc] using h, rfl⟩
    rw [hf] at hcard
    have hne := hloop e
    by_cases h1 : G.src e ∈ I <;> by_cases h2 : G.dst e ∈ I
    · exfalso
      have : I.filter (fun v => G.src e = v ∨ G.dst e = v) = {G.src e, G.dst e} := by
        ext w; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨_, h | h⟩ <;> simp [h]
        · rintro (h | h) <;> subst h <;> simp [h1, h2]
      rw [this, Finset.card_pair hne] at hcard; omega
    · simp [h1, h2]
    · simp [h1, h2]
    · exfalso
      have : I.filter (fun v => G.src e = v ∨ G.dst e = v) = ∅ := by
        ext w; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        rintro hw (h | h) <;> subst h <;> contradiction
      rw [this] at hcard; simp at hcard
  · rintro ⟨e, he, rfl⟩
    have hf : I.filter (fun v => ∃ a ∈ G.inc v, G.col a = G.col e) =
        I.filter (fun v => G.src e = v ∨ G.dst e = v) := by
      refine Finset.filter_congr fun w _ => ?_
      constructor
      · rintro ⟨e', he', hee⟩
        have := G.col_inj hee
        subst this
        simpa [OGraph.inc] using he'
      · intro h
        exact ⟨e, by simpa [OGraph.inc] using h, rfl⟩
    by_cases h1 : G.src e ∈ I
    · have h2 : G.dst e ∉ I := fun h2 => he (by simp [h1, h2])
      refine ⟨⟨G.src e, h1, e, by simp [OGraph.inc], rfl⟩, ?_⟩
      rw [hf]
      have : I.filter (fun v => G.src e = v ∨ G.dst e = v) = {G.src e} := by
        ext w; simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hw, h | h⟩
          · exact h.symm
          · subst h; exact absurd hw h2
        · rintro rfl; exact ⟨h1, Or.inl rfl⟩
      rw [this]; simp
    · have h2 : G.dst e ∈ I := by
        by_contra h2; exact he (by simp [h1, h2])
      refine ⟨⟨G.dst e, h2, e, by simp [OGraph.inc], rfl⟩, ?_⟩
      rw [hf]
      have : I.filter (fun v => G.src e = v ∨ G.dst e = v) = {G.dst e} := by
        ext w; simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hw, h | h⟩
          · subst h; exact absurd hw h1
          · exact h.symm
        · rintro rfl; exact ⟨h2, Or.inr rfl⟩
      rw [this]; simp

theorem OGraph.card_bdry (hloop : ∀ e, G.src e ≠ G.dst e) (I : Finset V) :
    (bdry G.J I).card = (G.cut I).card := by
  rw [G.bdry_eq hloop, Finset.card_image_of_injective _ G.col_inj]

/-- **D1 main theorem (generic form).**  If the root sets are `ℓ`-immune (the hypothesis `himm`,
which is AR Theorem 4.4 for the mod-`q` vertex predicate, to be discharged by AR-B), the vertex
degrees are at most `s`, and the edge cuts of vertex sets of size at most `r` have at least
`c |I|` edges, with `4 (s-c) < ℓ` and `s ≤ r (ℓ/4 - (s-c))`, then the Tseitin CNF has no
polynomial calculus refutation of degree `≤ r (ℓ/4 - (s-c))`. -/
theorem tseitin_no_refutation {F : Type} [Field F] (hloop : ∀ e, G.src e ≠ G.dst e)
    (q : ℕ) (σ : V → ZMod q) {ℓ r : ℕ} {s c : ℝ}
    (himm : ∀ v, ∀ g : ML F, g ≠ 0 → (∀ a ∈ G.Z q σ v, ev a g = 0) → ℓ ≤ deg g)
    (hwt : ∀ v, ((G.J v).card : ℝ) ≤ s)
    (hexp : ∀ I : Finset V, I.card ≤ r → c * (I.card : ℝ) ≤ ((G.cut I).card : ℝ))
    (hr : 1 ≤ r) (hl : 1 ≤ ℓ) (hsc : 4 * (s - c) < ℓ) (hsD : s ≤ Dbd ℓ r s c)
    {d : ℕ} (hd : (d : ℝ) ≤ Dbd ℓ r s c) : ¬ PCD (G.Ax F q σ) d 1 := by
  have Gd : Good F G.J (G.Z q σ) ℓ r s c :=
    { loc := fun v a b h ha => G.Z_local q σ v a b h ha
      imm := himm
      wt := hwt
      exp := fun I hI => by rw [G.card_bdry hloop]; exact hexp I hI
      hr := hr
      hl := hl
      hsc := hsc }
  exact ar_no_refutation Gd hsD (fun p hp => G.cl_axiom q σ hp) hd

/-! ## The Gabber-Galil walk multigraph as an oriented graph -/

open SATurday.ProofComplexity.Expander in
/-- The bipartite walk multigraph `GGW m k`, oriented from the left copy to the right copy. -/
def ggwGraph (m : ℕ) (hm : 3 ≤ m) (k : ℕ) :
    OGraph (MggTorus m ⊕ MggTorus m) (MggTorus m × (Fin k → Fin 8)) where
  src e := Sum.inl e.1
  dst e := Sum.inr ((ggSys m hm).walkEnd k e.1 e.2)
  col e := (Fintype.equivFin _ e : ℕ)
  col_inj := fun x y h => (Fintype.equivFin _).injective (Fin.ext h)

open SATurday.ProofComplexity.Expander in
theorem ggwGraph_cut (m : ℕ) (hm : 3 ≤ m) (k : ℕ) (I : Finset (MggTorus m ⊕ MggTorus m)) :
    (ggwGraph m hm k).cut I = ggwBoundary m hm k I.toLeft I.toRight := by
  unfold OGraph.cut ggwBoundary
  ext e
  simp [ggwGraph]

open SATurday.ProofComplexity.Expander in
theorem ggwGraph_inc_card (m : ℕ) (hm : 3 ≤ m) (k : ℕ) (v : MggTorus m ⊕ MggTorus m) :
    (((ggwGraph m hm k).inc v).card : ℝ) = (8 : ℝ) ^ k := by
  rcases v with u | w
  · have h := ggw_left_count m hm k {u}
    have e : (ggwGraph m hm k).inc (Sum.inl u) =
        (Finset.univ : Finset (MggTorus m × (Fin k → Fin 8))).filter fun e => e.1 ∈ ({u} : Finset _) := by
      ext e; simp [OGraph.inc, ggwGraph]
    rw [e, h]; simp
  · have h := ggw_right_count m hm k {w}
    have e : (ggwGraph m hm k).inc (Sum.inr w) =
        (Finset.univ : Finset (MggTorus m × (Fin k → Fin 8))).filter fun e =>
          (ggSys m hm).walkEnd k e.1 e.2 ∈ ({w} : Finset _) := by
      ext e; simp [OGraph.inc, ggwGraph, eq_comm]
    rw [e, h]; simp

open SATurday.ProofComplexity.Expander in
/-- **D1 connected to the expander (boundary form).**  The Tseitin mod `q` CNF on the walk
multigraph `GGW m k` (degree `8^k`, `k ≥ k0 q`) has no PC refutation of degree
`≤ rBound · (ℓ/4 - 8^k/(16 q))` provided the vertex root sets are `ℓ`-immune (AR Theorem 4.4,
hypothesis `himm`, open) and `4 · 8^k/(16 q) < ℓ`, `8^k ≤ r (ℓ/4 - 8^k/(16q))`. -/
theorem ggw_tseitin_no_refutation {F : Type} [Field F] (m : ℕ) (hm : 3 ≤ m) {q : ℕ} (hq : 1 ≤ q)
    {k : ℕ} (hk : k0 q ≤ k) (σ : MggTorus m ⊕ MggTorus m → ZMod q) {ℓ : ℕ}
    (himm : ∀ v, ∀ g : ML F, g ≠ 0 → (∀ a ∈ (ggwGraph m hm k).Z q σ v, ev a g = 0) → ℓ ≤ deg g)
    (hr : 1 ≤ rBound m q) (hl : 1 ≤ ℓ)
    (hsc : 4 * ((8 : ℝ) ^ k - (8 : ℝ) ^ k * (1 - 1 / (16 * q))) < ℓ)
    (hsD : (8 : ℝ) ^ k ≤ Dbd ℓ (rBound m q) ((8 : ℝ) ^ k) ((8 : ℝ) ^ k * (1 - 1 / (16 * q))))
    {d : ℕ} (hd : (d : ℝ) ≤ Dbd ℓ (rBound m q) ((8 : ℝ) ^ k) ((8 : ℝ) ^ k * (1 - 1 / (16 * q)))) :
    ¬ PCD ((ggwGraph m hm k).Ax F q σ) d 1 := by
  refine tseitin_no_refutation (ggwGraph m hm k) (fun e => by simp [ggwGraph]) q σ himm
    (fun v => ?_) (fun I hI => ?_) hr hl hsc hsD hd
  · have h1 : ((ggwGraph m hm k).J v).card ≤ ((ggwGraph m hm k).inc v).card :=
      Finset.card_image_le
    have h2 : (((ggwGraph m hm k).J v).card : ℝ) ≤ (((ggwGraph m hm k).inc v).card : ℝ) := by
      exact_mod_cast h1
    exact h2.trans (ggwGraph_inc_card m hm k v).le
  · rw [ggwGraph_cut]
    have h := ggw_rsc m hm hq hk I.toLeft I.toRight (by
      have := Finset.card_toLeft_add_card_toRight (u := I)
      omega)
    have e : (I.toLeft.card + I.toRight.card : ℕ) = I.card := Finset.card_toLeft_add_card_toRight
    rw [e] at h
    linarith [h, mul_comm ((8 : ℝ) ^ k * (1 - 1 / (16 * q))) (I.card : ℝ)]

end

end SATurday.ProofComplexity.TseitinEdge
