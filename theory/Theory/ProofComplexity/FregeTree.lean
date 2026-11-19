import Theory.ProofComplexity.PICTree

/-!
# Tree-like proofs in the pinned sequent calculus: no degree wall

`TProof p F P S s`: a tree-like derivation of the sequent `S` with `s` nodes in the sequent calculus
of `AC0pFrege.lean`.  A node is one application of the pinned step relation `FStep p F prev S` (the
same 18 rules as in `FProof`), where every sequent of the list `prev` carries its own subtree; the
size is the number of nodes.  `P` is a condition on every sequent of the tree (the fragment).

For the fragment `DegS p d` of `FregeDegBridge.lean` (every term of the translation of every
sequent has syntactic degree at most `d`; formulas of any depth) a tree-like refutation with `s`
nodes gives a polynomial calculus refutation of degree at most `d * log2 s + max w (3 d)`
(`tree_frege_pc_degree`).  The proof does not go through the dag-like bridge `frege_to_PIC` (which
reuses lines); it bounds the measure `PICT.Ref` of the translated sequent at every node directly:

* premise free rules except the clause axiom: the sequent is valid, has at most three formulas, and
  each of them has `pd ≤ d`, so the single terms are derived from the terms of the translation
  (`split_cd`) and the product of their complements vanishes on the cube (`valid_ref`);
* weakening, negation rules, `AND` left, `OR` right: the translated premise is a subset;
* cut on `φ`: deduction on the smaller premise with the indicator of `φ` (`cut_core`);
* `AND` right, `OR` left with any number of premises: deduction on every premise except the one
  with the largest subtree (`gate_core`).

With the polynomial calculus degree bound for Tseitin this gives an exponential size bound for
tree-like refutations in the fragment at every degree up to `n^(1-δ)` (`frege_tree_main_idx`),
with a refutation in the fragment for `d ≥ q + 3`.  Known mathematics (tree-like size-degree
argument); no novelty is claimed.

LOG: R4 treedeg fable session, tree-like sequent calculus
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.PCL MvPolynomial PIC FDeg PICT

namespace FTree

set_option linter.unusedSectionVars false

noncomputable section
open Classical Pang

variable {p : ℕ} [Fact p.Prime]

/-! ## Polynomial calculus lemmas for the translation -/

theorem sg_deg (s : Bool) (φ : Fm) : (sg s (val p φ)).totalDegree ≤ pd p φ := by
  cases s
  · exact (deg_one_sub _).trans (deg_val φ)
  · exact deg_val φ

theorem sg_cube (s : Bool) (φ : Fm) (a : Assignment) :
    eval (boolPt (F := ZMod p) a) (sg s (val p φ)) = 0 ∨
      eval (boolPt (F := ZMod p) a) (sg s (val p φ)) = 1 := by
  rw [eval_sg_val]; split_ifs <;> simp

theorem deg_tr {φ : Fm} {s : Bool} {g : PP p} (hg : g ∈ trL p s φ) :
    g.totalDegree ≤ td p s φ := by
  obtain ⟨ψ, s', rfl, h2, -, -⟩ := tr_form φ s g hg
  exact (sg_deg s' ψ).trans h2

theorem deg_trS {d : ℕ} {S : Seq} (hd : DegS p d S) {g : PP p} (hg : g ∈ trS p S) :
    g.totalDegree ≤ d := by
  rcases mem_trS.1 hg with ⟨φ, hφ, h⟩ | ⟨φ, hφ, h⟩
  · exact (deg_tr h).trans (hd.1 φ hφ)
  · exact (deg_tr h).trans (hd.2 φ hφ)

/-- `1 - ∏ f ψ` from the `1 - f ψ`. -/
theorem one_sub_prod {A : Set (PP p)} {E : ℕ} (f : Fm → PP p)
    (hf : ∀ ψ, (f ψ).totalDegree ≤ pd p ψ) :
    ∀ l : List Fm, (∀ ψ ∈ l, 1 - f ψ ∈ CD A E) → (l.map (pd p)).sum ≤ E →
      1 - (l.map f).prod ∈ CD A E := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons ψ l ih =>
    intro h hE
    rw [List.map_cons, List.sum_cons] at hE
    rw [List.map_cons, List.prod_cons]
    have e : 1 - f ψ * (l.map f).prod = (1 - f ψ) + f ψ * (1 - (l.map f).prod) := by ring
    rw [e]
    refine add_mem (h ψ (by simp))
      (cd_mul (ih (fun χ hχ => h χ (List.mem_cons_of_mem _ hχ)) (by omega)) ?_)
    have d1 := hf ψ
    have d2 : (1 - (l.map f).prod).totalDegree ≤ (l.map (pd p)).sum :=
      (deg_one_sub _).trans (deg_list_prod l f (pd p) fun χ _ => hf χ)
    omega

/-- **Splitting in polynomial calculus.**  If all terms of the translation of `φ` with sign `s`
are derived, so is the single term `sg s (val p φ)`, in degree `pd p φ`. -/
theorem split_cd {A : Set (PP p)} {E : ℕ} : ∀ (φ : Fm) (s : Bool), pd p φ ≤ E →
    (∀ g ∈ trL p s φ, g ∈ CD A E) → sg s (val p φ) ∈ CD A E := by
  refine Fm_ind ?_ ?_ ?_ ?_ ?_
  · intro i s _ h
    exact h _ (by rw [trL_var, val_var]; simp)
  · intro φ ih s hE h
    rw [pd_neg] at hE
    have h1 := ih (!s) hE (fun g hg => h g (by rw [trL_neg]; exact hg))
    have e : sg s (val p (.neg φ)) = sg (!s) (val p φ) := by
      rw [val_neg]; cases s <;> simp [sg]
    rw [e]; exact h1
  · intro l ih s hE h
    cases s
    · show 1 - val p (.and l) ∈ CD A E
      rw [val_and]
      refine one_sub_prod (val p) deg_val l (fun ψ hψ => ?_) (by rw [pd_and] at hE; exact hE)
      exact ih ψ hψ false ((pd_le_and hψ).trans hE)
        (fun g hg => h g ((mem_trL_and_false l g).2 ⟨ψ, hψ, hg⟩))
    · have := h (val p (.and l)) (by rw [trL_and_true]; simp)
      exact this
  · intro l ih s hE h
    cases s
    · have := h (1 - val p (.or l)) (by rw [trL_or_false]; simp)
      exact this
    · show val p (.or l) ∈ CD A E
      rw [val_or]
      refine one_sub_prod (fun ψ => 1 - val p ψ) (fun ψ => (deg_one_sub _).trans (deg_val ψ)) l
        (fun ψ hψ => ?_) (by rw [pd_or] at hE; exact hE)
      have h1 := ih ψ hψ true ((pd_le_or hψ).trans hE)
        (fun g hg => h g ((mem_trL_or_true l g).2 ⟨ψ, hψ, hg⟩))
      show 1 - (1 - val p ψ) ∈ CD A E
      rw [sub_sub_cancel]; exact h1
  · intro r l _ s _ h
    exact h _ (by rw [trL_mod]; simp)

/-- `1 - ∏ (1 - x)` from the `x`. -/
theorem one_sub_prod_list {A : Set (PP p)} {E d : ℕ} :
    ∀ xs : List (PP p), (∀ x ∈ xs, x ∈ CD A E ∧ x.totalDegree ≤ d) → d * xs.length ≤ E →
      1 - (xs.map fun x => 1 - x).prod ∈ CD A E ∧
        ((xs.map fun x => 1 - x).prod).totalDegree ≤ d * xs.length := by
  intro xs
  induction xs with
  | nil => intro _ _; simp
  | cons x xs ih =>
    intro h hE
    rw [List.length_cons, Nat.mul_succ] at hE ⊢
    obtain ⟨i1, i2⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) (by omega)
    obtain ⟨hx, hxd⟩ := h x (by simp)
    rw [List.map_cons, List.prod_cons]
    have dx := (deg_one_sub x).trans hxd
    have d2 := deg_one_sub (xs.map fun x => 1 - x).prod
    refine ⟨?_, (totalDegree_mul _ _).trans (by omega)⟩
    have e : 1 - (1 - x) * (xs.map fun x => 1 - x).prod =
        x + (1 - x) * (1 - (xs.map fun x => 1 - x).prod) := by ring
    rw [e]
    exact add_mem hx (cd_mul i1 (by omega))

/-- A valid sequent with at most three formulas, each with `pd ≤ d`, is refuted in degree `3 d`. -/
theorem valid_ref {Φ : CNF} {S : Seq} {d D' : ℕ} (hval : ∀ a : Assignment, SeqSat p a S)
    (hpd : ∀ φ ∈ S.1 ++ S.2, pd p φ ≤ d) (hlen : (S.1 ++ S.2).length ≤ 3) (h3 : 3 * d ≤ D')
    (h2 : 2 ≤ D') : Ref Φ (trS p S) D' := by
  unfold Ref
  set A : Set (PP p) := cnfAx Φ ∪ (↑(trS p S) : Set (PP p)) with hA
  set xs : List (PP p) := S.1.map (fun φ => sg false (val p φ)) ++
    S.2.map (fun φ => sg true (val p φ)) with hxs
  have hdD : d ≤ D' := by omega
  have hx : ∀ x ∈ xs, x ∈ CD A D' ∧ x.totalDegree ≤ d := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 h
      have hp := hpd φ (List.mem_append_left _ hφ)
      refine ⟨split_cd φ false (hp.trans hdD) fun g hg => ?_, (sg_deg _ _).trans hp⟩
      exact ax_mem (mem_trS.2 (Or.inl ⟨φ, hφ, hg⟩))
        (((deg_tr hg).trans (td_le_pd φ false)).trans (hp.trans hdD))
    · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 h
      have hp := hpd φ (List.mem_append_right _ hφ)
      refine ⟨split_cd φ true (hp.trans hdD) fun g hg => ?_, (sg_deg _ _).trans hp⟩
      exact ax_mem (mem_trS.2 (Or.inr ⟨φ, hφ, hg⟩))
        (((deg_tr hg).trans (td_le_pd φ true)).trans (hp.trans hdD))
  have hl : xs.length ≤ 3 := by
    rw [hxs, List.length_append, List.length_map, List.length_map]
    rw [List.length_append] at hlen; exact hlen
  have hdl : d * xs.length ≤ D' := (Nat.mul_le_mul_left d hl).trans (by omega)
  obtain ⟨k1, k2⟩ := one_sub_prod_list xs hx hdl
  have hcube : ∀ a : Set ℕ, eval (indPt a) ((xs.map fun x => 1 - x).prod) = 0 := by
    intro a
    rw [C1.indPt_eq]
    set b : Assignment := fun i => decide (i ∈ a) with hb
    have hex : ∃ x ∈ xs, eval (boolPt (F := ZMod p) b) x = 1 := by
      by_cases hall : ∀ φ ∈ S.1, φ.eval p b = true
      · obtain ⟨ψ, hψ, he⟩ := hval b hall
        exact ⟨sg true (val p ψ), List.mem_append_right _ (List.mem_map.2 ⟨ψ, hψ, rfl⟩), by
          rw [eval_sg_val, if_pos he]⟩
      · push Not at hall
        obtain ⟨φ, hφ, he⟩ := hall
        have he' : φ.eval p b = false := by simpa using he
        exact ⟨sg false (val p φ), List.mem_append_left _ (List.mem_map.2 ⟨φ, hφ, rfl⟩), by
          rw [eval_sg_val, if_pos he']⟩
    obtain ⟨x, hxm, hx1⟩ := hex
    rw [map_list_prod, List.map_map]
    refine List.prod_eq_zero (List.mem_map.2 ⟨x, hxm, ?_⟩)
    simp [hx1]
  have k3 := cd_of_cube (Ax := A) (D := D') h2 (k2.trans hdl) hcube
  have := add_mem k1 k3
  rwa [sub_add_cancel] at this

/-- Variant of `PICT.ref_of_derive` with the degree of the term at hand. -/
theorem ref_of_derive' {Φ : CNF} {L₁ L' : PLine p} {D₁ D' : ℕ} (hD : D₁ ≤ D')
    (h : ∀ g ∈ L₁, g.totalDegree ≤ D₁ → g ∈ CD (cnfAx Φ ∪ (↑L' : Set (PP p))) D')
    (h1 : Ref Φ L₁ D₁) : Ref Φ L' D' := by
  refine cd_subst hD ?_ h1
  rintro f (hf | hf) hd
  · exact mem_CD_of_pcd (PCD.ax (Or.inl hf) (hd.trans hD))
  · exact h f (Finset.mem_coe.1 hf) hd

/-- **Deduction on a line.**  If every term of `L₁` is a term of `L'` or implies the indicator `h`,
a refutation below `L₁` in degree `D₀` derives `1 - h` below `L'` in degree `max D₀ (2 d) + d`. -/
theorem ded_line {Φ : CNF} {L₁ L' : PLine p} {h : PP p} {d D₀ D' : ℕ} (hd1 : 1 ≤ d)
    (hcube : ∀ a : Assignment, eval (boolPt (F := ZMod p) a) h = 0 ∨
      eval (boolPt (F := ZMod p) a) h = 1)
    (hdeg : h.totalDegree ≤ d)
    (hL : ∀ g ∈ L₁, g ∈ L' ∨ (g.totalDegree ≤ d ∧ ∀ a : Assignment,
      eval (boolPt (F := ZMod p) a) g * (1 - eval (boolPt (F := ZMod p) a) h) = 0))
    (hD : D₀ + d ≤ D') (h3 : 3 * d ≤ D') (hr : Ref Φ L₁ D₀) :
    1 - h ∈ CD (cnfAx Φ ∪ (↑L' : Set (PP p))) D' := by
  set A' : Set (PP p) := cnfAx Φ ∪ (↑L' : Set (PP p)) with hA'
  have m1 : D₀ ≤ max D₀ (2 * d) := le_max_left _ _
  have m2 : 2 * d ≤ max D₀ (2 * d) := le_max_right _ _
  have key : (1 : PP p) ∈ CD (insert h A') (max D₀ (2 * d)) := by
    refine cd_subst m1 ?_ hr
    rintro f (hf | hf) hfd
    · exact mem_CD_of_pcd (PCD.ax (Or.inr (Or.inl hf)) (hfd.trans m1))
    · rcases hL f (Finset.mem_coe.1 hf) with h' | ⟨hfd', hc⟩
      · exact mem_CD_of_pcd (PCD.ax (Or.inr (Or.inr (Finset.mem_coe.2 h'))) (hfd.trans m1))
      · have hh : h ∈ CD (insert h A') (max D₀ (2 * d)) :=
          mem_CD_of_pcd (PCD.ax (Or.inl rfl) (by omega))
        have e : f = f * h + f * (1 - h) := by ring
        rw [e]
        have t1 := deg_one_sub h
        refine add_mem (cd_mul hh (by omega)) (cd_of_cube (by omega) ?_ fun a => ?_)
        · exact (totalDegree_mul _ _).trans (by omega)
        · rw [C1.indPt_eq, map_mul, map_sub, map_one]; exact hc _
  have hm : max D₀ (2 * d) + d ≤ D' := by
    have := max_le (show D₀ ≤ D' - d by omega) (show 2 * d ≤ D' - d by omega)
    omega
  have := cd_deduct (PIC.cube_set hcube) hdeg hm (by omega) key
  rwa [mul_one] at this

/-- **Cut with an indicator.**  Terms of `L₁` outside `L'` imply `h`, terms of `L₂` outside `L'`
exclude `h`.  Deduction on `L₁`. -/
theorem cut_core {Φ : CNF} {L₁ L₂ L' : PLine p} {h : PP p} {d D₀ D' : ℕ} (hd1 : 1 ≤ d)
    (hcube : ∀ a : Assignment, eval (boolPt (F := ZMod p) a) h = 0 ∨
      eval (boolPt (F := ZMod p) a) h = 1)
    (hdeg : h.totalDegree ≤ d)
    (hL₁ : ∀ g ∈ L₁, g ∈ L' ∨ (g.totalDegree ≤ d ∧ ∀ a : Assignment,
      eval (boolPt (F := ZMod p) a) g * (1 - eval (boolPt (F := ZMod p) a) h) = 0))
    (hL₂ : ∀ g ∈ L₂, g ∈ L' ∨ (g.totalDegree ≤ d ∧ ∀ a : Assignment,
      eval (boolPt (F := ZMod p) a) g * eval (boolPt (F := ZMod p) a) h = 0))
    (hD : D₀ + d ≤ D') (h3 : 3 * d ≤ D') (hr1 : Ref Φ L₁ D₀) (hr2 : Ref Φ L₂ D') :
    Ref Φ L' D' := by
  have hb := ded_line hd1 hcube hdeg hL₁ hD h3 hr1
  refine ref_of_derive' le_rfl (fun g hg hgd => ?_) hr2
  rcases hL₂ g hg with h' | ⟨hgd', hc⟩
  · exact ax_mem h' hgd
  · have e : g = g * (1 - h) + g * h := by ring
    rw [e]
    have t1 := deg_one_sub h
    refine add_mem (cd_mul hb (by omega)) (cd_of_cube (by omega) ?_ fun a => ?_)
    · exact (totalDegree_mul _ _).trans (by omega)
    · rw [C1.indPt_eq, map_mul]; exact hc _

/-- Absorption at a gate: `y (1 - ∏ x_ψ)` is derived if `1 - x_ψ` is derived for all members
except the pivot `ψs`, and `y` implies `x_ψs`. -/
theorem gate_absorb {A : Set (PP p)} {E d : ℕ} (s : Bool) (ψs : Fm) {y : PP p}
    (hy : y.totalDegree ≤ d) (h2 : 2 ≤ E) (h2d : 2 * d ≤ E) :
    ∀ l : List Fm, (l.map (pd p)).sum ≤ d →
      (∀ ψ ∈ l, ψ ≠ ψs → 1 - sg s (val p ψ) ∈ CD A E) →
      (ψs ∈ l → ∀ a : Assignment, eval (boolPt (F := ZMod p) a) y *
        (1 - eval (boolPt (F := ZMod p) a) (sg s (val p ψs))) = 0) →
      y * (1 - (l.map fun ψ => sg s (val p ψ)).prod) ∈ CD A E := by
  intro l
  induction l with
  | nil => intro _ _ _; simp
  | cons ψ l ih =>
    intro hsum hsm hcb
    rw [List.map_cons, List.sum_cons] at hsum
    rw [List.map_cons, List.prod_cons]
    have dP : ((l.map fun ψ => sg s (val p ψ)).prod).totalDegree ≤ (l.map (pd p)).sum :=
      deg_list_prod l _ _ (fun χ _ => sg_deg s χ)
    have dx : (1 - sg s (val p ψ)).totalDegree ≤ pd p ψ := (deg_one_sub _).trans (sg_deg s ψ)
    have dyP := totalDegree_mul y ((l.map fun ψ => sg s (val p ψ)).prod)
    have e : y * (1 - sg s (val p ψ) * (l.map fun ψ => sg s (val p ψ)).prod) =
        y * (1 - (l.map fun ψ => sg s (val p ψ)).prod) +
          (y * (l.map fun ψ => sg s (val p ψ)).prod) * (1 - sg s (val p ψ)) := by ring
    rw [e]
    refine add_mem (ih (by omega) (fun χ hχ => hsm χ (List.mem_cons_of_mem _ hχ))
      (fun hm => hcb (List.mem_cons_of_mem _ hm))) ?_
    by_cases e' : ψ = ψs
    · refine cd_of_cube h2 ((totalDegree_mul _ _).trans (by omega)) fun a => ?_
      rw [C1.indPt_eq, map_mul, map_mul, map_sub, map_one]
      have := hcb (by rw [e']; exact List.mem_cons_self) (fun i => decide (i ∈ a))
      rw [← e'] at this
      linear_combination
        (eval (boolPt (F := ZMod p) fun i => decide (i ∈ a))
          ((l.map fun ψ => sg s (val p ψ)).prod)) * this
    · exact cd_mul (hsm ψ List.mem_cons_self e') (by omega)

/-- **Gate rule with many premises.**  The conclusion `L'` contains the product term of the gate;
the premise for the member `ψ` consists of terms of `L'` and terms of `ψ`.  All premises except
the pivot are refuted in degree `D₀`, the pivot in degree `D'`. -/
theorem gate_core {Φ : CNF} {L' : PLine p} {d D₀ D' : ℕ} (hd1 : 1 ≤ d) (s : Bool) (l : List Fm)
    (ψs : Fm) (Lψ : Fm → PLine p) (hsum : (l.map (pd p)).sum ≤ d)
    (hu : (l.map fun ψ => sg s (val p ψ)).prod ∈ L')
    (hL : ∀ ψ ∈ l, ∀ g ∈ Lψ ψ, g ∈ L' ∨ g ∈ trL p s ψ)
    (hD : D₀ + d ≤ D') (h3 : 3 * d ≤ D')
    (hsmall : ∀ ψ ∈ l, ψ ≠ ψs → Ref Φ (Lψ ψ) D₀) (hbig : ψs ∈ l → Ref Φ (Lψ ψs) D') :
    Ref Φ L' D' := by
  have hpdψ : ∀ ψ ∈ l, pd p ψ ≤ d := fun ψ hψ =>
    (le_sum_of_mem (List.mem_map.2 ⟨ψ, hψ, rfl⟩)).trans hsum
  have hterm : ∀ ψ ∈ l, ∀ g ∈ trL p s ψ, g.totalDegree ≤ d ∧ ∀ a : Assignment,
      eval (boolPt (F := ZMod p) a) g *
        (1 - eval (boolPt (F := ZMod p) a) (sg s (val p ψ))) = 0 := fun ψ hψ g hg =>
    ⟨((deg_tr hg).trans (td_le_pd ψ s)).trans (hpdψ ψ hψ), tr_imp hg⟩
  have h1 : ∀ ψ ∈ l, ψ ≠ ψs →
      1 - sg s (val p ψ) ∈ CD (cnfAx Φ ∪ (↑L' : Set (PP p))) D' := fun ψ hψ hne =>
    ded_line hd1 (sg_cube s ψ) ((sg_deg s ψ).trans (hpdψ ψ hψ))
      (fun g hg => (hL ψ hψ g hg).imp id (hterm ψ hψ g)) hD h3 (hsmall ψ hψ hne)
  have du : ((l.map fun ψ => sg s (val p ψ)).prod).totalDegree ≤ d :=
    (deg_list_prod l _ _ (fun χ _ => sg_deg s χ)).trans hsum
  have hu' := ax_mem (Φ := Φ) (D := D') hu (du.trans (by omega))
  by_cases hm : ψs ∈ l
  · refine ref_of_derive' le_rfl (fun g hg hgd => ?_) (hbig hm)
    rcases hL ψs hm g hg with h' | h'
    · exact ax_mem h' hgd
    · obtain ⟨hgd', hc⟩ := hterm ψs hm g h'
      have e : g = g * (1 - (l.map fun ψ => sg s (val p ψ)).prod) +
          g * (l.map fun ψ => sg s (val p ψ)).prod := by ring
      rw [e]
      exact add_mem (gate_absorb s ψs hgd' (by omega) (by omega) l hsum h1 (fun _ => hc))
        (cd_mul hu' (by omega))
  · have := gate_absorb (A := cnfAx Φ ∪ (↑L' : Set (PP p))) (E := D') s ψs (y := 1) (d := d)
      (by simp) (by omega) (by omega) l hsum h1 (fun h => absurd h hm)
    rw [one_mul] at this
    have h4 := add_mem this hu'
    unfold Ref
    rwa [sub_add_cancel] at h4

/-! ## One step of the sequent calculus -/

/-- **Step lemma.**  `S` follows from `prev` by a rule of the pinned calculus, all sequents in
`DegS p d`.  If every premise is refuted in degree `D'` and every premise except the pivot `Ts` in
degree `D₀ ≤ D' - d`, then `S` is refuted in degree `D'`. -/
theorem step_ref {F : CNF} {d w D₀ D' : ℕ} (hd1 : 1 ≤ d) (hw : ∀ C ∈ F, C.card ≤ w)
    (hwD : w ≤ D') (hD : D₀ + d ≤ D') (h3 : 3 * d ≤ D')
    {prev : List Seq} {S : Seq} (hstep : FStep p F prev S) (hdS : DegS p d S)
    (hdT : ∀ T ∈ prev, DegS p d T) (Ts : Seq)
    (hbig : ∀ T ∈ prev, Ref F (trS p T) D')
    (hsmall : ∀ T ∈ prev, T ≠ Ts → Ref F (trS p T) D₀) : Ref F (trS p S) D' := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have h2 : 2 ≤ D' := by omega
  have hsat : ∀ {S' : Seq}, FStep p (∅ : CNF) [] S' → ∀ a : Assignment, SeqSat p a S' :=
    fun hS' a => fstep_sound hp0 (F := ∅) (a := a) (fun C hC => by simp at hC)
      (prev := []) (fun T hT => by simp at hT) hS'
  have hsubref : ∀ T ∈ prev, trS p T ⊆ trS p S → Ref F (trS p S) D' := fun T hT hsub =>
    ref_of_derive' le_rfl (fun g hg hgd => ax_mem (hsub hg) hgd) (hbig T hT)
  rcases hstep with ⟨C, hC, rfl⟩ | ⟨φ, rfl⟩ | rfl | rfl | rfl | ⟨r, hr, rfl⟩ | ⟨r, φ, l, rfl⟩ |
      ⟨r, φ, l, rfl⟩ | ⟨r, φ, l, rfl⟩ | ⟨r, φ, l, rfl⟩ | ⟨T, hT, h1, h2'⟩ | ⟨φ, h1, h2'⟩ |
      ⟨φ, Γ, Δ, rfl, h1⟩ | ⟨φ, Γ, Δ, rfl, h1⟩ | ⟨l, Γ, Δ, φ, hφ, rfl, h1⟩ | ⟨l, Γ, Δ, rfl, h1⟩ |
      ⟨l, Γ, Δ, rfl, h1⟩ | ⟨l, Γ, Δ, φ, hφ, rfl, h1⟩
  · -- clause axiom
    have hsub : (C.image litInd : PLine p) ⊆ trS p ([], [clauseFm C]) := by
      intro g hg
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hg
      refine mem_trS.2 (Or.inr ⟨clauseFm C, by simp, ?_⟩)
      exact (mem_trL_or_true _ _).2 ⟨litFm l, List.mem_map.2 ⟨l, Finset.mem_toList.2 hl, rfl⟩,
        litInd_mem l⟩
    exact ref_of_derive' le_rfl (fun g hg hgd => ax_mem (hsub hg) hgd)
      (ref_init hC ((hw C hC).trans hwD) (by omega))
  · -- φ ⊢ φ
    refine valid_ref (hsat (Or.inr (Or.inl ⟨φ, rfl⟩))) ?_ (by simp) h3 h2
    intro ψ hψ
    have e : ψ = φ := by simpa using hψ
    subst e
    obtain ⟨s, hs, -⟩ := tr_single (p := p) ψ
    rw [← hs]
    cases s
    · exact hdS.1 ψ (by simp)
    · exact hdS.2 ψ (by simp)
  · -- ⊢ AND()
    refine valid_ref (hsat (Or.inr (Or.inr (Or.inl rfl)))) ?_ (by simp) h3 h2
    intro ψ hψ
    have e : ψ = .and [] := by simpa using hψ
    subst e; rw [pd_and]; simp
  · -- OR() ⊢
    refine valid_ref (hsat (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) ?_ (by simp) h3 h2
    intro ψ hψ
    have e : ψ = .or [] := by simpa using hψ
    subst e; rw [pd_or]; simp
  · -- ⊢ MOD_0()
    refine valid_ref (hsat (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) ?_ (by simp) h3 h2
    intro ψ hψ
    have e : ψ = .mod 0 [] := by simpa using hψ
    subst e; rw [pd_mod]; simp
  · -- MOD_r() ⊢
    refine valid_ref (hsat (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, rfl⟩)))))))
      ?_ (by simp) h3 h2
    intro ψ hψ
    have e : ψ = .mod r [] := by simpa using hψ
    subst e; rw [pd_mod]; simp
  · -- MOD axiom 1
    refine valid_ref (hsat (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨r, φ, l, rfl⟩)))))))) ?_ (by simp) h3 h2
    have hA : pd p (.mod r (φ :: l)) ≤ d := by
      have := hdS.1 (.mod r (φ :: l)) (by simp); rwa [td_mod] at this
    have hB : pd p (.mod (r + p - 1) l) ≤ d := by
      have := hdS.2 (.mod (r + p - 1) l) (by simp); rwa [td_mod] at this
    intro ψ hψ
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      at hψ
    rcases hψ with rfl | rfl | rfl
    · exact hA
    · exact (pd_le_mod (r := r) (l := ψ :: l) (by simp)).trans hA
    · exact hB
  · -- MOD axiom 2
    refine valid_ref (hsat (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨r, φ, l, rfl⟩))))))))) ?_ (by simp) h3 h2
    have hA : pd p (.mod r (φ :: l)) ≤ d := by
      have := hdS.1 (.mod r (φ :: l)) (by simp); rwa [td_mod] at this
    have hB : pd p (.mod r l) ≤ d := by
      have := hdS.2 (.mod r l) (by simp); rwa [td_mod] at this
    intro ψ hψ
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      at hψ
    rcases hψ with rfl | rfl | rfl
    · exact hA
    · exact (pd_le_mod (r := r) (l := ψ :: l) (by simp)).trans hA
    · exact hB
  · -- MOD axiom 3
    refine valid_ref (hsat (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨r, φ, l, rfl⟩)))))))))) ?_ (by simp) h3 h2
    have hA : pd p (.mod r (φ :: l)) ≤ d := by
      have := hdS.2 (.mod r (φ :: l)) (by simp); rwa [td_mod] at this
    have hB : pd p (.mod (r + p - 1) l) ≤ d := by
      have := hdS.1 (.mod (r + p - 1) l) (by simp); rwa [td_mod] at this
    intro ψ hψ
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      at hψ
    rcases hψ with rfl | rfl | rfl
    · exact (pd_le_mod (r := r) (l := ψ :: l) (by simp)).trans hA
    · exact hB
    · exact hA
  · -- MOD axiom 4
    refine valid_ref (hsat (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨r, φ, l, rfl⟩))))))))))) ?_ (by simp) h3 h2
    have hA : pd p (.mod r (φ :: l)) ≤ d := by
      have := hdS.2 (.mod r (φ :: l)) (by simp); rwa [td_mod] at this
    have hB : pd p (.mod r l) ≤ d := by
      have := hdS.1 (.mod r l) (by simp); rwa [td_mod] at this
    intro ψ hψ
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      at hψ
    rcases hψ with rfl | rfl | rfl
    · exact hB
    · exact (pd_le_mod (r := r) (l := ψ :: l) (by simp)).trans hA
    · exact hA
  · -- weakening
    refine hsubref T hT fun g hg => ?_
    rcases mem_trS.1 hg with ⟨ψ, hψ, h⟩ | ⟨ψ, hψ, h⟩
    · exact mem_trS.2 (Or.inl ⟨ψ, h1 hψ, h⟩)
    · exact mem_trS.2 (Or.inr ⟨ψ, h2' hψ, h⟩)
  · -- cut
    have hpd : pd p φ ≤ d := by
      obtain ⟨s, hs, -⟩ := tr_single (p := p) φ
      rw [← hs]
      cases s
      · exact (hdT _ h2').1 φ (by simp)
      · exact (hdT _ h1).2 φ (by simp)
    have m1 : ∀ g ∈ trS p (S.1, φ :: S.2), g ∈ trS p S ∨ g ∈ trL p true φ := by
      intro g hg
      rcases mem_trS.1 hg with ⟨ψ, hψ, h⟩ | ⟨ψ, hψ, h⟩
      · exact Or.inl (mem_trS.2 (Or.inl ⟨ψ, hψ, h⟩))
      · rcases List.mem_cons.1 hψ with rfl | hψ'
        · exact Or.inr h
        · exact Or.inl (mem_trS.2 (Or.inr ⟨ψ, hψ', h⟩))
    have m2 : ∀ g ∈ trS p (φ :: S.1, S.2), g ∈ trS p S ∨ g ∈ trL p false φ := by
      intro g hg
      rcases mem_trS.1 hg with ⟨ψ, hψ, h⟩ | ⟨ψ, hψ, h⟩
      · rcases List.mem_cons.1 hψ with rfl | hψ'
        · exact Or.inr h
        · exact Or.inl (mem_trS.2 (Or.inl ⟨ψ, hψ', h⟩))
      · exact Or.inl (mem_trS.2 (Or.inr ⟨ψ, hψ, h⟩))
    have dg : ∀ (s : Bool) (g : PP p), g ∈ trL p s φ → g.totalDegree ≤ d := fun s g hg =>
      ((deg_tr hg).trans (td_le_pd φ s)).trans hpd
    have hne : (S.1, φ :: S.2) ≠ (φ :: S.1, S.2) := by
      intro e
      have := congrArg (fun T : Seq => T.1.length) e
      simp at this
    by_cases e1 : (S.1, φ :: S.2) = Ts
    · -- deduction on the second premise, with the indicator of "φ false"
      have e2 : (φ :: S.1, S.2) ≠ Ts := fun e => hne (e1.trans e.symm)
      refine cut_core hd1 (sg_cube false φ) ((sg_deg false φ).trans hpd) (L₁ := trS p (φ :: S.1, S.2))
        (L₂ := trS p (S.1, φ :: S.2)) ?_ ?_ hD h3 (hsmall _ h2' e2) (hbig _ h1)
      · intro g hg
        exact (m2 g hg).imp id fun h => ⟨dg false g h, tr_imp h⟩
      · intro g hg
        refine (m1 g hg).imp id fun h => ⟨dg true g h, fun a => ?_⟩
        have := tr_excl (s := false) (φ := φ) (g := g) h a
        simpa using this
    · refine cut_core hd1 (sg_cube true φ) ((sg_deg true φ).trans hpd) (L₁ := trS p (S.1, φ :: S.2))
        (L₂ := trS p (φ :: S.1, S.2)) ?_ ?_ hD h3 (hsmall _ h1 e1) (hbig _ h2')
      · intro g hg
        exact (m1 g hg).imp id fun h => ⟨dg true g h, tr_imp h⟩
      · intro g hg
        refine (m2 g hg).imp id fun h => ⟨dg false g h, fun a => ?_⟩
        have := tr_excl (s := true) (φ := φ) (g := g) h a
        simpa using this
  · -- NOT left
    refine hsubref _ h1 fun g hg => ?_
    rcases mem_trS.1 hg with ⟨ψ, hψ, h⟩ | ⟨ψ, hψ, h⟩
    · exact mem_trS.2 (Or.inl ⟨ψ, List.mem_cons_of_mem _ hψ, h⟩)
    · rcases List.mem_cons.1 hψ with rfl | hψ'
      · exact mem_trS.2 (Or.inl ⟨.neg ψ, List.mem_cons_self, by rw [trL_neg]; exact h⟩)
      · exact mem_trS.2 (Or.inr ⟨ψ, hψ', h⟩)
  · -- NOT right
    refine hsubref _ h1 fun g hg => ?_
    rcases mem_trS.1 hg with ⟨ψ, hψ, h⟩ | ⟨ψ, hψ, h⟩
    · rcases List.mem_cons.1 hψ with rfl | hψ'
      · exact mem_trS.2 (Or.inr ⟨.neg ψ, List.mem_cons_self, by rw [trL_neg]; exact h⟩)
      · exact mem_trS.2 (Or.inl ⟨ψ, hψ', h⟩)
    · exact mem_trS.2 (Or.inr ⟨ψ, List.mem_cons_of_mem _ hψ, h⟩)
  · -- AND left
    refine hsubref _ h1 fun g hg => ?_
    rcases mem_trS.1 hg with ⟨ψ, hψ, h⟩ | ⟨ψ, hψ, h⟩
    · rcases List.mem_cons.1 hψ with rfl | hψ'
      · exact mem_trS.2 (Or.inl ⟨.and l, List.mem_cons_self,
          (mem_trL_and_false l g).2 ⟨ψ, hφ, h⟩⟩)
      · exact mem_trS.2 (Or.inl ⟨ψ, List.mem_cons_of_mem _ hψ', h⟩)
    · exact mem_trS.2 (Or.inr ⟨ψ, hψ, h⟩)
  · -- AND right
    have hsum : (l.map (pd p)).sum ≤ d := by
      have := hdS.2 (.and l) (by simp)
      rwa [td_and_true, pd_and] at this
    refine gate_core hd1 true l (Ts.2.headD (.var 0)) (fun ψ => trS p (Γ, ψ :: Δ)) hsum ?_ ?_ hD
      h3 (fun ψ hψ hne => hsmall _ (h1 ψ hψ) (fun e => hne (by rw [← e]; rfl)))
      (fun hm => hbig _ (h1 _ hm))
    · refine mem_trS.2 (Or.inr ⟨.and l, List.mem_cons_self, ?_⟩)
      rw [trL_and_true, val_and]
      have e : (l.map fun ψ => sg true (val p ψ)) = l.map (val p) :=
        List.map_congr_left fun ψ _ => by simp [sg]
      rw [e]; simp
    · intro ψ hψ g hg
      rcases mem_trS.1 hg with ⟨χ, hχ, h⟩ | ⟨χ, hχ, h⟩
      · exact Or.inl (mem_trS.2 (Or.inl ⟨χ, hχ, h⟩))
      · rcases List.mem_cons.1 hχ with rfl | hχ'
        · exact Or.inr h
        · exact Or.inl (mem_trS.2 (Or.inr ⟨χ, List.mem_cons_of_mem _ hχ', h⟩))
  · -- OR left
    have hsum : (l.map (pd p)).sum ≤ d := by
      have := hdS.1 (.or l) (by simp)
      rwa [td_or_false, pd_or] at this
    refine gate_core hd1 false l (Ts.1.headD (.var 0)) (fun ψ => trS p (ψ :: Γ, Δ)) hsum ?_ ?_ hD
      h3 (fun ψ hψ hne => hsmall _ (h1 ψ hψ) (fun e => hne (by rw [← e]; rfl)))
      (fun hm => hbig _ (h1 _ hm))
    · refine mem_trS.2 (Or.inl ⟨.or l, List.mem_cons_self, ?_⟩)
      rw [trL_or_false, val_or]
      have e : (l.map fun ψ => sg false (val p ψ)) = l.map (fun ψ => 1 - val p ψ) :=
        List.map_congr_left fun ψ _ => by simp [sg]
      rw [e, sub_sub_cancel]; simp
    · intro ψ hψ g hg
      rcases mem_trS.1 hg with ⟨χ, hχ, h⟩ | ⟨χ, hχ, h⟩
      · rcases List.mem_cons.1 hχ with rfl | hχ'
        · exact Or.inr h
        · exact Or.inl (mem_trS.2 (Or.inl ⟨χ, List.mem_cons_of_mem _ hχ', h⟩))
      · exact Or.inl (mem_trS.2 (Or.inr ⟨χ, hχ, h⟩))
  · -- OR right
    refine hsubref _ h1 fun g hg => ?_
    rcases mem_trS.1 hg with ⟨ψ, hψ, h⟩ | ⟨ψ, hψ, h⟩
    · exact mem_trS.2 (Or.inl ⟨ψ, hψ, h⟩)
    · rcases List.mem_cons.1 hψ with rfl | hψ'
      · exact mem_trS.2 (Or.inr ⟨.or l, List.mem_cons_self,
          (mem_trL_or_true l g).2 ⟨ψ, hφ, h⟩⟩)
      · exact mem_trS.2 (Or.inr ⟨ψ, List.mem_cons_of_mem _ hψ', h⟩)

/-! ## Tree-like proofs -/

/-- Tree-like derivations in the pinned sequent calculus.  One node: the sequent `S` follows by
`FStep p F prev S` from the sequents of the list `prev`, each with its own subtree of `sz T` nodes.
`P` holds for every sequent of the tree.  The last index is the number of nodes. -/
inductive TProof (p : ℕ) (F : CNF) (P : Seq → Prop) : Seq → ℕ → Prop
  | node {S : Seq} (prev : List Seq) (sz : Seq → ℕ)
      (hprev : ∀ T ∈ prev, TProof p F P T (sz T)) (hstep : FStep p F prev S) (hP : P S) :
      TProof p F P S ((prev.map sz).sum + 1)

theorem TProof.pos {F : CNF} {P : Seq → Prop} {S : Seq} {s : ℕ} (h : TProof p F P S s) :
    1 ≤ s := by
  cases h; omega

theorem TProof.prop {F : CNF} {P : Seq → Prop} {S : Seq} {s : ℕ} (h : TProof p F P S s) :
    P S := by
  cases h with
  | node _ _ _ _ hP => exact hP

theorem two_le_sum {α : Type} (f : α → ℕ) : ∀ (l : List α) {x y : α}, x ∈ l → y ∈ l → x ≠ y →
    f x + f y ≤ (l.map f).sum
  | [], _, _, hx, _, _ => by simp at hx
  | a :: l, x, y, hx, hy, hne => by
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hx with hxa | hx'
    · rcases List.mem_cons.1 hy with hya | hy'
      · exact absurd (hxa.trans hya.symm) hne
      · have := le_sum_of_mem (List.mem_map.2 ⟨y, hy', rfl⟩ : f y ∈ l.map f)
        rw [hxa]; omega
    · rcases List.mem_cons.1 hy with hya | hy'
      · have := le_sum_of_mem (List.mem_map.2 ⟨x, hx', rfl⟩ : f x ∈ l.map f)
        rw [hya]; omega
      · have := two_le_sum f l hx' hy' hne
        omega

/-- A pivot: every other member of the list has at most half of the total. -/
theorem exists_pivot (prev : List Seq) (sz : Seq → ℕ) :
    ∃ Ts : Seq, ∀ T ∈ prev, T ≠ Ts → 2 * sz T ≤ (prev.map sz).sum := by
  by_cases hne : prev.toFinset.Nonempty
  · obtain ⟨Ts, hTs, hmax⟩ := prev.toFinset.exists_max_image sz hne
    refine ⟨Ts, fun T hT hTne => ?_⟩
    have h1 := two_le_sum sz prev hT (List.mem_toFinset.1 hTs) hTne
    have h2 := hmax T (List.mem_toFinset.2 hT)
    omega
  · refine ⟨([], []), fun T hT _ => ?_⟩
    exact absurd ⟨T, List.mem_toFinset.2 hT⟩ hne

/-- **Degree of a sequent tree.** -/
theorem tproof_ref {F : CNF} {d w c : ℕ} (hd1 : 1 ≤ d) (hw : ∀ C ∈ F, C.card ≤ w)
    (hwc : w ≤ c) (hdc : 3 * d ≤ c) {S : Seq} {s : ℕ} (h : TProof p F (DegS p d) S s) :
    ∀ k, s ≤ 2 ^ k → Ref F (trS p S) (d * k + c) := by
  induction h with
  | @node S prev sz hprev hstep hP ih =>
    intro k hk
    have hszle : ∀ T ∈ prev, sz T ≤ (prev.map sz).sum := fun T hT =>
      le_sum_of_mem (List.mem_map.2 ⟨T, hT, rfl⟩)
    have hbig : ∀ T ∈ prev, Ref F (trS p T) (d * k + c) := fun T hT =>
      ih T hT k (by have := hszle T hT; omega)
    have hdT : ∀ T ∈ prev, DegS p d T := fun T hT => (hprev T hT).prop
    have hck : c ≤ d * k + c := Nat.le_add_left _ _
    cases k with
    | zero =>
      have hemp : ∀ T ∈ prev, False := fun T hT => by
        have := (hprev T hT).pos
        have := hszle T hT
        simp at hk
        omega
      exact step_ref hd1 hw (by omega) (D₀ := 0) (by omega) (by omega) hstep hP hdT S hbig
        (fun T hT _ => (hemp T hT).elim)
    | succ k =>
      obtain ⟨Ts, hTs⟩ := exists_pivot prev sz
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      have e : d * (k + 1) + c = d * k + c + d := by ring
      have hck' : c ≤ d * k + c := Nat.le_add_left _ _
      exact step_ref hd1 hw (by omega) (D₀ := d * k + c) (by omega) (by omega) hstep hP hdT Ts
        hbig (fun T hT hne => ih T hT k (by have := hTs T hT hne; omega))

/-- **Tree-like degree-size relation for the pinned sequent calculus.**  A tree-like refutation
with at most `2^k` nodes, all sequents in `DegS p d`, of a CNF of width at most `w`, gives a
polynomial calculus refutation over `F_p` of degree `d k + max w (3 d)`.  No bound on the depth of
the formulas and no bound on `d`. -/
theorem tree_frege_pc_degree {F : CNF} {d w : ℕ} (hd1 : 1 ≤ d) (hw : ∀ C ∈ F, C.card ≤ w)
    {s : ℕ} (h : TProof p F (DegS p d) ([], []) s) {k : ℕ} (hk : s ≤ 2 ^ k) :
    PCD (cnfAx (F := ZMod p) F) (d * k + max w (3 * d)) 1 := by
  have h1 := tproof_ref hd1 hw (le_max_left _ _) (le_max_right _ _) h k hk
  unfold Ref at h1
  rw [trS_empty, Finset.coe_empty, Set.union_empty] at h1
  rcases h1 with h0 | h1
  · exact absurd h0 one_ne_zero
  · exact h1

/-- **Size from degree** for tree-like refutations in the sequent calculus. -/
theorem tree_frege_size_of_degree {F : CNF} {d w D0 : ℕ} (hd1 : 1 ≤ d)
    (hw : ∀ C ∈ F, C.card ≤ w) (hno : ¬ PCD (cnfAx (F := ZMod p) F) D0 1) {s : ℕ}
    (h : TProof p F (DegS p d) ([], []) s) : 2 ^ ((D0 - max w (3 * d)) / d) ≤ s := by
  by_contra hlt
  push Not at hlt
  have hpc := tree_frege_pc_degree hd1 hw h hlt.le
  generalize max w (3 * d) = c at hlt hpc
  by_cases hc : c ≤ D0
  · refine hno (pcd_mono ?_ hpc)
    have := Nat.mul_div_le (D0 - c) d
    omega
  · have e : D0 - c = 0 := by omega
    rw [e, Nat.zero_div, pow_zero] at hlt
    have := h.pos
    omega

end

end FTree
