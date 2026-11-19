import Theory.ProofComplexity.FregeDegBridge
import Theory.ProofComplexity.ReviewNonvacuity

/-!
# Tree-like `PIC`: the degree-size relation without a degree wall

For the polynomial indicator calculus `PIC` of `PolyIndCalc.lean` (lines are finite sets of `0/1`
valued polynomials over `F_p` of degree at most `d`, rules: clause axioms, excluded middle,
weakening, the semantic rule with one or two premises), a tree-like refutation with `s` nodes gives
a polynomial calculus refutation of degree at most `d * log2 s + max w (3 d)`, `w` the clause width.

Proof (Section 5.2 of `docs/ladder/rungs/r4-wideand-fable-report.md`).  For a line `L` let
`Ref Φ L D` say: polynomial calculus refutes, in degree `D`, the clauses of `Φ` together with the
equations `g = 0` for the terms `g` of `L`.  Weakening and the one premise rule do not raise the
degree above `max D (2 d)`.  At a two premise step the refutation below one premise `L₁` is
multiplied by `1 - g₁` (deduction, cost `d`), which derives `1 - g₁`; then
`g₂ = g₂ (1 - g₁) + g₁ g₂ (1 - g₃) + g₁ g₂ g₃` is derived in degree `3 d` and the refutation below
the other premise applies unchanged.  Deducting on the smaller subtree gives the logarithm.  This is
the tree-like size-width argument of Ben-Sasson and Wigderson with degree in place of width; known
mathematics, no novelty is claimed.

Main statements (namespace `PICT`):

* `TDer Φ V d L s`: tree-like derivations of the line `L` with `s` nodes, same rules as
  `PIC.PInfer`, all terms indicators of degree at most `d` over `V`.
* `tree_pc_degree`, `tree_pc_degree_clog`: the degree bound.
* `tree_size_of_degree`: `2 ^ ((D0 - max w (3 d)) / d) ≤ s` if degree `D0` does not refute.
* `tder_to_prefutation`: a tree-like refutation is a `PIC.PRefutation` of no larger size.
* `tder_of_unsat`: every unsatisfiable CNF over `V` has a tree-like refutation at every `d ≥ 1`.
* `pic_tree_tseitin_idx`, `pic_tree_main_idx`: Tseitin mod `q` on `cubFam m` over `F_p`, `p ∤ q`:
  every tree-like refutation with terms of degree `d ≤ n^(1-δ)` has at least `2^(n^δ / (2624 q))`
  nodes, `n = 8 m^2`, all `m ≥ m0`; the instance is unsatisfiable and has tree-like refutations.

LOG: R4 treedeg fable session, tree-like degree-size relation for PIC
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.PCL MvPolynomial PIC

namespace PICT

noncomputable section
open Classical Pang

variable {p : ℕ} [Fact p.Prime]

/-! ## General lemmas on `C_D` -/

/-- `C_D` is monotone in the axioms and in the degree. -/
theorem cd_mono {Ax Ax' : Set (PP p)} {D D' : ℕ} (hA : Ax ⊆ Ax') (hD : D ≤ D') {f : PP p}
    (h : f ∈ CD Ax D) : f ∈ CD Ax' D' := by
  rcases h with rfl | h
  · exact zero_mem _
  · refine mem_CD_of_pcd ?_
    induction h with
    | ax hf hd => exact PCD.ax (hA hf) (hd.trans hD)
    | bool i h2 => exact PCD.bool i (h2.trans hD)
    | lin a b _ _ ihf ihg => exact PCD.lin a b ihf ihg
    | mul i _ hd ih => exact PCD.mul i ih (hd.trans hD)

/-- Axioms may be replaced by derived polynomials. -/
theorem cd_subst {Ax Ax' : Set (PP p)} {D D' : ℕ} (hD : D ≤ D')
    (hA : ∀ f ∈ Ax, f.totalDegree ≤ D → f ∈ CD Ax' D') {f : PP p} (h : f ∈ CD Ax D) :
    f ∈ CD Ax' D' := by
  rcases h with rfl | h
  · exact zero_mem _
  · induction h with
    | ax hf hd => exact hA _ hf hd
    | bool i h2 => exact mem_CD_of_pcd (PCD.bool i (h2.trans hD))
    | lin a b _ _ ihf ihg =>
      have := (CD Ax' D').add_mem ((CD Ax' D').smul_mem a ihf) ((CD Ax' D').smul_mem b ihg)
      simpa [smul_eq_C_mul] using this
    | mul i _ hd ih => exact cd_X_mul ih i (hd.trans hD)

/-- **Deduction.**  If `f` is derived in degree `D` from `Ax` and the extra axiom `h`, a `0/1`
valued polynomial of degree at most `d`, then `(1 - h) f` is derived from `Ax` in degree `D + d`. -/
theorem cd_deduct {Ax : Set (PP p)} {D D' d : ℕ} {h : PP p}
    (hcube : ∀ a : Set ℕ, eval (indPt a) h = 0 ∨ eval (indPt a) h = 1)
    (hd : h.totalDegree ≤ d) (hD' : D + d ≤ D') (h2 : 2 ≤ D') {f : PP p}
    (hf : f ∈ CD (insert h Ax) D) : (1 - h) * f ∈ CD Ax D' := by
  have h1 : (1 - h).totalDegree ≤ d := (FDeg.deg_one_sub h).trans hd
  rcases hf with rfl | hf
  · simp
  · induction hf with
    | @ax f hf hdf =>
      rcases hf with hf | hf
      · rw [hf]
        refine cd_of_cube h2 ((totalDegree_mul _ _).trans ?_) fun a => ?_
        · rw [hf] at hdf; omega
        · rw [map_mul, map_sub, map_one]
          rcases hcube a with e | e <;> rw [e] <;> simp
      · exact cd_mul (mem_CD_of_pcd (PCD.ax hf (hdf.trans (by omega)))) (by omega)
    | bool i h2' => exact cd_bool_mul h2 i (by omega)
    | @lin f g a b _ _ ihf ihg =>
      have := (CD Ax D').add_mem ((CD Ax D').smul_mem a ihf) ((CD Ax D').smul_mem b ihg)
      have e : (1 - h) * (C a * f + C b * g) = a • ((1 - h) * f) + b • ((1 - h) * g) := by
        simp only [smul_eq_C_mul]; ring
      rw [e]; exact this
    | @mul f i _ hdf ih =>
      have e : (1 - h) * (X i * f) = X i * ((1 - h) * f) := by ring
      rw [e]
      refine cd_X_mul ih i ?_
      rw [← e]
      exact (totalDegree_mul _ _).trans (by omega)

/-! ## The measure -/

/-- Degree `D` polynomial calculus refutes `Φ` together with "every term of `L` is zero". -/
def Ref (Φ : CNF) (L : PLine p) (D : ℕ) : Prop :=
  (1 : PP p) ∈ CD (cnfAx Φ ∪ (↑L : Set (PP p))) D

theorem ax_mem {Φ : CNF} {L : PLine p} {D : ℕ} {g : PP p} (hg : g ∈ L) (hd : g.totalDegree ≤ D) :
    g ∈ CD (cnfAx Φ ∪ (↑L : Set (PP p))) D :=
  mem_CD_of_pcd (PCD.ax (Or.inr (Finset.mem_coe.2 hg)) hd)

theorem deg_litInd (l : Literal) : (litInd l : PP p).totalDegree ≤ 1 := by
  unfold litInd
  exact (FDeg.deg_one_sub _).trans (C1.totalDegree_litPoly l)

theorem deg_prod_lit (s : Finset Literal) : (∏ l ∈ s, (litPoly l : PP p)).totalDegree ≤ s.card := by
  refine (totalDegree_finset_prod _ _).trans ?_
  calc ∑ l ∈ s, (litPoly l : PP p).totalDegree ≤ ∑ _l ∈ s, 1 :=
        Finset.sum_le_sum fun l _ => C1.totalDegree_litPoly l
    _ = s.card := by simp

/-- Clause axiom: the line of a clause of `Φ` is refuted in degree `|C|`. -/
theorem ref_init {Φ : CNF} {C : Clause} (hC : C ∈ Φ) {D : ℕ} (hw : C.card ≤ D) (h1 : 1 ≤ D) :
    Ref (p := p) Φ (C.image litInd) D := by
  unfold Ref
  set A : Set (PP p) := cnfAx Φ ∪ (↑(C.image (litInd (p := p))) : Set (PP p)) with hA
  have key : ∀ s : Finset Literal, s ⊆ C → (∏ l ∈ s, (litPoly l : PP p)) - 1 ∈ CD A D := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hsub
      have hs : s ⊆ C := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have haC : a ∈ C := hsub (Finset.mem_insert_self _ _)
      have hcard : s.card + 1 ≤ C.card := by
        have := Finset.card_le_card hsub
        rwa [Finset.card_insert_of_notMem ha] at this
      rw [Finset.prod_insert ha]
      have e : (litPoly a : PP p) * ∏ l ∈ s, (litPoly l : PP p) - 1 =
          litPoly a * (∏ l ∈ s, (litPoly l : PP p) - 1) + -(litInd a : PP p) := by
        unfold litInd; ring
      rw [e]
      refine add_mem (cd_mul (ih hs) ?_) (neg_mem ?_)
      · have d1 := C1.totalDegree_litPoly (p := p) a
        have d2 : (∏ l ∈ s, (litPoly l : PP p) - 1).totalDegree ≤ s.card :=
          (totalDegree_sub _ _).trans (max_le (deg_prod_lit s) (by simp))
        omega
      · exact mem_CD_of_pcd (PCD.ax (Or.inr (Finset.mem_coe.2 (Finset.mem_image_of_mem _ haC)))
          ((deg_litInd a).trans h1))
  have hax : (clausePoly C : PP p) ∈ CD A D :=
    mem_CD_of_pcd (PCD.ax (Or.inl ⟨C, hC, rfl⟩) ((deg_prod_lit C).trans hw))
  have := sub_mem hax (key C subset_rfl)
  have e : (clausePoly C : PP p) - (∏ l ∈ C, (litPoly l : PP p) - 1) = 1 := by
    unfold clausePoly; ring
  rwa [e] at this

/-- Excluded middle. -/
theorem ref_taut {Φ : CNF} (g : PP p) {D : ℕ} (hg : g.totalDegree ≤ D) :
    Ref Φ ({g, 1 - g} : PLine p) D := by
  have a1 : g ∈ CD (cnfAx Φ ∪ (↑({g, 1 - g} : PLine p) : Set (PP p))) D := ax_mem (by simp) hg
  have a2 : 1 - g ∈ CD (cnfAx Φ ∪ (↑({g, 1 - g} : PLine p) : Set (PP p))) D :=
    ax_mem (by simp) ((FDeg.deg_one_sub g).trans hg)
  have h := add_mem a1 a2
  rwa [show g + (1 - g) = (1 : PP p) by ring] at h

/-- If every term of `L₁` is derived from `Φ` and `L'`, a refutation below `L₁` gives one below
`L'`, of no larger degree. -/
theorem ref_of_derive {Φ : CNF} {L₁ L' : PLine p} {D₁ D' : ℕ} (hD : D₁ ≤ D')
    (h : ∀ g ∈ L₁, g ∈ CD (cnfAx Φ ∪ (↑L' : Set (PP p))) D') (h1 : Ref Φ L₁ D₁) :
    Ref Φ L' D' := by
  refine cd_subst hD ?_ h1
  rintro f (hf | hf) hd
  · exact mem_CD_of_pcd (PCD.ax (Or.inl hf) (hd.trans hD))
  · exact h f (Finset.mem_coe.1 hf)

theorem g3_props {Φ : CNF} {V : Finset ℕ} {d D' : ℕ} {L' : PLine p} {g₃ : PP p}
    (h₃ : g₃ ∈ L' ∨ g₃ = 0) (hg' : ∀ g ∈ L', Ind V d g) (hdD : d ≤ D') :
    g₃.totalDegree ≤ d ∧ g₃ ∈ CD (cnfAx Φ ∪ (↑L' : Set (PP p))) D' := by
  rcases h₃ with h | rfl
  · exact ⟨(hg' _ h).deg, ax_mem h ((hg' _ h).deg.trans hdD)⟩
  · exact ⟨by simp, zero_mem _⟩

/-- The semantic rule with one premise. -/
theorem ref_sem1 {Φ : CNF} {V : Finset ℕ} {d : ℕ} {L₁ L' : PLine p} {g₁ g₃ : PP p}
    (h₁ : g₁ ∈ L₁)
    (hs : ∀ a : Assignment, eval (boolPt (F := ZMod p) a) g₁ *
      (1 - eval (boolPt (F := ZMod p) a) g₃) = 0)
    (hL' : L₁.erase g₁ ⊆ L') (h₃ : g₃ ∈ L' ∨ g₃ = 0)
    (hg1 : ∀ g ∈ L₁, Ind V d g) (hg' : ∀ g ∈ L', Ind V d g)
    {D₁ D' : ℕ} (hD : D₁ ≤ D') (h2d : 2 * d ≤ D') (h2 : 2 ≤ D') (hr : Ref Φ L₁ D₁) :
    Ref Φ L' D' := by
  obtain ⟨hd3, hm3⟩ := g3_props (Φ := Φ) h₃ hg' (D' := D') (by omega)
  have hd1 := (hg1 _ h₁).deg
  refine ref_of_derive hD (fun g hg => ?_) hr
  by_cases e : g = g₁
  · subst e
    have e2 : g = g * (1 - g₃) + g * g₃ := by ring
    rw [e2]
    refine add_mem (cd_of_cube h2 ?_ fun a => ?_) (cd_mul hm3 (by omega))
    · have := FDeg.deg_one_sub g₃
      exact (totalDegree_mul _ _).trans (by omega)
    · rw [C1.indPt_eq, map_mul, map_sub, map_one]; exact hs _
  · exact ax_mem (hL' (Finset.mem_erase.2 ⟨e, hg⟩)) ((hg1 _ hg).deg.trans (by omega))

/-- The semantic rule with two premises: deduction on the first premise. -/
theorem ref_sem2 {Φ : CNF} {V : Finset ℕ} {d : ℕ} {L₁ L₂ L' : PLine p} {g₁ g₂ g₃ : PP p}
    (h₁ : g₁ ∈ L₁) (h₂ : g₂ ∈ L₂)
    (hs : ∀ a : Assignment, eval (boolPt (F := ZMod p) a) g₁ * eval (boolPt (F := ZMod p) a) g₂ *
      (1 - eval (boolPt (F := ZMod p) a) g₃) = 0)
    (hL₁ : L₁.erase g₁ ⊆ L') (hL₂ : L₂.erase g₂ ⊆ L') (h₃ : g₃ ∈ L' ∨ g₃ = 0)
    (hg1 : ∀ g ∈ L₁, Ind V d g) (hg2 : ∀ g ∈ L₂, Ind V d g) (hg' : ∀ g ∈ L', Ind V d g)
    {D₁ D₂ D' : ℕ} (hD1 : D₁ + d ≤ D') (hD2 : D₂ ≤ D') (h3d : 3 * d ≤ D') (h2 : 2 ≤ D')
    (hr1 : Ref Φ L₁ D₁) (hr2 : Ref Φ L₂ D₂) : Ref Φ L' D' := by
  obtain ⟨hd3, hm3⟩ := g3_props (Φ := Φ) h₃ hg' (D' := D') (by omega)
  have hd1 := (hg1 _ h₁).deg
  have hd2 := (hg2 _ h₂).deg
  have hsub : cnfAx Φ ∪ (↑L₁ : Set (PP p)) ⊆ insert g₁ (cnfAx Φ ∪ (↑L' : Set (PP p))) := by
    rintro f (hf | hf)
    · exact Or.inr (Or.inl hf)
    · by_cases e : f = g₁
      · exact Or.inl e
      · exact Or.inr (Or.inr (Finset.mem_coe.2 (hL₁ (Finset.mem_erase.2 ⟨e, Finset.mem_coe.1 hf⟩))))
  have ha : (1 : PP p) ∈ CD (insert g₁ (cnfAx Φ ∪ (↑L' : Set (PP p)))) D₁ :=
    cd_mono hsub le_rfl hr1
  have hb := cd_deduct (PIC.cube_set (hg1 _ h₁).cube) hd1 hD1 h2 ha
  rw [mul_one] at hb
  refine ref_of_derive hD2 (fun g hg => ?_) hr2
  by_cases e : g = g₂
  · subst e
    have e2 : g = g * (1 - g₁) + g₁ * g * (1 - g₃) + (g₁ * g) * g₃ := by ring
    rw [e2]
    have t1 := FDeg.deg_one_sub g₁
    have t3 := FDeg.deg_one_sub g₃
    have t12 := totalDegree_mul g₁ g
    refine add_mem (add_mem (cd_mul hb (by omega)) (cd_of_cube h2 ?_ fun a => ?_))
      (cd_mul hm3 (by omega))
    · exact (totalDegree_mul _ _).trans (by omega)
    · rw [C1.indPt_eq, map_mul, map_mul, map_sub, map_one]; exact hs _
  · exact ax_mem (hL₂ (Finset.mem_erase.2 ⟨e, hg⟩)) ((hg2 _ hg).deg.trans (by omega))

/-! ## Tree-like derivations -/

/-- Tree-like derivations in `PIC`: `TDer Φ V d L s` is a derivation tree of the line `L` with `s`
nodes, with the rules of `PIC.PInfer`, every term an indicator of degree at most `d` over `V`. -/
inductive TDer (Φ : CNF) (V : Finset ℕ) (d : ℕ) : PLine p → ℕ → Prop
  | leaf {L : PLine p} (h : PInfer Φ [] L) (hg : ∀ g ∈ L, Ind V d g) : TDer Φ V d L 1
  | un {L₁ L : PLine p} {s : ℕ} (h₁ : TDer Φ V d L₁ s) (h : PInfer Φ [L₁] L)
      (hg : ∀ g ∈ L, Ind V d g) : TDer Φ V d L (s + 1)
  | bin {L₁ L₂ L : PLine p} {s₁ s₂ : ℕ} (h₁ : TDer Φ V d L₁ s₁) (h₂ : TDer Φ V d L₂ s₂)
      (h : PInfer Φ [L₁, L₂] L) (hg : ∀ g ∈ L, Ind V d g) : TDer Φ V d L (s₁ + s₂ + 1)

theorem TDer.good {Φ : CNF} {V : Finset ℕ} {d : ℕ} {L : PLine p} {s : ℕ} (h : TDer Φ V d L s) :
    ∀ g ∈ L, Ind V d g := by
  cases h with
  | leaf _ hg => exact hg
  | un _ _ hg => exact hg
  | bin _ _ _ hg => exact hg

theorem TDer.pos {Φ : CNF} {V : Finset ℕ} {d : ℕ} {L : PLine p} {s : ℕ} (h : TDer Φ V d L s) :
    1 ≤ s := by
  cases h <;> omega

/-- **Degree of a tree.**  A tree with at most `2^k` nodes below `L` gives `Ref Φ L (d k + c)`,
for `c ≥ max w (3 d)`. -/
theorem tder_ref {Φ : CNF} {V : Finset ℕ} {d w c : ℕ} (hd1 : 1 ≤ d)
    (hw : ∀ C ∈ Φ, C.card ≤ w) (hwc : w ≤ c) (hdc : 3 * d ≤ c)
    {L : PLine p} {s : ℕ} (h : TDer Φ V d L s) : ∀ k, s ≤ 2 ^ k → Ref Φ L (d * k + c) := by
  induction h with
  | @leaf L hinf hg =>
    intro k _
    have hck : c ≤ d * k + c := Nat.le_add_left _ _
    cases hinf with
    | init C hC => exact ref_init hC (by have := hw C hC; omega) (by omega)
    | taut g => exact ref_taut g ((hg g (by simp)).deg.trans (by omega))
  | @un L₁ L s h₁ hinf hg ih =>
    intro k hk
    have hck : c ≤ d * k + c := Nat.le_add_left _ _
    have ih' := ih k (by omega)
    cases hinf with
    | weak _ hsub =>
      exact ref_of_derive le_rfl
        (fun g hg1 => ax_mem (hsub hg1) ((h₁.good g hg1).deg.trans (by omega))) ih'
    | sem1 hm hs _ hL' h₃ =>
      exact ref_sem1 hm hs hL' h₃ h₁.good hg le_rfl (by omega) (by omega) ih'
  | @bin L₁ L₂ L s₁ s₂ h₁ h₂ hinf hg ih₁ ih₂ =>
    intro k hk
    have p1 := h₁.pos
    have p2 := h₂.pos
    cases k with
    | zero => simp at hk; omega
    | succ k =>
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      have e : d * (k + 1) + c = d * k + c + d := by ring
      have hck : c ≤ d * k + c := Nat.le_add_left _ _
      cases hinf with
      | sem2 hm1 hm2 hs _ hL₁ hL₂ h₃ =>
        rcases le_total s₁ s₂ with hle | hle
        · exact ref_sem2 hm1 hm2 hs hL₁ hL₂ h₃ h₁.good h₂.good hg (D₁ := d * k + c)
            (by omega) le_rfl (by omega) (by omega) (ih₁ k (by omega)) (ih₂ (k + 1) (by omega))
        · refine ref_sem2 hm2 hm1 (fun a => ?_) hL₂ hL₁ h₃ h₂.good h₁.good hg (D₁ := d * k + c)
            (by omega) le_rfl (by omega) (by omega) (ih₂ k (by omega)) (ih₁ (k + 1) (by omega))
          have := hs a
          rw [mul_comm (eval (boolPt (F := ZMod p) a) _) (eval (boolPt (F := ZMod p) a) _)]
          exact this

/-- **Tree-like degree-size relation for `PIC`.**  A tree-like refutation with at most `2^k` nodes
and terms of degree at most `d`, of a CNF of width at most `w`, gives a polynomial calculus
refutation of degree `d k + max w (3 d)`. -/
theorem tree_pc_degree {Φ : CNF} {V : Finset ℕ} {d w : ℕ} (hd1 : 1 ≤ d)
    (hw : ∀ C ∈ Φ, C.card ≤ w) {s : ℕ} (h : TDer Φ V d (∅ : PLine p) s) {k : ℕ}
    (hk : s ≤ 2 ^ k) : PCD (cnfAx (F := ZMod p) Φ) (d * k + max w (3 * d)) 1 := by
  have h1 := tder_ref hd1 hw (le_max_left _ _) (le_max_right _ _) h k hk
  unfold Ref at h1
  rw [Finset.coe_empty, Set.union_empty] at h1
  rcases h1 with h0 | h1
  · exact absurd h0 one_ne_zero
  · exact h1

/-- The same with the ceiling of the binary logarithm of the number of nodes. -/
theorem tree_pc_degree_clog {Φ : CNF} {V : Finset ℕ} {d w : ℕ} (hd1 : 1 ≤ d)
    (hw : ∀ C ∈ Φ, C.card ≤ w) {s : ℕ} (h : TDer Φ V d (∅ : PLine p) s) :
    PCD (cnfAx (F := ZMod p) Φ) (d * Nat.clog 2 s + max w (3 * d)) 1 :=
  tree_pc_degree hd1 hw h (Nat.le_pow_clog one_lt_two s)

/-- **Size from degree.**  If polynomial calculus of degree `D0` does not refute `Φ`, every
tree-like `PIC` refutation with terms of degree at most `d` has at least
`2 ^ ((D0 - max w (3 d)) / d)` nodes. -/
theorem tree_size_of_degree {Φ : CNF} {V : Finset ℕ} {d w D0 : ℕ} (hd1 : 1 ≤ d)
    (hw : ∀ C ∈ Φ, C.card ≤ w) (hno : ¬ PCD (cnfAx (F := ZMod p) Φ) D0 1) {s : ℕ}
    (h : TDer Φ V d (∅ : PLine p) s) : 2 ^ ((D0 - max w (3 * d)) / d) ≤ s := by
  by_contra hlt
  push Not at hlt
  have hpc := tree_pc_degree hd1 hw h hlt.le
  generalize max w (3 * d) = c at hlt hpc
  by_cases hc : c ≤ D0
  · refine hno (pcd_mono ?_ hpc)
    have := Nat.mul_div_le (D0 - c) d
    omega
  · have e : D0 - c = 0 := by omega
    rw [e, Nat.zero_div, pow_zero] at hlt
    have := h.pos
    omega

/-! ## Tree-like is a special case of dag-like -/

/-- A tree-like derivation is a list derivation with at most as many lines. -/
theorem tder_to_der {Φ : CNF} {V : Finset ℕ} {d : ℕ} {L : PLine p} {s : ℕ}
    (h : TDer Φ V d L s) : ∀ Ls : List (PLine p), FDeg.Der Φ V d Ls →
      ∃ Ls₂, FDeg.Ext Φ V d Ls Ls₂ s ∧ L ∈ Ls₂ := by
  induction h with
  | leaf hinf hg => exact fun Ls hLs => FDeg.reach_step hLs (prems := []) (by simp) hinf hg
  | @un L₁ L s _ hinf hg ih =>
    intro Ls hLs
    obtain ⟨Ls₁, hE₁, hm₁⟩ := ih Ls hLs
    obtain ⟨Ls₂, hE₂, hm₂⟩ := FDeg.reach_step hE₁.1 (prems := [L₁]) (by simpa using hm₁) hinf hg
    exact ⟨Ls₂, hE₁.trans hE₂, hm₂⟩
  | @bin L₁ L₂ L s₁ s₂ _ _ hinf hg ih₁ ih₂ =>
    intro Ls hLs
    obtain ⟨Ls₁, hE₁, hm₁⟩ := ih₁ Ls hLs
    obtain ⟨Ls₂, hE₂, hm₂⟩ := ih₂ Ls₁ hE₁.1
    obtain ⟨Ls₃, hE₃, hm₃⟩ := FDeg.reach_step hE₂.1 (prems := [L₁, L₂])
      (by simpa using ⟨hE₂.2.1 _ hm₁, hm₂⟩) hinf hg
    exact ⟨Ls₃, (hE₁.trans hE₂).trans hE₃, hm₃⟩

/-- A tree-like refutation with `s` nodes is a `PIC` refutation (`PIC.PRefutation`, the dag-like
object of `PolyIndCalc.lean`) with at most `s` nodes. -/
theorem tder_to_prefutation {Φ : CNF} {V : Finset ℕ} {d : ℕ} {s : ℕ}
    (h : TDer Φ V d (∅ : PLine p) s) : ∃ R : PRefutation Φ V d p, R.S ≤ s := by
  obtain ⟨Ls, hE, hm⟩ := tder_to_der h [] FDeg.Der.nil
  obtain ⟨R, hR⟩ := FDeg.der_refutation hE.1 hm
  exact ⟨R, hR.trans (by simpa using hE.2.2)⟩

/-- Soundness of tree-like refutations. -/
theorem TDer.unsat {Φ : CNF} {V : Finset ℕ} {d : ℕ} {s : ℕ}
    (h : TDer Φ V d (∅ : PLine p) s) : ¬ Satisfiable Φ := by
  obtain ⟨R, -⟩ := tder_to_prefutation h
  exact R.unsat

/-! ## Non-vacuity: resolution trees are `PIC` trees -/

theorem ind_litInd {V : Finset ℕ} {d : ℕ} (hd1 : 1 ≤ d) {l : Literal} (hl : l.var ∈ V) :
    Ind V d (litInd l : PP p) := by
  refine FDeg.tr_ind (φ := litFm l) (s := true) ?_ ?_ (FDeg.litInd_mem l)
  · unfold litFm
    split_ifs
    · rw [FDeg.td_var]; exact hd1
    · rw [FDeg.td_neg, FDeg.td_var]; exact hd1
  · unfold litFm
    split_ifs
    · rw [FDeg.fv_var]; simpa using hl
    · rw [FDeg.fv_neg, FDeg.fv_var]; simpa using hl

/-- A resolution derivation of `C` is a tree-like `PIC` derivation of the line of `C`. -/
theorem tder_of_derivation {Φ : CNF} {V : Finset ℕ} {d : ℕ} (hd1 : 1 ≤ d)
    (hV : ∀ C ∈ Φ, ∀ l ∈ C, l.var ∈ V) {C : Clause} (D : Derivation Φ C) :
    (∀ l ∈ C, l.var ∈ V) ∧ ∃ s, TDer (p := p) Φ V d (C.image litInd) s := by
  have good : ∀ C : Clause, (∀ l ∈ C, l.var ∈ V) →
      ∀ g ∈ C.image (litInd (p := p)), Ind V d g := by
    intro C hC g hg
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hg
    exact ind_litInd hd1 (hC l hl)
  induction D with
  | hyp C hC => exact ⟨hV C hC, 1, TDer.leaf (PInfer.init C hC) (good C (hV C hC))⟩
  | @res x C D dC dD hx hnx ihC ihD =>
    obtain ⟨vC, s₁, t₁⟩ := ihC
    obtain ⟨vD, s₂, t₂⟩ := ihD
    have hR : ∀ l ∈ resolvent C D x, l.var ∈ V := by
      intro l hl
      unfold SATurday.ProofComplexity.resolvent at hl
      rcases Finset.mem_union.1 hl with h | h
      · exact vC l (Finset.mem_of_mem_erase h)
      · exact vD l (Finset.mem_of_mem_erase h)
    refine ⟨hR, s₁ + s₂ + 1, TDer.bin t₁ t₂ ?_ (good _ hR)⟩
    refine PInfer.sem2 (g₁ := litInd ⟨x, true⟩) (g₂ := litInd ⟨x, false⟩) (g₃ := 0)
      (Finset.mem_image_of_mem _ hx) (Finset.mem_image_of_mem _ hnx) ?_ _ ?_ ?_ (Or.inr rfl)
    · intro a
      unfold litInd litPoly boolPt
      cases a x <;> simp
    · intro g hg
      obtain ⟨hne, hg⟩ := Finset.mem_erase.1 hg
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hg
      refine Finset.mem_image_of_mem _ ?_
      unfold SATurday.ProofComplexity.resolvent
      exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨fun e => hne (by rw [e]), hl⟩)
    · intro g hg
      obtain ⟨hne, hg⟩ := Finset.mem_erase.1 hg
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hg
      refine Finset.mem_image_of_mem _ ?_
      unfold SATurday.ProofComplexity.resolvent
      exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨fun e => hne (by rw [e]), hl⟩)

/-- **Non-vacuity.**  An unsatisfiable CNF over `V` has a tree-like `PIC` refutation for every
`d ≥ 1` (existence only, from completeness of resolution). -/
theorem tder_of_unsat {Φ : CNF} {V : Finset ℕ} {d : ℕ} (hd1 : 1 ≤ d)
    (hV : ∀ C ∈ Φ, ∀ l ∈ C, l.var ∈ V) (h : ¬ Satisfiable Φ) :
    ∃ s, TDer (p := p) Φ V d (∅ : PLine p) s := by
  obtain ⟨D⟩ := resolution_complete h
  obtain ⟨-, s, hs⟩ := tder_of_derivation (p := p) hd1 hV D
  rw [Finset.image_empty] at hs
  exact ⟨s, hs⟩

/-! ## Tseitin -/

open SATurday.ProofComplexity.TseitinPC

/-- **Tree-like `PIC`, Tseitin, natural number form.**  For `m ≥ tseitinFloor p q`, every charge,
every `d ≥ 1`: a tree-like refutation of one-hot Tseitin mod `q` on `cubFam m` with terms of degree
at most `d` over `F_p` has at least `2 ^ ((D0 - max (q+3) (3 d)) / d)` nodes, `D0` the polynomial
calculus degree bound of `tseitin_bool_degree_Fp_idx`. -/
theorem pic_tree_tseitin_idx (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) {m : ℕ} (hm : tseitinFloor p q ≤ m) (b : Fin (m * m * 8) → ZMod q)
    {d : ℕ} (hd1 : 1 ≤ d) {s : ℕ}
    (h : TDer (p := p) (tcnf (cubFam m) q b) (tVars (cubFam m) q) d ∅ s) :
    2 ^ (((((m * m * 8) - 2) / 1312 - q * (q + 3)) / (q - 1) - max (q + 3) (3 * d)) / d) ≤ s := by
  obtain ⟨hreg, -, hdeg⟩ := tseitin_bool_degree_Fp_idx p hq hpq hm
  exact tree_size_of_degree hd1 (fun C hC => (tcnf_clause_props hreg hC).2) (hdeg b) h

/-- The degree bound `D0` is at least `n / (1312 q)` for `n ≥ 1312 q (q^2 + 4 q + 2)`. -/
theorem D0_ge {q n : ℕ} (hq : 2 ≤ q) (hn : 1312 * q * (q * q + 4 * q + 2) ≤ n) :
    n ≤ 1312 * q * (((n - 2) / 1312 - q * (q + 3)) / (q - 1)) := by
  set X := (n - 2) / 1312 with hX
  set Y := X - q * (q + 3) with hY
  set D0 := Y / (q - 1) with hD0
  have hq1 : 0 < q - 1 := by omega
  have hnX : n ≤ 1312 * X + 1313 := by
    have h1 := Nat.div_add_mod (n - 2) 1312
    have h2 := Nat.mod_lt (n - 2) (show 0 < 1312 by norm_num)
    rw [← hX] at h1
    omega
  have hYD : Y ≤ (q - 1) * D0 + (q - 2) := by
    have h1 := Nat.div_add_mod Y (q - 1)
    have h2 := Nat.mod_lt Y hq1
    rw [← hD0] at h1
    omega
  have hXY : X ≤ Y + q * (q + 3) := by omega
  have e0 : q * (q + 3) = q * q + 3 * q := by ring
  have e1 : 1312 * q * D0 = 1312 * ((q - 1) * D0) + 1312 * D0 := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  by_cases hc : q * q + 4 * q ≤ D0
  · rw [e1]; omega
  · exfalso
    have h3 : (q - 1) * D0 ≤ (q - 1) * (q * q + 4 * q) := Nat.mul_le_mul_left _ (by omega)
    have e2 : q * (q * q + 4 * q) = (q - 1) * (q * q + 4 * q) + (q * q + 4 * q) := by
      obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    have e3 : 1312 * q * (q * q + 4 * q + 2) = 1312 * (q * (q * q + 4 * q)) + 2624 * q := by ring
    rw [e3] at hn
    omega

/-- **Tree-like `PIC`, Tseitin, indexed family, real form.**  Primes `p ∤ q`, `δ > 0`.  There is
`m0` such that for all `m ≥ m0`, with `n = 8 m^2`: one-hot Tseitin mod `q` on `cubFam m` with the
explicit charge is unsatisfiable; for every `d ≥ 1` it has a tree-like `PIC` refutation over `F_p`
with terms of degree at most `d`; and for every `d` with `1 ≤ d ≤ n^(1-δ)` every such refutation
has at least `2 ^ (n^δ / (2624 q))` nodes.  There is no logarithmic bound on the degree. -/
theorem pic_tree_main_idx (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (δ : ℝ) (hδ : 0 < δ) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
      ¬ Satisfiable (tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q)) ∧
      ∀ d : ℕ, 1 ≤ d →
        (∃ s, TDer (p := p) (tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q))
          (tVars (cubFam m) q) d ∅ s) ∧
        ((d : ℝ) ≤ ((m * m * 8 : ℕ) : ℝ) ^ (1 - δ) →
          ∀ s : ℕ, TDer (p := p) (tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q))
            (tVars (cubFam m) q) d ∅ s →
            (2 : ℝ) ^ (((m * m * 8 : ℕ) : ℝ) ^ δ / (2624 * q)) ≤ s) := by
  set B : ℝ := 2624 * q * (q + 7) with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨max (tseitinFloor p q) (max (1312 * q * (q * q + 4 * q + 2)) ⌈B ^ δ⁻¹⌉₊),
    fun m hm => ?_⟩
  have hmF : tseitinFloor p q ≤ m := (le_max_left _ _).trans hm
  have hmN : 1312 * q * (q * q + 4 * q + 2) ≤ m :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hm
  have hmB : ⌈B ^ δ⁻¹⌉₊ ≤ m := ((le_max_right _ _).trans (le_max_right _ _)).trans hm
  have hmn : m ≤ m * m * 8 := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp
    · nlinarith
  set n := m * m * 8 with hn
  obtain ⟨hreg, -, -⟩ := cubFam_props (cubFam_floor_le hmF).1
  obtain ⟨-, hunsat⟩ := tseitin_idx_explicit_unsat p hq hmF
  refine ⟨hunsat, fun d hd1 => ⟨tder_of_unsat hd1 ?_ hunsat, fun hd s hs => ?_⟩⟩
  · intro C hC l hl
    exact (tcnf_clause_props hreg hC).1 (Finset.mem_image_of_mem _ hl)
  have hS := pic_tree_tseitin_idx p hq hpq hmF _ hd1 hs
  rw [← hn] at hS
  set D0 := ((n - 2) / 1312 - q * (q + 3)) / (q - 1) with hD0
  set E := (D0 - max (q + 3) (3 * d)) / d with hE
  have hnpos : 0 < n := by
    have : 0 < 1312 * q * (q * q + 4 * q + 2) := by positivity
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  -- natural number facts
  have hD0n : n ≤ 1312 * q * D0 := D0_ge hq (hmN.trans hmn)
  have hED : D0 ≤ d * (E + 1) + (q + 3) + 3 * d := by
    have h1 : max (q + 3) (3 * d) ≤ q + 3 + 3 * d := max_le (by omega) (by omega)
    have h2 := Nat.lt_mul_div_succ (D0 - max (q + 3) (3 * d)) (show 0 < d by omega)
    rw [← hE] at h2
    omega
  -- real facts
  set t : ℝ := (n : ℝ) ^ δ with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hnR.le _
  have htB : B ≤ t := by
    have h1 : B ^ δ⁻¹ ≤ (n : ℝ) := by
      have := Nat.le_ceil (B ^ δ⁻¹)
      exact this.trans (by exact_mod_cast hmB.trans hmn)
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hB0 _) h1 hδ.le
    rwa [Real.rpow_inv_rpow hB0 hδ.ne'] at h2
  have hdt : (d : ℝ) * t ≤ n := by
    have h1 : (n : ℝ) ^ (1 - δ) * t = n := by
      rw [ht, ← Real.rpow_add hnR]; simp
    calc (d : ℝ) * t ≤ (n : ℝ) ^ (1 - δ) * t := mul_le_mul_of_nonneg_right hd ht0
      _ = n := h1
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (n : ℝ) ≤ 1312 * q * D0 := by exact_mod_cast hD0n
  have h2 : (D0 : ℝ) ≤ d * (E + 1) + (q + 3) + 3 * d := by exact_mod_cast hED
  have h3 : (d : ℝ) * t ≤ d * (1312 * q * (E + q + 7)) := by
    have h4 : (q + 3 : ℝ) ≤ d * (q + 3) := by nlinarith
    have h5 : (1312 * q : ℝ) * D0 ≤ 1312 * q * (d * (E + 1) + d * (q + 3) + 3 * d) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc (d : ℝ) * t ≤ n := hdt
      _ ≤ 1312 * q * D0 := h1
      _ ≤ 1312 * q * (d * (E + 1) + d * (q + 3) + 3 * d) := h5
      _ = d * (1312 * q * (E + q + 7)) := by ring
  have h6 : t ≤ 1312 * q * (E + q + 7) := le_of_mul_le_mul_left h3 (by linarith)
  have hEt : t / (2624 * q) ≤ E := by
    rw [div_le_iff₀ (by positivity)]
    have : (2624 : ℝ) * q * (q + 7) ≤ t := htB
    nlinarith
  calc (2 : ℝ) ^ (t / (2624 * q)) ≤ (2 : ℝ) ^ (E : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hEt
    _ = ((2 ^ E : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
    _ ≤ s := by exact_mod_cast hS

end

end PICT
