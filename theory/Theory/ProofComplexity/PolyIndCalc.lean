import Theory.ProofComplexity.C1Final
import Theory.ProofComplexity.TseitinIndexed

/-!
# The polynomial indicator calculus `PIC_d^p` and its size lower bound

Generalization of the bounded rank calculus `R_ρ^p` of `C1Rank.lean`.  A term is an arbitrary
polynomial over `F_p` that takes values in `{0, 1}` on the Boolean cube, has degree at most `d` and
variables in `V` (an "indicator").  A line is a finite set of terms, read as their disjunction.
Rules: clause axioms, excluded middle `{g, 1 - g}`, weakening, and the semantic term rule with one
or two premises (as in `R_ρ^p`, with semantic consequence on the whole cube).

A term of `R_ρ^p` (a conjunction of affine equations of rank `≤ ρ`) has an indicator of degree
`(p-1) ρ`, so `R_ρ^p` is the special case of conjunctions of linear equations.  New here: a term may
be, for example, a `MOD_p` gate over conjunctions, or a conjunction of `MOD_p` gates.

The lower bound is the one of `C1.c1_main`, with the same proof (the step lemmas of `C1Sim.lean`
are stated for an arbitrary indicator family) and the same constants, for `d = (p-1) ρ`.
Mathematically this is Pang's degree-size method (arXiv 2610.00837) for resolution over polynomials
of degree `d`; no novelty is claimed.

LOG: R4 ac0p fable session, polynomial indicator calculus
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.PCL MvPolynomial

namespace PIC

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime]

open Pang

/-- A line: a finite set of polynomials (their disjunction, each read as "value 1"). -/
abbrev PLine (p : ℕ) [Fact p.Prime] := Finset (PP p)

/-- The indicator of a literal being true. -/
def litInd (l : Literal) : PP p := 1 - litPoly l

/-- An indicator over `V` of degree at most `d`: values in `{0, 1}` on the cube. -/
structure Ind (V : Finset ℕ) (d : ℕ) (g : PP p) : Prop where
  cube : ∀ a : Assignment, eval (boolPt (F := ZMod p) a) g = 0 ∨ eval (boolPt (F := ZMod p) a) g = 1
  deg : g.totalDegree ≤ d
  vars : ∀ v ∈ g.vars, v ∈ V

/-- One inference step.  `g₃ = 0` in the semantic rules means the empty conclusion. -/
inductive PInfer (Φ : CNF) : List (PLine p) → PLine p → Prop
  | init (C : Clause) (hC : C ∈ Φ) : PInfer Φ [] (C.image litInd)
  | taut (g : PP p) : PInfer Φ [] {g, 1 - g}
  | weak {L : PLine p} (L' : PLine p) (h : L ⊆ L') : PInfer Φ [L] L'
  | sem1 {L₁ : PLine p} {g₁ g₃ : PP p} (h₁ : g₁ ∈ L₁)
      (hs : ∀ a : Assignment, eval (boolPt (F := ZMod p) a) g₁ *
        (1 - eval (boolPt (F := ZMod p) a) g₃) = 0)
      (L' : PLine p) (hL' : L₁.erase g₁ ⊆ L') (h₃ : g₃ ∈ L' ∨ g₃ = 0) : PInfer Φ [L₁] L'
  | sem2 {L₁ L₂ : PLine p} {g₁ g₂ g₃ : PP p} (h₁ : g₁ ∈ L₁) (h₂ : g₂ ∈ L₂)
      (hs : ∀ a : Assignment, eval (boolPt (F := ZMod p) a) g₁ * eval (boolPt (F := ZMod p) a) g₂ *
        (1 - eval (boolPt (F := ZMod p) a) g₃) = 0)
      (L' : PLine p) (hL₁ : L₁.erase g₁ ⊆ L') (hL₂ : L₂.erase g₂ ⊆ L') (h₃ : g₃ ∈ L' ∨ g₃ = 0) :
      PInfer Φ [L₁, L₂] L'

/-- A line holds at a point: some term has value 1. -/
def LTrue (a : Assignment) (L : PLine p) : Prop := ∃ g ∈ L, eval (boolPt (F := ZMod p) a) g = 1

theorem eval_litInd {a : Assignment} {l : Literal} (h : litSat a l) :
    eval (boolPt (F := ZMod p) a) (litInd l : PP p) = 1 := by
  unfold litInd; rw [map_sub, map_one, eval_litPoly h]; simp

/-- Soundness of one step at a Boolean point, for lines of `0/1` valued terms. -/
theorem PInfer.sound {Φ : CNF} {a : Assignment} (ha : cnfSat a Φ)
    {Ls : List (PLine p)} {L : PLine p} (h : PInfer Φ Ls L)
    (h01 : ∀ g ∈ L, eval (boolPt (F := ZMod p) a) g = 0 ∨ eval (boolPt (F := ZMod p) a) g = 1)
    (hL : ∀ M ∈ Ls, LTrue a M) : LTrue a L := by
  cases h with
  | init C hC =>
    obtain ⟨l, hl, hs⟩ := ha C hC
    exact ⟨litInd l, Finset.mem_image.2 ⟨l, hl, rfl⟩, eval_litInd hs⟩
  | taut g =>
    rcases h01 g (by simp) with h0 | h1
    · exact ⟨1 - g, by simp, by rw [map_sub, map_one, h0]; simp⟩
    · exact ⟨g, by simp, h1⟩
  | weak L' h =>
    obtain ⟨g, hg, hz⟩ := hL _ (List.mem_singleton_self _)
    exact ⟨g, h hg, hz⟩
  | @sem1 L₁ g₁ g₃ h₁ hs L' hL' h₃ =>
    obtain ⟨g, hg, hz⟩ := hL L₁ (by simp)
    by_cases e : g = g₁
    · subst e
      have h := hs a
      rw [hz, one_mul] at h
      rcases h₃ with h3 | h3
      · exact ⟨g₃, h3, by linear_combination -h⟩
      · rw [h3] at h; simp at h
    · exact ⟨g, hL' (Finset.mem_erase.2 ⟨e, hg⟩), hz⟩
  | @sem2 L₁ L₂ g₁ g₂ g₃ h₁ h₂ hs L' hL₁ hL₂ h₃ =>
    obtain ⟨g, hg, hz⟩ := hL L₁ (by simp)
    obtain ⟨u, hu, hy⟩ := hL L₂ (by simp)
    by_cases e : g = g₁
    · by_cases e2 : u = g₂
      · subst e; subst e2
        have h := hs a
        rw [hz, hy, one_mul, one_mul] at h
        rcases h₃ with h3 | h3
        · exact ⟨g₃, h3, by linear_combination -h⟩
        · rw [h3] at h; simp at h
      · exact ⟨u, hL₂ (Finset.mem_erase.2 ⟨e2, hu⟩), hy⟩
    · exact ⟨g, hL₁ (Finset.mem_erase.2 ⟨e, hg⟩), hz⟩

/-- A dag-like refutation over `V` with indicators of degree at most `d`; size = number of nodes. -/
structure PRefutation (Φ : CNF) (V : Finset ℕ) (d : ℕ) (p : ℕ) [Fact p.Prime] where
  S : ℕ
  line : ℕ → PLine p
  prem : ℕ → List ℕ
  S_pos : 0 < S
  prem_lt : ∀ i < S, ∀ j ∈ prem i, j < i
  infer : ∀ i < S, PInfer Φ ((prem i).map line) (line i)
  good : ∀ i < S, ∀ g ∈ line i, Ind V d g
  last : line (S - 1) = ∅

/-- **Soundness**: a satisfiable CNF has no refutation. -/
theorem PRefutation.unsat {Φ : CNF} {V : Finset ℕ} {d : ℕ} (R : PRefutation Φ V d p) :
    ¬ Satisfiable Φ := by
  rintro ⟨a, ha⟩
  have key : ∀ i < R.S, LTrue a (R.line i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      refine PInfer.sound ha (R.infer i hi) (fun g hg => (R.good i hi g hg).cube a) ?_
      intro M hM
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hM
      exact ih j (R.prem_lt i hi j hj) ((R.prem_lt i hi j hj).trans hi)
  have hS := R.S_pos
  obtain ⟨g, hg, -⟩ := key (R.S - 1) (by omega)
  rw [R.last] at hg
  simp at hg

/-! ## Simulation in polynomial calculus -/

section Main
variable {Φ : CNF} {V : Finset ℕ}

lemma prem_single {α : Type*} {l : List ℕ} {f : ℕ → α} {a : α} (h : l.map f = [a]) :
    ∃ j, l = [j] ∧ f j = a := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    cases xs with
    | nil => simp at h; exact ⟨x, rfl, h⟩
    | cons y ys => simp at h

lemma prem_pair {α : Type*} {l : List ℕ} {f : ℕ → α} {a b : α} (h : l.map f = [a, b]) :
    ∃ j k, l = [j, k] ∧ f j = a ∧ f k = b := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    cases xs with
    | nil => simp at h
    | cons y ys =>
      cases ys with
      | nil => simp at h; exact ⟨x, y, rfl, h.1, h.2⟩
      | cons z zs => simp at h

lemma cube_set {g : PP p}
    (h : ∀ a : Assignment, eval (boolPt (F := ZMod p) a) g = 0 ∨ eval (boolPt (F := ZMod p) a) g = 1)
    (a : Set ℕ) : eval (indPt a) g = 0 ∨ eval (indPt a) g = 1 := by
  rw [C1.indPt_eq]; exact h _

theorem pic_simulation {d : ℕ} (R : PRefutation Φ V d p) {D K Δ w : ℕ} (hD : 2 ≤ D)
    (hd1 : 1 ≤ d) (hdΔ : d ≤ Δ) (hw : ∀ C ∈ Φ, C.card ≤ w)
    (hb1 : K + 2 * Δ + 2 * d ≤ D) (hb2 : K + Δ + w ≤ D) {f : PP p} (hf : f.totalDegree ≤ K)
    (P : ℕ → PP p) (hP : ∀ i < R.S, (P i).totalDegree ≤ Δ)
    (hpref : ∀ i < R.S, ∃ U : PP p → PP p,
      (∀ T ∈ R.line i, (U T).totalDegree + d ≤ Δ) ∧
      1 - P i = ∑ T ∈ R.line i, U T * T)
    (herr : ∀ i < R.S, ∀ T ∈ R.line i, P i * T * f ∈ CD (cnfAx Φ) D) :
    ∀ i < R.S, P i * f ∈ CD (cnfAx Φ) D := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hgi : ∀ T ∈ R.line i, T.totalDegree ≤ d := fun T hT => (R.good i hi T hT).deg
    have key : ∀ (Ls : List (PLine p)) (L : PLine p), PInfer Φ Ls L →
        (R.prem i).map R.line = Ls → R.line i = L → P i * f ∈ CD (cnfAx Φ) D := by
      intro Ls L hinf hLs hL
      cases hinf with
      | init C hC =>
        have hG : ∀ l : Literal, (litInd l : PP p).totalDegree ≤ d := fun l => by
          unfold litInd
          exact (totalDegree_sub _ _).trans (max_le (by simp) ((C1.totalDegree_litPoly l).trans hd1))
        refine C1.init_step' hD (fun l => (litInd l : PP p)) hG ?_ hd1 hf (hP i hi) (hw C hC) ?_
          (by omega) (by omega) ?_
        · intro l
          have : (litInd l : PP p) - (1 - litPoly l) = 0 := by unfold litInd; ring
          rw [this]; exact zero_mem _
        · refine mem_CD_of_pcd (PCD.ax ⟨C, hC, rfl⟩ ?_)
          have : (clausePoly C : PP p).totalDegree ≤ C.card := by
            unfold clausePoly
            refine (totalDegree_finset_prod _ _).trans ?_
            calc ∑ l ∈ C, (litPoly l : PP p).totalDegree ≤ ∑ _l ∈ C, 1 :=
                  Finset.sum_le_sum fun l _ => C1.totalDegree_litPoly l
              _ = C.card := by simp
          have := hw C hC
          omega
        · intro l hl
          exact herr i hi _ (by rw [hL]; exact Finset.mem_image.2 ⟨l, hl, rfl⟩)
      | taut g =>
        have m1 : g ∈ R.line i := by rw [hL]; simp
        have m2 : 1 - g ∈ R.line i := by rw [hL]; simp
        refine C1.bool_step' hD hf (hP i hi) (hgi _ m1) (hgi _ m2) (by omega)
          (herr i hi _ m1) (herr i hi _ m2) fun a => ?_
        simp
      | @weak L0 L' hsub =>
        obtain ⟨j, hpj, hjL⟩ := prem_single hLs
        have hj : j < i := R.prem_lt i hi j (by rw [hpj]; simp)
        have hjS : j < R.S := hj.trans hi
        obtain ⟨U, hU, hprefj⟩ := hpref j hjS
        refine C1.cover_step (fun g : PP p => g) hD hf (hP i hi) (hP j hjS) hU
          (fun T hT => (R.good j hjS T hT).deg) hprefj (by omega) ?_
          (herr i hi) (ih j hj hjS)
        intro T hT
        left
        rw [hL]; exact hsub (by rw [← hjL]; exact hT)
      | @sem1 L₁ g₁ g₃ h₁ hs L' hL' h₃ =>
        obtain ⟨j, hpj, hjL⟩ := prem_single hLs
        have hj : j < i := R.prem_lt i hi j (by rw [hpj]; simp)
        have hjS : j < R.S := hj.trans hi
        obtain ⟨U, hU, hprefj⟩ := hpref j hjS
        have hh1 : g₁ ∈ R.line j := by rw [hjL]; exact h₁
        have c1 := C1.claim_step (fun g : PP p => g) (h := g₁)
          (cube_set (R.good j hjS g₁ hh1).cube) hD (L1 := R.line j) (L := R.line i) hh1 hf
          (hP i hi) (hP j hjS) hU (fun T hT => (R.good j hjS T hT).deg) hprefj (by omega)
          (fun k hk => by
            rw [hL]; obtain ⟨hne, hkm⟩ := Finset.mem_erase.1 hk
            exact hL' (Finset.mem_erase.2 ⟨hne, by rw [← hjL]; exact hkm⟩))
          (herr i hi) (ih j hj hjS)
        have hg1 := (R.good j hjS g₁ hh1).deg
        have hcube : ∀ a : Set ℕ, eval (indPt a) g₁ * (1 - eval (indPt a) g₃) = 0 := fun a => by
          rw [C1.indPt_eq]; exact hs _
        rcases h₃ with h3 | h3
        · have hmem : g₃ ∈ R.line i := by rw [hL]; exact h3
          exact C1.mul_step hD hf (hP i hi) hg1 (hgi _ hmem) (by omega) c1 (herr i hi _ hmem) hcube
        · subst h3
          exact C1.mul_step (g2 := 0) hD hf (hP i hi) hg1 (by simp) (by omega) c1 (by simp) hcube
      | @sem2 L₁ L₂ g₁ g₂ g₃ h₁ h₂ hs L' hL₁ hL₂ h₃ =>
        obtain ⟨j1, j2, hpj, hj1L, hj2L⟩ := prem_pair hLs
        have hj1 : j1 < i := R.prem_lt i hi j1 (by rw [hpj]; simp)
        have hj2 : j2 < i := R.prem_lt i hi j2 (by rw [hpj]; simp)
        have hjS1 : j1 < R.S := hj1.trans hi
        have hjS2 : j2 < R.S := hj2.trans hi
        obtain ⟨U1, hU1, hpref1⟩ := hpref j1 hjS1
        obtain ⟨U2, hU2, hpref2⟩ := hpref j2 hjS2
        have hh1 : g₁ ∈ R.line j1 := by rw [hj1L]; exact h₁
        have hh2 : g₂ ∈ R.line j2 := by rw [hj2L]; exact h₂
        have c1 := C1.claim_step (fun g : PP p => g) (h := g₁)
          (cube_set (R.good j1 hjS1 g₁ hh1).cube) hD (L1 := R.line j1) (L := R.line i) hh1 hf
          (hP i hi) (hP j1 hjS1) hU1 (fun T hT => (R.good j1 hjS1 T hT).deg) hpref1 (by omega)
          (fun k hk => by
            rw [hL]; obtain ⟨hne, hkm⟩ := Finset.mem_erase.1 hk
            exact hL₁ (Finset.mem_erase.2 ⟨hne, by rw [← hj1L]; exact hkm⟩))
          (herr i hi) (ih j1 hj1 hjS1)
        have c2 := C1.claim_step (fun g : PP p => g) (h := g₂)
          (cube_set (R.good j2 hjS2 g₂ hh2).cube) hD (L1 := R.line j2) (L := R.line i) hh2 hf
          (hP i hi) (hP j2 hjS2) hU2 (fun T hT => (R.good j2 hjS2 T hT).deg) hpref2 (by omega)
          (fun k hk => by
            rw [hL]; obtain ⟨hne, hkm⟩ := Finset.mem_erase.1 hk
            exact hL₂ (Finset.mem_erase.2 ⟨hne, by rw [← hj2L]; exact hkm⟩))
          (herr i hi) (ih j2 hj2 hjS2)
        have hg1 := (R.good j1 hjS1 g₁ hh1).deg
        have hg2 := (R.good j2 hjS2 g₂ hh2).deg
        have hcube : ∀ a : Set ℕ, eval (indPt a) g₁ * eval (indPt a) g₂ *
            (1 - eval (indPt a) g₃) = 0 := fun a => by
          rw [C1.indPt_eq]; exact hs _
        rcases h₃ with h3 | h3
        · have hmem : g₃ ∈ R.line i := by rw [hL]; exact h3
          exact C1.comb_step hD hf (hP i hi) hdΔ hg1 hg2 (hgi _ hmem) hb1 c1 c2
            (herr i hi _ hmem) hcube
        · subst h3
          exact C1.comb_step (g3 := 0) hD hf (hP i hi) hdΔ hg1 hg2 (by simp) hb1 c1 c2 (by simp)
            hcube
    exact key _ _ (R.infer i hi) rfl rfl

/-- The final line is empty and `P = 1` there, so `f ∈ C_D`. -/
theorem pic_simulation_final {d : ℕ} (R : PRefutation Φ V d p) {D K Δ w : ℕ} (hD : 2 ≤ D)
    (hd1 : 1 ≤ d) (hdΔ : d ≤ Δ) (hw : ∀ C ∈ Φ, C.card ≤ w)
    (hb1 : K + 2 * Δ + 2 * d ≤ D) (hb2 : K + Δ + w ≤ D) {f : PP p} (hf : f.totalDegree ≤ K)
    (P : ℕ → PP p) (hP : ∀ i < R.S, (P i).totalDegree ≤ Δ)
    (hpref : ∀ i < R.S, ∃ U : PP p → PP p,
      (∀ T ∈ R.line i, (U T).totalDegree + d ≤ Δ) ∧
      1 - P i = ∑ T ∈ R.line i, U T * T)
    (herr : ∀ i < R.S, ∀ T ∈ R.line i, P i * T * f ∈ CD (cnfAx Φ) D) :
    f ∈ CD (cnfAx Φ) D := by
  have hS := R.S_pos
  have hlt : R.S - 1 < R.S := by omega
  have h1 := pic_simulation R hD hd1 hdΔ hw hb1 hb2 hf P hP hpref herr (R.S - 1) hlt
  obtain ⟨U, _, hU⟩ := hpref (R.S - 1) hlt
  rw [R.last, Finset.sum_empty] at hU
  have : P (R.S - 1) = 1 := by linear_combination -hU
  rwa [this, one_mul] at h1

open Pang in
theorem pic_degree_size {d : ℕ} (R : PRefutation Φ V d p) {D K t w : ℕ}
    (hd1 : 1 ≤ d)
    (hD : 2 ≤ D) (h1 : (1 : PP p) ∉ CD (cnfAx Φ) D) (ht : 1 ≤ t)
    (hw : ∀ C ∈ Φ, C.card ≤ w) (hdK : d ≤ K) (hKn : K ≤ V.card)
    (hb1 : K + 2 * (t * ((p - 1) * d)) + 2 * d ≤ D)
    (hb2 : K + t * ((p - 1) * d) + w ≤ D) :
    (p * Nn V.card K) ^ t ≤
      R.S * (p * Nn V.card K - (p - 1) * Nn V.card (K - d)) ^ t := by
  by_contra hlt
  push Not at hlt
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdΔ : d ≤ t * ((p - 1) * d) := by
    have : d ≤ (p - 1) * d := Nat.le_mul_of_pos_left d (by omega)
    nlinarith
  let m : Fin R.S → ℕ := fun ν => (R.line ν).card
  let g : ∀ ν : Fin R.S, Fin (m ν) → PP p := fun ν k => ((R.line ν).equivFin.symm k : PP p)
  have hgd : ∀ ν k, (g ν k).totalDegree ≤ d := fun ν k =>
    (R.good ν ν.2 _ (R.line ν |>.equivFin.symm k).2).deg
  have hgV : ∀ ν k, ∀ v ∈ (g ν k).vars, v ∈ V := fun ν k =>
    (R.good ν ν.2 _ (R.line ν |>.equivFin.symm k).2).vars
  obtain ⟨c, f, hfV, hfn, hdeg, herr⟩ := common_multiplier (Ax := cnfAx Φ) hD h1 hdK hKn
    (by omega) m g hgd hgV hlt
  set Pn : ∀ ν : Fin R.S, PP p := fun ν =>
    ∏ j ∈ Finset.range t, (1 - (∑ k, c ν j k • g ν k) ^ (p - 1)) with hPn
  let P : ℕ → PP p := fun i => if hi : i < R.S then Pn ⟨i, hi⟩ else 1
  have hPi : ∀ i (hi : i < R.S), P i = Pn ⟨i, hi⟩ := fun i hi => by simp [P, hi]
  have hf : (polyOf f).totalDegree ≤ K :=
    (totalDegree_polyOf_le f).trans (deg_le_of_mem_Vk V hfV)
  refine hfn (pic_simulation_final R hD hd1 hdΔ hw hb1 hb2 hf P ?_ ?_ ?_)
  · intro i hi
    rw [hPi i hi]; exact hdeg ⟨i, hi⟩
  · intro i hi
    let ν : Fin R.S := ⟨i, hi⟩
    let L := R.line i
    let c' : ℕ → PP p → ZMod p := fun j h => if hh : h ∈ L then c ν j (L.equivFin ⟨h, hh⟩) else 0
    have hsumeq : ∀ j, ∑ k, c ν j k • g ν k = ∑ h ∈ L, c' j h • h := by
      intro j
      rw [← C1.sum_equivFin' L (fun h => c' j h • h)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [c', g]
      rw [dif_pos (L.equivFin.symm k).2]
      simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
      rfl
    obtain ⟨U, hU, hid⟩ := prefix_identity L (fun g : PP p => g) c' (t := t) (d := d) ht
      (fun h hh => (R.good i hi h hh).deg)
    refine ⟨U, hU, ?_⟩
    rw [hPi i hi]
    show 1 - (∏ j ∈ Finset.range t, (1 - (∑ k, c ν j k • g ν k) ^ (p - 1))) =
      ∑ h ∈ R.line i, U h * h
    simp_rw [hsumeq]
    exact hid
  · intro i hi h hh
    rw [hPi i hi]
    have := herr ⟨i, hi⟩ (R.line i |>.equivFin ⟨h, hh⟩)
    simpa [g, Pn] using this

open Pang in
/-- **Exponential form** of the degree-size relation for `R_ρ^p` (`d = (p-1) ρ`). -/
theorem pic_size_exp {d : ℕ} (R : PRefutation Φ V d p) {D K t w lam : ℕ}
    (hd1 : 1 ≤ d)
    (hD : 2 ≤ D) (h1 : (1 : PP p) ∉ CD (cnfAx Φ) D) (ht : 1 ≤ t)
    (hw : ∀ C ∈ Φ, C.card ≤ w) (hdK : d ≤ K) (hKn : K ≤ V.card)
    (hb1 : K + 2 * (t * ((p - 1) * d)) + 2 * d ≤ D)
    (hb2 : K + t * ((p - 1) * d) + w ≤ D)
    (h2d : 2 * d < K) (hlam : V.card ≤ lam * (K - 2 * d)) :
    2 ^ (t / (2 * (1 + lam ^ d))) ≤ R.S := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hds := pic_degree_size R hd1 hD h1 ht hw hdK hKn hb1 hb2
  set N := Nn V.card K with hN
  set N' := Nn V.card (K - d) with hN'
  have hNN' : N' ≤ N := Nn_mono (Nat.sub_le _ _)
  have hNpos : 0 < N := Nn_pos V K
  have hratio : N ≤ (1 + lam ^ d) * N' := Nn_ratio h2d hlam
  have hθpos : 0 < p * N - (p - 1) * N' := by
    have : (p - 1) * N' ≤ (p - 1) * N := Nat.mul_le_mul_left _ hNN'
    have h3 : p * N = (p - 1) * N + N := by
      rw [← Nat.succ_mul]; congr 1; omega
    omega
  have hle : (p - 1) * N' ≤ p * N := by
    calc (p - 1) * N' ≤ p * N' := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ ≤ p * N := Nat.mul_le_mul_left _ hNN'
  refine exp_bound (M := p * N) (θ := p * N - (p - 1) * N') (a := (p - 1) * N')
    (s := 2 * (1 + lam ^ d)) (by omega) hθpos ?_ hds
  calc p * N - (p - 1) * N' ≤ p * N := Nat.sub_le _ _
    _ ≤ 2 * ((p - 1) * N) := by
        have : p ≤ 2 * (p - 1) := by omega
        calc p * N ≤ (2 * (p - 1)) * N := Nat.mul_le_mul_right _ this
          _ = 2 * ((p - 1) * N) := by ring
    _ ≤ 2 * ((p - 1) * ((1 + lam ^ d) * N')) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hratio)
    _ = 2 * (1 + lam ^ d) * ((p - 1) * N') := by ring


theorem pic_exp_of_degree {d : ℕ} (R : PRefutation Φ V d p) {q n : ℕ}
    (hd1 : 1 ≤ d) (hq : 2 ≤ q)
    (hn : C1.cN0R p q d ≤ n) (h1n : n ≤ 2 * V.card) (h2n : V.card ≤ 3 * n * q)
    (hw : ∀ C ∈ Φ, C.card ≤ q + 3)
    (h1 : (1 : PP p) ∉ CD (cnfAx Φ) (((n - 2) / 1312 - q * (q + 3)) / (q - 1))) :
    2 ^ (n / C1.cCR p q d) ≤ R.S := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨E, hE⟩ : ∃ E, E = (p - 1) * d := ⟨_, rfl⟩
  have hEd : d ≤ E := by rw [hE]; exact Nat.le_mul_of_pos_left d (by omega)
  have hE1 : 1 ≤ E := by omega
  set X := (n - 2) / 1312 with hX
  set D := (X - q * (q + 3)) / (q - 1) with hDdef
  have hq1 : 0 < q - 1 := by omega
  have hXge : q * (q + 3) + (q - 1) * C1.cDminR p q d ≤ X := by
    rw [hX, Nat.le_div_iff_mul_le (by norm_num)]
    unfold C1.cN0R at hn; omega
  have hDmin : C1.cDminR p q d ≤ D := by
    rw [hDdef, Nat.le_div_iff_mul_le hq1]
    have e : C1.cDminR p q d * (q - 1) = (q - 1) * C1.cDminR p q d := mul_comm _ _
    omega
  have hnX : n ≤ 1312 * X + 1313 := by
    have h1 := Nat.div_add_mod (n - 2) 1312
    have h2 := Nat.mod_lt (n - 2) (show 0 < 1312 by norm_num)
    rw [← hX] at h1
    omega
  have hXD : X < (q - 1) * (D + 1) + q * (q + 3) := by
    have h1 := Nat.div_add_mod (X - q * (q + 3)) (q - 1)
    have h2 := Nat.mod_lt (X - q * (q + 3)) hq1
    rw [← hDdef] at h1
    have hXq : q * (q + 3) ≤ X := by
      have : 0 ≤ (q - 1) * C1.cDminR p q d := Nat.zero_le _
      omega
    have e : (q - 1) * (D + 1) = (q - 1) * D + (q - 1) := by ring
    omega
  unfold C1.cDminR at hDmin
  rw [← hE] at hDmin
  have hnD : n ≤ cA q * D := by
    unfold cA
    have e1 : (q - 1) * (D + 1) ≤ q * D + q := by
      have : (q - 1) * (D + 1) = (q - 1) * D + (q - 1) := by ring
      have h6 : (q - 1) * D ≤ q * D := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      omega
    have e2 : q * (q + 3) ≤ q * D := Nat.mul_le_mul_left _ (by omega)
    have e3 : q ≤ D := by omega
    have e4 : X ≤ (2 * q + 1) * D := by nlinarith [e1, e2, e3, hXD]
    have e5 : 1312 * X ≤ 1312 * ((2 * q + 1) * D) := Nat.mul_le_mul_left _ e4
    nlinarith [e5, hnX, hDmin]
  set K := D / 4 with hK
  set t := D / (8 * E) with ht
  have hK4 : 4 * K ≤ D := Nat.mul_div_le D 4
  have hK4' : D ≤ 4 * K + 3 := by omega
  have ht8 : 8 * E * t ≤ D := Nat.mul_div_le D _
  have hT : 8 * (t * E) ≤ D := by nlinarith [ht8]
  have ht1 : 1 ≤ t := Nat.div_pos (by omega) (by omega)
  have hDX : D ≤ X := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hXn : 1312 * X ≤ n := by
    rw [hX]; exact (Nat.mul_div_le (n - 2) 1312).trans (Nat.sub_le _ _)
  have hKV : K ≤ V.card := by omega
  have hD6 : D ≤ 6 * (K - 2 * d) := by omega
  have hlamb : V.card ≤ cLam q * (K - 2 * d) := by
    calc V.card ≤ 3 * n * q := h2n
      _ ≤ 3 * (cA q * D) * q := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hnD)
      _ ≤ 3 * (cA q * (6 * (K - 2 * d))) * q :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hD6))
      _ = cLam q * (K - 2 * d) := by unfold cLam; ring
  have hsz := pic_size_exp (Φ := Φ) (V := V) R (D := D) (K := K) (t := t) (w := q + 3)
    (lam := cLam q) hd1
    (by omega) h1 ht1 hw (by omega) hKV (by rw [← hE]; omega) (by rw [← hE]; omega) (by omega)
    hlamb
  refine le_trans (Nat.pow_le_pow_right (by norm_num) ?_) hsz
  have e : C1.cCR p q d = cA q * (8 * E) * C1.cSR q d := by unfold C1.cCR; rw [hE]
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  have h1' : n / cA q ≤ D := Nat.div_le_of_le_mul hnD
  have h2' : n / cA q / (8 * E) ≤ t := Nat.div_le_div_right h1'
  exact Nat.div_le_div_right h2'


end Main

/-! ## Tseitin -/

open SATurday.ProofComplexity.TseitinPC

/-- Natural number form, indexed family.  Terms have degree at most `d ≥ 1`. -/
theorem pic_tseitin_exp_idx (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    {m : ℕ} (hm : tseitinFloor p q ≤ m) (b : Fin (m * m * 8) → ZMod q) :
    ∀ d : ℕ, 1 ≤ d → C1.cN0R p q d ≤ m * m * 8 →
      ∀ R : PRefutation (tcnf (cubFam m) q b) (tVars (cubFam m) q) d p,
        2 ^ ((m * m * 8) / C1.cCR p q d) ≤ R.S := by
  obtain ⟨hreg, hconn, hdeg⟩ := tseitin_bool_degree_Fp_idx p hq hpq hm
  intro d hd1 hn R
  have hn0 : 0 < m * m * 8 := by unfold C1.cN0R at hn; omega
  refine pic_exp_of_degree R hd1 hq hn ?_ ?_ (fun C hC => (tcnf_clause_props hreg hC).2) ?_
  · have := card_G_ge hreg
    have := card_tVars_ge (q := q) hn0 (cubFam m)
    omega
  · have h1 := Pang.card_tVars_le (q := q) (cubFam m)
    have h2 := Pang.card_G_le hreg
    calc (tVars (cubFam m) q).card ≤ (cubFam m).card * q := h1
      _ ≤ (3 * (m * m * 8)) * q := Nat.mul_le_mul_right _ h2
  · intro h
    rcases h with h0 | hp
    · exact one_ne_zero h0
    · exact hdeg b hp

/-- One graph for all admissible degrees (existential family). -/
theorem pic_tseitin_exp' (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧ ∀ b : Fin n → ZMod q,
      ∀ d : ℕ, 1 ≤ d → C1.cN0R p q d ≤ n →
      ∀ R : PRefutation (tcnf G q b) (tVars G q) d p,
        2 ^ (n / C1.cCR p q d) ≤ R.S := by
  obtain ⟨n, G, hN, hreg, hdeg⟩ := tseitin_bool_degree_Fp p hq hpq N
  refine ⟨n, G, hN, hreg, fun b d hd1 hn R => ?_⟩
  have hn0 : 0 < n := by unfold C1.cN0R at hn; omega
  refine pic_exp_of_degree R hd1 hq hn ?_ ?_ (fun C hC => (tcnf_clause_props hreg hC).2) ?_
  · have := card_G_ge hreg
    have := card_tVars_ge (q := q) hn0 G
    omega
  · have h1 := Pang.card_tVars_le (q := q) G
    have h2 := Pang.card_G_le hreg
    calc (tVars G q).card ≤ G.card * q := h1
      _ ≤ (3 * n) * q := Nat.mul_le_mul_right _ h2
  · intro h
    rcases h with h0 | hp
    · exact one_ne_zero h0
    · exact hdeg b hp

/-- **Lower bound for `PIC`, existential family.**  Primes `p ∤ q`, `ε > 0` with `(κ+1) ε < 1`,
`κ = C1.kappa p q`.  For every `M` there is a cubic graph on `n ≥ M` vertices such that for every
charge `b` and every `1 ≤ ρ ≤ ε ln n`, every refutation of one-hot Tseitin mod `q` with indicators
of degree at most `(p-1) ρ` has at least `exp (n^(1-(κ+1) ε))` nodes. -/
theorem pic_main (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (ε : ℝ) (hε : 0 < ε) (hεκ : (C1.kappa p q + 1) * ε < 1) (M : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), M ≤ n ∧ IsRegular G 3 ∧ ∀ b : Fin n → ZMod q,
      ∀ ρ : ℕ, 1 ≤ ρ → (ρ : ℝ) ≤ ε * Real.log n →
      ∀ R : PRefutation (tcnf G q b) (tVars G q) ((p - 1) * ρ) p,
        Real.exp ((n : ℝ) ^ (1 - (C1.kappa p q + 1) * ε)) ≤ R.S := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨M₀, hM₀⟩ := C1.eventually_conditions p q hp ε hε
  obtain ⟨n, G, hN, hreg, H⟩ := pic_tseitin_exp' p hq hpq (max M M₀)
  have hnM₀ : M₀ ≤ n := (le_max_right _ _).trans hN
  obtain ⟨h2, hE1, hE2⟩ := hM₀ n hnM₀
  refine ⟨n, G, (le_max_left _ _).trans hN, hreg, fun b ρ hρ1 hρ R => ?_⟩
  obtain ⟨hc, hex⟩ := C1.real_chain p q ρ n hp hq ε hε hεκ hρ1 hρ h2 hE1 hE2
  have hS := H b ((p - 1) * ρ) (Nat.mul_pos (by omega) hρ1) hc R
  refine hex.trans ?_
  exact_mod_cast hS

/-- **Lower bound for `PIC`, indexed family** `cubFam m`, `n = 8 m^2`, all `m ≥ m0`. -/
theorem pic_main_idx (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (ε : ℝ) (hε : 0 < ε) (hεκ : (C1.kappa p q + 1) * ε < 1) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → ∀ b : Fin (m * m * 8) → ZMod q,
      ∀ ρ : ℕ, 1 ≤ ρ → (ρ : ℝ) ≤ ε * Real.log (m * m * 8 : ℕ) →
      ∀ R : PRefutation (tcnf (cubFam m) q b) (tVars (cubFam m) q) ((p - 1) * ρ) p,
        Real.exp (((m * m * 8 : ℕ) : ℝ) ^ (1 - (C1.kappa p q + 1) * ε)) ≤ R.S := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨M₀, hM₀⟩ := C1.eventually_conditions p q hp ε hε
  refine ⟨max M₀ (tseitinFloor p q), fun m hm b ρ hρ1 hρ R => ?_⟩
  have hmF : tseitinFloor p q ≤ m := (le_max_right _ _).trans hm
  have hmM : M₀ ≤ m := (le_max_left _ _).trans hm
  have hmn : m ≤ m * m * 8 := by nlinarith [tseitinFloor_pos p q]
  obtain ⟨h2, hE1, hE2⟩ := hM₀ (m * m * 8) (hmM.trans hmn)
  obtain ⟨hc, hex⟩ := C1.real_chain p q ρ (m * m * 8) hp hq ε hε hεκ hρ1 hρ h2 hE1 hE2
  have hS := pic_tseitin_exp_idx p hq hpq hmF b ((p - 1) * ρ) (Nat.mul_pos (by omega) hρ1) hc R
  refine hex.trans ?_
  exact_mod_cast hS

end

end PIC
