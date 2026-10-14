import Theory.ProofComplexity.C1Rank
import Theory.ProofComplexity.PangSim

/-!
# Candidate C1: direct simulation of an `R_ρ^p` refutation in polynomial calculus

The step lemmas of `PangSim` (`cover_step`, `claim_step`, `comb_step`, `mul_step`) are re-stated for an
arbitrary index type `ι` of "equations" with an arbitrary family of indicator polynomials `g : ι → PP p`.
For `R_ρ^p` the indices are terms and `g T = polyOf (ml (chi T))` has degree `≤ d = (p-1) ρ`.  No
translation into `Res(PC_r)` is needed: the semantic rule is validated on the cube (`cd_of_cube`).
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.PCL MvPolynomial

namespace C1

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime]

section Local
variable {Ax : Set (Pang.PP p)} {D : ℕ} {ι : Type*} [DecidableEq ι]
open Pang

lemma cover_step (g : ι → PP p) (hD : 2 ≤ D) {Pi Pj f : PP p} {L0 L : Finset ι} {U : ι → PP p}
    {K Δ d : ℕ} (hf : f.totalDegree ≤ K) (hPi : Pi.totalDegree ≤ Δ) (hPj : Pj.totalDegree ≤ Δ)
    (hU : ∀ h ∈ L0, (U h).totalDegree + d ≤ Δ)
    (hg : ∀ h ∈ L0, (g h).totalDegree ≤ d)
    (hpref : 1 - Pj = ∑ h ∈ L0, U h * g h) (hbud : K + 2 * Δ ≤ D)
    (hcov : ∀ h ∈ L0, h ∈ L ∨ g h = 0)
    (herr : ∀ h ∈ L, Pi * g h * f ∈ CD Ax D) (hij : Pj * f ∈ CD Ax D) :
    Pi * f ∈ CD Ax D := by
  have hsum : ∑ h ∈ L0, U h * (Pi * g h * f) = Pi * f * ∑ h ∈ L0, U h * g h := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  have e : Pi * f = Pi * (Pj * f) + ∑ h ∈ L0, U h * (Pi * g h * f) := by
    rw [hsum, ← hpref]; ring
  rw [e]
  refine add_mem ?_ (Submodule.sum_mem _ fun h hh => ?_)
  · refine cd_mul hij ?_
    have := (totalDegree_mul _ _).trans (Nat.add_le_add hPj hf)
    omega
  · rcases hcov h hh with hL | h0
    · refine cd_mul (herr h hL) ?_
      have e1 : (Pi * g h * f).totalDegree ≤ Δ + d + K :=
        (totalDegree_mul _ _).trans (Nat.add_le_add
          ((totalDegree_mul _ _).trans (Nat.add_le_add hPi (hg h hh))) hf)
      have := hU h hh
      omega
    · rw [h0]; simp
/-- The "useful claim": `(1 - g_h) f P_L ∈ C_D` when `L ⊇ L1 \ {h}` and `L1` is a premise. -/

lemma claim_step (g : ι → PP p) (g01 : ∀ (a : Set ℕ) (k : ι), eval (indPt a) (g k) = 0 ∨ eval (indPt a) (g k) = 1)
    (hD : 2 ≤ D) {Pi Pj f : PP p} {L1 L : Finset ι} {h : ι} {U : ι → PP p}
    {K Δ d : ℕ} (hh : h ∈ L1) (hf : f.totalDegree ≤ K) (hPi : Pi.totalDegree ≤ Δ)
    (hPj : Pj.totalDegree ≤ Δ) (hU : ∀ k ∈ L1, (U k).totalDegree + d ≤ Δ)
    (hg : ∀ k ∈ L1, (g k).totalDegree ≤ d)
    (hpref : 1 - Pj = ∑ k ∈ L1, U k * g k) (hbud : K + 2 * Δ + 2 * d ≤ D)
    (hcov : ∀ k ∈ L1.erase h, k ∈ L)
    (herr : ∀ k ∈ L, Pi * g k * f ∈ CD Ax D) (hij : Pj * f ∈ CD Ax D) :
    (1 - g h) * (Pi * f) ∈ CD Ax D := by
  set X : PP p := Pi * (Pj * f) + ∑ k ∈ L1.erase h, U k * (Pi * g k * f) with hX
  have hXc : X ∈ CD Ax D := by
    refine add_mem ?_ (Submodule.sum_mem _ fun k hk => ?_)
    · refine cd_mul hij ?_
      have := (totalDegree_mul _ _).trans (Nat.add_le_add hPj hf)
      omega
    · have hk' := hcov k hk
      refine cd_mul (herr k hk') ?_
      have hk1 : k ∈ L1 := Finset.mem_of_mem_erase hk
      have e1 : (Pi * g k * f).totalDegree ≤ Δ + d + K :=
        (totalDegree_mul _ _).trans (Nat.add_le_add
          ((totalDegree_mul _ _).trans (Nat.add_le_add hPi (hg k hk1))) hf)
      have := hU k hk1
      omega
  have hXdeg : X.totalDegree ≤ K + 2 * Δ := by
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · have := (totalDegree_mul _ _).trans (Nat.add_le_add hPi ((totalDegree_mul _ _).trans (Nat.add_le_add hPj hf)))
      omega
    · refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun k hk => ?_)
      have hk1 : k ∈ L1 := Finset.mem_of_mem_erase hk
      have e1 : (Pi * g k * f).totalDegree ≤ Δ + d + K :=
        (totalDegree_mul _ _).trans (Nat.add_le_add
          ((totalDegree_mul _ _).trans (Nat.add_le_add hPi (hg k hk1))) hf)
      have := (totalDegree_mul _ _).trans (Nat.add_le_add_left e1 (U k).totalDegree)
      have := hU k hk1
      omega
  have hid : X = Pi * f * (1 - U h * g h) := by
    have hsplit : ∑ k ∈ L1, U k * g k = U h * g h + ∑ k ∈ L1.erase h, U k * g k :=
      (Finset.add_sum_erase _ _ hh).symm
    have hsum : ∑ k ∈ L1.erase h, U k * (Pi * g k * f) =
        Pi * f * ∑ k ∈ L1.erase h, U k * g k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h1 : ∑ k ∈ L1.erase h, U k * g k = 1 - Pj - U h * g h := by
      rw [hpref, hsplit]; ring
    rw [hX, hsum, h1]; ring
  have hcube : U h * g h * (1 - g h) * (Pi * f) ∈ CD Ax D := by
    refine cd_of_cube hD ?_ fun a => ?_
    · have a1 : (U h).totalDegree + d ≤ Δ := hU h hh
      have a2 := hg h hh
      have a3 : (1 - g h).totalDegree ≤ d :=
        (totalDegree_sub _ _).trans (max_le (by simp) a2)
      have a4 : (Pi * f).totalDegree ≤ Δ + K := (totalDegree_mul _ _).trans (Nat.add_le_add hPi hf)
      have a5 : (U h * g h).totalDegree ≤ (U h).totalDegree + d :=
        (totalDegree_mul _ _).trans (Nat.add_le_add_left a2 _)
      have a6 : (U h * g h * (1 - g h)).totalDegree ≤ (U h).totalDegree + d + d :=
        (totalDegree_mul _ _).trans (Nat.add_le_add a5 a3)
      have a7 := (totalDegree_mul (U h * g h * (1 - g h)) (Pi * f)).trans
        (Nat.add_le_add a6 a4)
      omega
    · rcases g01 a h with h0 | h1
      · simp [h0]
      · simp [h1]
  have : (1 - g h) * (Pi * f) = (1 - g h) * X + U h * g h * (1 - g h) * (Pi * f) := by
    rw [hid]; ring
  rw [this]
  refine add_mem ?_ hcube
  refine cd_mul hXc ?_
  have h1 : (1 - g h).totalDegree ≤ d :=
    (totalDegree_sub _ _).trans (max_le (by simp) (by have := hg h hh; omega))
  omega

lemma tele_prod {ι : Type*} (ℓ : ι → PP p) :
    ∀ S : Finset ι, (∀ i ∈ S, (1 - ℓ i).totalDegree ≤ 1) → ∃ W : ι → PP p,
      (∀ i ∈ S, (W i).totalDegree + 1 ≤ S.card) ∧
      1 = ∏ i ∈ S, (1 - ℓ i) + ∑ i ∈ S, W i * ℓ i := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; exact ⟨fun _ => 0, by simp, by simp⟩
  | insert a S ha ih =>
    intro hℓ
    obtain ⟨W, hW, hid⟩ := ih fun i hi => hℓ i (Finset.mem_insert_of_mem hi)
    refine ⟨fun i => if i = a then ∏ j ∈ S, (1 - ℓ j) else W i, ?_, ?_⟩
    · intro i hi
      rw [Finset.card_insert_of_notMem ha]
      by_cases hia : i = a
      · simp only [hia, if_true]
        have : (∏ j ∈ S, (1 - ℓ j)).totalDegree ≤ S.card :=
          (totalDegree_finset_prod _ _).trans (by
            calc ∑ j ∈ S, (1 - ℓ j).totalDegree ≤ ∑ _j ∈ S, 1 :=
                  Finset.sum_le_sum fun j hj => hℓ j (Finset.mem_insert_of_mem hj)
              _ = S.card := by simp)
        omega
      · simp only [hia, if_false]
        have := hW i ((Finset.mem_insert.1 hi).resolve_left hia)
        omega
    · rw [Finset.prod_insert ha, Finset.sum_insert ha]
      simp only [if_true]
      have : ∑ i ∈ S, (if i = a then ∏ j ∈ S, (1 - ℓ j) else W i) * ℓ i = ∑ i ∈ S, W i * ℓ i :=
        Finset.sum_congr rfl fun i hi => by
          rw [if_neg (by rintro rfl; exact ha hi)]
      rw [this]
      linear_combination hid


lemma eval_litPoly_01 (a : Set ℕ) (l : Literal) :
    eval (indPt a) (litPoly l : PP p) = 0 ∨ eval (indPt a) (litPoly l : PP p) = 1 := by
  unfold litPoly
  by_cases hp : l.pos <;> by_cases hv : l.var ∈ a <;> simp [hp, hv, indPt]

lemma totalDegree_litPoly (l : Literal) : (litPoly l : PP p).totalDegree ≤ 1 := by
  unfold litPoly
  split_ifs
  · exact (totalDegree_sub _ _).trans (max_le (by simp) (by simp))
  · simp


lemma comb_step (hD : 2 ≤ D) {Pi f g1 g2 g3 : PP p} {K Δ d : ℕ} (hf : f.totalDegree ≤ K)
    (hPi : Pi.totalDegree ≤ Δ) (hdΔ : d ≤ Δ) (hg1 : g1.totalDegree ≤ d) (hg2 : g2.totalDegree ≤ d)
    (hg3 : g3.totalDegree ≤ d) (hb : K + 2 * Δ + 2 * d ≤ D)
    (c1 : (1 - g1) * (Pi * f) ∈ CD Ax D) (c2 : (1 - g2) * (Pi * f) ∈ CD Ax D)
    (e3 : Pi * g3 * f ∈ CD Ax D)
    (hcube : ∀ a : Set ℕ, eval (indPt a) g1 * eval (indPt a) g2 * (1 - eval (indPt a) g3) = 0) :
    Pi * f ∈ CD Ax D := by
  have hPf : (Pi * f).totalDegree ≤ Δ + K := (totalDegree_mul _ _).trans (Nat.add_le_add hPi hf)
  have h1d : (1 - g1).totalDegree ≤ d := (totalDegree_sub _ _).trans (max_le (by simp) hg1)
  have h2d : (1 - g2).totalDegree ≤ d := (totalDegree_sub _ _).trans (max_le (by simp) hg2)
  have h3d : (1 - g3).totalDegree ≤ d := (totalDegree_sub _ _).trans (max_le (by simp) hg3)
  have t2 : g1 * ((1 - g2) * (Pi * f)) ∈ CD Ax D := by
    refine cd_mul c2 ?_
    have := (totalDegree_mul (1 - g2) (Pi * f)).trans (Nat.add_le_add h2d hPf)
    omega
  have t3 : g1 * g2 * (1 - g3) * (Pi * f) ∈ CD Ax D := by
    refine cd_of_cube hD ?_ fun a => ?_
    · have a1 := (totalDegree_mul g1 g2).trans (Nat.add_le_add hg1 hg2)
      have a2 := (totalDegree_mul (g1 * g2) (1 - g3)).trans (Nat.add_le_add a1 h3d)
      have a3 := (totalDegree_mul (g1 * g2 * (1 - g3)) (Pi * f)).trans (Nat.add_le_add a2 hPf)
      omega
    · have h := hcube a
      simp only [map_mul, map_sub, map_one] at h ⊢
      linear_combination (eval (indPt a) Pi * eval (indPt a) f) * h
  have t4 : g1 * g2 * (Pi * g3 * f) ∈ CD Ax D := by
    refine cd_mul e3 ?_
    have a1 := (totalDegree_mul g1 g2).trans (Nat.add_le_add hg1 hg2)
    have a2 : (Pi * g3 * f).totalDegree ≤ Δ + d + K :=
      (totalDegree_mul _ _).trans (Nat.add_le_add
        ((totalDegree_mul _ _).trans (Nat.add_le_add hPi hg3)) hf)
    omega
  have : Pi * f = (1 - g1) * (Pi * f) + g1 * ((1 - g2) * (Pi * f)) +
      g1 * g2 * (1 - g3) * (Pi * f) + g1 * g2 * (Pi * g3 * f) := by ring
  rw [this]
  exact add_mem (add_mem (add_mem c1 t2) t3) t4


lemma mul_step (hD : 2 ≤ D) {Pi f g1 g2 : PP p} {K Δ d : ℕ} (hf : f.totalDegree ≤ K)
    (hPi : Pi.totalDegree ≤ Δ) (hg1 : g1.totalDegree ≤ d) (hg2 : g2.totalDegree ≤ d)
    (hb : K + Δ + 2 * d ≤ D) (c1 : (1 - g1) * (Pi * f) ∈ CD Ax D)
    (e2 : Pi * g2 * f ∈ CD Ax D)
    (hcube : ∀ a : Set ℕ, eval (indPt a) g1 * (1 - eval (indPt a) g2) = 0) :
    Pi * f ∈ CD Ax D := by
  have hPf : (Pi * f).totalDegree ≤ Δ + K := (totalDegree_mul _ _).trans (Nat.add_le_add hPi hf)
  have h2d : (1 - g2).totalDegree ≤ d := (totalDegree_sub _ _).trans (max_le (by simp) hg2)
  have t2 : g1 * (1 - g2) * (Pi * f) ∈ CD Ax D := by
    refine cd_of_cube hD ?_ fun a => ?_
    · have a1 := (totalDegree_mul g1 (1 - g2)).trans (Nat.add_le_add hg1 h2d)
      have a3 := (totalDegree_mul (g1 * (1 - g2)) (Pi * f)).trans (Nat.add_le_add a1 hPf)
      omega
    · have h := hcube a
      simp only [map_mul, map_sub, map_one] at h ⊢
      linear_combination (eval (indPt a) Pi * eval (indPt a) f) * h
  have t3 : g1 * (Pi * g2 * f) ∈ CD Ax D := by
    refine cd_mul e2 ?_
    have a2 : (Pi * g2 * f).totalDegree ≤ Δ + d + K :=
      (totalDegree_mul _ _).trans (Nat.add_le_add
        ((totalDegree_mul _ _).trans (Nat.add_le_add hPi hg2)) hf)
    omega
  have : Pi * f = (1 - g1) * (Pi * f) + g1 * (1 - g2) * (Pi * f) + g1 * (Pi * g2 * f) := by ring
  rw [this]
  exact add_mem (add_mem c1 t2) t3


lemma init_step' (hD : 2 ≤ D) {Pi f : PP p} {C : Clause} {K Δ w d : ℕ} (G : Literal → PP p)
    (hG : ∀ l, (G l).totalDegree ≤ d) (hGc : ∀ l, G l - (1 - litPoly l) ∈ CD Ax D) (hd1 : 1 ≤ d)
    (hf : f.totalDegree ≤ K) (hPi : Pi.totalDegree ≤ Δ) (hC : C.card ≤ w)
    (hQ : clausePoly C ∈ CD Ax D) (hb1 : K + Δ + w ≤ D) (hb2 : K + Δ + d ≤ D)
    (herr : ∀ l ∈ C, Pi * G l * f ∈ CD Ax D) : Pi * f ∈ CD Ax D := by
  obtain ⟨W, hW, hid⟩ := tele_prod (fun l => (1 : PP p) - litPoly l) C (fun l _ => by
    simpa using totalDegree_litPoly (p := p) l)
  have hprod : ∏ l ∈ C, (1 - (1 - litPoly l : PP p)) = clausePoly C := by
    unfold clausePoly; simp
  rw [hprod] at hid
  have hPf : (Pi * f).totalDegree ≤ Δ + K := (totalDegree_mul _ _).trans (Nat.add_le_add hPi hf)
  have e : Pi * f = (Pi * f) * clausePoly C + ∑ l ∈ C, W l * ((1 - litPoly l) * (Pi * f)) := by
    have : ∑ l ∈ C, W l * ((1 - litPoly l) * (Pi * f)) = (∑ l ∈ C, W l * (1 - litPoly l)) * (Pi * f) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [this]; linear_combination (Pi * f) * hid
  rw [e]
  refine add_mem ?_ (Submodule.sum_mem _ fun l hl => ?_)
  · refine cd_mul hQ ?_
    have : (clausePoly C : PP p).totalDegree ≤ C.card := by
      unfold clausePoly
      refine (totalDegree_finset_prod _ _).trans ?_
      calc ∑ l ∈ C, (litPoly l : PP p).totalDegree ≤ ∑ _l ∈ C, 1 :=
            Finset.sum_le_sum fun l _ => totalDegree_litPoly l
        _ = C.card := by simp
    omega
  · have hterm : (1 - litPoly l : PP p) * (Pi * f) ∈ CD Ax D := by
      have h1 := cd_mul (hGc l) (g := Pi * f) (by
        have h2 : (G l - (1 - litPoly l)).totalDegree ≤ d :=
          (totalDegree_sub _ _).trans (max_le (hG l)
            ((totalDegree_sub _ _).trans (max_le (by simp) ((totalDegree_litPoly l).trans hd1))))
        omega)
      have h3 := sub_mem (herr l hl) h1
      convert h3 using 1
      ring
    refine cd_mul hterm ?_
    have := hW l hl
    have h4 : ((1 - litPoly l : PP p) * (Pi * f)).totalDegree ≤ 1 + (Δ + K) :=
      (totalDegree_mul _ _).trans (Nat.add_le_add
        ((totalDegree_sub _ _).trans (max_le (by simp) (totalDegree_litPoly l))) hPf)
    omega


lemma bool_step' (hD : 2 ≤ D) {Pi f g1 g2 : PP p} {K Δ d : ℕ} (hf : f.totalDegree ≤ K)
    (hPi : Pi.totalDegree ≤ Δ) (hg1 : g1.totalDegree ≤ d)
    (hg2 : g2.totalDegree ≤ d) (hb : K + Δ + d ≤ D)
    (e1 : Pi * g1 * f ∈ CD Ax D) (e2 : Pi * g2 * f ∈ CD Ax D)
    (hcube : ∀ a : Set ℕ, 1 - eval (indPt a) g1 - eval (indPt a) g2 = 0) :
    Pi * f ∈ CD Ax D := by
  have hc : Pi * f * (1 - g1 - g2) ∈ CD Ax D := by
    refine cd_of_cube hD ?_ fun a => ?_
    · have := (totalDegree_mul _ _).trans (Nat.add_le_add
        ((totalDegree_mul _ _).trans (Nat.add_le_add hPi hf))
        ((totalDegree_sub _ _).trans (max_le ((totalDegree_sub _ _).trans
          (max_le (by simp) hg1)) hg2) : (1 - g1 - g2).totalDegree ≤ d))
      omega
    · have := hcube a
      simp only [map_mul, map_sub, map_one]
      rw [this]; simp
  have : Pi * f = Pi * g1 * f + Pi * g2 * f + Pi * f * (1 - g1 - g2) := by ring
  rw [this]
  exact add_mem (add_mem e1 e2) hc

lemma prem_single' {l : List ℕ} {f : ℕ → RLine p} {a : RLine p} (h : l.map f = [a]) :
    ∃ j, l = [j] ∧ f j = a := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    cases xs with
    | nil => simp at h; exact ⟨x, rfl, h⟩
    | cons y ys => simp at h

lemma prem_pair' {l : List ℕ} {f : ℕ → RLine p} {a b : RLine p} (h : l.map f = [a, b]) :
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

end Local

section Indicators
open Pang
variable {ρ : ℕ}

/-- The indicator polynomial of a term (multilinear reduction of `chi T`). -/
def gT (T : Term p) : PP p := polyOf (PCL.ml (chi T))

lemma indPt_eq (a : Set ℕ) :
    indPt a = boolPt (F := ZMod p) (fun i => decide (i ∈ a)) := by
  funext i; simp [indPt, boolPt]

lemma eval_gT (a : Set ℕ) (T : Term p) :
    eval (indPt a) (gT T) = if TrueAt (indPt a) T then 1 else 0 := by
  unfold gT; rw [eval_polyOf, ev_ml_eq, eval_chi]

lemma gT_cube (a : Set ℕ) (T : Term p) :
    eval (indPt a) (gT T) = 0 ∨ eval (indPt a) (gT T) = 1 := by
  rw [eval_gT]; split_ifs <;> simp

lemma totalDegree_gT {T : Term p} (hT : rank T ≤ ρ) : (gT T).totalDegree ≤ (p - 1) * ρ := by
  unfold gT
  refine (totalDegree_polyOf_le _).trans ?_
  refine PCL.deg_le fun S hS => (card_le_totalDegree hS).trans ?_
  exact (totalDegree_chi T).trans (Nat.mul_le_mul_left _ hT)

lemma vars_formPoly (l : AffForm p) : ∀ v ∈ (formPoly l).vars, v ∈ l.1.support := by
  intro v hv
  unfold formPoly at hv
  have h1 := vars_add_subset _ _ hv
  rcases Finset.mem_union.1 h1 with h | h
  · have h2 := vars_sum_subset _ _ h
    obtain ⟨i, hi, hv'⟩ := Finset.mem_biUnion.1 h2
    have h3 := vars_mul _ _ hv'
    rcases Finset.mem_union.1 h3 with h4 | h4
    · simp at h4
    · rw [vars_X] at h4
      simp at h4; subst h4; exact hi
  · simp at h

lemma vars_gT {V : Finset ℕ} {T : Term p} (hT : rank T ≤ ρ) (hs : ∀ l ∈ T, l.1.support ⊆ V) :
    ∀ v ∈ (gT T).vars, v ∈ V := by
  have hmem : PCL.ml (chi T) ∈ Vk (F := ZMod p) V ((p - 1) * ρ) := by
    refine ml_mem_Vk (fun v hvv => ?_) ((totalDegree_chi T).trans (Nat.mul_le_mul_left _ hT))
    unfold chi at hvv
    have h1 := vars_prod _ hvv
    obtain ⟨l, hl, hv'⟩ := Finset.mem_biUnion.1 h1
    have h2 := (vars_sub_subset ..) hv'
    rcases Finset.mem_union.1 h2 with h3 | h3
    · simp at h3
    · exact hs l ((basisOf_spec T).1 hl) (vars_formPoly l v (vars_pow _ _ h3))
  exact fun v hvv => vars_polyOf_subset ⟨_, hmem⟩ hvv

end Indicators

section Main
open Pang
variable {Φ : CNF} {V : Finset ℕ} {ρ : ℕ}

lemma semOK_cube {T₁ : Term p} {T₂ T₃ : Option (Term p)} (hs : SemOK T₁ T₂ T₃) (a : Set ℕ) :
    TrueAt (indPt a) T₁ → (∀ T, T₂ = some T → TrueAt (indPt a) T) →
      ∃ T, T₃ = some T ∧ TrueAt (indPt a) T := by
  rw [indPt_eq]; exact hs _

lemma rank_litTerm (l : Literal) : rank (litTerm l : Term p) ≤ 1 := by
  unfold rank
  refine (finrank_span_finset_le_card (R := ZMod p) _).trans ?_
  unfold litTerm; split_ifs <;> simp

lemma lit_cube (a : Set ℕ) (l : Literal) :
    eval (indPt a) (gT (litTerm l : Term p)) = eval (indPt a) (1 - litPoly l : PP p) := by
  rw [eval_gT]
  unfold litTerm litPoly
  by_cases hp : l.pos <;> by_cases hv : l.var ∈ a <;>
    simp [TrueAt, ev_formVarSub, ev_formVar, indPt, hp, hv]

theorem c1_simulation (R : RRefutation Φ V ρ p) {D K Δ d w : ℕ} (hD : 2 ≤ D)
    (hd : d = (p - 1) * ρ) (hρ : 1 ≤ ρ) (hdΔ : d ≤ Δ) (hw : ∀ C ∈ Φ, C.card ≤ w)
    (hb1 : K + 2 * Δ + 2 * d ≤ D) (hb2 : K + Δ + w ≤ D) {f : PP p} (hf : f.totalDegree ≤ K)
    (P : ℕ → PP p) (hP : ∀ i < R.S, (P i).totalDegree ≤ Δ)
    (hpref : ∀ i < R.S, ∃ U : Term p → PP p,
      (∀ T ∈ R.line i, (U T).totalDegree + d ≤ Δ) ∧
      1 - P i = ∑ T ∈ R.line i, U T * gT T)
    (herr : ∀ i < R.S, ∀ T ∈ R.line i, P i * gT T * f ∈ CD (cnfAx Φ) D) :
    ∀ i < R.S, P i * f ∈ CD (cnfAx Φ) D := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hd1 : 1 ≤ d := by rw [hd]; exact Nat.mul_pos (by omega) hρ
  have hgdeg : ∀ T : Term p, rank T ≤ ρ → (gT T).totalDegree ≤ d := fun T hT => by
    rw [hd]; exact totalDegree_gT hT
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hbd := R.bdd i hi
    have hgi : ∀ T ∈ R.line i, (gT T).totalDegree ≤ d := fun T hT => hgdeg T (hbd T hT)
    have key : ∀ (Ls : List (RLine p)) (L : RLine p), RInfer Φ ρ Ls L →
        (R.prem i).map R.line = Ls → R.line i = L → P i * f ∈ CD (cnfAx Φ) D := by
      intro Ls L hinf hLs hL
      cases hinf with
      | init C hC =>
        have hG : ∀ l : Literal, (gT (litTerm l : Term p)).totalDegree ≤ d := fun l =>
          hgdeg _ ((rank_litTerm l).trans hρ)
        refine init_step' hD (fun l => gT (litTerm l : Term p)) hG ?_ hd1 hf (hP i hi) (hw C hC) ?_
          (by omega) (by omega) ?_
        · intro l
          refine cd_of_cube hD ?_ fun a => ?_
          · refine (totalDegree_sub _ _).trans (max_le ((hG l).trans (by omega)) ?_)
            exact (totalDegree_sub _ _).trans (max_le (by simp) ((totalDegree_litPoly l).trans (by omega)))
          · rw [map_sub, lit_cube, map_sub]; simp
        · refine mem_CD_of_pcd (PCD.ax ⟨C, hC, rfl⟩ ?_)
          have : (clausePoly C : PP p).totalDegree ≤ C.card := by
            unfold clausePoly
            refine (totalDegree_finset_prod _ _).trans ?_
            calc ∑ l ∈ C, (litPoly l : PP p).totalDegree ≤ ∑ _l ∈ C, 1 :=
                  Finset.sum_le_sum fun l _ => totalDegree_litPoly l
              _ = C.card := by simp
          have := hw C hC
          omega
        · intro l hl
          exact herr i hi _ (by rw [hL]; exact Finset.mem_image.2 ⟨l, hl, rfl⟩)
      | taut j =>
        have m1 : ({formVar j} : Term p) ∈ R.line i := by rw [hL]; simp
        have m2 : ({formVarSub j} : Term p) ∈ R.line i := by rw [hL]; simp
        refine bool_step' hD hf (hP i hi) (hgi _ m1) (hgi _ m2) (by omega)
          (herr i hi _ m1) (herr i hi _ m2) fun a => ?_
        rw [eval_gT, eval_gT]
        by_cases hv : j ∈ a <;> simp [TrueAt, ev_formVarSub, ev_formVar, indPt, hv]
      | @weak L0 L' hsub =>
        obtain ⟨j, hpj, hjL⟩ := prem_single' hLs
        have hj : j < i := R.prem_lt i hi j (by rw [hpj]; simp)
        have hjS : j < R.S := hj.trans hi
        obtain ⟨U, hU, hprefj⟩ := hpref j hjS
        have hbdj := R.bdd j hjS
        refine cover_step gT hD hf (hP i hi) (hP j hjS) hU
          (fun T hT => hgdeg T (hbdj T hT)) hprefj (by omega) ?_
          (herr i hi) (ih j hj hjS)
        intro T hT
        left
        rw [hL]; exact hsub (by rw [← hjL]; exact hT)
      | @sem1 L₁ T₁ T₃ h₁ hs L' hL' hT₃ hb =>
        obtain ⟨j, hpj, hjL⟩ := prem_single' hLs
        have hj : j < i := R.prem_lt i hi j (by rw [hpj]; simp)
        have hjS : j < R.S := hj.trans hi
        obtain ⟨U, hU, hprefj⟩ := hpref j hjS
        have hbdj := R.bdd j hjS
        have hh1 : T₁ ∈ R.line j := by rw [hjL]; exact h₁
        have c1 := claim_step gT gT_cube hD (L1 := R.line j) (L := R.line i) (h := T₁) hh1 hf
          (hP i hi) (hP j hjS) hU (fun T hT => hgdeg T (hbdj T hT)) hprefj (by omega)
          (fun k hk => by
            rw [hL]; obtain ⟨hne, hkm⟩ := Finset.mem_erase.1 hk
            exact hL' (Finset.mem_erase.2 ⟨hne, by rw [← hjL]; exact hkm⟩))
          (herr i hi) (ih j hj hjS)
        have hg1 := hgdeg T₁ (hbdj T₁ hh1)
        cases T₃ with
        | none =>
          refine mul_step (g2 := 0) hD hf (hP i hi) hg1 (by simp) (by omega) c1 (by simp) ?_
          intro a
          by_cases ht : TrueAt (indPt a) T₁
          · obtain ⟨T, hT, _⟩ := semOK_cube hs a ht (by simp)
            simp at hT
          · rw [eval_gT, if_neg ht]; simp
        | some T =>
          have hmem : T ∈ R.line i := by rw [hL]; exact hT₃ T rfl
          refine mul_step hD hf (hP i hi) hg1 (hgi _ hmem) (by omega) c1 (herr i hi _ hmem) ?_
          intro a
          by_cases ht : TrueAt (indPt a) T₁
          · obtain ⟨T', hT', h'⟩ := semOK_cube hs a ht (by simp)
            have : T' = T := (Option.some.inj hT').symm
            subst this
            rw [eval_gT, eval_gT, if_pos h']; simp
          · rw [eval_gT, if_neg ht]; simp
      | @sem2 L₁ L₂ T₁ T₂ T₃ h₁ h₂ hs L' hL₁ hL₂ hT₃ hb =>
        obtain ⟨j1, j2, hpj, hj1L, hj2L⟩ := prem_pair' hLs
        have hj1 : j1 < i := R.prem_lt i hi j1 (by rw [hpj]; simp)
        have hj2 : j2 < i := R.prem_lt i hi j2 (by rw [hpj]; simp)
        have hjS1 : j1 < R.S := hj1.trans hi
        have hjS2 : j2 < R.S := hj2.trans hi
        obtain ⟨U1, hU1, hpref1⟩ := hpref j1 hjS1
        obtain ⟨U2, hU2, hpref2⟩ := hpref j2 hjS2
        have hbd1 := R.bdd j1 hjS1
        have hbd2 := R.bdd j2 hjS2
        have hh1 : T₁ ∈ R.line j1 := by rw [hj1L]; exact h₁
        have hh2 : T₂ ∈ R.line j2 := by rw [hj2L]; exact h₂
        have c1 := claim_step gT gT_cube hD (L1 := R.line j1) (L := R.line i) (h := T₁) hh1 hf
          (hP i hi) (hP j1 hjS1) hU1 (fun T hT => hgdeg T (hbd1 T hT)) hpref1 (by omega)
          (fun k hk => by
            rw [hL]; obtain ⟨hne, hkm⟩ := Finset.mem_erase.1 hk
            exact hL₁ (Finset.mem_erase.2 ⟨hne, by rw [← hj1L]; exact hkm⟩))
          (herr i hi) (ih j1 hj1 hjS1)
        have c2 := claim_step gT gT_cube hD (L1 := R.line j2) (L := R.line i) (h := T₂) hh2 hf
          (hP i hi) (hP j2 hjS2) hU2 (fun T hT => hgdeg T (hbd2 T hT)) hpref2 (by omega)
          (fun k hk => by
            rw [hL]; obtain ⟨hne, hkm⟩ := Finset.mem_erase.1 hk
            exact hL₂ (Finset.mem_erase.2 ⟨hne, by rw [← hj2L]; exact hkm⟩))
          (herr i hi) (ih j2 hj2 hjS2)
        have hg1 := hgdeg T₁ (hbd1 T₁ hh1)
        have hg2 := hgdeg T₂ (hbd2 T₂ hh2)
        cases T₃ with
        | none =>
          refine comb_step (g3 := 0) hD hf (hP i hi) hdΔ hg1 hg2 (by simp) hb1 c1 c2 (by simp) ?_
          intro a
          by_cases ht1 : TrueAt (indPt a) T₁
          · by_cases ht2 : TrueAt (indPt a) T₂
            · obtain ⟨T, hT, _⟩ := semOK_cube hs a ht1 (by intro T hT; cases hT; exact ht2)
              simp at hT
            · rw [eval_gT a T₂, if_neg ht2]; simp
          · rw [eval_gT a T₁, if_neg ht1]; simp
        | some T =>
          have hmem : T ∈ R.line i := by rw [hL]; exact hT₃ T rfl
          refine comb_step hD hf (hP i hi) hdΔ hg1 hg2 (hgi _ hmem) hb1 c1 c2
            (herr i hi _ hmem) ?_
          intro a
          by_cases ht1 : TrueAt (indPt a) T₁
          · by_cases ht2 : TrueAt (indPt a) T₂
            · obtain ⟨T', hT', h'⟩ := semOK_cube hs a ht1 (by intro T hT; cases hT; exact ht2)
              have : T' = T := (Option.some.inj hT').symm
              subst this
              rw [eval_gT a T₁, eval_gT a T₂, eval_gT a T', if_pos ht1, if_pos ht2, if_pos h']; simp
            · rw [eval_gT a T₂, if_neg ht2]; simp
          · rw [eval_gT a T₁, if_neg ht1]; simp
    exact key _ _ (R.infer i hi) rfl rfl

/-- The final line is empty and `P = 1` there, so `f ∈ C_D`. -/
theorem c1_simulation_final (R : RRefutation Φ V ρ p) {D K Δ d w : ℕ} (hD : 2 ≤ D)
    (hd : d = (p - 1) * ρ) (hρ : 1 ≤ ρ) (hdΔ : d ≤ Δ) (hw : ∀ C ∈ Φ, C.card ≤ w)
    (hb1 : K + 2 * Δ + 2 * d ≤ D) (hb2 : K + Δ + w ≤ D) {f : PP p} (hf : f.totalDegree ≤ K)
    (P : ℕ → PP p) (hP : ∀ i < R.S, (P i).totalDegree ≤ Δ)
    (hpref : ∀ i < R.S, ∃ U : Term p → PP p,
      (∀ T ∈ R.line i, (U T).totalDegree + d ≤ Δ) ∧
      1 - P i = ∑ T ∈ R.line i, U T * gT T)
    (herr : ∀ i < R.S, ∀ T ∈ R.line i, P i * gT T * f ∈ CD (cnfAx Φ) D) :
    f ∈ CD (cnfAx Φ) D := by
  have hS := R.S_pos
  have hlt : R.S - 1 < R.S := by omega
  have h1 := c1_simulation R hD hd hρ hdΔ hw hb1 hb2 hf P hP hpref herr (R.S - 1) hlt
  obtain ⟨U, _, hU⟩ := hpref (R.S - 1) hlt
  rw [R.last, Finset.sum_empty] at hU
  have : P (R.S - 1) = 1 := by linear_combination -hU
  rwa [this, one_mul] at h1

end Main

end

end C1
