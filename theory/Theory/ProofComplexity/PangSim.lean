import Theory.ProofComplexity.PangPrefix
import Theory.ProofComplexity.PangDag

/-!
# Pang route, layer G (part 3): simulation of a dag-like refutation in low degree PC (Prop 5.1)
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.PCL MvPolynomial

namespace Pang

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime]

section Local
variable {Ax : Set (PP p)} {D : ℕ}

/-- Indicators are `0/1`-valued on the cube. -/
lemma gInd_cube (a : Set ℕ) (h : PP p) :
    eval (indPt a) (gInd h) = 0 ∨ eval (indPt a) (gInd h) = 1 := by
  rw [eval_gInd_eq]; split_ifs <;> simp

/-- The "cover" step: weakening, contraction and deletion of false constants. -/
lemma cover_step (hD : 2 ≤ D) {Pi Pj f : PP p} {L0 L : Finset (PP p)} {U : PP p → PP p}
    {K Δ d : ℕ} (hf : f.totalDegree ≤ K) (hPi : Pi.totalDegree ≤ Δ) (hPj : Pj.totalDegree ≤ Δ)
    (hU : ∀ h ∈ L0, (U h).totalDegree + d ≤ Δ)
    (hg : ∀ h ∈ L0, (gInd h).totalDegree ≤ d)
    (hpref : 1 - Pj = ∑ h ∈ L0, U h * gInd h) (hbud : K + 2 * Δ ≤ D)
    (hcov : ∀ h ∈ L0, h ∈ L ∨ gInd h = 0)
    (herr : ∀ h ∈ L, Pi * gInd h * f ∈ CD Ax D) (hij : Pj * f ∈ CD Ax D) :
    Pi * f ∈ CD Ax D := by
  have hsum : ∑ h ∈ L0, U h * (Pi * gInd h * f) = Pi * f * ∑ h ∈ L0, U h * gInd h := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  have e : Pi * f = Pi * (Pj * f) + ∑ h ∈ L0, U h * (Pi * gInd h * f) := by
    rw [hsum, ← hpref]; ring
  rw [e]
  refine add_mem ?_ (Submodule.sum_mem _ fun h hh => ?_)
  · refine cd_mul hij ?_
    have := (totalDegree_mul _ _).trans (Nat.add_le_add hPj hf)
    omega
  · rcases hcov h hh with hL | h0
    · refine cd_mul (herr h hL) ?_
      have e1 : (Pi * gInd h * f).totalDegree ≤ Δ + d + K :=
        (totalDegree_mul _ _).trans (Nat.add_le_add
          ((totalDegree_mul _ _).trans (Nat.add_le_add hPi (hg h hh))) hf)
      have := hU h hh
      omega
    · rw [h0]; simp
/-- The "useful claim": `(1 - g_h) f P_L ∈ C_D` when `L ⊇ L1 \ {h}` and `L1` is a premise. -/
lemma claim_step (hD : 2 ≤ D) {Pi Pj f : PP p} {L1 L : Finset (PP p)} {h : PP p} {U : PP p → PP p}
    {K Δ d : ℕ} (hh : h ∈ L1) (hf : f.totalDegree ≤ K) (hPi : Pi.totalDegree ≤ Δ)
    (hPj : Pj.totalDegree ≤ Δ) (hU : ∀ k ∈ L1, (U k).totalDegree + d ≤ Δ)
    (hg : ∀ k ∈ L1, (gInd k).totalDegree ≤ d)
    (hpref : 1 - Pj = ∑ k ∈ L1, U k * gInd k) (hbud : K + 2 * Δ + 2 * d ≤ D)
    (hcov : ∀ k ∈ L1.erase h, k ∈ L)
    (herr : ∀ k ∈ L, Pi * gInd k * f ∈ CD Ax D) (hij : Pj * f ∈ CD Ax D) :
    (1 - gInd h) * (Pi * f) ∈ CD Ax D := by
  set X : PP p := Pi * (Pj * f) + ∑ k ∈ L1.erase h, U k * (Pi * gInd k * f) with hX
  have hXc : X ∈ CD Ax D := by
    refine add_mem ?_ (Submodule.sum_mem _ fun k hk => ?_)
    · refine cd_mul hij ?_
      have := (totalDegree_mul _ _).trans (Nat.add_le_add hPj hf)
      omega
    · have hk' := hcov k hk
      refine cd_mul (herr k hk') ?_
      have hk1 : k ∈ L1 := Finset.mem_of_mem_erase hk
      have e1 : (Pi * gInd k * f).totalDegree ≤ Δ + d + K :=
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
      have e1 : (Pi * gInd k * f).totalDegree ≤ Δ + d + K :=
        (totalDegree_mul _ _).trans (Nat.add_le_add
          ((totalDegree_mul _ _).trans (Nat.add_le_add hPi (hg k hk1))) hf)
      have := (totalDegree_mul _ _).trans (Nat.add_le_add_left e1 (U k).totalDegree)
      have := hU k hk1
      omega
  have hid : X = Pi * f * (1 - U h * gInd h) := by
    have hsplit : ∑ k ∈ L1, U k * gInd k = U h * gInd h + ∑ k ∈ L1.erase h, U k * gInd k :=
      (Finset.add_sum_erase _ _ hh).symm
    have hsum : ∑ k ∈ L1.erase h, U k * (Pi * gInd k * f) =
        Pi * f * ∑ k ∈ L1.erase h, U k * gInd k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h1 : ∑ k ∈ L1.erase h, U k * gInd k = 1 - Pj - U h * gInd h := by
      rw [hpref, hsplit]; ring
    rw [hX, hsum, h1]; ring
  have hcube : U h * gInd h * (1 - gInd h) * (Pi * f) ∈ CD Ax D := by
    refine cd_of_cube hD ?_ fun a => ?_
    · have a1 : (U h).totalDegree + d ≤ Δ := hU h hh
      have a2 := hg h hh
      have a3 : (1 - gInd h).totalDegree ≤ d :=
        (totalDegree_sub _ _).trans (max_le (by simp) a2)
      have a4 : (Pi * f).totalDegree ≤ Δ + K := (totalDegree_mul _ _).trans (Nat.add_le_add hPi hf)
      have a5 : (U h * gInd h).totalDegree ≤ (U h).totalDegree + d :=
        (totalDegree_mul _ _).trans (Nat.add_le_add_left a2 _)
      have a6 : (U h * gInd h * (1 - gInd h)).totalDegree ≤ (U h).totalDegree + d + d :=
        (totalDegree_mul _ _).trans (Nat.add_le_add a5 a3)
      have a7 := (totalDegree_mul (U h * gInd h * (1 - gInd h)) (Pi * f)).trans
        (Nat.add_le_add a6 a4)
      omega
    · rcases gInd_cube a h with h0 | h1
      · simp [h0]
      · simp [h1]
  have : (1 - gInd h) * (Pi * f) = (1 - gInd h) * X + U h * gInd h * (1 - gInd h) * (Pi * f) := by
    rw [hid]; ring
  rw [this]
  refine add_mem ?_ hcube
  refine cd_mul hXc ?_
  have h1 : (1 - gInd h).totalDegree ≤ d :=
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

lemma cd_gInd_sub_lit (hD : 2 ≤ D) {d : ℕ} (hd : p - 1 ≤ d) (hdD : d ≤ D) (l : Literal) :
    gInd (litPoly l : PP p) - (1 - litPoly l) ∈ CD Ax D := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  refine cd_of_cube hD ?_ fun a => ?_
  · refine (totalDegree_sub _ _).trans (max_le ((totalDegree_gInd (totalDegree_litPoly l)).trans (hd.trans hdD)) ?_)
    refine (totalDegree_sub _ _).trans (max_le (by simp) ((totalDegree_litPoly l).trans (by omega)))
  · rw [map_sub, map_sub, eval_gInd_eq, map_one]
    rcases eval_litPoly_01 (p := p) a l with h0 | h1
    · simp [h0]
    · have : (1 : ZMod p) ≠ 0 := one_ne_zero
      simp [h1, this]

lemma init_step (hD : 2 ≤ D) {Pi f : PP p} {C : Clause} {K Δ w d : ℕ} (hd : p - 1 ≤ d)
    (hf : f.totalDegree ≤ K) (hPi : Pi.totalDegree ≤ Δ) (hC : C.card ≤ w)
    (hQ : clausePoly C ∈ CD Ax D) (hb1 : K + Δ + w ≤ D) (hb2 : K + Δ + d ≤ D)
    (herr : ∀ l ∈ C, Pi * gInd (litPoly l : PP p) * f ∈ CD Ax D) : Pi * f ∈ CD Ax D := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
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
      have h1 := cd_mul (cd_gInd_sub_lit (Ax := Ax) hD hd (by omega) l) (g := Pi * f) (by
        have := totalDegree_gInd (p := p) (totalDegree_litPoly l)
        have h2 : (gInd (litPoly l : PP p) - (1 - litPoly l)).totalDegree ≤ d := by
          refine (totalDegree_sub _ _).trans (max_le (this.trans hd) ?_)
          exact (totalDegree_sub _ _).trans (max_le (by simp) ((totalDegree_litPoly l).trans (by omega)))
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

lemma gInd_zero : gInd (0 : PP p) = 1 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  unfold gInd
  rw [zero_pow (by omega), sub_zero, PCL.ml_one, polyOf_single]; simp

lemma bool_step (hD : 2 ≤ D) {Pi f : PP p} {i : ℕ} {K Δ d : ℕ} (hf : f.totalDegree ≤ K)
    (hPi : Pi.totalDegree ≤ Δ) (hg1 : (gInd (X i : PP p)).totalDegree ≤ d)
    (hg2 : (gInd (X i - 1 : PP p)).totalDegree ≤ d) (hb : K + Δ + d ≤ D)
    (e1 : Pi * gInd (X i : PP p) * f ∈ CD Ax D) (e2 : Pi * gInd (X i - 1 : PP p) * f ∈ CD Ax D) :
    Pi * f ∈ CD Ax D := by
  have hcube : Pi * f * (1 - gInd (X i : PP p) - gInd (X i - 1 : PP p)) ∈ CD Ax D := by
    refine cd_of_cube hD ?_ fun a => ?_
    · have := (totalDegree_mul _ _).trans (Nat.add_le_add
        ((totalDegree_mul _ _).trans (Nat.add_le_add hPi hf))
        ((totalDegree_sub _ _).trans (max_le ((totalDegree_sub _ _).trans
          (max_le (by simp) hg1)) hg2) : (1 - gInd (X i : PP p) - gInd (X i - 1 : PP p)).totalDegree ≤ d))
      omega
    · have hx : eval (indPt a) (X i : PP p) = 0 ∨ eval (indPt a) (X i : PP p) = 1 := by
        by_cases h : i ∈ a <;> simp [indPt, h]
      rw [map_mul, map_sub, map_sub, eval_gInd_eq, eval_gInd_eq, map_one, map_sub, eval_X, map_one]
      rcases hx with h0 | h1
      · rw [eval_X] at h0
        have : (0 : ZMod p) - 1 ≠ 0 := by simp
        simp [h0, this]
      · rw [eval_X] at h1
        simp [h1]
  have : Pi * f = Pi * gInd (X i : PP p) * f + Pi * gInd (X i - 1 : PP p) * f +
      Pi * f * (1 - gInd (X i : PP p) - gInd (X i - 1 : PP p)) := by ring
  rw [this]
  exact add_mem (add_mem e1 e2) hcube

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

lemma prem_single {l : List ℕ} {f : ℕ → Line p} {a : Line p} (h : l.map f = [a]) :
    ∃ j, l = [j] ∧ f j = a := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    cases xs with
    | nil => simp at h; exact ⟨x, rfl, h⟩
    | cons y ys => simp at h

lemma prem_pair {l : List ℕ} {f : ℕ → Line p} {a b : Line p} (h : l.map f = [a, b]) :
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

section Main
variable {Φ : CNF} {V : Finset ℕ}

/-- **Pang Proposition 5.1** (simulation in PC), for `r = 1`, `d = p - 1`, `Δ = t d^2`. -/
theorem simulation (R : Refutation Φ V p) {D K t w : ℕ} (hD : 2 ≤ D) (ht : 1 ≤ t)
    (hw : ∀ C ∈ Φ, C.card ≤ w)
    (hb1 : K + 2 * (t * ((p - 1) * (p - 1))) + 2 * (p - 1) ≤ D)
    (hb2 : K + t * ((p - 1) * (p - 1)) + w ≤ D) {f : PP p} (hf : f.totalDegree ≤ K)
    (P : ℕ → PP p) (hP : ∀ i < R.S, (P i).totalDegree ≤ t * ((p - 1) * (p - 1)))
    (hpref : ∀ i < R.S, ∃ U : PP p → PP p,
      (∀ h ∈ R.line i, (U h).totalDegree + (p - 1) ≤ t * ((p - 1) * (p - 1))) ∧
      1 - P i = ∑ h ∈ R.line i, U h * gInd h)
    (herr : ∀ i < R.S, ∀ h ∈ R.line i, P i * gInd h * f ∈ CD (cnfAx Φ) D) :
    ∀ i < R.S, P i * f ∈ CD (cnfAx Φ) D := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  set d := p - 1 with hd
  set Δ := t * (d * d) with hΔ
  have hdΔ : d ≤ Δ := by
    have : d ≤ d * d := Nat.le_mul_self d
    nlinarith
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hwf := R.wf i hi
    have hgi : ∀ h ∈ R.line i, (gInd h).totalDegree ≤ d := fun h hh => totalDegree_gInd (hwf h hh).1
    have key : ∀ (Ls : List (Line p)) (L : Line p), Infer Φ V Ls L →
        (R.prem i).map R.line = Ls → R.line i = L → P i * f ∈ CD (cnfAx Φ) D := by
      intro Ls L hinf hLs hL
      cases hinf with
      | init C hC =>
        refine init_step hD (le_refl d) hf (hP i hi) (hw C hC) ?_ (by omega) (by omega) ?_
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
      | zero =>
        have := herr i hi 0 (by rw [hL]; simp)
        rwa [gInd_zero, mul_one] at this
      | bool j hj =>
        refine bool_step hD hf (hP i hi) (hgi (X j) (by rw [hL]; simp))
          (hgi (X j - 1) (by rw [hL]; simp))
          (by omega) (herr i hi (X j) (by rw [hL]; simp)) (herr i hi (X j - 1) (by rw [hL]; simp))
      | @weak L0 L' hsub =>
        obtain ⟨j, hpj, hjL⟩ := prem_single hLs
        have hj : j < i := R.prem_lt i hi j (by rw [hpj]; simp)
        have hjS : j < R.S := hj.trans hi
        obtain ⟨U, hU, hprefj⟩ := hpref j hjS
        have hwfj := R.wf j hjS
        refine cover_step (L0 := R.line j) (L := R.line i) hD hf (hP i hi) (hP j hjS) hU
          (fun h hh => totalDegree_gInd (hwfj h hh).1) hprefj (by omega) ?_
          (herr i hi) (ih j hj hjS)
        intro h hh
        left
        rw [hL]; exact hsub (by rw [← hjL]; exact hh)
      | @falseConst L0 c hc hmem L' h =>
        obtain ⟨j, hpj, hjL⟩ := prem_single hLs
        have hj : j < i := R.prem_lt i hi j (by rw [hpj]; simp)
        have hjS : j < R.S := hj.trans hi
        obtain ⟨U, hU, hprefj⟩ := hpref j hjS
        have hwfj := R.wf j hjS
        refine cover_step (L0 := R.line j) (L := R.line i) hD hf (hP i hi) (hP j hjS) hU
          (fun h hh => totalDegree_gInd (hwfj h hh).1) hprefj (by omega) ?_
          (herr i hi) (ih j hj hjS)
        intro h' hh
        by_cases heq : h' = C c
        · right; rw [heq]; exact gInd_const hc
        · left; rw [hL]
          exact h (Finset.mem_erase.2 ⟨heq, by rw [← hjL]; exact hh⟩)
      | @comb L₁ L₂ h1 h2 hh1 hh2 a b L' h =>
        obtain ⟨j1, j2, hpj, hj1L, hj2L⟩ := prem_pair hLs
        have hj1 : j1 < i := R.prem_lt i hi j1 (by rw [hpj]; simp)
        have hj2 : j2 < i := R.prem_lt i hi j2 (by rw [hpj]; simp)
        have hjS1 : j1 < R.S := hj1.trans hi
        have hjS2 : j2 < R.S := hj2.trans hi
        obtain ⟨U1, hU1, hpref1⟩ := hpref j1 hjS1
        obtain ⟨U2, hU2, hpref2⟩ := hpref j2 hjS2
        have hwf1 := R.wf j1 hjS1
        have hwf2 := R.wf j2 hjS2
        have hh1' : h1 ∈ R.line j1 := by rw [hj1L]; exact hh1
        have hh2' : h2 ∈ R.line j2 := by rw [hj2L]; exact hh2
        have hmem3 : (C a * h1 + C b * h2 : PP p) ∈ R.line i := by
          rw [hL]; exact h (Finset.mem_insert_self _ _)
        have c1 := claim_step (L1 := R.line j1) (L := R.line i) (h := h1) hD hh1' hf (hP i hi)
          (hP j1 hjS1) hU1 (fun k hk => totalDegree_gInd (hwf1 k hk).1) hpref1 (by omega)
          (fun k hk => by
            rw [hL]; refine h (Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_))
            rw [← hj1L]; exact hk)
          (herr i hi) (ih j1 hj1 hjS1)
        have c2 := claim_step (L1 := R.line j2) (L := R.line i) (h := h2) hD hh2' hf (hP i hi)
          (hP j2 hjS2) hU2 (fun k hk => totalDegree_gInd (hwf2 k hk).1) hpref2 (by omega)
          (fun k hk => by
            rw [hL]; refine h (Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_))
            rw [← hj2L]; exact hk)
          (herr i hi) (ih j2 hj2 hjS2)
        refine comb_step hD hf (hP i hi) hdΔ (totalDegree_gInd (hwf1 h1 hh1').1)
          (totalDegree_gInd (hwf2 h2 hh2').1) (hgi _ hmem3) hb1 c1 c2 (herr i hi _ hmem3) ?_
        intro a'
        rw [eval_gInd_eq, eval_gInd_eq, eval_gInd_eq]
        by_cases e1 : eval (indPt a') h1 = 0
        · by_cases e2 : eval (indPt a') h2 = 0
          · have : eval (indPt a') (C a * h1 + C b * h2 : PP p) = 0 := by
              simp [e1, e2]
            simp [this]
          · simp [e2]
        · simp [e1]
      | @mul L0 h1 hh1 g' hdeg hvars L' h =>
        obtain ⟨j, hpj, hjL⟩ := prem_single hLs
        have hj : j < i := R.prem_lt i hi j (by rw [hpj]; simp)
        have hjS : j < R.S := hj.trans hi
        obtain ⟨U, hU, hprefj⟩ := hpref j hjS
        have hwfj := R.wf j hjS
        have hh1' : h1 ∈ R.line j := by rw [hjL]; exact hh1
        have hmem : (h1 * g' : PP p) ∈ R.line i := by rw [hL]; exact h (Finset.mem_insert_self _ _)
        have c1 := claim_step (L1 := R.line j) (L := R.line i) (h := h1) hD hh1' hf (hP i hi)
          (hP j hjS) hU (fun k hk => totalDegree_gInd (hwfj k hk).1) hprefj (by omega)
          (fun k hk => by
            rw [hL]; refine h (Finset.mem_insert_of_mem ?_)
            rw [← hjL]; exact hk)
          (herr i hi) (ih j hj hjS)
        refine mul_step hD hf (hP i hi) (totalDegree_gInd (hwfj h1 hh1').1) (hgi _ hmem)
          (by omega) c1 (herr i hi _ hmem) ?_
        intro a'
        rw [eval_gInd_eq, eval_gInd_eq]
        by_cases e1 : eval (indPt a') h1 = 0
        · have : eval (indPt a') (h1 * g' : PP p) = 0 := by simp [e1]
          simp [this]
        · simp [e1]
    exact key _ _ (R.infer i hi) rfl rfl

/-- The final line is empty and `P = 1` there, so `f ∈ C_D`. -/
theorem simulation_final (R : Refutation Φ V p) {D K t w : ℕ} (hD : 2 ≤ D) (ht : 1 ≤ t)
    (hw : ∀ C ∈ Φ, C.card ≤ w)
    (hb1 : K + 2 * (t * ((p - 1) * (p - 1))) + 2 * (p - 1) ≤ D)
    (hb2 : K + t * ((p - 1) * (p - 1)) + w ≤ D) {f : PP p} (hf : f.totalDegree ≤ K)
    (P : ℕ → PP p) (hP : ∀ i < R.S, (P i).totalDegree ≤ t * ((p - 1) * (p - 1)))
    (hpref : ∀ i < R.S, ∃ U : PP p → PP p,
      (∀ h ∈ R.line i, (U h).totalDegree + (p - 1) ≤ t * ((p - 1) * (p - 1))) ∧
      1 - P i = ∑ h ∈ R.line i, U h * gInd h)
    (herr : ∀ i < R.S, ∀ h ∈ R.line i, P i * gInd h * f ∈ CD (cnfAx Φ) D) :
    f ∈ CD (cnfAx Φ) D := by
  have hS := R.S_pos
  have hlt : R.S - 1 < R.S := by omega
  have h1 := simulation R hD ht hw hb1 hb2 hf P hP hpref herr (R.S - 1) hlt
  obtain ⟨U, _, hU⟩ := hpref (R.S - 1) hlt
  rw [R.last, Finset.sum_empty] at hU
  have : P (R.S - 1) = 1 := by linear_combination -hU
  rwa [this, one_mul] at h1

end Main


end

end Pang
