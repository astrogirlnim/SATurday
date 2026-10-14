import Theory.ProofComplexity.PangHyp
import Theory.ProofComplexity.PangAbsorb

/-!
# Pang route: Corollary 3.4 proper (Frobenius hypothesis for multiplication maps)

For polynomials `g_i` of degree `≤ a`, `h_j` of degree `≤ b` over `F_p`, a finite dimensional space
`U` of polynomials of degree `≤ k`, and `b + k + p a ≤ D`, `2 ≤ D`, the maps
`M_i : U → (P / C_D)^t, f ↦ ([g_i h_j f])_j` satisfy the polynomial-coefficient Frobenius hypothesis
`AH` (`ah_mult`), hence `pang_retention_lin` applies (`pang_cor34`).

The argument works with `λ`-polynomials whose coefficients are polynomials in `x`
(`MvPolynomial (Fin s) P`), so no base change lemma is needed: absorption is applied coefficientwise.
-/

set_option linter.unusedSectionVars false

open SATurday.ProofComplexity
namespace Pang
open MvPolynomial

noncomputable section

section Aux
variable {R : Type*} [CommRing R] {s : ℕ}

lemma coeff_X_pow_mul_gen (e : ℕ) (i : Fin s) (q : MvPolynomial (Fin s) R) (β : Fin s →₀ ℕ) :
    coeff β (X i ^ e * q) = if e ≤ β i then coeff (β - Finsupp.single i e) q else 0 := by
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  simp only [one_mul, Finsupp.single_le_iff]

/-- All `λ`-coefficients have `x`-degree `≤ m`. -/
def DegLe {σ : Type*} (m : ℕ) (Ξ : MvPolynomial σ (MvPolynomial ℕ (ZMod p))) : Prop :=
  ∀ β, (coeff β Ξ).totalDegree ≤ m

end Aux

variable {p : ℕ} [Fact p.Prime] {s t : ℕ}

abbrev PP (p : ℕ) [Fact p.Prime] := MvPolynomial ℕ (ZMod p)

section Deg
variable {σ : Type*} [DecidableEq σ] {m n : ℕ}

lemma DegLe.mono {Ξ : MvPolynomial σ (PP p)} (h : DegLe m Ξ) (hmn : m ≤ n) : DegLe n Ξ :=
  fun β => (h β).trans hmn

lemma DegLe.add {Ξ Θ : MvPolynomial σ (PP p)} (h : DegLe m Ξ) (h' : DegLe m Θ) : DegLe m (Ξ + Θ) :=
  fun β => by rw [coeff_add]; exact (totalDegree_add _ _).trans (max_le (h β) (h' β))

lemma DegLe.sum {ι : Type*} (S : Finset ι) {f : ι → MvPolynomial σ (PP p)}
    (h : ∀ i ∈ S, DegLe m (f i)) : DegLe m (∑ i ∈ S, f i) := fun β => by
  rw [coeff_sum]
  exact (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i hi => h i hi β)

lemma DegLe.C (c : PP p) : DegLe c.totalDegree (C c : MvPolynomial σ (PP p)) := fun β => by
  rw [coeff_C]; split_ifs
  · exact le_rfl
  · simp

lemma DegLe.X (i : σ) : DegLe 0 (X i : MvPolynomial σ (PP p)) := fun β => by
  rw [coeff_X']; split_ifs <;> simp

lemma DegLe.mul {Ξ Θ : MvPolynomial σ (PP p)} (h : DegLe m Ξ) (h' : DegLe n Θ) :
    DegLe (m + n) (Ξ * Θ) := fun β => by
  rw [coeff_mul]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun x _ => ?_)
  exact (totalDegree_mul _ _).trans (Nat.add_le_add (h _) (h' _))

lemma DegLe.pow {Ξ : MvPolynomial σ (PP p)} (h : DegLe m Ξ) (n : ℕ) : DegLe (n * m) (Ξ ^ n) := by
  induction n with
  | zero => intro β; rw [pow_zero, coeff_one]; split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul h
    rwa [show n * m + m = (n + 1) * m by ring] at this

end Deg


section Main
variable {D : ℕ} {Ax : Set (PP p)}

/-- Coefficient `β` of `∑_i λ_i^e c_i u(λ)`. -/
def Pshift (e : ℕ) (c : Fin s → PP p) (u : (Fin s →₀ ℕ) → PP p) (β : Fin s →₀ ℕ) : PP p :=
  ∑ i, if e ≤ β i then c i * u (β - Finsupp.single i e) else 0

/-- The `λ`-polynomial with coefficients `u_α`. -/
def Phi (u : (Fin s →₀ ℕ) → PP p) (hfin : (Function.support u).Finite) :
    MvPolynomial (Fin s) (PP p) :=
  ∑ α ∈ hfin.toFinset, monomial α (u α)

lemma coeff_Phi (u : (Fin s →₀ ℕ) → PP p) (hfin : (Function.support u).Finite) (β : Fin s →₀ ℕ) :
    coeff β (Phi u hfin) = u β := by
  classical
  unfold Phi
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at h
    exact h.symm

lemma coeff_shift (e : ℕ) (c : Fin s → PP p) (u : (Fin s →₀ ℕ) → PP p)
    (hfin : (Function.support u).Finite) (β : Fin s →₀ ℕ) :
    coeff β (∑ i, X i ^ e * (C (c i) * Phi u hfin)) = Pshift e c u β := by
  rw [coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_X_pow_mul_gen, coeff_C_mul, coeff_Phi]

lemma coeff_mul_mem {m₁ m₂ : ℕ} {Ψ Ξ : MvPolynomial (Fin s) (PP p)}
    (hΨ : ∀ β, coeff β Ψ ∈ CD Ax D) (hΨd : DegLe m₁ Ψ) (hΞ : DegLe m₂ Ξ) (hm : m₁ + m₂ ≤ D) :
    ∀ β, coeff β (Ξ * Ψ) ∈ CD Ax D := by
  intro β
  rw [coeff_mul]
  refine Submodule.sum_mem _ fun x _ => ?_
  exact cd_mul (hΨ x.2) (by have := hΞ x.1; have := hΨd x.2; omega)

/-- The multiplication map `f ↦ ([g h_j f])_j` from `U` to `(P / C_D)^t`. -/
def multMap (Ax : Set (PP p)) (D : ℕ) (U : Submodule (ZMod p) (PP p)) (h : Fin t → PP p)
    (g : PP p) : U →ₗ[ZMod p] (Fin t → PP p ⧸ CD Ax D) :=
  LinearMap.pi fun j => (CD Ax D).mkQ ∘ₗ (LinearMap.mulLeft (ZMod p) (g * h j)) ∘ₗ U.subtype

lemma totalDegree_frob_le {g : PP p} {a : ℕ} (hg : g.totalDegree ≤ a) :
    (g ^ p - g).totalDegree ≤ p * a := by
  refine (totalDegree_sub _ _).trans (max_le ((totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left _ hg)) (hg.trans ?_))
  have : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  nlinarith

/-- **Frobenius hypothesis for multiplication maps** (Pang Cor. 3.4, the kernel inclusion), in
polynomial-coefficient form. -/
theorem ah_mult (hD : 2 ≤ D) (U : Submodule (ZMod p) (PP p)) {k a b : ℕ}
    (hU : ∀ f ∈ U, f.totalDegree ≤ k) (g : Fin s → PP p) (h : Fin t → PP p)
    (hg : ∀ i, (g i).totalDegree ≤ a) (hh : ∀ j, (h j).totalDegree ≤ b)
    (hbud : b + k + p * a ≤ D) :
    AH (fun i => multMap Ax D U h (g i)) := by
  classical
  intro u hfin h1 β
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  let uP : (Fin s →₀ ℕ) → PP p := fun α => (u α : PP p)
  have hfinP : (Function.support uP).Finite := by
    refine hfin.subset fun α hα => ?_
    simp only [Function.mem_support, ne_eq] at hα ⊢
    intro h0; apply hα; simp [uP, h0]
  have hshift : ∀ e γ j, shiftSum e (fun i x => multMap Ax D U h (g i) x) u γ j =
      (CD Ax D).mkQ (Pshift e (fun i => g i * h j) uP γ) := by
    intro e γ j
    unfold shiftSum Pshift
    rw [Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs
    · simp [multMap, uP, mul_assoc]
    · simp
  have h1' : ∀ γ j, Pshift 1 (fun i => g i * h j) uP γ ∈ CD Ax D := by
    intro γ j
    have := congrFun (h1 γ) j
    rw [hshift] at this
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  suffices H : ∀ γ j, Pshift p (fun i => g i * h j) uP γ ∈ CD Ax D by
    funext j
    rw [hshift]
    exact (Submodule.Quotient.mk_eq_zero _).2 (H β j)
  intro γ j
  set Φ := Phi uP hfinP with hΦ
  set q : MvPolynomial (Fin s) (PP p) := ∑ i, X i * C (g i) with hq
  have hΦd : DegLe k Φ := fun β => by
    rw [hΦ, coeff_Phi]; exact hU _ (u β).2
  have hqd : DegLe a q := by
    have : DegLe (0 + a) q := DegLe.sum _ fun i _ => by
      have := (DegLe.X (p := p) i).mul (DegLe.C (g i))
      exact this.mono (by have := hg i; omega) |>.mono le_rfl
    simpa using this
  have hhd : DegLe b (C (h j) : MvPolynomial (Fin s) (PP p)) := (DegLe.C (h j)).mono (hh j)
  -- Ψ₁ = C h * q * Φ
  set Ψ₁ : MvPolynomial (Fin s) (PP p) := C (h j) * q * Φ with hΨ₁
  have hΨ₁eq : Ψ₁ = ∑ i, X i ^ 1 * (C (g i * h j) * Φ) := by
    rw [hΨ₁, hq, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_one, map_mul]; ring
  have hΨ₁c : ∀ β, coeff β Ψ₁ ∈ CD Ax D := fun β => by
    rw [hΨ₁eq, coeff_shift]; exact h1' β j
  have hΨ₁d : DegLe (b + a + k) Ψ₁ := (hhd.mul hqd).mul hΦd
  -- Ψ₂ = q^(p-1) * Ψ₁ = C h * q^p * Φ
  have hm : b + a + k + (p - 1) * a ≤ D := by
    have : (p - 1) * a + a = p * a := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hp1]
    omega
  have hΨ₂c := coeff_mul_mem hΨ₁c hΨ₁d (hqd.pow (p - 1)) hm
  have hqp : q ^ p = ∑ i, X i ^ p * C (g i ^ p) := by
    haveI : CharP (MvPolynomial (Fin s) (PP p)) p := inferInstance
    rw [hq, sum_pow_char]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, ← map_pow]
  have hΨ₂eq : q ^ (p - 1) * Ψ₁ = ∑ i, X i ^ p * (C (h j * g i ^ p) * Φ) := by
    have : q ^ (p - 1) * Ψ₁ = C (h j) * q ^ p * Φ := by
      have hpq : q ^ p = q ^ (p - 1) * q := by
        rw [← pow_succ]; congr 1; omega
      rw [hΨ₁, hpq]; ring
    rw [this, hqp, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]; ring
  -- Ψ₃
  have hΨ₃c : ∀ β, coeff β (∑ i, X i ^ p * (C (h j * (g i ^ p - g i)) * Φ)) ∈ CD Ax D := by
    intro β
    rw [coeff_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [coeff_X_pow_mul_gen, coeff_C_mul, hΦ, coeff_Phi]
    split_ifs
    · have hf : g i ^ p - g i ∈ CD Ax D := cd_frobenius hD (hg i) (le_trans (Nat.le_add_left _ _) hbud)
      have := cd_mul (Ax := Ax) (D := D) hf (g := h j * uP (β - Finsupp.single i p)) (by
        have h2 := totalDegree_mul (h j) (uP (β - Finsupp.single i p))
        have h3 : (uP (β - Finsupp.single i p)).totalDegree ≤ k := hU _ (u _).2
        have h4 := totalDegree_frob_le (hg i)
        have h5 := hh j
        omega)
      convert this using 1
      ring_nf
    · exact zero_mem _
  have hfinal : ∑ i, X i ^ p * (C (g i * h j) * Φ) =
      q ^ (p - 1) * Ψ₁ - ∑ i, X i ^ p * (C (h j * (g i ^ p - g i)) * Φ) := by
    rw [hΨ₂eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, ← sub_mul, ← map_sub]
    congr 2
    ring_nf
  have := (CD Ax D).sub_mem (hΨ₂c γ) (hΨ₃c γ)
  rw [← coeff_sub, ← hfinal, coeff_shift] at this
  exact this

lemma multMap_sum (U : Submodule (ZMod p) (PP p)) (h : Fin t → PP p) (g : Fin s → PP p)
    (c : Fin s → ZMod p) :
    (∑ i, c i • multMap Ax D U h (g i)) = multMap Ax D U h (∑ i, c i • g i) := by
  ext f j
  simp [multMap, Finset.sum_mul, mul_assoc]

/-- **Pang Corollary 3.4**: for the multiplication maps `f ↦ ([g_i h_j f])_j` on `U` modulo `C_D`
(with `b + k + p a ≤ D`) some `F_p`-combination `q = ∑ c_i g_i` retains a `1 - 1/p` fraction of the
rank of the stacked map. -/
theorem pang_cor34 (hD : 2 ≤ D) (U : Submodule (ZMod p) (PP p)) [Module.Finite (ZMod p) U]
    {k a b : ℕ} (hU : ∀ f ∈ U, f.totalDegree ≤ k) (g : Fin s → PP p) (h : Fin t → PP p)
    (hg : ∀ i, (g i).totalDegree ≤ a) (hh : ∀ j, (h j).totalDegree ≤ b)
    (hbud : b + k + p * a ≤ D) :
    ∃ c : Fin s → ZMod p,
      Module.finrank (ZMod p) (LinearMap.range (LinearMap.pi fun i => multMap Ax D U h (g i))) *
        (p - 1) ≤
      p * Module.finrank (ZMod p) (LinearMap.range (multMap Ax D U h (∑ i, c i • g i))) := by
  obtain ⟨c, hc⟩ := pang_retention_lin (fun i => multMap Ax D U h (g i))
    (ah_mult hD U hU g h hg hh hbud)
  refine ⟨c, ?_⟩
  rwa [multMap_sum] at hc

end Main

end

end Pang
