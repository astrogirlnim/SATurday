import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Finsupp.Fin
/-
# Pang route, layer D (part 1): multiplicity Schwartz-Zippel over a finite field

Taylor shift `f(a + z)`, multiplicity `mult a f` (least total degree of a nonzero monomial of
`shift a f`), and the Dawson-Kopparty-Saraf-Shpilka style bound
`(sum_a mult a H) * q <= totalDegree H * q ^ n` for nonzero `H` in `n` variables over a field
with `q` elements (Pang 2610.00837, Lemma 3.1 proof, eq. (multiplicity)). Elementary; proved by
induction on `n` through `finSuccEquiv`.
-/

open MvPolynomial Finset
open scoped Polynomial
namespace Pang
variable {F : Type*} [Field F] {σ : Type*}

noncomputable def shift (a : σ → F) : MvPolynomial σ F →ₐ[F] MvPolynomial σ F :=
  aeval fun i => X i + C (a i)

@[simp] lemma shift_X (a : σ → F) (i : σ) : shift a (X i) = X i + C (a i) := by simp [shift]

lemma shift_neg_shift (a : σ → F) (f : MvPolynomial σ F) : shift (-a) (shift a f) = f := by
  have : (shift (-a)).comp (shift a) = AlgHom.id F _ := by
    apply MvPolynomial.algHom_ext; intro i
    simp [add_assoc, ← C_add]
  exact AlgHom.congr_fun this f

lemma shift_injective (a : σ → F) : Function.Injective (shift a) := by
  intro f g h
  rw [← shift_neg_shift a f, h, shift_neg_shift]

noncomputable def mult (a : σ → F) (f : MvPolynomial σ F) : ℕ :=
  sInf {n | ∃ d : σ →₀ ℕ, (d.sum fun _ e => e) = n ∧ coeff d (shift a f) ≠ 0}

lemma mult_spec {a : σ → F} {f : MvPolynomial σ F} (hf : f ≠ 0) :
    ∃ d : σ →₀ ℕ, (d.sum fun _ e => e) = mult a f ∧ coeff d (shift a f) ≠ 0 := by
  have h : shift a f ≠ 0 := fun h => hf (shift_injective a (by simpa using h))
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp h
  have hne : {n | ∃ d : σ →₀ ℕ, (d.sum fun _ e => e) = n ∧ coeff d (shift a f) ≠ 0}.Nonempty :=
    ⟨_, d, rfl, hd⟩
  exact Nat.sInf_mem hne

lemma mult_le {a : σ → F} {f : MvPolynomial σ F} (d : σ →₀ ℕ) (hd : coeff d (shift a f) ≠ 0) :
    mult a f ≤ d.sum fun _ e => e := Nat.sInf_le ⟨d, rfl, hd⟩



lemma lin_comp_coeff {A : Type*} [CommRing A] [Algebra F A] (ℓ : A →ₗ[F] F) (c : F)
    (G : A[X]) (m : ℕ) :
    ℓ ((G.comp (Polynomial.X + Polynomial.C (algebraMap F A c))).coeff m) =
      (Polynomial.taylor c (G.sum fun j a => Polynomial.monomial j (ℓ a))).coeff m := by
  induction G using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.add_comp, Polynomial.coeff_add, map_add, hp, hq, Polynomial.sum_add_index,
      map_add, Polynomial.coeff_add]
    · intro i; simp
    · intro i a b; simp [map_add]
  | monomial j a =>
    have h1 := Polynomial.sum_monomial_index (n := j) a (f := fun j a => Polynomial.monomial j (ℓ a)) (by simp)
    rw [h1, Polynomial.taylor_apply]
    show _ = ((Polynomial.monomial j (ℓ a)).comp (Polynomial.X + Polynomial.C c)).coeff m
    rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_add_C_pow]
    have : a * ((algebraMap F A c) ^ (j - m) * (j.choose m : A)) = (c ^ (j - m) * (j.choose m : F)) • a := by
      rw [Algebra.smul_def]; simp [mul_comm, mul_left_comm, mul_assoc]
    rw [this, map_smul, smul_eq_mul]; ring

lemma coeff_lsum {A : Type*} [CommRing A] [Algebra F A] (ℓ : A →ₗ[F] F) (G : A[X]) (k : ℕ) :
    (G.sum fun j a => Polynomial.monomial j (ℓ a)).coeff k = ℓ (G.coeff k) := by
  induction G using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.sum_add_index, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, map_add]
    · intro i; simp
    · intro i a b; simp [map_add]
  | monomial j a =>
    have h1 := Polynomial.sum_monomial_index (n := j) a (f := fun j a => Polynomial.monomial j (ℓ a)) (by simp)
    rw [h1]
    by_cases h : k = j
    · subst h; simp
    · simp [Polynomial.coeff_monomial, h, Ne.symm h]

noncomputable def hpoly {n : ℕ} (b : Fin n → F) (α : Fin n →₀ ℕ)
    (G : (MvPolynomial (Fin n) F)[X]) : F[X] :=
  G.sum fun j a => Polynomial.monomial j (coeff α (shift b a))

lemma coeff_hpoly {n : ℕ} (b : Fin n → F) (α : Fin n →₀ ℕ) (G : (MvPolynomial (Fin n) F)[X])
    (j : ℕ) : (hpoly b α G).coeff j = coeff α (shift b (G.coeff j)) := by
  induction G using Polynomial.induction_on' with
  | add p q hp hq =>
    unfold hpoly at *
    rw [Polynomial.sum_add_index, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add]
    · simp [map_add]
    · intro i; simp
    · intro i a b; simp [map_add]
  | monomial k a =>
    unfold hpoly
    have h1 := Polynomial.sum_monomial_index (n := k) a (f := fun j a => Polynomial.monomial j (coeff α (shift b a))) (by simp)
    rw [h1]
    by_cases h : j = k
    · subst h; simp
    · simp [Polynomial.coeff_monomial, h, Ne.symm h]

lemma fse_C {n : ℕ} (a : F) : finSuccEquiv F n (C a) = Polynomial.C (C a) := by
  simp [finSuccEquiv_apply]

lemma finSuccEquiv_shift {n : ℕ} (c : F) (b : Fin n → F) (H : MvPolynomial (Fin (n+1)) F) :
    finSuccEquiv F n (shift (Fin.cons c b : Fin (n+1) → F) H) =
      (Polynomial.map (shift b : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n) F)
        (finSuccEquiv F n H)).comp (Polynomial.X + Polynomial.C (C c)) := by
  induction H using MvPolynomial.induction_on with
  | C a => simp [fse_C]
  | add p q hp hq => simp [hp, hq, Polynomial.add_comp]
  | mul_X p i hp =>
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [map_mul, map_add, shift_X, Fin.cons_zero, hp, finSuccEquiv_X_zero, fse_C,
        Polynomial.map_mul, Polynomial.map_X, Polynomial.mul_comp, Polynomial.X_comp]
    · simp only [map_mul, map_add, shift_X, Fin.cons_succ, hp, finSuccEquiv_X_succ, fse_C,
        Polynomial.map_mul, Polynomial.map_C, Polynomial.mul_comp, Polynomial.C_comp,
        Polynomial.map_add]
      simp

lemma coeff_cons_shift {n : ℕ} (c : F) (b : Fin n → F) (H : MvPolynomial (Fin (n+1)) F) (m : ℕ)
    (α : Fin n →₀ ℕ) :
    coeff (Finsupp.cons m α) (shift (Fin.cons c b : Fin (n+1) → F) H) =
      (Polynomial.taylor c (hpoly b α (finSuccEquiv F n H))).coeff m := by
  rw [← finSuccEquiv_coeff_coeff, finSuccEquiv_shift]
  let ℓ : MvPolynomial (Fin n) F →ₗ[F] F := lcoeff F α
  have h := lin_comp_coeff ℓ c (Polynomial.map (shift b : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n) F)
        (finSuccEquiv F n H)) m
  have e : (Polynomial.map (shift b : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n) F)
        (finSuccEquiv F n H)).sum (fun j a => Polynomial.monomial j (ℓ a)) = hpoly b α (finSuccEquiv F n H) := by
    ext j
    rw [coeff_lsum, coeff_hpoly]
    simp [ℓ]
  rw [e] at h
  simpa [ℓ] using h

lemma sum_rootMult_le [Fintype F] [DecidableEq F] (h : F[X]) (hh : h ≠ 0) :
    ∑ c : F, h.rootMultiplicity c ≤ h.natDegree := by
  calc ∑ c : F, h.rootMultiplicity c = ∑ c : F, h.roots.count c := by
        simp [Polynomial.count_roots]
    _ = ∑ c ∈ h.roots.toFinset, h.roots.count c := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro x _ hx
        exact Multiset.count_eq_zero.2 (fun hm => hx (Multiset.mem_toFinset.2 hm))
    _ = Multiset.card h.roots := Multiset.toFinset_sum_count_eq _
    _ ≤ h.natDegree := Polynomial.card_roots' h

lemma mult_cons_le {n : ℕ} (b : Fin n → F) (H : MvPolynomial (Fin (n+1)) F)
    (hH : H ≠ 0) :
    ∃ h : F[X], h ≠ 0 ∧ h.natDegree = (finSuccEquiv F n H).natDegree ∧ ∀ c : F,
      mult (Fin.cons c b : Fin (n+1) → F) H ≤
        mult b ((finSuccEquiv F n H).leadingCoeff) + h.rootMultiplicity c := by
  set H' := finSuccEquiv F n H with hH'
  have hH'0 : H' ≠ 0 := by simpa [hH'] using hH
  have hlc : H'.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hH'0
  obtain ⟨α, hαdeg, hαc⟩ := mult_spec (a := b) hlc
  set h := hpoly b α H' with hh
  have hcoeff : h.coeff H'.natDegree ≠ 0 := by
    rw [hh, coeff_hpoly]; exact hαc
  have hle : h.natDegree ≤ H'.natDegree := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.2
    intro j hj
    rw [hh, coeff_hpoly, Polynomial.coeff_eq_zero_of_natDegree_lt hj]
    simp
  have hnd : h.natDegree = H'.natDegree := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle hcoeff
  have h0 : h ≠ 0 := by
    intro h0; apply hcoeff; rw [h0]; simp
  refine ⟨h, h0, hnd, fun c => ?_⟩
  set m := h.rootMultiplicity c with hm
  have hm' : m = (Polynomial.taylor c h).natTrailingDegree := by
    rw [hm, Polynomial.rootMultiplicity_eq_natTrailingDegree, Polynomial.taylor_apply]
  have hnz : (Polynomial.taylor c h).coeff m ≠ 0 := by
    have := Polynomial.trailingCoeff_nonzero_iff_nonzero.2 ((Polynomial.taylor_eq_zero c h).not.2 h0)
    rw [hm']; exact this
  have hc : coeff (Finsupp.cons m α) (shift (Fin.cons c b : Fin (n+1) → F) H) ≠ 0 := by
    rw [coeff_cons_shift]; exact hnz
  have := mult_le (a := (Fin.cons c b : Fin (n+1) → F)) _ hc
  rw [Finsupp.sum_cons] at this
  rw [← hαdeg]
  omega

theorem sum_mult_le [Fintype F] [DecidableEq F] :
    ∀ (n : ℕ) (H : MvPolynomial (Fin n) F), H ≠ 0 →
      (∑ a : Fin n → F, mult a H) * Fintype.card F ≤ H.totalDegree * Fintype.card F ^ n
  | 0, H, hH => by
    have h0 : ∀ a : Fin 0 → F, mult a H = 0 := by
      intro a
      obtain ⟨d, hd, _⟩ := mult_spec (a := a) hH
      rw [← hd, Subsingleton.elim d 0, Finsupp.sum_zero_index]
    rw [Finset.sum_eq_zero (fun a _ => h0 a)]
    simp
  | n + 1, H, hH => by
    set q := Fintype.card F with hq
    set H' := finSuccEquiv F n H with hH'
    set t := H'.natDegree with ht
    have hH'0 : H' ≠ 0 := by simpa [hH'] using hH
    have hlc : H'.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hH'0
    have hIH := sum_mult_le n _ hlc
    have hdeg : H'.leadingCoeff.totalDegree + t ≤ H.totalDegree := by
      exact totalDegree_coeff_finSuccEquiv_add_le H t hlc
    choose h hh0 hhd hle using fun (b : Fin n → F) => mult_cons_le b H hH
    have hcardfun : Fintype.card (Fin n → F) = q ^ n := by simp [hq]
    have hb : ∀ b : Fin n → F, ∑ c : F, mult (Fin.cons c b : Fin (n+1) → F) H ≤
        q * mult b H'.leadingCoeff + t := by
      intro b
      calc ∑ c : F, mult (Fin.cons c b : Fin (n+1) → F) H
          ≤ ∑ c : F, (mult b H'.leadingCoeff + (h b).rootMultiplicity c) :=
            Finset.sum_le_sum (fun c _ => hle b c)
        _ = q * mult b H'.leadingCoeff + ∑ c : F, (h b).rootMultiplicity c := by
            rw [Finset.sum_add_distrib]; simp [hq]
        _ ≤ q * mult b H'.leadingCoeff + t := by
            have := sum_rootMult_le (h b) (hh0 b)
            have h2 : (h b).natDegree = t := hhd b
            omega
    have hsum : ∑ a : Fin (n+1) → F, mult a H =
        ∑ b : Fin n → F, ∑ c : F, mult (Fin.cons c b : Fin (n+1) → F) H := by
      rw [← (Fin.consEquiv (fun _ => F)).sum_comp, Fintype.sum_prod_type_right]
      rfl
    have hfin : ∑ a : Fin (n+1) → F, mult a H ≤
        q * ∑ b : Fin n → F, mult b H'.leadingCoeff + t * q ^ n := by
      rw [hsum]
      calc _ ≤ ∑ b : Fin n → F, (q * mult b H'.leadingCoeff + t) := Finset.sum_le_sum (fun b _ => hb b)
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            hcardfun, smul_eq_mul]
          ring
    have hq0 : 0 < q := Fintype.card_pos
    calc (∑ a : Fin (n+1) → F, mult a H) * q
        ≤ (q * ∑ b : Fin n → F, mult b H'.leadingCoeff + t * q ^ n) * q :=
          Nat.mul_le_mul_right _ hfin
      _ = q * ((∑ b : Fin n → F, mult b H'.leadingCoeff) * q) + t * q ^ (n+1) := by ring
      _ ≤ q * (H'.leadingCoeff.totalDegree * q ^ n) + t * q ^ (n+1) := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_left q hIH) _
      _ = H'.leadingCoeff.totalDegree * q ^ (n+1) + t * q ^ (n+1) := by ring
      _ = (H'.leadingCoeff.totalDegree + t) * q ^ (n+1) := by ring
      _ ≤ H.totalDegree * q ^ (n+1) := Nat.mul_le_mul_right _ hdeg
end Pang
