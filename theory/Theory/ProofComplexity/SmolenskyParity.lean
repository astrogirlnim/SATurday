import Theory.ProofComplexity.Smolensky
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Log

/-!
# Smolensky's argument for parity (Ladder Rung R4, 1A.5)

For an odd prime `p`, write `z_i = 1 - 2 x_i` (values `±1` in `ZMod p`). Every function on the
cube is a combination of the monomials `z_K`. If a degree `D` function agrees with parity on
a set `G`, then `z_[n] = 1 - 2 PAR` agrees with a degree `D` function on `G`, and every
monomial `z_K` with `|K| > n/2` equals `z_[n] z_{K^c}` there. So every function on `G` has
degree at most `⌊n/2⌋ + D`, and counting coefficients gives
`|G| ≤ #{K : |K| ≤ ⌊n/2⌋ + D}`.

LOG: R4 SmolenskyParity module (Fourier expansion, representation on agreement sets)
-/

namespace SATurday.ProofComplexity

open Finset

noncomputable section

open Classical

variable {n p : ℕ} [hp : Fact p.Prime]

/-- `±1` variable. -/
def zf (x : Fin n → Bool) (i : Fin n) : ZMod p := 1 - 2 * bitF p x i

/-- `±1` monomial. -/
def zmono (K : Finset (Fin n)) (x : Fin n → Bool) : ZMod p := ∏ i ∈ K, zf (p := p) x i

theorem zf_sq (x : Fin n → Bool) (i : Fin n) : zf (p := p) x i * zf (p := p) x i = 1 := by
  unfold zf bitF; split_ifs <;> ring

theorem zmono_lowDeg (K : Finset (Fin n)) : LowDeg p n K.card (zmono (p := p) K) := by
  have := LowDeg.prod (n := n) (p := p) (D := 1) K
    (f := fun i x => zf (p := p) x i) (fun i _ => by
      unfold zf
      exact (LowDeg.const_le 1).sub ((LowDeg.var (p := p) i).smul 2 |>.mono_deg le_rfl))
  simpa [zmono] using this

theorem zmono_union {K L : Finset (Fin n)} (h : Disjoint K L) (x : Fin n → Bool) :
    zmono (p := p) (K ∪ L) x = zmono (p := p) K x * zmono (p := p) L x := by
  unfold zmono; exact Finset.prod_union h

/-- Large monomials factor through the full product. -/
theorem zmono_compl (K : Finset (Fin n)) (x : Fin n → Bool) :
    zmono (p := p) K x = zmono (p := p) Finset.univ x * zmono (p := p) Kᶜ x := by
  have h1 : zmono (p := p) Finset.univ x = zmono (p := p) K x * zmono (p := p) Kᶜ x := by
    rw [← zmono_union disjoint_compl_right, Finset.union_compl]
  have h2 : zmono (p := p) Kᶜ x * zmono (p := p) Kᶜ x = 1 := by
    unfold zmono
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => zf_sq x i
  rw [h1, mul_assoc, h2, mul_one]

/-- Parity of the input. -/
def parity (x : Fin n → Bool) : Bool := decide ((Finset.univ.filter fun i => x i = true).card % 2 = 1)

theorem zmono_univ_parity (x : Fin n → Bool) :
    zmono (p := p) Finset.univ x = 1 - 2 * bz p (parity x) := by
  unfold zmono
  have key : ∀ s : Finset (Fin n), ∏ i ∈ s, zf (p := p) x i =
      (-1) ^ (s.filter fun i => x i = true).card := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, ih, Finset.filter_insert]
        unfold zf bitF
        by_cases hx : x a = true
        · rw [if_pos hx, if_pos hx, Finset.card_insert_of_notMem (by simp [ha])]; ring
        · rw [if_neg hx, if_neg hx]; ring
  rw [key]
  unfold parity bz
  rcases Nat.even_or_odd (Finset.univ.filter fun i => x i = true).card with he | ho
  · rw [he.neg_one_pow, if_neg (by rw [decide_eq_true_iff]; exact Nat.not_odd_iff_even.2 he ∘
      Nat.odd_iff.2)]
    ring
  · rw [ho.neg_one_pow, if_pos (by rw [decide_eq_true_iff]; exact Nat.odd_iff.1 ho)]
    ring

theorem two_ne_zero_of_odd (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have h2 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this
  exact hp2 h2

/-- Point indicator in `±1` form. -/
theorem delta_eq (hp2 : p ≠ 2) (x y : Fin n → Bool) :
    ∏ i : Fin n, ((1 + zf (p := p) x i * zf (p := p) y i) * (2 : ZMod p)⁻¹) =
      if x = y then 1 else 0 := by
  have h2 := two_ne_zero_of_odd (p := p) hp2
  split_ifs with hxy
  · subst hxy
    refine Finset.prod_eq_one fun i _ => ?_
    rw [zf_sq]; field_simp; norm_num
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hno; push_neg at hno; exact hxy (funext hno)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    unfold zf bitF
    cases hx : x i <;> cases hy : y i <;> simp_all <;> ring

/-- Every function is a combination of `±1` monomials. -/
theorem fourier (hp2 : p ≠ 2) (f : (Fin n → Bool) → ZMod p) :
    ∃ e : Finset (Fin n) → ZMod p, ∀ x, f x = ∑ K : Finset (Fin n), e K * zmono (p := p) K x := by
  refine ⟨fun K => (2 : ZMod p)⁻¹ ^ n * ∑ y : Fin n → Bool, f y * zmono (p := p) K y,
    fun x => ?_⟩
  have hx : f x = ∑ y : Fin n → Bool, f y * ∏ i : Fin n,
      ((1 + zf (p := p) x i * zf (p := p) y i) * (2 : ZMod p)⁻¹) := by
    simp only [delta_eq hp2]
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; rw [if_neg (Ne.symm hy), mul_zero]
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [hx]
  have hexp : ∀ y : Fin n → Bool, ∏ i : Fin n,
      ((1 + zf (p := p) x i * zf (p := p) y i) * (2 : ZMod p)⁻¹) =
      (2 : ZMod p)⁻¹ ^ n * ∑ K : Finset (Fin n), zmono (p := p) K x * zmono (p := p) K y := by
    intro y
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_one_add, mul_comm]
    congr 1
    rw [Finset.powerset_univ]
    refine Finset.sum_congr rfl fun K _ => ?_
    unfold zmono; rw [Finset.prod_mul_distrib]
  simp only [hexp]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- On an agreement set with parity, every function has degree at most `⌊n/2⌋ + D`. -/
theorem rep_on_agree (hp2 : p ≠ 2) {D : ℕ} {P : (Fin n → Bool) → ZMod p} (hP : LowDeg p n D P)
    {G : Finset (Fin n → Bool)} (hG : ∀ x ∈ G, P x = bz p (parity x))
    (f : (Fin n → Bool) → ZMod p) :
    ∃ h : (Fin n → Bool) → ZMod p, LowDeg p n (n / 2 + D) h ∧ ∀ x ∈ G, f x = h x := by
  obtain ⟨e, he⟩ := fourier hp2 f
  let term : Finset (Fin n) → (Fin n → Bool) → ZMod p := fun K x =>
    if K.card ≤ n / 2 then zmono (p := p) K x else (1 - 2 * P x) * zmono (p := p) Kᶜ x
  refine ⟨fun x => ∑ K : Finset (Fin n), e K * term K x, ?_, fun x hx => ?_⟩
  · refine LowDeg.sum _ fun K _ => LowDeg.smul (e K) ?_
    by_cases hK : K.card ≤ n / 2
    · have := (zmono_lowDeg (p := p) K).mono_deg (show K.card ≤ n / 2 + D by omega)
      refine ⟨this.choose, this.choose_spec.1, fun x => ?_⟩
      simp only [term, if_pos hK]; exact this.choose_spec.2 x
    · have h1 : LowDeg p n D (fun x => 1 - 2 * P x) := (LowDeg.const_le 1).sub (hP.smul 2)
      have h2 := zmono_lowDeg (p := p) Kᶜ
      have hc : Kᶜ.card ≤ n / 2 := by
        rw [Finset.card_compl, Fintype.card_fin]; omega
      have := (h1.mul h2).mono_deg (show D + Kᶜ.card ≤ n / 2 + D by omega)
      refine ⟨this.choose, this.choose_spec.1, fun x => ?_⟩
      simp only [term, if_neg hK]; exact this.choose_spec.2 x
  · rw [he x]
    refine Finset.sum_congr rfl fun K _ => ?_
    simp only [term]
    split_ifs with hK
    · rfl
    · rw [zmono_compl K x, zmono_univ_parity, hG x hx]

/-- Smolensky's counting: an agreement set with parity has at most as many points as there
are monomials of degree at most `⌊n/2⌋ + D`. -/
theorem agree_card_le (hp2 : p ≠ 2) {D : ℕ} {P : (Fin n → Bool) → ZMod p} (hP : LowDeg p n D P)
    {G : Finset (Fin n → Bool)} (hG : ∀ x ∈ G, P x = bz p (parity x)) :
    G.card ≤ (Finset.univ.filter fun K : Finset (Fin n) => K.card ≤ n / 2 + D).card := by
  set T := Finset.univ.filter fun K : Finset (Fin n) => K.card ≤ n / 2 + D
  let Φ : (T → ZMod p) → (G → ZMod p) := fun c x =>
    ∑ K : T, c K * mono p K.1 x.1
  have hsurj : Function.Surjective Φ := by
    intro φ
    let f : (Fin n → Bool) → ZMod p := fun x => if hx : x ∈ G then φ ⟨x, hx⟩ else 0
    obtain ⟨h, ⟨c, hc, hh⟩, hfh⟩ := rep_on_agree hp2 hP hG f
    refine ⟨fun K => c K.1, funext fun x => ?_⟩
    show ∑ K : T, c K.1 * mono p K.1 x.1 = φ x
    have e1 : ∑ K : T, c K.1 * mono p K.1 x.1 = ∑ K ∈ T, c K * mono p K x.1 :=
      Finset.sum_coe_sort T (fun K => c K * mono p K x.1)
    have e2 : ∑ K ∈ T, c K * mono p K x.1 = ∑ K : Finset (Fin n), c K * mono p K x.1 := by
      refine Finset.sum_subset (Finset.subset_univ _) fun K _ hK => ?_
      have : c K = 0 := by
        by_contra hne
        exact hK (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc K hne⟩)
      rw [this, zero_mul]
    rw [e1, e2, ← hh, ← hfh x.1 x.2]
    simp [f, x.2]
  have hcard := Fintype.card_le_of_surjective Φ hsurj
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_coe] at hcard
  exact (Nat.pow_le_pow_iff_right hp.out.two_le).1 hcard

/-- Monomials of degree at most `⌊n/2⌋ + D`. -/
theorem low_card_le (n D : ℕ) :
    (Finset.univ.filter fun K : Finset (Fin n) => K.card ≤ n / 2 + D).card * 2 ≤
      2 ^ n + 2 * ((D + 1) * n.choose (n / 2)) := by
  set A := Finset.univ.filter fun K : Finset (Fin n) => 2 * K.card < n
  set B := Finset.univ.filter fun K : Finset (Fin n) => n ≤ 2 * K.card ∧ K.card ≤ n / 2 + D
  have hcompl : ∀ K : Finset (Fin n), Kᶜ.card = n - K.card := by
    intro K; rw [Finset.card_compl, Fintype.card_fin]
  have hA : A.card * 2 ≤ 2 ^ n := by
    have hdisj : Disjoint A (A.image compl) := by
      rw [Finset.disjoint_left]
      intro K hK hK'
      obtain ⟨L, hL, rfl⟩ := Finset.mem_image.1 hK'
      have h1 := (Finset.mem_filter.1 hK).2
      have h2 := (Finset.mem_filter.1 hL).2
      rw [hcompl] at h1
      have := Finset.card_le_univ L; simp at this
      omega
    have himg : (A.image compl).card = A.card := Finset.card_image_of_injective _ compl_injective
    have := Finset.card_le_univ (A ∪ A.image compl)
    rw [Finset.card_union_of_disjoint hdisj, himg, Fintype.card_finset, Fintype.card_fin] at this
    omega
  have hB : B.card ≤ (D + 1) * n.choose (n / 2) := by
    have hsub : B ⊆ (Finset.Icc ((n + 1) / 2) (n / 2 + D)).biUnion fun k =>
        (Finset.univ : Finset (Fin n)).powersetCard k := by
      intro K hK
      obtain ⟨_, h1, h2⟩ := Finset.mem_filter.1 hK
      exact Finset.mem_biUnion.2 ⟨K.card, Finset.mem_Icc.2 ⟨by omega, h2⟩,
        Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩⟩
    calc B.card ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ k ∈ Finset.Icc ((n + 1) / 2) (n / 2 + D),
            ((Finset.univ : Finset (Fin n)).powersetCard k).card := Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ Finset.Icc ((n + 1) / 2) (n / 2 + D), n.choose (n / 2) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          exact Nat.choose_le_middle k n
      _ = (Finset.Icc ((n + 1) / 2) (n / 2 + D)).card * n.choose (n / 2) := by simp
      _ ≤ (D + 1) * n.choose (n / 2) := by
          apply Nat.mul_le_mul_right
          rw [Nat.card_Icc]; omega
  have hT : (Finset.univ.filter fun K : Finset (Fin n) => K.card ≤ n / 2 + D) ⊆ A ∪ B := by
    intro K hK
    have h := (Finset.mem_filter.1 hK).2
    by_cases h2 : 2 * K.card < n
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega, h⟩)
  have := (Finset.card_le_card hT).trans (Finset.card_union_le A B)
  omega

/-- Central binomial bound `C(2m, m)^2 (3m + 1) ≤ 16^m`. -/
theorem centralBinom_sq_le : ∀ m : ℕ, (2 * m).choose m ^ 2 * (3 * m + 1) ≤ 16 ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hid := Nat.succ_mul_centralBinom_succ m
      rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at hid
      set C := (2 * m).choose m
      set C' := (2 * (m + 1)).choose (m + 1)
      have hpoly : (2 * m + 1) ^ 2 * (3 * m + 4) ≤ 4 * (m + 1) ^ 2 * (3 * m + 1) := by nlinarith
      have hsq : (C' * (m + 1)) ^ 2 = 4 * (2 * m + 1) ^ 2 * C ^ 2 := by
        rw [show (m + 1) * C' = C' * (m + 1) from Nat.mul_comm _ _] at hid
        rw [show C' * (m + 1) = 2 * (2 * m + 1) * C from hid]; ring
      have key : C' ^ 2 * (3 * (m + 1) + 1) * (m + 1) ^ 2 ≤ 16 ^ (m + 1) * (m + 1) ^ 2 := by
        calc C' ^ 2 * (3 * (m + 1) + 1) * (m + 1) ^ 2
            = (C' * (m + 1)) ^ 2 * (3 * m + 4) := by ring
          _ = 4 * ((2 * m + 1) ^ 2 * (3 * m + 4)) * C ^ 2 := by rw [hsq]; ring
          _ ≤ 4 * (4 * (m + 1) ^ 2 * (3 * m + 1)) * C ^ 2 :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpoly)
          _ = 16 * (m + 1) ^ 2 * (C ^ 2 * (3 * m + 1)) := by ring
          _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := Nat.mul_le_mul_left _ ih
          _ = 16 ^ (m + 1) * (m + 1) ^ 2 := by ring
      exact Nat.le_of_mul_le_mul_right key (by positivity)

/-- `C(n, ⌊n/2⌋)^2 (n + 1) ≤ 2 · 4^n`. -/
theorem choose_half_sq_le (n : ℕ) : n.choose (n / 2) ^ 2 * (n + 1) ≤ 2 * 4 ^ n := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have h := centralBinom_sq_le m
    rw [show m + m = 2 * m by ring, show 2 * m / 2 = m by omega]
    have e : (4 : ℕ) ^ (2 * m) = 16 ^ m := by rw [pow_mul]; norm_num
    rw [e]
    calc (2 * m).choose m ^ 2 * (2 * m + 1) ≤ (2 * m).choose m ^ 2 * (3 * m + 1) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ 16 ^ m := h
      _ ≤ 2 * 16 ^ m := by omega
  · have h := centralBinom_sq_le m
    rw [show (2 * m + 1) / 2 = m by omega]
    have hc : (2 * m + 1).choose m ≤ 2 * (2 * m).choose m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        rw [show 2 * (k + 1) + 1 = (2 * (k + 1)) + 1 by rfl, Nat.choose_succ_succ']
        have := Nat.choose_le_middle k (2 * (k + 1))
        have e : 2 * (k + 1) / 2 = k + 1 := by omega
        rw [e] at this
        omega
    have e : (4 : ℕ) ^ (2 * m + 1) = 4 * 16 ^ m := by rw [pow_succ, pow_mul]; norm_num; ring
    rw [e]
    calc (2 * m + 1).choose m ^ 2 * (2 * m + 1 + 1)
        ≤ (2 * (2 * m).choose m) ^ 2 * (2 * (3 * m + 1)) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hc 2) (by omega)
      _ = 8 * ((2 * m).choose m ^ 2 * (3 * m + 1)) := by ring
      _ ≤ 8 * 16 ^ m := Nat.mul_le_mul_left _ h
      _ = 2 * (4 * 16 ^ m) := by ring

/-- Polynomials are eventually below `2^t`. -/
theorem eventually_poly_lt_two_pow (A b : ℕ) : ∃ T, ∀ t ≥ T, A * (t + 1) ^ b < 2 ^ t := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt b (by norm_num : (1 : ℝ) < 2)
  have hpos : (0 : ℝ) < 1 / (2 * A + 2) := by positivity
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (hlim.eventually (gt_mem_nhds hpos))
  refine ⟨T, fun t ht => ?_⟩
  have h := hT (t + 1) (by omega)
  have h2 : (0 : ℝ) < 2 ^ (t + 1) := by positivity
  rw [div_lt_div_iff₀ h2 (by positivity), one_mul] at h
  push_cast at h
  have h3 : ((2 * A + 2) * (t + 1) ^ b : ℝ) < 2 ^ (t + 1) := by linarith
  have h4 : (2 * A + 2) * (t + 1) ^ b < 2 ^ (t + 1) := by exact_mod_cast h3
  rw [pow_succ] at h4
  nlinarith [Nat.one_le_pow b (t + 1) (by omega)]

/-- Smolensky's theorem for parity: for an odd prime `p` and depth `d`, AC0[p] circuits
computing parity on `n` bits have super polynomial size. -/
def ParityAC0pLB (p : ℕ) : Prop :=
  ∀ d c : ℕ, ∃ N, ∀ n ≥ N, ∀ (g : ℕ → CG) (s : ℕ),
    CComputes (n := n) p g s d parity → n ^ c < s

theorem smolensky_parity (hp2 : p ≠ 2) : ParityAC0pLB p := by
  intro d c
  set K := ((p - 1) * (c + 3)) ^ d
  obtain ⟨T, hT⟩ := eventually_poly_lt_two_pow (128 * K * K) (2 * d)
  refine ⟨2 ^ (T + 1), fun n hn g s hC => ?_⟩
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_two_pow) hn
  set t := Nat.log 2 n
  have htT : T ≤ t := by
    have : T + 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
    omega
  have h2t : 2 ^ t ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hnt : n < 2 ^ (t + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  set ℓ := (c + 3) * (t + 1)
  have hℓ : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  set D := ((p - 1) * ℓ) ^ d
  by_contra hlt
  push_neg at hlt
  obtain ⟨P, hP, hE⟩ := circuit_approx (p := p) ℓ g hℓ hC
  set E := Finset.univ.filter fun x => P x ≠ bz p (parity x)
  set G := Finset.univ.filter fun x => P x = bz p (parity x)
  have hGE : G.card + E.card = 2 ^ n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n → Bool)))
      (fun x => P x = bz p (parity x))
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
    exact this
  have hG := agree_card_le hp2 hP (G := G) (fun x hx => (Finset.mem_filter.1 hx).2)
  have hT2 := low_card_le n D
  -- the error set is small: 8 |E| ≤ 2^n
  have h2l : 8 * n ^ c ≤ 2 ^ ℓ := by
    have h1 : (n + 1) ^ (c + 3) ≤ 2 ^ ℓ := by
      calc (n + 1) ^ (c + 3) ≤ (2 ^ (t + 1)) ^ (c + 3) := Nat.pow_le_pow_left hnt (c + 3)
        _ = 2 ^ ℓ := by
            show (2 ^ (t + 1)) ^ (c + 3) = 2 ^ ((c + 3) * (t + 1))
            rw [← pow_mul]; ring_nf
    have h2 : 8 * n ^ c ≤ (n + 1) ^ (c + 3) := by
      calc 8 * n ^ c ≤ (n + 1) ^ 3 * (n + 1) ^ c :=
            Nat.mul_le_mul (le_trans (by norm_num) (Nat.pow_le_pow_left (show 2 ≤ n + 1 by omega) 3))
              (Nat.pow_le_pow_left (by omega) c)
        _ = (n + 1) ^ (c + 3) := by ring
    omega
  have hEs : 8 * E.card ≤ 2 ^ n := by
    have h1 : E.card * (8 * n ^ c) ≤ E.card * 2 ^ ℓ := Nat.mul_le_mul_left _ h2l
    have h2 : s * 2 ^ n ≤ n ^ c * 2 ^ n := Nat.mul_le_mul_right _ hlt
    have hnc : 0 < n ^ c := by positivity
    have : E.card * 8 * n ^ c ≤ n ^ c * 2 ^ n := by nlinarith
    have : E.card * 8 ≤ 2 ^ n := by
      have := Nat.le_of_mul_le_mul_right (a := E.card * 8) (b := 2 ^ n) (c := n ^ c)
        (by nlinarith) hnc
      exact this
    omega
  -- the binomial term is small: 4 (D + 1) C ≤ 2^n
  have hD : 32 * (D + 1) ^ 2 ≤ n + 1 := by
    have hDK : D + 1 ≤ 2 * K * (t + 1) ^ d := by
      have e : D = K * (t + 1) ^ d := by
        simp only [D, K, ℓ]; rw [← mul_pow]; congr 1; ring
      have hK1 : 1 ≤ K * (t + 1) ^ d := by
        have : 1 ≤ K := Nat.one_le_pow _ _ (Nat.mul_pos (by have := hp.out.two_le; omega)
          (by omega))
        have : 1 ≤ (t + 1) ^ d := Nat.one_le_pow _ _ (by omega)
        nlinarith
      have e2 : 2 * K * (t + 1) ^ d = 2 * (K * (t + 1) ^ d) := by ring
      rw [e, e2]; omega
    have hpoly := hT t htT
    calc 32 * (D + 1) ^ 2 ≤ 32 * (2 * K * (t + 1) ^ d) ^ 2 := Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left hDK 2)
      _ = 128 * K * K * (t + 1) ^ (2 * d) := by ring
      _ ≤ 2 ^ t := hpoly.le
      _ ≤ n + 1 := by omega
  have hC := choose_half_sq_le n
  have hW : 4 * ((D + 1) * n.choose (n / 2)) ≤ 2 ^ n := by
    have h1 : (4 * ((D + 1) * n.choose (n / 2))) ^ 2 * 2 ≤ (2 ^ n) ^ 2 * 2 := by
      calc (4 * ((D + 1) * n.choose (n / 2))) ^ 2 * 2
          = (32 * (D + 1) ^ 2) * n.choose (n / 2) ^ 2 := by ring
        _ ≤ (n + 1) * n.choose (n / 2) ^ 2 := Nat.mul_le_mul_right _ hD
        _ = n.choose (n / 2) ^ 2 * (n + 1) := by ring
        _ ≤ 2 * 4 ^ n := hC
        _ = (2 ^ n) ^ 2 * 2 := by rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
    have h2 := Nat.le_of_mul_le_mul_right h1 (by norm_num : 0 < 2)
    exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).1 h2
  have hX : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [show ((p - 1) * ℓ) ^ d = D from rfl] at hG
  omega

end

end SATurday.ProofComplexity
