import Theory.ProofComplexity.PangApprox

/-!
# Pang route, layer F (part 3): iteration and common multiplier (Theorem 4.3)
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.PCL MvPolynomial

namespace Pang

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime]

lemma Nn_mono {n k k' : ℕ} (h : k ≤ k') : Nn n k ≤ Nn n k' :=
  Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

section Iter
variable {Ax : Set (PP p)} {D : ℕ} {V : Finset ℕ} {s : ℕ}

/-- One round of the recursion: `p N(K) c_{P'}(K) + (p-1) N(K-d) c_P(K) ≤ p N(K) c_P(K)`. -/
theorem round (hD : 2 ≤ D) (P : PP p) (g : Fin s → PP p) {a d K : ℕ}
    (hP : P.totalDegree ≤ a) (hg : ∀ α, (g α).totalDegree ≤ d)
    (hgV : ∀ α, ∀ v ∈ (g α).vars, v ∈ V) (hdK : d ≤ K) (hKn : K ≤ V.card)
    (hbud : a + K + p * d ≤ D) :
    ∃ c : Fin s → ZMod p,
      (p * Nn V.card K) * cP Ax D V (P * (1 - (∑ i, c i • g i) ^ (p - 1))) g K +
        ((p - 1) * Nn V.card (K - d)) * cP Ax D V P g K ≤ (p * Nn V.card K) * cP Ax D V P g K := by
  obtain ⟨c, hc⟩ := onestep (Ax := Ax) hD P g hP hg hgV hdK hbud
  refine ⟨c, ?_⟩
  have hpd : d ≤ p * d := Nat.le_mul_of_pos_left d (by have := (Fact.out : p.Prime).two_le; omega)
  have hH := hilbert_lin V (Tmap Ax D V P g K) hKn
    (fun z hz i hi h0 => Tmap_closed hD hP hg (K := K) (by omega) z hz i hi h0) (k := K - d) (Nat.sub_le K d)
  have e : cP Ax D V P g (K - d) = Module.finrank (ZMod p) (LinearMap.range
      (Tmap Ax D V P g K ∘ₗ Submodule.inclusion (Vk_mono V (show K - d ≤ K by omega)))) := by
    unfold cP; rw [← Tmap_incl _ _ (Nat.sub_le K d)]
  have hK : cP Ax D V P g K = Module.finrank (ZMod p) (LinearMap.range (Tmap Ax D V P g K)) := rfl
  rw [← e, ← hK] at hH
  have h1 := Nat.mul_le_mul_left (Nn V.card K) hc
  have h2 := Nat.mul_le_mul_left (p - 1) hH
  nlinarith [h1, h2]

end Iter

section Iterate
variable {Ax : Set (PP p)} {D : ℕ} {V : Finset ℕ} {s : ℕ}

/-- After `t` rounds the product `P_t = ∏ (1 - q_j^{p-1})` has
`(pN)^t c_{P_t}(K) ≤ θ^t c_1(K)` with `θ = pN - (p-1)N(K-d)`. -/
theorem iterate_rank (hD : 2 ≤ D) (g : Fin s → PP p) {d K T : ℕ}
    (hg : ∀ α, (g α).totalDegree ≤ d) (hgV : ∀ α, ∀ v ∈ (g α).vars, v ∈ V) (hdK : d ≤ K)
    (hKn : K ≤ V.card) (hbud : T * ((p - 1) * d) + K + d ≤ D) :
    ∀ t ≤ T, ∃ c : ℕ → Fin s → ZMod p,
      (∏ j ∈ Finset.range t, (1 - (∑ i, c j i • g i) ^ (p - 1))).totalDegree ≤ t * ((p - 1) * d) ∧
      (p * Nn V.card K) ^ t * cP Ax D V (∏ j ∈ Finset.range t, (1 - (∑ i, c j i • g i) ^ (p - 1))) g K ≤
        (p * Nn V.card K - (p - 1) * Nn V.card (K - d)) ^ t * cP Ax D V 1 g K := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨fun _ _ => 0, ?_, ?_⟩ <;> simp
  | succ t ih =>
    intro ht
    obtain ⟨c, hdeg, hrank⟩ := ih (by omega)
    set P := ∏ j ∈ Finset.range t, (1 - (∑ i, c j i • g i) ^ (p - 1)) with hP
    have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
    have hb : t * ((p - 1) * d) + K + p * d ≤ D := by
      have h1 : (t + 1) * ((p - 1) * d) ≤ T * ((p - 1) * d) := Nat.mul_le_mul_right _ ht
      have h2 : p * d = (p - 1) * d + d := by
        rw [← Nat.succ_mul]; congr 1; omega
      nlinarith [h1, h2]
    obtain ⟨c', hr⟩ := round (Ax := Ax) hD P g hdeg hg hgV hdK hKn hb
    refine ⟨fun j => if j = t then c' else c j, ?_, ?_⟩
    · rw [Finset.prod_range_succ]
      have e1 : ∏ j ∈ Finset.range t, (1 - (∑ i, (if j = t then c' else c j) i • g i) ^ (p - 1)) = P := by
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [if_neg (Finset.mem_range.1 hj).ne]
      rw [e1]; beta_reduce; rw [if_pos rfl]
      refine (totalDegree_mul _ _).trans ?_
      have := totalDegree_one_sub_pow_le (totalDegree_lincomb c' g hg) (p - 1)
      rw [Nat.succ_mul]
      omega
    · rw [Finset.prod_range_succ]
      have e1 : ∏ j ∈ Finset.range t, (1 - (∑ i, (if j = t then c' else c j) i • g i) ^ (p - 1)) = P := by
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [if_neg (Finset.mem_range.1 hj).ne]
      rw [e1]; beta_reduce; rw [if_pos rfl]
      set N := Nn V.card K
      set N' := Nn V.card (K - d)
      set c1 := cP Ax D V (P * (1 - (∑ i, c' i • g i) ^ (p - 1))) g K
      set c0 := cP Ax D V P g K
      have hNN : N' ≤ N := Nn_mono (Nat.sub_le K d)
      have hθ : (p - 1) * N' ≤ p * N := by
        calc (p - 1) * N' ≤ p * N' := Nat.mul_le_mul_right _ (Nat.sub_le p 1)
          _ ≤ p * N := Nat.mul_le_mul_left _ hNN
      have step : (p * N) * c1 ≤ (p * N - (p - 1) * N') * c0 := by
        rw [Nat.sub_mul]; omega
      calc (p * N) ^ (t + 1) * c1 = (p * N) ^ t * ((p * N) * c1) := by ring
        _ ≤ (p * N) ^ t * ((p * N - (p - 1) * N') * c0) := Nat.mul_le_mul_left _ step
        _ = (p * N - (p - 1) * N') * ((p * N) ^ t * c0) := by ring
        _ ≤ (p * N - (p - 1) * N') * ((p * N - (p - 1) * N') ^ t * cP Ax D V 1 g K) :=
            Nat.mul_le_mul_left _ hrank
        _ = _ := by ring

end Iterate

section Common
variable {Ax : Set (PP p)} {D : ℕ} {V : Finset ℕ}

/-- `x ↦ [polyOf x]` on `V_K`; its rank is `h_K = dim V_K / C_{≤K}`. -/
def hMap (Ax : Set (PP p)) (D : ℕ) (V : Finset ℕ) (K : ℕ) :
    Vk (F := ZMod p) V K →ₗ[ZMod p] (PP p ⧸ CD Ax D) := (CD Ax D).mkQ ∘ₗ iotaV V K

lemma mem_ker_hMap {K : ℕ} {x : Vk (F := ZMod p) V K} :
    x ∈ LinearMap.ker (hMap Ax D V K) ↔ iotaV V K x ∈ CD Ax D := by
  simp [hMap, LinearMap.mem_ker, Submodule.Quotient.mk_eq_zero]

lemma rank_one_le (hD : 2 ≤ D) {s : ℕ} (g : Fin s → PP p) {d K : ℕ}
    (hg : ∀ α, (g α).totalDegree ≤ d) (hbud : d + K ≤ D) :
    cP Ax D V 1 g K ≤ Module.finrank (ZMod p) (LinearMap.range (hMap Ax D V K)) := by
  have hker : LinearMap.ker (hMap Ax D V K) ≤ LinearMap.ker (Tmap Ax D V 1 g K) := by
    intro x hx
    rw [mem_ker_hMap] at hx
    rw [LinearMap.mem_ker, Tmap_eq_zero_iff]
    intro α
    rw [one_mul]
    have := cd_mul hx (g := g α) (by have := totalDegree_iotaV V x; have := hg α; omega)
    exact this
  have e1 := LinearMap.finrank_range_add_finrank_ker (Tmap Ax D V 1 g K)
  have e2 := LinearMap.finrank_range_add_finrank_ker (hMap Ax D V K)
  have e3 := Submodule.finrank_mono hker
  unfold cP; omega

theorem exists_common_kernel {X : Type*} [AddCommGroup X] [Module (ZMod p) X]
    [FiniteDimensional (ZMod p) X] {S : ℕ} {Y : Fin S → Type*} [∀ ν, AddCommGroup (Y ν)]
    [∀ ν, Module (ZMod p) (Y ν)] (T : ∀ ν, X →ₗ[ZMod p] Y ν) (B : Submodule (ZMod p) X)
    (h : ∑ ν, Module.finrank (ZMod p) (LinearMap.range (T ν)) <
      Module.finrank (ZMod p) X - Module.finrank (ZMod p) B) :
    ∃ x, x ∉ B ∧ ∀ ν, T ν x = 0 := by
  let I : Finset (Fin S) → Submodule (ZMod p) X := fun s => s.inf fun ν => LinearMap.ker (T ν)
  have key : ∀ s : Finset (Fin S), Module.finrank (ZMod p) X ≤
      Module.finrank (ZMod p) (I s) +
        ∑ ν ∈ s, Module.finrank (ZMod p) (LinearMap.range (T ν)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : I ∅ = ⊤ := Finset.inf_empty
      rw [this, finrank_top]; simp
    | insert a s ha ih =>
      have hI : I (insert a s) = LinearMap.ker (T a) ⊓ I s := Finset.inf_insert ..
      rw [hI, Finset.sum_insert ha]
      have e1 := LinearMap.finrank_range_add_finrank_ker (T a)
      have e2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (T a)) (I s)
      have e3 := Submodule.finrank_le (LinearMap.ker (T a) ⊔ I s)
      omega
  have hk := key Finset.univ
  by_contra hno
  have hle : I Finset.univ ≤ B := by
    intro x hx
    by_contra hxB
    apply hno
    refine ⟨x, hxB, fun ν => ?_⟩
    have := (Finset.inf_le (f := fun ν => LinearMap.ker (T ν)) (Finset.mem_univ ν)) hx
    exact LinearMap.mem_ker.1 this
  have := Submodule.finrank_mono hle
  omega

end Common

section CommonMult
variable {Ax : Set (PP p)} {D : ℕ} {V : Finset ℕ}

/-- **Pang Theorem 4.3 (common multiplier)**. -/
theorem common_multiplier (hD : 2 ≤ D) (h1 : (1 : PP p) ∉ CD Ax D) {S d K t : ℕ} (hdK : d ≤ K)
    (hKn : K ≤ V.card) (hbud : t * ((p - 1) * d) + K + d ≤ D) (m : Fin S → ℕ)
    (g : ∀ ν, Fin (m ν) → PP p) (hg : ∀ ν i, (g ν i).totalDegree ≤ d)
    (hgV : ∀ ν i, ∀ v ∈ (g ν i).vars, v ∈ V)
    (hsize : S * (p * Nn V.card K - (p - 1) * Nn V.card (K - d)) ^ t < (p * Nn V.card K) ^ t) :
    ∃ (c : ∀ ν, ℕ → Fin (m ν) → ZMod p) (f : ML (ZMod p)), f ∈ Vk (F := ZMod p) V K ∧
      polyOf f ∉ CD Ax D ∧
      (∀ ν, (∏ j ∈ Finset.range t, (1 - (∑ i, c ν j i • g ν i) ^ (p - 1))).totalDegree ≤
        t * ((p - 1) * d)) ∧
      ∀ ν i, (∏ j ∈ Finset.range t, (1 - (∑ k, c ν j k • g ν k) ^ (p - 1))) * g ν i * polyOf f ∈
        CD Ax D := by
  classical
  have hex : ∀ ν, ∃ c : ℕ → Fin (m ν) → ZMod p,
      (∏ j ∈ Finset.range t, (1 - (∑ i, c j i • g ν i) ^ (p - 1))).totalDegree ≤ t * ((p - 1) * d) ∧
      (p * Nn V.card K) ^ t * cP Ax D V
        (∏ j ∈ Finset.range t, (1 - (∑ i, c j i • g ν i) ^ (p - 1))) (g ν) K ≤
        (p * Nn V.card K - (p - 1) * Nn V.card (K - d)) ^ t * cP Ax D V 1 (g ν) K := fun ν =>
    iterate_rank hD (g ν) (hg ν) (hgV ν) hdK hKn hbud t le_rfl
  choose c hdeg hrank using hex
  set P : ∀ ν, PP p := fun ν => ∏ j ∈ Finset.range t, (1 - (∑ i, c ν j i • g ν i) ^ (p - 1)) with hP
  set θ := p * Nn V.card K - (p - 1) * Nn V.card (K - d) with hθ
  set h := Module.finrank (ZMod p) (LinearMap.range (hMap Ax D V K)) with hh
  have hone : ∀ ν, cP Ax D V 1 (g ν) K ≤ h := fun ν =>
    rank_one_le hD (g ν) (hg ν) (by omega)
  have hNpos : 0 < p * Nn V.card K :=
    Nat.mul_pos (Fact.out : p.Prime).pos (Nn_pos V _)
  have hpow : 0 < (p * Nn V.card K) ^ t := pow_pos hNpos t
  -- h > 0
  have hone_mem : (Finsupp.single ∅ 1 : ML (ZMod p)) ∈ Vk (F := ZMod p) V K := by
    rw [mem_Vk]; intro T hT
    have := Finsupp.support_single_subset hT
    rw [Finset.mem_singleton] at this
    subst this; simp
  have hiota : iotaV V K ⟨Finsupp.single ∅ 1, hone_mem⟩ = (1 : PP p) := by
    show polyOf (Finsupp.single ∅ 1) = 1
    rw [polyOf_single]; simp
  have hhpos : 0 < h := by
    rw [hh, Nat.pos_iff_ne_zero]
    intro h0
    have hbot : LinearMap.range (hMap Ax D V K) = ⊥ := by
      rw [← Submodule.finrank_eq_zero]; exact h0
    have hx : (⟨Finsupp.single ∅ 1, hone_mem⟩ : Vk (F := ZMod p) V K) ∈
        LinearMap.ker (hMap Ax D V K) := by
      rw [LinearMap.mem_ker]
      have hmem : hMap Ax D V K ⟨Finsupp.single ∅ 1, hone_mem⟩ ∈ LinearMap.range (hMap Ax D V K) :=
        ⟨_, rfl⟩
      rw [hbot] at hmem
      exact hmem
    rw [mem_ker_hMap, hiota] at hx
    exact h1 hx
  -- the sum of ranks
  have hsum : ∑ ν, Module.finrank (ZMod p) (LinearMap.range (Tmap Ax D V (P ν) (g ν) K)) < h := by
    set R := ∑ ν, Module.finrank (ZMod p) (LinearMap.range (Tmap Ax D V (P ν) (g ν) K)) with hR
    have h2 : (p * Nn V.card K) ^ t * R ≤ S * θ ^ t * h := by
      calc (p * Nn V.card K) ^ t * R
          = ∑ ν, (p * Nn V.card K) ^ t * cP Ax D V (P ν) (g ν) K := by
            rw [hR, Finset.mul_sum]; rfl
        _ ≤ ∑ _ν : Fin S, θ ^ t * h := Finset.sum_le_sum fun ν _ =>
            (hrank ν).trans (Nat.mul_le_mul_left _ (hone ν))
        _ = S * θ ^ t * h := by simp [Finset.sum_const, mul_assoc]
    by_contra hge
    push Not at hge
    have h3 : (p * Nn V.card K) ^ t * h ≤ (p * Nn V.card K) ^ t * R := Nat.mul_le_mul_left _ hge
    have h4 : S * θ ^ t * h < (p * Nn V.card K) ^ t * h := Nat.mul_lt_mul_of_pos_right hsize hhpos
    omega
  -- common kernel
  have hB : Module.finrank (ZMod p) (Vk (F := ZMod p) V K) -
      Module.finrank (ZMod p) (LinearMap.ker (hMap Ax D V K)) = h := by
    have := LinearMap.finrank_range_add_finrank_ker (hMap Ax D V K)
    omega
  obtain ⟨x, hxB, hx0⟩ := exists_common_kernel (fun ν => Tmap Ax D V (P ν) (g ν) K)
    (LinearMap.ker (hMap Ax D V K)) (by rw [hB]; exact hsum)
  refine ⟨c, x.1, x.2, ?_, hdeg, ?_⟩
  · intro hmem
    exact hxB (mem_ker_hMap.2 hmem)
  · intro ν i
    exact (Tmap_eq_zero_iff.1 (hx0 ν)) i

end CommonMult

end

end Pang
