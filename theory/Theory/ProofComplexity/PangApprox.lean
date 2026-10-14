import Theory.ProofComplexity.PangBridge

/-!
# Pang route, layer F (part 2): approximation gain (Lemma 4.2 "onestep")
-/

open SATurday.ProofComplexity SATurday.ProofComplexity.PCL MvPolynomial

namespace Pang

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime]

section Maps
variable (Ax : Set (PP p)) (D : ℕ) (V : Finset ℕ) {s : ℕ}

/-- `T_{u,k} : V_k → (P/C_D)^s, f ↦ ([u g_α f])_α`. -/
def Tmap (u : PP p) (g : Fin s → PP p) (k : ℕ) :
    Vk (F := ZMod p) V k →ₗ[ZMod p] (Fin s → PP p ⧸ CD Ax D) :=
  multMap Ax D (iotaV V k) (fun α => u * g α) 1

variable {Ax D V}

lemma Tmap_eq_zero_iff {u : PP p} {g : Fin s → PP p} {k : ℕ} {x : Vk (F := ZMod p) V k} :
    Tmap Ax D V u g k x = 0 ↔ ∀ α, u * g α * iotaV V k x ∈ CD Ax D := by
  constructor
  · intro h α
    have := congrFun h α
    simp only [Tmap, multMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Submodule.mkQ_apply, one_mul, Pi.zero_apply] at this
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  · intro h
    funext α
    simp only [Tmap, multMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Submodule.mkQ_apply, one_mul, Pi.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero _).2 (h α)

lemma Tmap_incl (u : PP p) (g : Fin s → PP p) {k k' : ℕ} (h : k ≤ k') :
    Tmap Ax D V u g k = Tmap Ax D V u g k' ∘ₗ Submodule.inclusion (Vk_mono V h) := by
  ext x
  rfl

lemma Tmap_closed (hD : 2 ≤ D) {P : PP p} {g : Fin s → PP p} {a d K : ℕ}
    (hP : P.totalDegree ≤ a) (hg : ∀ α, (g α).totalDegree ≤ d) (hbud : a + d + K ≤ D)
    (z : Vk (F := ZMod p) V K) (hz : PCL.deg z.1 < K) (i : ℕ) (hi : i ∈ V)
    (h0 : Tmap Ax D V P g K z = 0) :
    Tmap Ax D V P g K ⟨shl {i} z.1, shl_mem_Vk V z.2 hz hi⟩ = 0 := by
  rw [Tmap_eq_zero_iff] at h0 ⊢
  intro α
  have hu : (P * g α).totalDegree ≤ a + d :=
    (totalDegree_mul _ _).trans (Nat.add_le_add hP (hg α))
  have h1 : (X i * (P * g α * iotaV V K z) : PP p) ∈ CD Ax D := by
    refine cd_mul (h0 α) ?_
    have h2 : (P * g α * iotaV V K z).totalDegree ≤ (a + d) + PCL.deg z.1 :=
      (totalDegree_mul _ _).trans (Nat.add_le_add hu (totalDegree_polyOf_le _))
    rw [totalDegree_X]; omega
  have h3 := cd_polyOf_shl (Ax := Ax) hD (P * g α) z.1 i (by omega)
  have : P * g α * iotaV V K ⟨shl {i} z.1, shl_mem_Vk V z.2 hz hi⟩ =
      X i * (P * g α * iotaV V K z) - P * g α * (X i * polyOf z.1 - polyOf (shl {i} z.1)) := by
    show P * g α * polyOf (shl {i} z.1) = X i * (P * g α * polyOf z.1) - _
    ring
  rw [this]
  exact sub_mem h1 h3

end Maps

section Helpers
variable {Ax : Set (PP p)} {D : ℕ} {V : Finset ℕ} {s : ℕ}

lemma multMap_eq_zero_iff {Dm : Type*} [AddCommGroup Dm] [Module (ZMod p) Dm]
    (ι : Dm →ₗ[ZMod p] PP p) {t : ℕ} (h : Fin t → PP p) (g : PP p) (x : Dm) :
    multMap Ax D ι h g x = 0 ↔ ∀ j, g * h j * ι x ∈ CD Ax D := by
  constructor
  · intro hx j
    have := congrFun hx j
    simp only [multMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Submodule.mkQ_apply, Pi.zero_apply] at this
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  · intro hx
    funext j
    simp only [multMap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Submodule.mkQ_apply, Pi.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero _).2 (hx j)

lemma vars_polyOf_subset {k : ℕ} (x : Vk (F := ZMod p) V k) : (polyOf x.1).vars ⊆ V := by
  classical
  have : polyOf x.1 = ∑ S ∈ x.1.support, C (x.1 S) * ∏ i ∈ S, (X i : PP p) := by
    conv_lhs => rw [← Finsupp.sum_single x.1]
    simp only [map_sum, polyOf_single, Finsupp.sum]
  rw [this]
  refine (vars_sum_subset _ _).trans (Finset.biUnion_subset.2 fun S hS => ?_)
  refine (vars_mul _ _).trans ?_
  rw [vars_C, Finset.empty_union]
  refine (vars_prod _).trans ?_
  refine Finset.biUnion_subset.2 fun i hi => ?_
  rw [vars_X]
  simpa using ((mem_Vk V).1 x.2 S hS).1 hi

lemma ml_mem_Vk {g : PP p} {K : ℕ} (hv : ∀ v ∈ g.vars, v ∈ V) (hd : g.totalDegree ≤ K) :
    PCL.ml g ∈ Vk (F := ZMod p) V K := by
  rw [mem_Vk]
  intro T hT
  refine ⟨?_, (card_le_totalDegree hT).trans hd⟩
  obtain ⟨m, hm, rfl⟩ := support_ml_subset g T hT
  intro i hi
  exact hv i ((mem_vars i).2 ⟨m, hm, hi⟩)

lemma totalDegree_lincomb {d : ℕ} (c : Fin s → ZMod p) (g : Fin s → PP p)
    (hg : ∀ i, (g i).totalDegree ≤ d) : (∑ i, c i • g i).totalDegree ≤ d := by
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
  exact (totalDegree_smul_le _ _).trans (hg i)

lemma vars_lincomb (c : Fin s → ZMod p) (g : Fin s → PP p) (hg : ∀ i, ∀ v ∈ (g i).vars, v ∈ V) :
    ∀ v ∈ (∑ i, c i • g i).vars, v ∈ V := by
  classical
  intro v hv
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 (vars_sum_subset _ _ hv)
  rw [MvPolynomial.smul_eq_C_mul] at hi
  have := vars_mul (C (c i) : PP p) (g i) hi
  rw [vars_C, Finset.empty_union] at this
  exact hg i v this

lemma totalDegree_one_sub_pow_le {q : PP p} {d : ℕ} (hq : q.totalDegree ≤ d) (n : ℕ) :
    (1 - q ^ n).totalDegree ≤ n * d := by
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · simp
  · exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hq)

/-- Cancelling a square: if `g (P g) e ∈ C_D` then `P g e ∈ C_D` (uses `g^p - g ∈ C_D`). -/
lemma frob_cancel (hD : 2 ≤ D) {P g e : PP p} {a d k : ℕ} (hP : P.totalDegree ≤ a)
    (hg : g.totalDegree ≤ d) (he : e.totalDegree ≤ k) (hbud : a + k + p * d ≤ D)
    (h : g * (P * g) * e ∈ CD Ax D) : P * g * e ∈ CD Ax D := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h1 : g ^ (p - 2) * (g * (P * g) * e) ∈ CD Ax D := by
    refine cd_mul h ?_
    have e1 : (g ^ (p - 2)).totalDegree ≤ (p - 2) * d :=
      (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hg)
    have e2 : (g * (P * g) * e).totalDegree ≤ d + (a + d) + k :=
      (totalDegree_mul _ _).trans (Nat.add_le_add
        ((totalDegree_mul _ _).trans (Nat.add_le_add hg ((totalDegree_mul _ _).trans (Nat.add_le_add hP hg)))) he)
    have e3 : (p - 2) * d + 2 * d = p * d := by
      rw [← Nat.add_mul]; congr 1; omega
    omega
  have h2 : (P * e) * (g ^ p - g) ∈ CD Ax D := by
    refine cd_mul (cd_frobenius hD hg (le_trans (Nat.le_add_left _ _) hbud)) ?_
    have := totalDegree_frob_le hg
    have e4 : (P * e).totalDegree ≤ a + k := (totalDegree_mul _ _).trans (Nat.add_le_add hP he)
    omega
  have : P * g * e = g ^ (p - 2) * (g * (P * g) * e) - (P * e) * (g ^ p - g) := by
    have hpp : g ^ p = g ^ (p - 2) * g * g := by
      rw [← pow_succ, ← pow_succ]; congr 1; omega
    rw [hpp]; ring
  rw [this]
  exact sub_mem h1 h2

end Helpers

section OneStep
variable {Ax : Set (PP p)} {D : ℕ} {V : Finset ℕ} {s : ℕ}

/-- The rank `c_P(k)` of `T_{P,k}`. -/
def cP (Ax : Set (PP p)) (D : ℕ) (V : Finset ℕ) (P : PP p) (g : Fin s → PP p) (k : ℕ) : ℕ :=
  Module.finrank (ZMod p) (LinearMap.range (Tmap Ax D V P g k))

/-- **Pang Lemma 4.2 (approximation gain)**: there is `q = ∑ c_i g_i` with
`c_{P(1-q^{p-1})}(K) ≤ c_P(K) - (1 - 1/p) c_P(K-d)` (stated without division). -/
theorem onestep (hD : 2 ≤ D) (P : PP p) (g : Fin s → PP p) {a d K : ℕ}
    (hP : P.totalDegree ≤ a) (hg : ∀ α, (g α).totalDegree ≤ d)
    (hgV : ∀ α, ∀ v ∈ (g α).vars, v ∈ V) (hdK : d ≤ K) (hbud : a + K + p * d ≤ D) :
    ∃ c : Fin s → ZMod p,
      (p - 1) * cP Ax D V P g (K - d) +
        p * cP Ax D V (P * (1 - (∑ i, c i • g i) ^ (p - 1))) g K ≤ p * cP Ax D V P g K := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpd : d ≤ p * d := Nat.le_mul_of_pos_left d (by omega)
  -- Corollary 3.4
  obtain ⟨c, hc⟩ := pang_cor34 (Ax := Ax) hD (iotaV V (K - d)) (k := K - d) (a := d) (b := a + d)
    (fun x => totalDegree_iotaV V x) g (fun α => P * g α) hg
    (fun α => (totalDegree_mul _ _).trans (Nat.add_le_add hP (hg α))) (by omega)
  refine ⟨c, ?_⟩
  set q : PP p := ∑ i, c i • g i with hq
  have hqd : q.totalDegree ≤ d := totalDegree_lincomb c g hg
  have hqV : ∀ v ∈ q.vars, v ∈ V := vars_lincomb c g hgV
  set P' : PP p := P * (1 - q ^ (p - 1)) with hP'
  have hP'd : P'.totalDegree ≤ a + (p - 1) * d :=
    (totalDegree_mul _ _).trans (Nat.add_le_add hP (totalDegree_one_sub_pow_le hqd _))
  -- stacked rank dominates c_P(K-d)
  have hker1 : LinearMap.ker (LinearMap.pi fun i => multMap Ax D (iotaV V (K - d))
      (fun α => P * g α) (g i)) ≤ LinearMap.ker (Tmap Ax D V P g (K - d)) := by
    intro x hx
    rw [LinearMap.mem_ker, Tmap_eq_zero_iff]
    intro α
    have hx' : ∀ i, multMap Ax D (iotaV V (K - d)) (fun α => P * g α) (g i) x = 0 := fun i =>
      congrFun hx i
    have := (multMap_eq_zero_iff _ _ _ x).1 (hx' α) α
    refine frob_cancel (Ax := Ax) hD hP (hg α) (totalDegree_iotaV V x) (by omega) this
  have hrk1 : cP Ax D V P g (K - d) ≤ Module.finrank (ZMod p) (LinearMap.range
      (LinearMap.pi fun i => multMap Ax D (iotaV V (K - d)) (fun α => P * g α) (g i))) := by
    have e1 := LinearMap.finrank_range_add_finrank_ker (Tmap Ax D V P g (K - d))
    have e2 := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun i =>
      multMap Ax D (iotaV V (K - d)) (fun α => P * g α) (g i))
    have e3 := Submodule.finrank_mono hker1
    unfold cP; omega
  -- the map φ
  have hmem : ∀ x : Vk (F := ZMod p) V (K - d),
      PCL.ml (q * iotaV V (K - d) x) ∈ Vk (F := ZMod p) V K := by
    intro x
    refine ml_mem_Vk (fun v hv => ?_) ?_
    · rcases Finset.mem_union.1 (vars_mul _ _ hv) with h | h
      · exact hqV v h
      · exact vars_polyOf_subset x h
    · refine (totalDegree_mul _ _).trans ?_
      have := totalDegree_iotaV V x
      omega
  let φ : Vk (F := ZMod p) V (K - d) →ₗ[ZMod p] Vk (F := ZMod p) V K :=
    LinearMap.codRestrict (Vk V K) (PCL.ml ∘ₗ LinearMap.mulLeft (ZMod p) q ∘ₗ iotaV V (K - d)) hmem
  have hφ : ∀ x, (φ x).1 = PCL.ml (q * iotaV V (K - d) x) := fun x => rfl
  have hdiff : ∀ x : Vk (F := ZMod p) V (K - d),
      q * iotaV V (K - d) x - iotaV V K (φ x) ∈ CD Ax D := by
    intro x
    have h := cd_sub_polyOf_ml (Ax := Ax) hD (g := q * iotaV V (K - d) x) (by
      refine le_trans ((totalDegree_mul _ _).trans (Nat.add_le_add hqd (totalDegree_iotaV V x))) ?_
      omega)
    exact h
  have hTφ : multMap Ax D (iotaV V (K - d)) (fun α => P * g α) q =
      Tmap Ax D V P g K ∘ₗ φ := by
    ext x α
    simp only [multMap, Tmap, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Submodule.mkQ_apply, one_mul]
    rw [Submodule.Quotient.eq]
    have := cd_mul (hdiff x) (g := P * g α) (by
      have h1 : (q * iotaV V (K - d) x - iotaV V K (φ x)).totalDegree ≤ K := by
        refine (totalDegree_sub _ _).trans (max_le ?_ (totalDegree_iotaV V _))
        refine (totalDegree_mul _ _).trans ?_
        have := totalDegree_iotaV V x
        omega
      have h2 := (totalDegree_mul _ _).trans (Nat.add_le_add hP (hg α))
      omega)
    convert this using 1
    ring
  -- kernel containment
  have hker2 : LinearMap.ker (Tmap Ax D V P g K) ≤ LinearMap.ker (Tmap Ax D V P' g K) := by
    intro x hx
    rw [LinearMap.mem_ker, Tmap_eq_zero_iff] at hx ⊢
    intro α
    have := cd_mul (hx α) (g := 1 - q ^ (p - 1)) (by
      have h1 := totalDegree_one_sub_pow_le hqd (p - 1)
      have h2 : (P * g α * iotaV V K x).totalDegree ≤ a + d + K :=
        (totalDegree_mul _ _).trans (Nat.add_le_add
          ((totalDegree_mul _ _).trans (Nat.add_le_add hP (hg α))) (totalDegree_iotaV V x))
      have h3 : (p - 1) * d + d = p * d := by
        rw [← Nat.succ_mul]; congr 1; omega
      omega)
    convert this using 1
    simp only [hP']; ring
  have hker3 : LinearMap.range φ ≤ LinearMap.ker (Tmap Ax D V P' g K) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, Tmap_eq_zero_iff]
    intro α
    set w := iotaV V (K - d) x with hw
    have hwd : w.totalDegree ≤ K - d := totalDegree_iotaV V x
    have hu : (P' * g α).totalDegree ≤ a + p * d := by
      refine (totalDegree_mul _ _).trans ?_
      have h3 : (p - 1) * d + d = p * d := by
        rw [← Nat.succ_mul]; congr 1; omega
      have := hg α
      omega
    -- first part: P' gα (q w - r) ∈ C_D
    have h1 : P' * g α * (q * w - iotaV V K (φ x)) ∈ CD Ax D := by
      refine cd_mul (hdiff x) (g := P' * g α) ?_
      have h1 : (q * w - iotaV V K (φ x)).totalDegree ≤ K := by
        refine (totalDegree_sub _ _).trans (max_le ?_ (totalDegree_iotaV V _))
        refine (totalDegree_mul _ _).trans ?_
        omega
      omega
    -- second part: P' gα q w = - (P gα w) (q^p - q)
    have hqf : q ^ p - q ∈ CD Ax D := cd_frobenius hD hqd (le_trans (Nat.le_add_left _ _) hbud)
    have h2 : (P * g α * w) * (q ^ p - q) ∈ CD Ax D := by
      refine cd_mul hqf ?_
      have h4 : (P * g α * w).totalDegree ≤ a + d + (K - d) :=
        (totalDegree_mul _ _).trans (Nat.add_le_add
          ((totalDegree_mul _ _).trans (Nat.add_le_add hP (hg α))) hwd)
      have h5 := totalDegree_frob_le hqd
      omega
    have hpq : q ^ p = q ^ (p - 1) * q := by
      rw [← pow_succ]; congr 1; omega
    have key : P' * g α * iotaV V K (φ x) =
        -(P' * g α * (q * w - iotaV V K (φ x))) - (P * g α * w) * (q ^ p - q) := by
      rw [hP', hpq]; ring
    rw [key]
    exact sub_mem (neg_mem h1) h2
  -- assemble
  have hAL := finrank_ker_add_rank_le (Tmap Ax D V P g K) φ _ hker2 hker3
  have e1 := LinearMap.finrank_range_add_finrank_ker (Tmap Ax D V P g K)
  have e2 := LinearMap.finrank_range_add_finrank_ker (Tmap Ax D V P' g K)
  have hMq : Module.finrank (ZMod p) (LinearMap.range (multMap Ax D (iotaV V (K - d))
      (fun α => P * g α) q)) = Module.finrank (ZMod p) (LinearMap.range (Tmap Ax D V P g K ∘ₗ φ)) := by
    rw [hTφ]
  rw [hMq] at hc
  unfold cP at hrk1 ⊢
  set A := Module.finrank (ZMod p) (LinearMap.range (Tmap Ax D V P g (K - d)))
  set S := Module.finrank (ZMod p) (LinearMap.range
      (LinearMap.pi fun i => multMap Ax D (iotaV V (K - d)) (fun α => P * g α) (g i)))
  set M := Module.finrank (ZMod p) (LinearMap.range (Tmap Ax D V P g K ∘ₗ φ))
  set B := Module.finrank (ZMod p) (LinearMap.range (Tmap Ax D V P' g K))
  set C := Module.finrank (ZMod p) (LinearMap.range (Tmap Ax D V P g K))
  have hBMC : B + M ≤ C := by omega
  have h1' := Nat.mul_le_mul_left (p - 1) hrk1
  have h2' := Nat.mul_le_mul_left p hBMC
  nlinarith [h1', h2', hc]

end OneStep

end

end Pang
