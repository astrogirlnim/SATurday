import Theory.ProofComplexity.PangDag
import Theory.ProofComplexity.ResLinFDag

/-!
# Linear equations over `F_p` versus polynomials of degree at most one (for the Pang embeddings)

`RLF.LEq (ZMod p)` is a pair `(c, a)` read as `∑ c_i x_i = a`; Pang's lines are sets of
polynomials `h` read as `h = 0`. The map `phi (c, a) = ∑ c_i X_i - a` is injective, compatible with
the resolution combination (`phi_cmb`), has degree `≤ 1`, and every polynomial of total degree
`≤ 1` is in its image (`exists_phi`).
-/

open SATurday.ProofComplexity MvPolynomial

namespace SATurday.ProofComplexity

namespace RLF

noncomputable section

open Classical

variable {p : ℕ} [Fact p.Prime]

/-- The linear polynomial `∑ c_i X_i`. -/
def lin (c : ℕ →₀ ZMod p) : MvPolynomial ℕ (ZMod p) := c.sum fun i a => C a * X i

/-- The polynomial `∑ c_i X_i - a` of the equation `∑ c_i x_i = a`. -/
def phi (e : LEq (ZMod p)) : MvPolynomial ℕ (ZMod p) := lin e.1 - C e.2

theorem lin_add (c d : ℕ →₀ ZMod p) : lin (c + d) = lin c + lin d := by
  unfold lin
  exact Finsupp.sum_add_index' (fun i => by simp) (fun i a b => by simp [add_mul])

theorem lin_smul (α : ZMod p) (c : ℕ →₀ ZMod p) : lin (α • c) = C α * lin c := by
  unfold lin
  rw [Finsupp.sum_smul_index' (fun i => by simp), Finsupp.mul_sum]
  simp [mul_assoc]

theorem lin_single (i : ℕ) (a : ZMod p) : lin (Finsupp.single i a) = C a * X i := by
  unfold lin
  rw [Finsupp.sum_single_index (by simp)]

theorem phi_cmb (α β : ZMod p) (e1 e2 : LEq (ZMod p)) :
    phi (cmb α β e1 e2) = C α * phi e1 + C β * phi e2 := by
  simp only [phi, cmb, lin_add, lin_smul, map_add, map_mul]
  ring

theorem coeff_lin (c : ℕ →₀ ZMod p) (m : ℕ →₀ ℕ) :
    coeff m (lin c) = c.sum fun i a => if Finsupp.single i 1 = m then a else 0 := by
  unfold lin
  rw [Finsupp.sum, Finsupp.sum, coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_C_mul, coeff_X']
  split_ifs <;> simp

theorem coeff_lin_single (c : ℕ →₀ ZMod p) (j : ℕ) :
    coeff (Finsupp.single j 1) (lin c) = c j := by
  rw [coeff_lin]
  have : (c.sum fun i a => if Finsupp.single i 1 = Finsupp.single j 1 then a else 0) =
      c.sum fun i a => if i = j then a else 0 := by
    refine Finsupp.sum_congr fun i _ => ?_
    have : (Finsupp.single i 1 = Finsupp.single j 1) ↔ i = j :=
      Finsupp.single_left_inj one_ne_zero
    simp only [this]
  rw [this]
  by_cases hj : j ∈ c.support
  · rw [Finsupp.sum, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd hj h
  · have : c j = 0 := Finsupp.notMem_support_iff.1 hj
    rw [this, Finsupp.sum]
    exact Finset.sum_eq_zero fun i hi => by
      have : i ≠ j := fun h => hj (h ▸ hi)
      simp [this]

theorem coeff_lin_zero (c : ℕ →₀ ZMod p) : coeff 0 (lin c) = 0 := by
  rw [coeff_lin]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : Finsupp.single i 1 ≠ (0 : ℕ →₀ ℕ) := by
    intro h
    have := congrArg (fun f => f i) h
    simp at this
  simp [this]

theorem phi_injective : Function.Injective (phi (p := p)) := by
  rintro ⟨c, a⟩ ⟨d, b⟩ h
  have h0 := congrArg (coeff 0) h
  have hs : ∀ j, c j = d j := fun j => by
    have := congrArg (coeff (Finsupp.single j 1)) h
    simp only [phi, coeff_sub, coeff_lin_single, coeff_C] at this
    have h1 : (0 : ℕ →₀ ℕ) ≠ Finsupp.single j 1 := by
      intro h; have := congrArg (fun f => f j) h; simp at this
    simpa [h1] using this
  simp only [phi, coeff_sub, coeff_lin_zero, coeff_C] at h0
  simp at h0
  exact Prod.ext (Finsupp.ext hs) h0

theorem phi_totalDegree (e : LEq (ZMod p)) : (phi e).totalDegree ≤ 1 := by
  unfold phi lin
  refine (totalDegree_sub _ _).trans (max_le ?_ (by simp))
  rw [Finsupp.sum]
  refine totalDegree_finsetSum_le fun i _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  simp

theorem vars_phi (e : LEq (ZMod p)) : ∀ v ∈ (phi e).vars, v ∈ e.1.support := by
  intro v hv
  unfold phi lin at hv
  have h1 := (vars_sub_subset (p := _) (q := _)) hv
  rcases Finset.mem_union.1 h1 with h | h
  · rw [Finsupp.sum] at h
    have h2 := vars_sum_subset _ _ h
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.1 h2
    have h3 := vars_mul _ _ hvi
    rcases Finset.mem_union.1 h3 with h | h
    · simp at h
    · simp at h; subst h; exact hi
  · simp at h

/-- Every polynomial of total degree at most one is `phi` of an equation. -/
theorem exists_phi (h : MvPolynomial ℕ (ZMod p)) (hd : h.totalDegree ≤ 1) :
    ∃ e : LEq (ZMod p), phi e = h := by
  have hsupp : ∀ i, coeff (Finsupp.single i 1) h ≠ 0 → i ∈ h.vars := by
    intro i hi
    rw [mem_vars]
    exact ⟨Finsupp.single i 1, mem_support_iff.2 hi, by simp⟩
  let c : ℕ →₀ ZMod p := Finsupp.onFinset h.vars (fun i => coeff (Finsupp.single i 1) h) hsupp
  refine ⟨(c, -coeff 0 h), ?_⟩
  ext m
  simp only [phi, coeff_sub, coeff_C]
  by_cases hm0 : m = 0
  · subst hm0; simp [coeff_lin_zero]
  · have hm0' : (0 : ℕ →₀ ℕ) ≠ m := fun h => hm0 h.symm
    simp only [hm0', if_false, sub_zero]
    by_cases hs : ∃ j, m = Finsupp.single j 1
    · obtain ⟨j, rfl⟩ := hs
      rw [coeff_lin_single]; rfl
    · push Not at hs
      have h1 : coeff m (lin c) = 0 := by
        rw [coeff_lin]
        refine Finset.sum_eq_zero fun i _ => ?_
        have : Finsupp.single i 1 ≠ m := fun h => hs i h.symm
        simp [this]
      rw [h1]
      by_contra hne
      have hmem : m ∈ h.support := mem_support_iff.2 (Ne.symm hne)
      have hdeg : m.sum (fun _ e => e) ≤ 1 :=
        (le_totalDegree hmem).trans hd
      -- a monomial of degree at most one is zero or a single variable
      rcases Nat.lt_or_ge (m.sum fun _ e => e) 1 with hlt | hge
      · apply hm0
        have : m.sum (fun _ e => e) = 0 := by omega
        rw [Finsupp.sum, Finset.sum_eq_zero_iff] at this
        ext i
        by_cases hi : i ∈ m.support
        · exact this i hi
        · exact Finsupp.notMem_support_iff.1 hi
      · have h1' : m.sum (fun _ e => e) = 1 := by omega
        obtain ⟨j, hj⟩ : ∃ j, j ∈ m.support := by
          by_contra hno
          push Not at hno
          have : m = 0 := Finsupp.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem hno)
          exact hm0 this
        have hmj : m j = 1 := by
          have hle : m j ≤ m.sum (fun _ e => e) :=
            Finset.single_le_sum (f := fun i => m i) (fun _ _ => Nat.zero_le _) hj
          have hpos : 0 < m j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hj)
          omega
        refine hs j ?_
        ext i
        by_cases hij : i = j
        · subst hij; simp [hmj]
        · have : m i = 0 := by
            by_contra hne
            have hi : i ∈ m.support := Finsupp.mem_support_iff.2 hne
            have : m j + m i ≤ m.sum (fun _ e => e) := by
              have := Finset.sum_le_sum_of_subset_of_nonneg
                (f := fun i => m i) (s := {j, i}) (t := m.support)
                (by intro x hx; rcases Finset.mem_insert.1 hx with rfl | hx
                    · exact hj
                    · rw [Finset.mem_singleton.1 hx]; exact hi)
                (fun _ _ _ => Nat.zero_le _)
              rw [Finset.sum_pair (Ne.symm hij)] at this
              exact this
            have hpos : 0 < m i := Nat.pos_of_ne_zero hne
            omega
          simp [this, hij]

end

end RLF

end SATurday.ProofComplexity
