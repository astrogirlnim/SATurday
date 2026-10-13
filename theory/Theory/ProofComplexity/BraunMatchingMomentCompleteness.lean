import Theory.ProofComplexity.BraunMatchingNormalForm
import Mathlib.LinearAlgebra.LinearPMap

/-!
# Matching moment completeness (R4 Phase 2.1, layer 6b)

Credit. Port, with our own proofs where they differ, of K. Braun (arXiv 2609.23015, author's Lean
development) `MatchingMomentCompleteness.lean` (`audit:matching-moment-completeness`): a functional
annihilates the ordinary Nullstellensatz space of the functional unary base at degree `B` iff it
annihilates the matching base and its squarefree moments satisfy the missing row marginal equations;
the moment functional `momentFunctional` built from a moment table `z`; and the bounded version on
the degree `B` subspace (`bounded_matching_moment_completeness`, `bounded_moment_recovery`).
`annihilator_extension` is his third party `LinearSeparation.annihilator_extension` (extend a
functional on a subspace `U` that kills `U ∩ S` to the whole space killing `S`).

LOG: R4 BraunMatchingMomentCompleteness module (Phase 2.1 layer 6b)
-/

namespace SATurday.ProofComplexity.BraunPC

noncomputable section

open MvPolynomial
open scoped BigOperators Classical

section Separation
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- Extension of a functional on `U` killing `U ∩ S` to a functional on `M` killing `S`
(Braun, `LinearSeparation.annihilator_extension`). -/
theorem annihilator_extension (U S : Submodule K M) (l : U →ₗ[K] K)
    (hcompat : ∀ x : U, (x : M) ∈ S → l x = 0) :
    ∃ L : M →ₗ[K] K, (∀ x : U, L x = l x) ∧ ∀ x ∈ S, L x = 0 := by
  let f : M →ₗ.[K] K := ⟨U, l⟩
  let g : M →ₗ.[K] K := ⟨S, 0⟩
  have hc : ∀ (x : f.domain) (y : g.domain), (x : M) = y → f x = g y := by
    intro x y hxy
    apply hcompat x
    exact hxy ▸ y.property
  let h := f.sup g hc
  obtain ⟨L, hL⟩ := h.toFun.exists_extend
  refine ⟨L, ?_, ?_⟩
  · intro x
    let z : ↥(U ⊔ S) := ⟨x, (le_sup_left : U ≤ U ⊔ S) x.property⟩
    have hz : (x : M) + ((0 : S) : M) = (z : M) := by simp [z]
    have hh := LinearPMap.sup_apply hc x (0 : S) z hz
    have he := LinearMap.congr_fun hL z
    change L (x : M) = h z at he
    exact he.trans (by simpa [f, g, h] using hh)
  · intro x hx
    let y : S := ⟨x, hx⟩
    let z : ↥(U ⊔ S) := ⟨x, (le_sup_right : S ≤ U ⊔ S) hx⟩
    have hz : ((0 : U) : M) + (y : M) = (z : M) := by simp [y, z]
    have hh := LinearPMap.sup_apply hc (0 : U) y z hz
    have he := LinearMap.congr_fun hL z
    change L x = h z at he
    exact he.trans (by simpa [f, g, h] using hh)

end Separation

def AnnihilatesNS {V : Type} (F : Set (Poly (ZMod 2) V)) (B : ℕ)
    (L : Poly (ZMod 2) V →ₗ[ZMod 2] ZMod 2) : Prop :=
  ∀ p ∈ nsSpace F B, L p=0

def MatchingMarginals (m N B : ℕ) (z : Finset (Cell m N) → ZMod 2) : Prop :=
  ∀ S, IsMatching S → S.card<B → ∀ i : Fin m, RowUnused i S →
    (∑ j : Fin N, if ColUnused j S then z (insert (i,j) S) else 0)=z S

theorem annihilates_matching_normal (m N B : ℕ)
    (L : Poly (ZMod 2) (Cell m N) →ₗ[ZMod 2] ZMod 2)
    (hL : AnnihilatesNS (matchingBase m N) B L)
    (P : Poly (ZMod 2) (Cell m N)) (hP : P.totalDegree≤B) :
    L P=L (matchingNormal m N P) := by
  have h := hL _ (nsSpace_mono (Set.Subset.refl _) hP (matchingNormal_ns m N P))
  rw [map_sub,sub_eq_zero] at h
  exact h

private theorem support_row_degree (m N : ℕ) (S : Finset (Cell m N)) (i : Fin m) :
    (sqMonomial S*rowEquation m N i).totalDegree≤S.card+1 :=
  (totalDegree_mul _ _).trans (Nat.add_le_add (sqMonomial_degree S) (rowEquation_degree_le m N i))

private theorem functional_matching_subset (m N : ℕ) :
    matchingBase m N ⊆ functionalUnaryBase (K := ZMod 2) m N := by
  rw [functionalUnaryBase_eq]
  exact Set.subset_union_left

private theorem functional_row_mem (m N : ℕ) (i : Fin m) :
    rowEquation m N i ∈ functionalUnaryBase (K := ZMod 2) m N := by
  rw [functionalUnaryBase_eq]
  exact Or.inr ⟨i,rfl⟩

theorem annihilates_implies_marginals (m N B : ℕ)
    (L : Poly (ZMod 2) (Cell m N) →ₗ[ZMod 2] ZMod 2)
    (hL : AnnihilatesNS (functionalUnaryBase m N) B L) :
    MatchingMarginals m N B (fun S => L (sqMonomial S)) := by
  have hmatch : AnnihilatesNS (matchingBase m N) B L :=
    fun p hp => hL p (nsSpace_mono (functional_matching_subset m N) le_rfl hp)
  intro S hS hcard i hi
  have hdeg : (sqMonomial S*rowEquation m N i).totalDegree≤B :=
    (support_row_degree m N S i).trans (by omega)
  have hz := hL _ (nsSpace_generator (functional_row_mem m N i) hdeg)
  have he := annihilates_matching_normal m N B L hmatch _ hdeg
  rw [matchingNormal_row_unused m N S hS i hi] at he
  have he' : L ((∑ j : Fin N, if ColUnused j S then sqMonomial (insert (i,j) S) else 0)-sqMonomial S)=0 :=
    he.symm.trans hz
  simpa only [map_sub,map_sum,apply_ite,map_zero,sub_eq_zero] using he'

private theorem matching_row_value_zero (m N B : ℕ)
    (L : Poly (ZMod 2) (Cell m N) →ₗ[ZMod 2] ZMod 2)
    (hL : AnnihilatesNS (matchingBase m N) B L)
    (hm : MatchingMarginals m N B (fun S => L (sqMonomial S)))
    (S : Finset (Cell m N)) (hS : IsMatching S) (hcard : S.card<B) (i : Fin m) :
    L (sqMonomial S*rowEquation m N i)=0 := by
  have hdeg : (sqMonomial S*rowEquation m N i).totalDegree≤B :=
    (support_row_degree m N S i).trans (by omega)
  rw [annihilates_matching_normal m N B L hL _ hdeg]
  by_cases hi : RowUnused i S
  · rw [matchingNormal_row_unused m N S hS i hi]
    simpa only [map_sub,map_sum,apply_ite,map_zero,sub_eq_zero] using hm S hS hcard i hi
  · rw [matchingNormal_row_occupied m N S hS i hi,map_zero]

theorem marginals_implies_annihilates (m N B : ℕ) (hN : 1≤N)
    (L : Poly (ZMod 2) (Cell m N) →ₗ[ZMod 2] ZMod 2)
    (hL : AnnihilatesNS (matchingBase m N) B L)
    (hm : MatchingMarginals m N B (fun S => L (sqMonomial S))) :
    AnnihilatesNS (functionalUnaryBase m N) B L := by
  intro P hP
  induction hP using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨f,hf,q,rfl,hdeg⟩ := hp
    rw [functionalUnaryBase_eq] at hf
    rcases hf with hf | hf
    · exact hL _ (nsSpace_generator hf hdeg)
    · obtain ⟨i,rfl⟩ := hf
      change L (q*rowEquation m N i)=0
      change (q*rowEquation m N i).totalDegree≤B at hdeg
      by_cases hq : q=0
      · simp [hq]
      have hdq : q.totalDegree+1≤B := by
        rw [totalDegree_mul_of_isDomain hq (rowEquation_ne_zero m N hN i),rowEquation_degree m N hN i] at hdeg
        exact hdeg
      have herr : rowEquation m N i*(q-matchingNormal m N q) ∈ nsSpace (matchingBase m N) B :=
        nsSpace_mono (Set.Subset.refl _) (by rw [rowEquation_degree m N hN i]; exact hdq)
          (nsSpace_mul (matchingNormal_ns m N q) (rowEquation m N i))
      have he := hL _ herr
      rw [mul_sub,map_sub,sub_eq_zero] at he
      have hnormal : L (matchingNormal m N q*rowEquation m N i)=0 := by
        change L ((∑ d ∈ q.support, q.coeff d • matchingBasis d)*rowEquation m N i)=0
        rw [Finset.sum_mul,map_sum]
        apply Finset.sum_eq_zero
        intro d hd
        rw [smul_mul_assoc,map_smul]
        by_cases hdmatch : IsMatching d.support
        · simp only [matchingBasis,hdmatch,↓reduceIte]
          have hcard : d.support.card≤d.sum (fun _ n => n) := by
            change d.support.card≤∑ x ∈ d.support, d x
            calc
              d.support.card=∑ _x ∈ d.support, 1 := by simp
              _≤∑ x ∈ d.support, d x := Finset.sum_le_sum (fun x hx =>
                Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hx))
          have hb : d.support.card<B := lt_of_le_of_lt (hcard.trans (le_totalDegree hd)) (by omega)
          rw [matching_row_value_zero m N B L hL hm d.support hdmatch hb i,smul_zero]
        · simp [matchingBasis,hdmatch]
      simpa only [mul_comm] using he.trans (by simpa only [mul_comm] using hnormal)
  | zero => exact map_zero _
  | add p q _ _ hp hq => rw [map_add,hp,hq,add_zero]
  | smul c p _ hp => rw [map_smul,hp,smul_zero]

theorem matching_marginal_completeness (m N B : ℕ) (hN : 1≤N)
    (L : Poly (ZMod 2) (Cell m N) →ₗ[ZMod 2] ZMod 2) :
    AnnihilatesNS (functionalUnaryBase m N) B L ↔
      AnnihilatesNS (matchingBase m N) B L ∧
        MatchingMarginals m N B (fun S => L (sqMonomial S)) := by
  constructor
  · intro h
    exact ⟨fun p hp => h p (nsSpace_mono (functional_matching_subset m N) le_rfl hp),
      annihilates_implies_marginals m N B L h⟩
  · rintro ⟨h,hm⟩
    exact marginals_implies_annihilates m N B hN L h hm
def momentRead (m N : ℕ) (z : Finset (Cell m N) → ZMod 2) :
    Poly (ZMod 2) (Cell m N) →ₗ[ZMod 2] ZMod 2 :=
  (Finsupp.linearCombination (ZMod 2) (fun d : Cell m N →₀ ℕ => z d.support)).comp
    (AddMonoidAlgebra.coeffLinearEquiv (ZMod 2)).toLinearMap

private theorem momentRead_monomial (m N : ℕ) (z : Finset (Cell m N) → ZMod 2)
    (d : Cell m N →₀ ℕ) (c : ZMod 2) : momentRead m N z (monomial d c)=c*z d.support :=
  Finsupp.linearCombination_single (ZMod 2) c d

private theorem momentRead_support (m N : ℕ) (z : Finset (Cell m N) → ZMod 2)
    (S : Finset (Cell m N)) : momentRead m N z (sqMonomial S)=z S := by
  rw [sqMonomial_eq_monomial,momentRead_monomial,squarefreeExponent_support,one_mul]

def momentFunctional (m N : ℕ) (z : Finset (Cell m N) → ZMod 2) :
    Poly (ZMod 2) (Cell m N) →ₗ[ZMod 2] ZMod 2 :=
  (momentRead m N z).comp (matchingNormal m N)

theorem momentFunctional_support (m N : ℕ) (z : Finset (Cell m N) → ZMod 2)
    (S : Finset (Cell m N)) (hS : IsMatching S) : momentFunctional m N z (sqMonomial S)=z S := by
  change momentRead m N z (matchingNormal m N (sqMonomial S))=z S
  rw [matchingNormal_support]
  simp only [hS,↓reduceIte,momentRead_support]

theorem momentFunctional_monomial (m N : ℕ) (z : Finset (Cell m N) → ZMod 2)
    (d : Cell m N →₀ ℕ) (c : ZMod 2) :
    momentFunctional m N z (monomial d c) = if IsMatching d.support then c*z d.support else 0 := by
  change momentRead m N z (matchingNormal m N (monomial d c))=_
  rw [matchingNormal_monomial,map_smul]
  by_cases h : IsMatching d.support <;> simp [matchingBasis,h,momentRead_support,smul_eq_mul]

theorem momentFunctional_one (m N : ℕ) (z : Finset (Cell m N) → ZMod 2) :
    momentFunctional m N z 1=z ∅ := by
  have h : IsMatching (∅ : Finset (Cell m N)) := by constructor <;> simp
  simpa [sqMonomial] using momentFunctional_support m N z ∅ h

theorem momentFunctional_annihilates_matching (m N B : ℕ) (z : Finset (Cell m N) → ZMod 2) :
    AnnihilatesNS (matchingBase m N) B (momentFunctional m N z) := by
  intro p hp
  change momentRead m N z (matchingNormal m N p)=0
  rw [matchingNormal_ns_zero m N B p hp,map_zero]

theorem momentFunctional_annihilates (m N B : ℕ) (hN : 1≤N)
    (z : Finset (Cell m N) → ZMod 2) (hz : MatchingMarginals m N B z) :
    AnnihilatesNS (functionalUnaryBase m N) B (momentFunctional m N z) := by
  apply marginals_implies_annihilates m N B hN _ (momentFunctional_annihilates_matching m N B z)
  intro S hS hcard i hi
  dsimp only
  rw [momentFunctional_support m N z S hS]
  calc
    _ = ∑ j : Fin N, if ColUnused j S then z (insert (i,j) S) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : ColUnused j S
      · simp only [hj,↓reduceIte]
        exact momentFunctional_support m N z _ ((matching_insert_unused S hS i hi j).mpr hj)
      · simp [hj]
    _ = z S := hz S hS hcard i hi

theorem momentFunctional_of_values (m N : ℕ)
    (L : Poly (ZMod 2) (Cell m N) →ₗ[ZMod 2] ZMod 2) (P : Poly (ZMod 2) (Cell m N)) :
    momentFunctional m N (fun S => L (sqMonomial S)) P=L (matchingNormal m N P) := by
  change momentRead m N (fun S => L (sqMonomial S))
    (∑ d ∈ P.support, P.coeff d • matchingBasis d)=L (∑ d ∈ P.support, P.coeff d • matchingBasis d)
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [map_smul,map_smul]
  by_cases h : IsMatching d.support <;> simp [matchingBasis,h,momentRead_support]

def BoundedAnnihilator (m N B : ℕ)
    (L : degreeSpace (K := ZMod 2) (V := Cell m N) B →ₗ[ZMod 2] ZMod 2) : Prop :=
  ∀ p : degreeSpace B, (p : Poly (ZMod 2) (Cell m N)) ∈ nsSpace (functionalUnaryBase m N) B → L p=0

theorem bounded_matching_moment_completeness (m N B : ℕ) (hN : 1≤N)
    (L : degreeSpace (K := ZMod 2) (V := Cell m N) B →ₗ[ZMod 2] ZMod 2) :
    BoundedAnnihilator m N B L ↔
      ∃ z : Finset (Cell m N) → ZMod 2, MatchingMarginals m N B z ∧
        ∀ p : degreeSpace B, L p=momentFunctional m N z p.val := by
  constructor
  · intro hL
    obtain ⟨E,hE,hzero⟩ := annihilator_extension
      (degreeSpace (K := ZMod 2) (V := Cell m N) B)
      (nsSpace (functionalUnaryBase m N) B) L hL
    refine ⟨fun S => E (sqMonomial S), annihilates_implies_marginals m N B E hzero, ?_⟩
    intro p
    rw [← hE p,momentFunctional_of_values]
    exact annihilates_matching_normal m N B E
      (fun q hq => hzero q (nsSpace_mono (functional_matching_subset m N) le_rfl hq)) p.val p.property
  · rintro ⟨z,hz,hL⟩ p hp
    rw [hL p]
    exact momentFunctional_annihilates m N B hN z hz p.val hp

theorem bounded_moment_recovery (m N B : ℕ)
    (L : degreeSpace (K := ZMod 2) (V := Cell m N) B →ₗ[ZMod 2] ZMod 2)
    (z : Finset (Cell m N) → ZMod 2)
    (hL : ∀ p : degreeSpace B, L p=momentFunctional m N z p.val)
    (S : Finset (Cell m N)) (hS : IsMatching S) (hcard : S.card≤B) :
    L ⟨sqMonomial S,(sqMonomial_degree S).trans hcard⟩=z S := by
  rw [hL,momentFunctional_support m N z S hS]

end

end SATurday.ProofComplexity.BraunPC
