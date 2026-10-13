import Theory.ProofComplexity.BraunCoordPairs
import Theory.ProofComplexity.BraunCubeDrop
import Theory.ProofComplexity.BraunRowLinear
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Row cube coefficient isolation (R4 Phase 2.1, layer 7j)

Credit. Port, with proofs adapted to our modules, of K. Braun (arXiv 2609.23015, author's Lean
development): `RowCubeCoefficientIsolation.lean` (`row_cube_coefficient_isolation`: mixed binary coordinate differences isolate a prescribed maximal row monomial coefficient of a row linear polynomial). Statements keep his quantifier shape.

LOG: R4 BraunRowCubeIsolation module (Phase 2.1 layer 7)
-/

namespace SATurday.ProofComplexity.BraunPC

noncomputable section

open MvPolynomial
open scoped BigOperators Classical

section

open MvPolynomial
open scoped BigOperators Classical

private theorem row_monomial_product {m ℓ k : ℕ} (y : RowMonomialIndex m ℓ k) (c : ZMod 2) :
    monomial (rowMonomialExponent y) c =
      C c * ∏ i : y.2.1.val, (X (i.val,y.2.2 i) : Poly (ZMod 2) (Fin m × Fin ℓ)) := by
  have hs : (rowMonomialExponent y).support = rowMonomialCells y := by
    simp [rowMonomialExponent]
  rw [monomial_eq,Finsupp.prod,hs]
  congr 1
  calc
    _ = ∏ v ∈ rowMonomialCells y, (X v : Poly (ZMod 2) (Fin m × Fin ℓ)) := by
      apply Finset.prod_congr rfl
      intro v hv
      have he : rowMonomialExponent y v = 1 :=
        Multiset.count_eq_one_of_mem (rowMonomialCells y).nodup hv
      rw [he,pow_one]
    _ = _ := by
      simp [rowMonomialCells]

private theorem coordinate_bit_difference {W : Type} (ℓ : ℕ) (d t : Fin ℓ) (c : Fin (2^ℓ)) :
    (∑ b : ZMod 2, (C (bitLabelEquiv ℓ (if b=0 then c else flipColumn ℓ d c) t) :
      Poly (ZMod 2) W)) = if t=d then 1 else 0 := by
  change (∑ b : Fin 2, (C (bitLabelEquiv ℓ (if b=0 then c else flipColumn ℓ d c) t) :
      Poly (ZMod 2) W)) = _
  rw [Fin.sum_univ_two]
  simp only [one_ne_zero,↓reduceIte,flipColumn_label]
  rw [← map_add,← add_assoc,ZModModule.add_self,zero_add]
  split_ifs <;> simp

private theorem same_rows_exponent_eq {m ℓ k : ℕ} (j : Fin (k+1))
    (S : (Finset.univ : Finset (Fin m)).powersetCard j.val) (d e : S.val → Fin ℓ) :
    rowMonomialExponent (⟨j,S,d⟩ : RowMonomialIndex m ℓ k) =
      rowMonomialExponent ⟨j,S,e⟩ ↔ d=e := by
  constructor
  · intro h
    have he := rowMonomialExponent_injective h
    have he' : (⟨S,d⟩ : Σ T : (Finset.univ : Finset (Fin m)).powersetCard j.val,
        T.val → Fin ℓ) = ⟨S,e⟩ := eq_of_heq (Sigma.mk.inj_iff.mp he).2
    exact eq_of_heq (Sigma.mk.inj_iff.mp he').2
  · intro h
    subst e
    rfl

private theorem row_monomial_cube_sum {m ℓ k : ℕ} {W : Type}
    (x y : RowMonomialIndex m ℓ k) (hy : y.1.val ≤ x.1.val)
    (base : x.2.1.val → Fin (2^ℓ))
    (Φ : (x.2.1.val → ZMod 2) → (Fin m × Fin ℓ → Poly (ZMod 2) W))
    (hselected : ∀ ε (i : x.2.1.val) t,
      Φ ε (i.val,t) = C (bitLabelEquiv ℓ
        (if ε i=0 then base i else flipColumn ℓ (x.2.2 i) (base i)) t))
    (houtside : ∀ ε ε' v, v.1 ∉ x.2.1.val → Φ ε v = Φ ε' v) (c : ZMod 2) :
    (∑ ε : x.2.1.val → ZMod 2, aeval (Φ ε) (monomial (rowMonomialExponent y) c)) =
      if rowMonomialExponent y = rowMonomialExponent x then C c else 0 := by
  rcases x with ⟨j,S,d⟩
  rcases y with ⟨l,T,e⟩
  change l.val ≤ j.val at hy
  by_cases hST : S.val ⊆ T.val
  · have hScard : S.val.card = j.val := (Finset.mem_powersetCard.mp S.property).2
    have hTcard : T.val.card = l.val := (Finset.mem_powersetCard.mp T.property).2
    have hsets : S.val = T.val := Finset.eq_of_subset_of_card_le hST (by omega)
    have hj : l=j := Fin.ext (by rw [← hTcard,← hScard,hsets])
    subst l
    have hTS : T=S := Subtype.ext hsets.symm
    subst T
    simp only [same_rows_exponent_eq]
    have hterm (ε : S.val → ZMod 2) :
        aeval (Φ ε) (monomial (rowMonomialExponent (⟨j,S,e⟩ : RowMonomialIndex m ℓ k)) c) =
          C c * ∏ i : S.val, C (bitLabelEquiv ℓ
            (if ε i=0 then base i else flipColumn ℓ (d i) (base i)) (e i)) := by
      rw [row_monomial_product]
      simp only [map_mul,map_prod,aeval_C,aeval_X,hselected]
      rfl
    calc
      _ = C c * ∑ ε : S.val → ZMod 2, ∏ i : S.val, C (bitLabelEquiv ℓ
          (if ε i=0 then base i else flipColumn ℓ (d i) (base i)) (e i)) := by
        simp_rw [hterm]
        rw [Finset.mul_sum]
      _ = C c * ∏ i : S.val, ∑ b : ZMod 2, C (bitLabelEquiv ℓ
          (if b=0 then base i else flipColumn ℓ (d i) (base i)) (e i)) := by
        rw [Fintype.prod_sum]
      _ = C c * ∏ i : S.val, (if e i=d i then (1 : Poly (ZMod 2) W) else 0) := by
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        exact coordinate_bit_difference ℓ (d i) (e i) (base i)
      _ = _ := by
        by_cases hed : e=d
        · simp [hed]
        · obtain ⟨i,hi⟩ := Function.ne_iff.mp hed
          have hp : (∏ r : S.val, if e r=d r then (1 : Poly (ZMod 2) W) else 0)=0 :=
            Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
          rw [hp,mul_zero,if_neg hed]
  · obtain ⟨r,hrS,hrT⟩ := Finset.not_subset.mp hST
    let i : S.val := ⟨r,hrS⟩
    have hxy : rowMonomialExponent (⟨l,T,e⟩ : RowMonomialIndex m ℓ k) ≠
        rowMonomialExponent ⟨j,S,d⟩ := by
      intro he
      have hidx := rowMonomialExponent_injective he
      have hrows := congrArg (fun z : RowMonomialIndex m ℓ k => z.2.1.val) hidx
      change T.val=S.val at hrows
      exact hrT (hrows.symm ▸ hrS)
    rw [if_neg hxy]
    have hflip (ε : S.val → ZMod 2) :
        aeval (Φ (flipChoice i ε)) (monomial (rowMonomialExponent (⟨l,T,e⟩ : RowMonomialIndex m ℓ k)) c) =
        aeval (Φ ε) (monomial (rowMonomialExponent (⟨l,T,e⟩ : RowMonomialIndex m ℓ k)) c) := by
      simp only [row_monomial_product,map_mul,map_prod,aeval_C,aeval_X]
      congr 1
      apply Finset.prod_congr rfl
      intro v _
      by_cases hvS : v.val ∈ S.val
      · let q : S.val := ⟨v.val,hvS⟩
        have hqi : q ≠ i := by
          intro he
          have hev : v.val=r := congrArg Subtype.val he
          exact hrT (hev ▸ v.property)
        have h1 := hselected (flipChoice i ε) q (e v)
        have h2 := hselected ε q (e v)
        change Φ (flipChoice i ε) (q.val,e v) = Φ ε (q.val,e v)
        rw [h1,h2]
        simp [flipChoice,hqi]
      · exact houtside (flipChoice i ε) ε (v.val,e v) hvS
    have hc := cube_sum_cancel (I := S.val) (A := Poly (ZMod 2) W) i (fun ε : S.val → ZMod 2 =>
      aeval (Φ ε) (monomial (rowMonomialExponent (⟨l,T,e⟩ : RowMonomialIndex m ℓ k)) c))
      (fun ε => hflip ε)
    rw [← hc]
    exact Finset.sum_congr (by congr <;> exact Subsingleton.elim _ _) (fun _ _ => rfl)

theorem row_cube_coefficient_isolation {m ℓ k : ℕ} {W : Type}
    (P : Poly (ZMod 2) (Fin m × Fin ℓ))
    (hp : P ∈ rowLinearSpace (ZMod 2) m ℓ k)
    (x : RowMonomialIndex m ℓ k) (hdegree : P.totalDegree ≤ x.1.val)
    (base : x.2.1.val → Fin (2^ℓ))
    (Φ : (x.2.1.val → ZMod 2) → (Fin m × Fin ℓ → Poly (ZMod 2) W))
    (hselected : ∀ ε (i : x.2.1.val) t,
      Φ ε (i.val,t) = C (bitLabelEquiv ℓ
        (if ε i=0 then base i else flipColumn ℓ (x.2.2 i) (base i)) t))
    (houtside : ∀ ε ε' v, v.1 ∉ x.2.1.val → Φ ε v = Φ ε' v) :
    (∑ ε : x.2.1.val → ZMod 2, aeval (Φ ε) P) = C (P.coeff (rowMonomialExponent x)) := by
  calc
    _ = ∑ ε : x.2.1.val → ZMod 2, ∑ d ∈ P.support, aeval (Φ ε) (monomial d (P.coeff d)) := by
      apply Finset.sum_congr rfl
      intro ε _
      conv_lhs => rw [P.as_sum,map_sum]
    _ = ∑ d ∈ P.support, ∑ ε : x.2.1.val → ZMod 2, aeval (Φ ε) (monomial d (P.coeff d)) :=
      Finset.sum_comm
    _ = ∑ d ∈ P.support, if d = rowMonomialExponent x then C (P.coeff d) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨y,rfl⟩ := hp hd
      have hy : y.1.val ≤ x.1.val := by
        rw [← rowMonomialExponent_degree y]
        exact (le_totalDegree hd).trans hdegree
      exact row_monomial_cube_sum x y hy base Φ hselected houtside _
    _ = _ := by
      by_cases hx : rowMonomialExponent x ∈ P.support
      · simp [hx]
      · have hz : P.coeff (rowMonomialExponent x)=0 := notMem_support_iff.mp hx
        simp [hx,hz]


end

end

end SATurday.ProofComplexity.BraunPC
