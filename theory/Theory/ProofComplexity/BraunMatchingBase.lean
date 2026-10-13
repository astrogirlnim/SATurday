import Theory.ProofComplexity.BraunPC

/-!
# Matching base prelude (R4 Phase 2.1, layer 7h; the definitional part of layer 6)

Credit. Port of the definitions of K. Braun (arXiv 2609.23015, author's Lean development)
`MatchingNormalForm.lean`: `Cell`, `exclusionBase`, `matchingBase`, `rowBase`, `rowEquation` and
`functionalUnaryBase_eq` (the functional unary base is the matching base plus the row equations).
Only what the row cube layer needs; the matching normal form itself (and `IsMatching`, which uses
the chessboard complex) belongs to layer 6 and is not ported here.

LOG: R4 BraunMatchingBase module (Phase 2.1 layer 7h)
-/

namespace SATurday.ProofComplexity.BraunPC

noncomputable section

open MvPolynomial
open scoped BigOperators Classical

abbrev Cell (m N : ℕ) := Fin m × Fin N

def exclusionBase (m N : ℕ) : Set (Poly (ZMod 2) (Cell m N)) :=
  {p | ∃ x y : Cell m N, x ≠ y ∧ (x.1=y.1 ∨ x.2=y.2) ∧ p=X x*X y}

def matchingBase (m N : ℕ) : Set (Poly (ZMod 2) (Cell m N)) :=
  booleanBase ∪ exclusionBase m N

def rowBase (m N : ℕ) : Set (Poly (ZMod 2) (Cell m N)) :=
  {p | ∃ i : Fin m, p=(∑ j : Fin N, X (i,j))-1}



theorem functionalUnaryBase_eq (m N : ℕ) :
    functionalUnaryBase (K := ZMod 2) m N = matchingBase m N ∪ rowBase m N := by
  ext p
  constructor
  · rintro (((hb | hr) | hc) | hr)
    · exact Or.inl (Or.inl hb)
    · exact Or.inr hr
    · obtain ⟨i,i',j,hne,rfl⟩ := hc
      exact Or.inl (Or.inr ⟨(i,j),(i',j),fun h => hne (congrArg Prod.fst h),Or.inr rfl,rfl⟩)
    · obtain ⟨i,j,j',hne,rfl⟩ := hr
      exact Or.inl (Or.inr ⟨(i,j),(i,j'),fun h => hne (congrArg Prod.snd h),Or.inl rfl,rfl⟩)
  · rintro ((hb | hc) | hr)
    · exact Or.inl (Or.inl (Or.inl hb))
    · obtain ⟨⟨i,j⟩,⟨i',j'⟩,hne,hc,rfl⟩ := hc
      rcases hc with hr | hc
      · change i=i' at hr
        subst i'
        exact Or.inr ⟨i,j,j',fun h => hne (Prod.ext rfl h),rfl⟩
      · change j=j' at hc
        subst j'
        exact Or.inl (Or.inr ⟨i,i',j,fun h => hne (Prod.ext h rfl),rfl⟩)
    · exact Or.inl (Or.inl (Or.inr hr))

def rowEquation (m N : ℕ) (i : Fin m) : Poly (ZMod 2) (Cell m N) :=
  (∑ j : Fin N, X (i,j))-1

end

end SATurday.ProofComplexity.BraunPC
