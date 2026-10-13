import Theory.ProofComplexity.ResLinFPC
import Theory.ProofComplexity.ResLinFWidth

/-!
# Tree-like size gives polynomial calculus degree for CNFs (Ladder Rung R4, Phase 2.2, layer 4a)

Part-Tzameret Theorems 44 and 45 combined: a tree-like `Res(lin F_p)` refutation of a CNF `Φ`
(clauses of at most `w0 ≥ 2` literals) with `s` leaves, of arbitrary width, gives a polynomial
calculus refutation of `Φ` over `F_p` of degree `w0 + (p - 1) ⌈log₂ s⌉ + p` (`rld_cnf_size`).

LOG: R4 Phase 2.2 ResLinFSize module
-/

namespace SATurday.ProofComplexity

namespace RLF

open scoped Classical

noncomputable section

theorem ofCl_noZ {F : Type} [Field F] (C : Clause) : ∀ e ∈ (ofCl C : Finset (LEq F)), ¬ IsZ e := by
  intro e he hz
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.1 he
  have := hz.1
  simp only [litEq] at this
  exact one_ne_zero (Finsupp.single_eq_zero.1 this)

/-- **Size gives degree** (Theorems 44 and 45). -/
theorem rld_cnf_size {p : ℕ} [Fact p.Prime] {Φ : CNF} {w0 : ℕ} (hw0 : 2 ≤ w0)
    (hΦ : ∀ C ∈ Φ, C.card ≤ w0) {w s : ℕ}
    (h : RLD (((fun C => (ofCl C : Finset (LEq (ZMod p)))) '' Φ) ∪ boolAx) w ∅ s) :
    PCD (cnfAx (F := ZMod p) Φ) (w0 + (p - 1) * Nat.clog 2 s + p) 1 := by
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  obtain ⟨s', h'⟩ := rld_size_width (Ax := (fun C => (ofCl C : Finset (LEq (ZMod p)))) '' Φ)
    hw0 (by
      rintro _ ⟨C, hC, rfl⟩
      exact (ofCl_card_le C).trans (hΦ C hC)) (by
      rintro _ ⟨C, hC, rfl⟩
      exact ofCl_noZ C) h
  rw [hcard] at h'
  exact rld_cnf_pcd (fun a => ZMod.pow_card a) (by omega) (fun C hC => (hΦ C hC).trans (by omega)) h'

end

end RLF

end SATurday.ProofComplexity
