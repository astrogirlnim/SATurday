import Theory.ProofComplexity.ReviewFollowups
import Theory.ProofComplexity.EmbedTree
import Theory.ProofComplexity.FregeRankBridge

/-!
# Non-vacuity with refutation existence for `RLD`, `RLDag` and `RRefutation`

Referee follow-up 3 (`docs/reports/response-to-expert-review-2026-11-19.md`, Section C).  For every
unsatisfiable CNF whose variables lie in `V`:

* `rld_refutation_of_unsat`: a tree-like `Res(lin F_p)` refutation (`RLF.RLD`) exists (some width and
  leaf count);
* `rldag_refutation_of_unsat`: a dag-like one (`RLF.RLDag`) exists;
* `rref_of_unsat`: a refutation in the bounded rank calculus `C1.RRefutation` exists for every
  `ρ ≥ 1`.

All three are existence only (no size control), from completeness of resolution.  Then the explicit
indexed instance `tcnf (cubFam m) q (tseitinCharge1 ..)` gets the combined statement
(regular, connected, expansion, unsatisfiable, a refutation exists, every refutation is large),
like `tseitin_dag_exp_idx_nonvacuous` does for `Pang.Refutation`.
-/

namespace SATurday.ProofComplexity

open TseitinPC

section Res

open scoped Classical

variable {p : ℕ} [Fact p.Prime]

/-- Resolution into tree-like `Res(lin F_p)`: every resolution derivation of a clause `C` gives an
`RLD` derivation of the linear clause `ofCl C`, for some width and leaf count. -/
theorem rld_of_derivation {F : Type} [Field F] {Φ : CNF} {C : Clause} (d : Derivation Φ C) :
    ∃ w s, RLF.RLD (((fun C => (RLF.ofCl C : Finset (RLF.LEq (F)))) '' Φ) ∪ RLF.boolAx)
      w (RLF.ofCl C) s := by
  induction d with
  | hyp C hC => exact ⟨_, 1, RLF.RLD.ax (Or.inl ⟨C, hC, rfl⟩) le_rfl⟩
  | @res x C D dC dD hx hnx ihC ihD =>
    obtain ⟨wC, sC, hC⟩ := ihC
    obtain ⟨wD, sD, hD⟩ := ihD
    set W := wC + wD + 1
    have hC' := RLF.rld_mono_w (show wC ≤ W by omega) hC
    have hD' := RLF.rld_mono_w (show wD ≤ W by omega) hD
    have he1 : RLF.litEq (F := F) ⟨x, true⟩ ∈ (RLF.ofCl C : Finset (RLF.LEq (F))) :=
      Finset.mem_image_of_mem _ hx
    have he2 : RLF.litEq (F := F) ⟨x, false⟩ ∈ (RLF.ofCl D : Finset (RLF.LEq (F))) :=
      Finset.mem_image_of_mem _ hnx
    have hcard := RLF.rld_card hC
    have hcard2 := RLF.rld_card hD
    have hcA := Finset.card_erase_le (a := RLF.litEq (F := F) ⟨x, true⟩)
      (s := (RLF.ofCl C : Finset (RLF.LEq (F))))
    have hcB := Finset.card_erase_le (a := RLF.litEq (F := F) ⟨x, false⟩)
      (s := (RLF.ofCl D : Finset (RLF.LEq (F))))
    have hw : ((RLF.ofCl C : Finset (RLF.LEq (F))).erase (RLF.litEq ⟨x, true⟩) ∪
        (RLF.ofCl D : Finset (RLF.LEq (F))).erase (RLF.litEq ⟨x, false⟩) ∪
        {RLF.cmb (1 : F) (-1) (RLF.litEq ⟨x, true⟩) (RLF.litEq ⟨x, false⟩)}).card ≤ W := by
      refine (Finset.card_union_le _ _).trans ?_
      have := Finset.card_union_le ((RLF.ofCl C : Finset (RLF.LEq (F))).erase
        (RLF.litEq ⟨x, true⟩)) ((RLF.ofCl D : Finset (RLF.LEq (F))).erase
        (RLF.litEq ⟨x, false⟩))
      simp only [Finset.card_singleton]
      omega
    have hcomb := RLF.RLD.comb (RLF.litEq ⟨x, true⟩) (RLF.litEq ⟨x, false⟩) (1 : F) (-1)
      hC' hD' he1 he2 hw
    have hcm : RLF.cmb (1 : F) (-1) (RLF.litEq ⟨x, true⟩) (RLF.litEq ⟨x, false⟩) =
        ((0 : ℕ →₀ F), (1 : F)) := by
      simp [RLF.cmb, RLF.litEq]
    rw [hcm] at hcomb
    have heq : (RLF.ofCl C : Finset (RLF.LEq (F))).erase (RLF.litEq ⟨x, true⟩) ∪
        (RLF.ofCl D : Finset (RLF.LEq (F))).erase (RLF.litEq ⟨x, false⟩) ∪
        {((0 : ℕ →₀ F), (1 : F))} =
        insert ((0 : ℕ →₀ F), (1 : F))
          ((RLF.ofCl C : Finset (RLF.LEq (F))).erase (RLF.litEq ⟨x, true⟩) ∪
            (RLF.ofCl D : Finset (RLF.LEq (F))).erase (RLF.litEq ⟨x, false⟩)) := by
      rw [Finset.union_comm _ {_}]; rfl
    rw [heq] at hcomb
    have hs := RLF.RLD.simp (1 : F) one_ne_zero hcomb
    have hres : RLF.ofCl (F := F) (resolvent C D x) =
        (RLF.ofCl C : Finset (RLF.LEq (F))).erase (RLF.litEq ⟨x, true⟩) ∪
        (RLF.ofCl D : Finset (RLF.LEq (F))).erase (RLF.litEq ⟨x, false⟩) := by
      unfold resolvent RLF.ofCl
      rw [Finset.image_union, Finset.image_erase RLF.litEq_inj, Finset.image_erase RLF.litEq_inj]
    rw [hres]
    exact ⟨W, _, hs⟩

theorem ofCl_empty_eq {F : Type} [Field F] : (RLF.ofCl (∅ : Clause) : Finset (RLF.LEq F)) = ∅ :=
  Finset.image_empty _

/-- **Non-vacuity, tree-like `Res(lin F_p)`.** -/
theorem rld_refutation_of_unsat {Φ : CNF} (h : ¬ Satisfiable Φ) :
    ∃ w s, RLF.RLD (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' Φ) ∪ RLF.boolAx)
      w ∅ s := by
  obtain ⟨d⟩ := resolution_complete h
  obtain ⟨w, s, hd⟩ := rld_of_derivation (F := ZMod p) d
  rw [ofCl_empty_eq] at hd
  exact ⟨w, s, hd⟩

/-- **Non-vacuity, dag-like `Res(lin F_p)` (`RLDag`).** -/
theorem rldag_refutation_of_unsat {Φ : CNF} (h : ¬ Satisfiable Φ) :
    ∃ 𝓛 : Finset (Finset (RLF.LEq (ZMod p))),
      RLF.RLDag (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) '' Φ) ∪ RLF.boolAx) 𝓛 ∧
        (∅ : Finset (RLF.LEq (ZMod p))) ∈ 𝓛 := by
  obtain ⟨w, s, hd⟩ := rld_refutation_of_unsat (p := p) h
  obtain ⟨n, hn⟩ := RLF.rld_to_rln hd
  obtain ⟨𝓛, h1, h2, -⟩ := RLF.rln_refutes_to_rldag hn
  exact ⟨𝓛, h1, h2⟩

end Res

section Rank

open C1 FBridge

variable {p : ℕ} [Fact p.Prime]

theorem goodL_clauseRLine {V : Finset ℕ} {ρ : ℕ} (hρ : 1 ≤ ρ) {C : Clause}
    (hV : ∀ l ∈ C, l.var ∈ V) : GoodL V ρ (clauseRLine (p := p) C) := by
  intro T hT
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hT
  have hv := hV l hl
  unfold litTerm
  split_ifs
  · refine goodT_singleton hρ ?_
    simpa [formVarSub, Finsupp.support_single_subset] using
      (Finsupp.support_single_subset.trans (Finset.singleton_subset_iff.2 hv))
  · refine goodT_singleton hρ ?_
    simpa [formVar] using
      (Finsupp.support_single_subset.trans (Finset.singleton_subset_iff.2 hv))

/-- Resolution into `R_ρ^p`: list derivations. -/
theorem der_of_derivation {Φ : CNF} {V : Finset ℕ} {ρ : ℕ} (hρ : 1 ≤ ρ)
    (hV : ∀ C ∈ Φ, ∀ l ∈ C, l.var ∈ V) {C : Clause} (d : Derivation Φ C) :
    (∀ l ∈ C, l.var ∈ V) ∧ ∀ Ls : List (RLine p), Der Φ V ρ Ls →
      ∃ Ls₂ : List (RLine p), Der Φ V ρ Ls₂ ∧ (∀ M ∈ Ls, M ∈ Ls₂) ∧
        clauseRLine C ∈ Ls₂ := by
  induction d with
  | hyp C hC =>
    refine ⟨hV C hC, fun Ls h => ?_⟩
    obtain ⟨Ls₂, ⟨h2, hm, -⟩, hmem⟩ := reach_step h (prems := []) (by simp)
      (RInfer.init C hC) (goodL_clauseRLine hρ (hV C hC))
    exact ⟨Ls₂, h2, hm, hmem⟩
  | @res x C D dC dD hx hnx ihC ihD =>
    obtain ⟨vC, ihC⟩ := ihC
    obtain ⟨vD, ihD⟩ := ihD
    have hR : ∀ l ∈ resolvent C D x, l.var ∈ V := by
      intro l hl
      unfold resolvent at hl
      rcases Finset.mem_union.1 hl with h | h
      · exact vC l (Finset.mem_of_mem_erase h)
      · exact vD l (Finset.mem_of_mem_erase h)
    refine ⟨hR, fun Ls h => ?_⟩
    obtain ⟨L1, h1, m1, c1⟩ := ihC Ls h
    obtain ⟨L2, h2, m2, c2⟩ := ihD L1 h1
    have hC2 : clauseRLine (p := p) C ∈ L2 := m2 _ c1
    have hs : RInfer Φ ρ [clauseRLine (p := p) C, clauseRLine D] (clauseRLine (resolvent C D x)) := by
      refine RInfer.sem2 (T₁ := litTerm ⟨x, true⟩) (T₂ := litTerm ⟨x, false⟩) (T₃ := none)
        (Finset.mem_image_of_mem _ hx) (Finset.mem_image_of_mem _ hnx) ?_ _ ?_ ?_ ?_ ?_
      · intro a h1 h2
        exfalso
        have e1 : ev (boolPt (F := ZMod p) a) (formVarSub x) = 0 :=
          h1 _ (by simp [litTerm])
        have e2 : ev (boolPt (F := ZMod p) a) (formVar x) = 0 :=
          h2 _ rfl _ (by simp [litTerm])
        rw [ev_formVarSub] at e1
        rw [ev_formVar] at e2
        rw [e2] at e1
        simp at e1
      · intro T hT
        obtain ⟨hne, hT⟩ := Finset.mem_erase.1 hT
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hT
        refine Finset.mem_image.2 ⟨l, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, hl⟩), rfl⟩
        rintro rfl; exact hne rfl
      · intro T hT
        obtain ⟨hne, hT⟩ := Finset.mem_erase.1 hT
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hT
        refine Finset.mem_image.2 ⟨l, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, hl⟩), rfl⟩
        rintro rfl; exact hne rfl
      · intro T hT; simp at hT
      · intro T hT; simp at hT
    obtain ⟨L3, ⟨h3, m3, -⟩, c3⟩ := reach_step h2 (prems := [clauseRLine C, clauseRLine D])
      (by
        intro M hM
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
        rcases hM with rfl | rfl
        · exact hC2
        · exact c2) hs (goodL_clauseRLine hρ hR)
    exact ⟨L3, h3, fun M hM => m3 _ (m2 _ (m1 _ hM)), c3⟩

/-- **Non-vacuity, bounded rank calculus.** An unsatisfiable CNF over `V` has an `R_ρ^p`
refutation for every `ρ ≥ 1` (existence only). -/
theorem rref_of_unsat {Φ : CNF} {V : Finset ℕ} {ρ : ℕ} (hρ : 1 ≤ ρ)
    (hV : ∀ C ∈ Φ, ∀ l ∈ C, l.var ∈ V) (h : ¬ Satisfiable Φ) :
    Nonempty (RRefutation Φ V ρ p) := by
  obtain ⟨d⟩ := resolution_complete h
  obtain ⟨-, H⟩ := der_of_derivation (p := p) hρ hV d
  obtain ⟨Ls, hD, -, hmem⟩ := H [] Der.nil
  have : clauseRLine (p := p) (∅ : Clause) = ∅ := Finset.image_empty _
  rw [this] at hmem
  obtain ⟨R, -⟩ := der_refutation hD hmem
  exact ⟨R⟩

end Rank

/-! ## The explicit indexed instances -/

/-- **Tree-like `Res(lin F_p)`: non-vacuous indexed statement.**  For every `m ≥ tseitinFloor p q`
the instance `tcnf (cubFam m) q (tseitinCharge1 ..)` is on a connected cubic expander, is
unsatisfiable, has a tree-like refutation, and every tree-like refutation has `2 s` at least the
stated power of two. -/
theorem reslin_tseitin_size_idx_nonvacuous (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (hpq : ¬ p ∣ q) {m : ℕ} (hm : tseitinFloor p q ≤ m) :
    IsRegular (cubFam m) 3 ∧ (cubFam m).IsConnected ∧ HasExpansionInv (cubFam m) mggF2CubK ∧
      ∑ v, tseitinCharge1 (m * m * 8) q v ≠ 0 ∧
      ¬ Satisfiable (tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q)) ∧
      (∃ w s, RLF.RLD (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) ''
          tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q)) ∪ RLF.boolAx) w ∅ s) ∧
      ∀ w s : ℕ, RLF.RLD (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) ''
          tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q)) ∪ RLF.boolAx) w ∅ s →
        2 ^ (((((m * m * 8) - 2) / 1312 - q * (q + 3)) / (q - 1) - (q + 3) - p) / (p - 1)) ≤ 2 * s := by
  obtain ⟨-, hI⟩ : True ∧ mggInformativeFloor ≤ m := ⟨trivial, (cubFam_floor_le hm).1⟩
  obtain ⟨hreg, hconn, hexp⟩ := cubFam_props hI
  obtain ⟨hs, hu⟩ := tseitin_idx_explicit_unsat p hq hm
  exact ⟨hreg, hconn, hexp, hs, hu, rld_refutation_of_unsat hu,
    fun w s h => reslin_tseitin_size_idx p hq hpq hm _ w s h⟩

/-- **Dag-like `Res(lin F_p)` (`RLDag`): non-vacuous indexed statement.** -/
theorem reslin_tseitin_dag_size_idx_nonvacuous (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (hpq : ¬ p ∣ q) {m : ℕ} (hm : tseitinFloor p q ≤ m) :
    IsRegular (cubFam m) 3 ∧ (cubFam m).IsConnected ∧ HasExpansionInv (cubFam m) mggF2CubK ∧
      ∑ v, tseitinCharge1 (m * m * 8) q v ≠ 0 ∧
      ¬ Satisfiable (tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q)) ∧
      (∃ 𝓛 : Finset (Finset (RLF.LEq (ZMod p))),
        RLF.RLDag (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) ''
          tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q)) ∪ RLF.boolAx) 𝓛 ∧
          (∅ : Finset (RLF.LEq (ZMod p))) ∈ 𝓛) ∧
      q + 5 ≤ tseitinW p q (m * m * 8) ∧
      ∀ 𝓛 : Finset (Finset (RLF.LEq (ZMod p))),
        RLF.RLDag (((fun C => (RLF.ofCl C : Finset (RLF.LEq (ZMod p)))) ''
          tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q)) ∪ RLF.boolAx) 𝓛 →
        (∅ : Finset (RLF.LEq (ZMod p))) ∈ 𝓛 →
        ((tseitinW p q (m * m * 8) - (q + 3)) * (tseitinW p q (m * m * 8) - (q + 3)) <
          72 * (q + 3) * 𝓛.card * (Nat.log 2 (3 * 𝓛.card) + 1)) ∧
        (tseitinW p q (m * m * 8) - (q + 3)) * (tseitinW p q (m * m * 8) - (q + 3)) /
          (72 * (q + 3) * (Nat.log 2 (3 * ((tseitinW p q (m * m * 8) - (q + 3)) *
            (tseitinW p q (m * m * 8) - (q + 3))) ) + 1)) ≤ 𝓛.card := by
  obtain ⟨hreg, hconn, hexp⟩ := cubFam_props (cubFam_floor_le hm).1
  obtain ⟨hs, hu⟩ := tseitin_idx_explicit_unsat p hq hm
  obtain ⟨hW, H⟩ := reslin_tseitin_dag_size_idx p hq hpq hm
  exact ⟨hreg, hconn, hexp, hs, hu, rldag_refutation_of_unsat hu, hW,
    fun 𝓛 h h0 => H _ 𝓛 h h0⟩

/-- **Bounded rank calculus: non-vacuous indexed statement** (outside the fidelity request). -/
theorem c1_main_idx_nonvacuous (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (ε : ℝ) (hε : 0 < ε) (hεκ : (C1.kappa p q + 1) * ε < 1) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
      IsRegular (cubFam m) 3 ∧ (cubFam m).IsConnected ∧ HasExpansionInv (cubFam m) mggF2CubK ∧
      ¬ Satisfiable (tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q)) ∧
      (∀ ρ : ℕ, 1 ≤ ρ → Nonempty (C1.RRefutation (tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q))
        (tVars (cubFam m) q) ρ p)) ∧
      ∀ ρ : ℕ, 1 ≤ ρ → (ρ : ℝ) ≤ ε * Real.log (m * m * 8 : ℕ) →
      ∀ R : C1.RRefutation (tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q))
        (tVars (cubFam m) q) ρ p,
        Real.exp (((m * m * 8 : ℕ) : ℝ) ^ (1 - (C1.kappa p q + 1) * ε)) ≤ R.S := by
  obtain ⟨m0, hm0⟩ := C1.c1_main_idx p hq hpq ε hε hεκ
  refine ⟨max m0 (tseitinFloor p q), fun m hm => ?_⟩
  have hF : tseitinFloor p q ≤ m := (le_max_right _ _).trans hm
  have hM : m0 ≤ m := (le_max_left _ _).trans hm
  obtain ⟨hreg, hconn, hexp⟩ := cubFam_props (cubFam_floor_le hF).1
  obtain ⟨-, hu⟩ := tseitin_idx_explicit_unsat p hq hF
  refine ⟨hreg, hconn, hexp, hu, fun ρ hρ => rref_of_unsat hρ ?_ hu, fun ρ h1 h2 R =>
    hm0 m hM _ ρ h1 h2 R⟩
  intro C hC l hl
  exact (tcnf_clause_props hreg hC).1 (Finset.mem_image_of_mem _ hl)

end SATurday.ProofComplexity
