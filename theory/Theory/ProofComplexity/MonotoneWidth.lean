import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Theory.ProofComplexity.ClauseComplexity

/-!
# Monotone Transform and Width Bound (R1, BP96 Lemma 1 / G6)

Beame and Pitassi 1996 Lemma 1 support, adapted to PHP(n+1, n):

1. Buss monotone transform: each negative grid literal ¬p_{i,k} expands to
   {p_{t,k} | t ≠ i}. Critical satisfaction (hence L and pigeonComplexity) is
   invariant.
2. Swap lemma: for i ∈ L(C), j ∉ L(C), and an i-critical falsifier π, the
   positive literal p_{i, hole_π(j)} lies in the monotone image.
3. One-pigeon width: for each i ∈ L(C), the monotone image has size at least
   |L(C)ᶜ| = (n+1) − pigeonComplexity(C).

The full product bound m·((n+1)−m) and the intermediate quadratic 2(n+1)²/9
are the next formalize target (assembly over all i ∈ L).

Requires n > 0. Builds on G5.

LOG: R1 monotone width module (BP96 Lemma 1 / G6, partial)
-/

namespace SATurday.ProofComplexity

open Classical

/-! ## Grid variable decoding -/

/-- A variable is a PHP(n+1, n) grid variable when it lies in `[0, (n+1)n)`. -/
def isGridVar (n : ℕ) (v : ℕ) : Prop := v < (n + 1) * n

theorem isGridVar_pvar (n : ℕ) (i : Fin (n + 1)) (j : Fin n) :
    isGridVar n (pvar n i j) := by
  simp only [isGridVar, pvar]
  calc i.val * n + j.val
      < i.val * n + n := Nat.add_lt_add_left j.isLt _
    _ = (i.val + 1) * n := by rw [Nat.succ_mul]
    _ ≤ (n + 1) * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)

/-- Pigeon coordinate of a grid variable (`v / n`). -/
def gridPigeon (n : ℕ) (_hn : 0 < n) (v : ℕ) (hv : isGridVar n v) : Fin (n + 1) :=
  ⟨v / n, by
    have : v < n * (n + 1) := by
      rw [Nat.mul_comm]; exact hv
    exact Nat.div_lt_of_lt_mul this⟩

/-- Hole coordinate of a grid variable (`v % n`). -/
def gridHole (n : ℕ) (hn : 0 < n) (v : ℕ) (_hv : isGridVar n v) : Fin n :=
  ⟨v % n, Nat.mod_lt v hn⟩

theorem gridPigeon_pvar (n : ℕ) (hn : 0 < n) (i : Fin (n + 1)) (j : Fin n) :
    gridPigeon n hn (pvar n i j) (isGridVar_pvar n i j) = i := by
  apply Fin.ext
  simp only [gridPigeon, pvar]
  rw [Nat.mul_comm i.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, Nat.add_zero]

theorem gridHole_pvar (n : ℕ) (hn : 0 < n) (i : Fin (n + 1)) (j : Fin n) :
    gridHole n hn (pvar n i j) (isGridVar_pvar n i j) = j := by
  apply Fin.ext
  simp [gridHole, pvar, Nat.mul_add_mod_of_lt j.isLt]

theorem pvar_grid_eq (n : ℕ) (hn : 0 < n) (v : ℕ) (hv : isGridVar n v) :
    pvar n (gridPigeon n hn v hv) (gridHole n hn v hv) = v := by
  simp only [pvar, gridPigeon, gridHole]
  rw [Nat.mul_comm (v / n) n]
  exact Nat.div_add_mod v n

/-! ## Monotone transform -/

/-- Expand one literal: positives stay; a negative grid literal ¬p_{i,k} becomes
{p_{t,k} | t ≠ i}; non-grid literals stay unchanged. -/
noncomputable def monotoneLiteral (n : ℕ) (hn : 0 < n) (l : Literal) : Finset Literal :=
  if l.pos then
    {l}
  else if hv : isGridVar n l.var then
    let i := gridPigeon n hn l.var hv
    let k := gridHole n hn l.var hv
    ((Finset.univ : Finset (Fin (n + 1))).erase i).image fun t =>
      (⟨pvar n t k, true⟩ : Literal)
  else
    {l}

/-- Monotone image of a clause (Buss transform). -/
noncomputable def monotoneClause (n : ℕ) (hn : 0 < n) (C : Clause) : Clause :=
  C.biUnion (monotoneLiteral n hn)

/-! ## Critical equivalence -/

theorem litSat_neg_grid_iff {n : ℕ} (pi : Crit n)
    (i : Fin (n + 1)) (k : Fin n) :
    litSat (criticalAssignment n pi) ⟨pvar n i k, false⟩ ↔
      ∃ t : Fin (n + 1), t ≠ i ∧ pi t = Fin.castSucc k := by
  constructor
  · intro hfalse
    have hne : pi i ≠ Fin.castSucc k := by
      intro hplace
      have htrue := (criticalAssignment_pvar pi i k).mpr hplace
      have : false = true := by
        change criticalAssignment n pi (pvar n i k) = false at hfalse
        exact hfalse.symm.trans htrue
      exact Bool.noConfusion this
    refine ⟨pi.symm (Fin.castSucc k), ?_, pi.apply_symm_apply _⟩
    intro heq
    apply hne
    rw [← heq, pi.apply_symm_apply]
  · rintro ⟨t, htne, hplace⟩
    have hne_i : pi i ≠ Fin.castSucc k := by
      intro h
      exact htne (pi.injective (h.trans hplace.symm)).symm
    change criticalAssignment n pi (pvar n i k) = false
    cases hval : criticalAssignment n pi (pvar n i k)
    · rfl
    · exact absurd ((criticalAssignment_pvar pi i k).mp hval) hne_i

theorem clauseSat_monotoneLiteral_iff {n : ℕ} (hn : 0 < n) (pi : Crit n) (l : Literal) :
    clauseSat (criticalAssignment n pi) (monotoneLiteral n hn l) ↔
      litSat (criticalAssignment n pi) l := by
  simp only [monotoneLiteral]
  by_cases hpos : l.pos = true
  · simp only [hpos, ↓reduceIte, clauseSat, Finset.mem_singleton, exists_eq_left]
  · have hposf : l.pos = false := eq_false_of_ne_true hpos
    simp only [hposf, Bool.false_eq_true, ↓reduceIte]
    by_cases hv : isGridVar n l.var
    · simp only [hv, ↓reduceDIte]
      let i := gridPigeon n hn l.var hv
      let k := gridHole n hn l.var hv
      have hlit : litSat (criticalAssignment n pi) l ↔
          litSat (criticalAssignment n pi) ⟨pvar n i k, false⟩ := by
        simp only [litSat, hposf]
        rw [(pvar_grid_eq n hn l.var hv).symm]
      rw [hlit, litSat_neg_grid_iff pi i k]
      simp only [clauseSat, Finset.mem_image, litSat]
      constructor
      · rintro ⟨_, ⟨t, htErase, rfl⟩, hsat⟩
        exact ⟨t, (Finset.mem_erase.mp htErase).1,
          (criticalAssignment_pvar pi t k).mp hsat⟩
      · rintro ⟨t, htne, hplace⟩
        exact ⟨⟨pvar n t k, true⟩,
          ⟨t, Finset.mem_erase.mpr ⟨htne, Finset.mem_univ t⟩, rfl⟩,
          (criticalAssignment_pvar pi t k).mpr hplace⟩
    · simp only [hv, ↓reduceDIte, clauseSat, Finset.mem_singleton, exists_eq_left]

theorem clauseSat_monotoneClause_iff {n : ℕ} (hn : 0 < n) (pi : Crit n) (C : Clause) :
    clauseSat (criticalAssignment n pi) (monotoneClause n hn C) ↔
      clauseSat (criticalAssignment n pi) C := by
  simp only [monotoneClause, clauseSat, Finset.mem_biUnion]
  constructor
  · rintro ⟨l', ⟨l, hlC, hl'⟩, hsat⟩
    exact ⟨l, hlC, (clauseSat_monotoneLiteral_iff hn pi l).mp ⟨l', hl', hsat⟩⟩
  · rintro ⟨l, hlC, hsat⟩
    obtain ⟨l', hl', hsat'⟩ := (clauseSat_monotoneLiteral_iff hn pi l).mpr hsat
    exact ⟨l', ⟨l, hlC, hl'⟩, hsat'⟩

theorem falsifies_monotoneClause_iff {n : ℕ} (hn : 0 < n) (C : Clause) (pi : Crit n) :
    falsifies n (monotoneClause n hn C) pi ↔ falsifies n C pi := by
  simp only [falsifies, clauseSat_monotoneClause_iff hn pi C]

theorem L_monotoneClause {n : ℕ} (hn : 0 < n) (C : Clause) :
    L n (monotoneClause n hn C) = L n C := by
  ext i
  simp only [mem_L_iff, falsifies_monotoneClause_iff hn]

theorem pigeonComplexity_monotoneClause {n : ℕ} (hn : 0 < n) (C : Clause) :
    pigeonComplexity n (monotoneClause n hn C) = pigeonComplexity n C := by
  simp only [pigeonComplexity, L_monotoneClause hn]

theorem monotoneClause_not_neg_grid {n : ℕ} (hn : 0 < n) (C : Clause) {l : Literal}
    (hl : l ∈ monotoneClause n hn C) (hneg : l.pos = false) :
    ¬ isGridVar n l.var := by
  simp only [monotoneClause, Finset.mem_biUnion] at hl
  obtain ⟨l0, _, hl0⟩ := hl
  simp only [monotoneLiteral] at hl0
  by_cases hp0 : l0.pos = true
  · simp only [hp0, ↓reduceIte, Finset.mem_singleton] at hl0
    subst hl0
    simp [hp0] at hneg
  · have hp0f : l0.pos = false := eq_false_of_ne_true hp0
    simp only [hp0f, Bool.false_eq_true, ↓reduceIte] at hl0
    by_cases hv0 : isGridVar n l0.var
    · simp only [hv0, ↓reduceDIte, Finset.mem_image] at hl0
      obtain ⟨_, _, rfl⟩ := hl0
      simp at hneg
    · simp only [hv0, ↓reduceDIte, Finset.mem_singleton] at hl0
      subst hl0
      exact hv0

/-! ## Swap construction -/

def Crit.swapLeftOut {n : ℕ} (pi : Crit n) (i j : Fin (n + 1)) : Crit n :=
  Equiv.trans (Equiv.swap i j) pi

theorem Crit.swapLeftOut_apply_j {n : ℕ} (pi : Crit n) {i j : Fin (n + 1)}
    (hi : pi i = Fin.last n) :
    (pi.swapLeftOut i j) j = Fin.last n := by
  simp [Crit.swapLeftOut, Equiv.trans_apply, Equiv.swap_apply_right, hi]

theorem Crit.swapLeftOut_apply_i {n : ℕ} (pi : Crit n) (i j : Fin (n + 1)) :
    (pi.swapLeftOut i j) i = pi j := by
  simp [Crit.swapLeftOut, Equiv.trans_apply, Equiv.swap_apply_left]

theorem Crit.swapLeftOut_apply_other {n : ℕ} (pi : Crit n) {i j t : Fin (n + 1)}
    (hti : t ≠ i) (htj : t ≠ j) :
    (pi.swapLeftOut i j) t = pi t := by
  simp [Crit.swapLeftOut, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hti htj]

def Crit.holeOf {n : ℕ} (pi : Crit n) (j : Fin (n + 1)) (h : pi j ≠ Fin.last n) : Fin n :=
  ⟨(pi j).val, by
    have hle : (pi j).val ≤ n := Nat.lt_succ_iff.mp (pi j).isLt
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact absurd (Fin.ext heq) h⟩

theorem Crit.holeOf_spec {n : ℕ} (pi : Crit n) (j : Fin (n + 1))
    (h : pi j ≠ Fin.last n) :
    pi j = Fin.castSucc (pi.holeOf j h) := by
  apply Fin.ext
  simp [Crit.holeOf]

theorem leftOut_ne_of_mem_L_not_mem {n : ℕ} {C : Clause}
    {i j : Fin (n + 1)} (hi : i ∈ L n C) (hj : j ∉ L n C) : i ≠ j := by
  intro heq; rw [heq] at hi; exact hj hi

theorem placed_of_leftOut_other {n : ℕ} (pi : Crit n) {i j : Fin (n + 1)}
    (hne : i ≠ j) (hleft : pi i = Fin.last n) : pi j ≠ Fin.last n := by
  intro h; exact hne (pi.injective (hleft.trans h.symm))

theorem not_mem_L_not_falsifies {n : ℕ} {C : Clause} {j : Fin (n + 1)}
    (hj : j ∉ L n C) (pi : Crit n) (hleft : pi j = Fin.last n) :
    ¬ falsifies n C pi := by
  intro hf; exact hj ((mem_L_iff C j).mpr ⟨pi, hleft, hf⟩)

/-- The BP96 swap forces `p_{i, hole(j)}` into the monotone image of `C`. -/
theorem monotoneClause_contains_swap_literal {n : ℕ} (hn : 0 < n) (C : Clause)
    {i j : Fin (n + 1)}
    (hiL : i ∈ L n C) (hjL : j ∉ L n C)
    (pi : Crit n) (hleft : pi i = Fin.last n) (hfals : falsifies n C pi) :
    (⟨pvar n i (pi.holeOf j (placed_of_leftOut_other pi
        (leftOut_ne_of_mem_L_not_mem hiL hjL) hleft)), true⟩ : Literal) ∈
      monotoneClause n hn C := by
  let k := pi.holeOf j (placed_of_leftOut_other pi
    (leftOut_ne_of_mem_L_not_mem hiL hjL) hleft)
  let M := monotoneClause n hn C
  have hfalsM : falsifies n M pi := (falsifies_monotoneClause_iff hn C pi).mpr hfals
  have hjLM : j ∉ L n M := by rw [L_monotoneClause hn]; exact hjL
  let σ := pi.swapLeftOut i j
  have hσleft : σ j = Fin.last n := Crit.swapLeftOut_apply_j pi hleft
  have hsat : clauseSat (criticalAssignment n σ) M := by
    have hnf : ¬ falsifies n M σ := not_mem_L_not_falsifies hjLM σ hσleft
    simpa [falsifies] using not_not.mp hnf
  obtain ⟨l, hlM, hla⟩ := hsat
  have hπunsat : ¬ litSat (criticalAssignment n pi) l :=
    (falsifies_iff_forall_lit M pi).mp hfalsM l hlM
  match l with
  | ⟨v, b⟩ =>
    cases hb : b
    · have : criticalAssignment n pi v ≠ false := by
        simpa [litSat, hb] using hπunsat
      have hπtrue : criticalAssignment n pi v = true := by
        cases hval : criticalAssignment n pi v
        · exact absurd hval this
        · rfl
      simp only [criticalAssignment, decide_eq_true_eq] at hπtrue
      obtain ⟨t, h, hvEq, _⟩ := hπtrue
      have hgrid : isGridVar n v := by rw [hvEq]; exact isGridVar_pvar n t h
      exact absurd hgrid
        (monotoneClause_not_neg_grid hn C (by simpa [hb] using hlM) (by simp [hb]))
    · have hσtrue : criticalAssignment n σ v = true := by simpa [litSat, hb] using hla
      have hπfalse : criticalAssignment n pi v = false := by
        cases hval : criticalAssignment n pi v
        · rfl
        · exact False.elim (hπunsat (by simpa [litSat, hb, hval]))
      simp only [criticalAssignment, decide_eq_true_eq] at hσtrue
      obtain ⟨t, h, hvEq, hσplace⟩ := hσtrue
      have hπne : pi t ≠ Fin.castSucc h := by
        intro hp
        have := (criticalAssignment_pvar pi t h).mpr hp
        simp only [hvEq] at hπfalse
        exact Bool.noConfusion (hπfalse.symm.trans this)
      by_cases htj : t = j
      · subst htj
        exact absurd hσplace
          (ne_of_eq_of_ne hσleft (ne_of_gt (Fin.castSucc_lt_last h)))
      · by_cases hti : t = i
        · -- Keep i; rewrite t to i (do not subst i away).
          rw [hti] at hσplace hvEq
          have hplacei : σ i = pi j := Crit.swapLeftOut_apply_i pi i j
          have hcast : Fin.castSucc h = pi j := hσplace.symm.trans hplacei
          have hjne := placed_of_leftOut_other pi
            (leftOut_ne_of_mem_L_not_mem hiL hjL) hleft
          have hEq : h = pi.holeOf j hjne := by
            apply Fin.ext
            calc h.val = (Fin.castSucc h).val := by simp
              _ = (pi j).val := congrArg Fin.val hcast
              _ = (pi.holeOf j hjne).val := by simp [Crit.holeOf]
          have hkEq : k = h := by
            apply Fin.ext
            simp only [k, Crit.holeOf, hEq]
          have hlM' : (⟨pvar n i k, true⟩ : Literal) ∈ M := by
            rw [hkEq, ← hvEq]
            simpa [hb] using hlM
          exact hlM'
        · have : σ t = pi t := Crit.swapLeftOut_apply_other pi hti htj
          exact absurd (this.symm.trans hσplace) hπne

/-! ## One-pigeon width lower bound -/

noncomputable abbrev Lcompl (n : ℕ) (C : Clause) : Finset (Fin (n + 1)) :=
  (L n C)ᶜ

theorem card_Lcompl (n : ℕ) (C : Clause) :
    (Lcompl n C).card = (n + 1) - pigeonComplexity n C := by
  simp only [Lcompl, pigeonComplexity, Finset.card_compl, Fintype.card_fin]

/-- Forced literals for a fixed i-critical falsifier: one per j outside L(C). -/
noncomputable def forcedLitsOne {n : ℕ} (C : Clause) (i : Fin (n + 1))
    (hiL : i ∈ L n C) (pi : Crit n) (hleft : pi i = Fin.last n) : Finset Literal :=
  (Lcompl n C).attach.image fun j =>
    ⟨pvar n i (pi.holeOf j.1 (placed_of_leftOut_other pi
      (leftOut_ne_of_mem_L_not_mem hiL (Finset.mem_compl.mp j.2)) hleft)), true⟩

theorem forcedLitsOne_subset_monotone {n : ℕ} (hn : 0 < n) (C : Clause)
    (i : Fin (n + 1)) (hiL : i ∈ L n C)
    (pi : Crit n) (hleft : pi i = Fin.last n) (hfals : falsifies n C pi) :
    forcedLitsOne C i hiL pi hleft ⊆ monotoneClause n hn C := by
  intro l hl
  simp only [forcedLitsOne, Finset.mem_image] at hl
  obtain ⟨j, _, rfl⟩ := hl
  have hjL : j.1 ∉ L n C := Finset.mem_compl.mp j.2
  exact monotoneClause_contains_swap_literal hn C hiL hjL pi hleft hfals

theorem forcedLitsOne_card {n : ℕ} (C : Clause) (i : Fin (n + 1))
    (hiL : i ∈ L n C) (pi : Crit n) (hleft : pi i = Fin.last n) :
    (forcedLitsOne C i hiL pi hleft).card = (Lcompl n C).card := by
  rw [forcedLitsOne, Finset.card_image_of_injOn, Finset.card_attach]
  intro a _ b _ hab
  apply Subtype.ext
  have hholes :
      pi.holeOf a.1 (placed_of_leftOut_other pi
        (leftOut_ne_of_mem_L_not_mem hiL (Finset.mem_compl.mp a.2)) hleft) =
      pi.holeOf b.1 (placed_of_leftOut_other pi
        (leftOut_ne_of_mem_L_not_mem hiL (Finset.mem_compl.mp b.2)) hleft) :=
    (pvar_inj (congrArg Literal.var hab)).2
  have hpa := Crit.holeOf_spec pi a.1
    (placed_of_leftOut_other pi (leftOut_ne_of_mem_L_not_mem hiL
      (Finset.mem_compl.mp a.2)) hleft)
  have hpb := Crit.holeOf_spec pi b.1
    (placed_of_leftOut_other pi (leftOut_ne_of_mem_L_not_mem hiL
      (Finset.mem_compl.mp b.2)) hleft)
  exact pi.injective (by rw [hpa, hpb, hholes])

/-- For each i ∈ L(C), the monotone image has at least (n+1) − m literals. -/
theorem monotoneClause_card_one_pigeon {n : ℕ} (hn : 0 < n) (C : Clause)
    (i : Fin (n + 1)) (hiL : i ∈ L n C) :
    (n + 1) - pigeonComplexity n C ≤ (monotoneClause n hn C).card := by
  obtain ⟨pi, hleft, hfals⟩ := (mem_L_iff C i).mp hiL
  have hsub := forcedLitsOne_subset_monotone hn C i hiL pi hleft hfals
  have hcard := forcedLitsOne_card C i hiL pi hleft
  calc (n + 1) - pigeonComplexity n C = (Lcompl n C).card := (card_Lcompl n C).symm
    _ = (forcedLitsOne C i hiL pi hleft).card := hcard.symm
    _ ≤ (monotoneClause n hn C).card := Finset.card_le_card hsub

/-! ## Product width bound (G6 assembly) -/

/-- A chosen i-critical falsifier for each i ∈ L(C). -/
noncomputable def chosenFalsifier {n : ℕ} (C : Clause) (i : Fin (n + 1))
    (hiL : i ∈ L n C) : Crit n :=
  Classical.choose ((mem_L_iff C i).mp hiL)

theorem chosenFalsifier_leftOut {n : ℕ} (C : Clause) (i : Fin (n + 1))
    (hiL : i ∈ L n C) :
    (chosenFalsifier C i hiL) i = Fin.last n :=
  (Classical.choose_spec ((mem_L_iff C i).mp hiL)).1

theorem chosenFalsifier_falsifies {n : ℕ} (C : Clause) (i : Fin (n + 1))
    (hiL : i ∈ L n C) :
    falsifies n C (chosenFalsifier C i hiL) :=
  (Classical.choose_spec ((mem_L_iff C i).mp hiL)).2

/-- All forced swap literals across every i ∈ L(C). -/
noncomputable def forcedLitsAll (n : ℕ) (C : Clause) : Finset Literal :=
  (L n C).attach.biUnion fun i =>
    forcedLitsOne C i.1 i.2 (chosenFalsifier C i.1 i.2)
      (chosenFalsifier_leftOut C i.1 i.2)

theorem forcedLitsAll_subset {n : ℕ} (hn : 0 < n) (C : Clause) :
    forcedLitsAll n C ⊆ monotoneClause n hn C := by
  intro l hl
  simp only [forcedLitsAll, Finset.mem_biUnion] at hl
  obtain ⟨i, _, hl'⟩ := hl
  exact forcedLitsOne_subset_monotone hn C i.1 i.2
    (chosenFalsifier C i.1 i.2) (chosenFalsifier_leftOut C i.1 i.2)
    (chosenFalsifier_falsifies C i.1 i.2) hl'

/-- Forced literals for distinct pigeons are disjoint (pvar encodes the pigeon). -/
theorem forcedLitsOne_disjoint {n : ℕ} (C : Clause)
    {i i' : Fin (n + 1)} (hiL : i ∈ L n C) (hiL' : i' ∈ L n C) (hne : i ≠ i')
    (pi : Crit n) (hleft : pi i = Fin.last n)
    (pi' : Crit n) (hleft' : pi' i' = Fin.last n) :
    Disjoint (forcedLitsOne C i hiL pi hleft) (forcedLitsOne C i' hiL' pi' hleft') := by
  rw [Finset.disjoint_left]
  intro l hl hl'
  simp only [forcedLitsOne, Finset.mem_image] at hl hl'
  obtain ⟨j, _, rfl⟩ := hl
  obtain ⟨j', _, heq⟩ := hl'
  have hinj := pvar_inj (congrArg Literal.var heq)
  exact hne hinj.1.symm

theorem forcedLitsAll_card (n : ℕ) (C : Clause) :
    (forcedLitsAll n C).card =
      pigeonComplexity n C * ((n + 1) - pigeonComplexity n C) := by
  -- Pairwise disjoint biUnion over attach
  have hdisj :
      ∀ x ∈ (L n C).attach, ∀ y ∈ (L n C).attach, x ≠ y →
        Disjoint
          (forcedLitsOne C x.1 x.2 (chosenFalsifier C x.1 x.2)
            (chosenFalsifier_leftOut C x.1 x.2))
          (forcedLitsOne C y.1 y.2 (chosenFalsifier C y.1 y.2)
            (chosenFalsifier_leftOut C y.1 y.2)) := by
    intro a _ b _ hne
    exact forcedLitsOne_disjoint C a.2 b.2 (fun heq => hne (Subtype.ext heq))
      _ _ _ _
  rw [forcedLitsAll, Finset.card_biUnion hdisj]
  have hsum :
      ∑ i ∈ (L n C).attach,
        (forcedLitsOne C i.1 i.2 (chosenFalsifier C i.1 i.2)
          (chosenFalsifier_leftOut C i.1 i.2)).card =
      ∑ _i ∈ (L n C).attach, (Lcompl n C).card := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact forcedLitsOne_card C i.1 i.2 _ _
  rw [hsum, Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
  -- LHS: |Lcompl| * |L|; RHS goal: |L| * ((n+1)-|L|)
  -- nsmul_eq_mul introduces a Nat.cast; strip it, then commute factors.
  simp [pigeonComplexity, card_Lcompl, Nat.cast_id]

/-- Main G6 bound: monotone image size is at least m·((n+1)−m). -/
theorem monotoneClause_card_ge {n : ℕ} (hn : 0 < n) (C : Clause) :
    pigeonComplexity n C * ((n + 1) - pigeonComplexity n C) ≤
      (monotoneClause n hn C).card := by
  calc pigeonComplexity n C * ((n + 1) - pigeonComplexity n C)
      = (forcedLitsAll n C).card := (forcedLitsAll_card n C).symm
    _ ≤ (monotoneClause n hn C).card := Finset.card_le_card (forcedLitsAll_subset hn C)

/-- On the intermediate band (k/3 < m ≤ 2k/3), both factors are at least k/3, so
the product is at least (k/3)². (Honest Nat bound; the real BP96 2k²/9 is the
continuum minimum at the band edge.) -/
theorem intermediate_product_ge {k m : ℕ}
    (hlo : k / 3 < m) (hhi : m ≤ 2 * k / 3) :
    (k / 3) * (k / 3) ≤ m * (k - m) := by
  have hm : k / 3 ≤ m := Nat.le_of_lt hlo
  have hkm : k / 3 ≤ k - m := by
    have h1 : k - 2 * k / 3 ≤ k - m := Nat.sub_le_sub_left hhi k
    have h2 : k / 3 ≤ k - 2 * k / 3 := by omega
    exact le_trans h2 h1
  exact Nat.mul_le_mul hm hkm

/-- Intermediate complexity yields quadratic width after the monotone transform. -/
theorem monotoneClause_card_intermediate {n : ℕ} (hn : 0 < n) (C : Clause)
    (hlo : (n + 1) / 3 < pigeonComplexity n C)
    (hhi : pigeonComplexity n C ≤ 2 * (n + 1) / 3) :
    ((n + 1) / 3) * ((n + 1) / 3) ≤ (monotoneClause n hn C).card := by
  have hprod := intermediate_product_ge hlo hhi
  exact le_trans hprod (monotoneClause_card_ge hn C)

end SATurday.ProofComplexity
