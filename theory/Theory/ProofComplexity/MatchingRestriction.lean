import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Theory.ProofComplexity.MonotoneWidth

/-!
# Matching Restrictions and Large Clause Averaging (R1, BP96 Theorem 2 / G7)

First formalize chunk of the Beame and Pitassi 1996 size assembly:

1. A matching step places one pigeon `i` into one hole `j`, forcing `p_{i,j}`
   true and the rest of row `i` and column `j` false.
2. Any clause containing the positive literal `p_{i,j}` is killed (satisfied)
   by that step.
3. Double counting: among a Finset of wide positive grid clauses (each of
   size at least `largeThreshold`), some grid literal hits at least the average
   share; formally
   `|Large| * W ≤ V * |{C ∈ Large | p_{i,j} ∈ C}|` for some `i,j`.

Honest threshold choice: BP96 takes W = V/10 with width ≥ 2(n+1)²/9. We only
certified width ((n+1)/3)², so we set `largeThreshold` to that certified width.
The exponential constant may need recalibration when the size assembly closes.

G7b: semantic restriction transport. G7c: size-nonincreasing syntactic
derivation surgery (`derivation_restrict_sub`, `exists_restrict_refutation`).
Iterative shrink, smaller PHP isomorphism, and Frontier close are deferred.

LOG: R1 matching restriction module (BP96 Theorem 2 / G7)
-/

namespace SATurday.ProofComplexity

open Classical
open Finset

/-! ## Grid positive literals -/

/-- All positive PHP(n+1, n) grid literals. -/
noncomputable def gridPosLits (n : ℕ) : Finset Literal :=
  ((Finset.univ : Finset (Fin (n + 1))).product (Finset.univ : Finset (Fin n))).image
    fun p => (⟨pvar n p.1 p.2, true⟩ : Literal)

theorem mem_gridPosLits_iff {n : ℕ} {l : Literal} :
    l ∈ gridPosLits n ↔
      ∃ i : Fin (n + 1), ∃ j : Fin n, l = ⟨pvar n i j, true⟩ := by
  constructor
  · intro hl
    simp only [gridPosLits, mem_image] at hl
    obtain ⟨⟨i, j⟩, _, rfl⟩ := hl
    exact ⟨i, j, rfl⟩
  · rintro ⟨i, j, rfl⟩
    simp only [gridPosLits, mem_image]
    exact ⟨⟨i, j⟩, by simp, rfl⟩

theorem gridPosLits_card (n : ℕ) : (gridPosLits n).card = (n + 1) * n := by
  rw [gridPosLits, card_image_of_injective]
  · simp [Fintype.card_fin]
  · intro a b h
    have hinj := pvar_inj (congrArg Literal.var h)
    exact Prod.ext hinj.1 hinj.2

/-- Large clause threshold: the certified intermediate monotone width ((n+1)/3)².
(Paper uses V/10 against the stronger 2(n+1)²/9 width bound.) -/
def largeThreshold (n : ℕ) : ℕ := ((n + 1) / 3) * ((n + 1) / 3)

theorem largeThreshold_eq_intermediate_sq (n : ℕ) :
    largeThreshold n = ((n + 1) / 3) * ((n + 1) / 3) :=
  rfl

/-! ## Matching step -/

/-- Forced (variable, value) pairs from placing pigeon `i` in hole `j`. -/
noncomputable def matchingForced (n : ℕ) (i : Fin (n + 1)) (j : Fin n) :
    Finset (ℕ × Bool) :=
  insert (pvar n i j, true)
    ((((Finset.univ : Finset (Fin n)).erase j).image fun j' => (pvar n i j', false)) ∪
      (((Finset.univ : Finset (Fin (n + 1))).erase i).image fun i' =>
        (pvar n i' j, false)))

theorem mem_matchingForced_place {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (pvar n i j, true) ∈ matchingForced n i j :=
  mem_insert_self _ _

theorem mem_matchingForced_row {n : ℕ} (i : Fin (n + 1)) {j j' : Fin n}
    (hne : j' ≠ j) :
    (pvar n i j', false) ∈ matchingForced n i j := by
  refine mem_insert_of_mem (mem_union_left _ ?_)
  exact mem_image_of_mem _ (mem_erase.mpr ⟨hne, mem_univ _⟩)

theorem mem_matchingForced_col {n : ℕ} {i i' : Fin (n + 1)} (j : Fin n)
    (hne : i' ≠ i) :
    (pvar n i' j, false) ∈ matchingForced n i j := by
  refine mem_insert_of_mem (mem_union_right _ ?_)
  exact mem_image_of_mem _ (mem_erase.mpr ⟨hne, mem_univ _⟩)

private theorem matchingForced_place_unique {n : ℕ} (i : Fin (n + 1)) (j : Fin n)
    {b : Bool} (hb : (pvar n i j, b) ∈ matchingForced n i j) : b = true := by
  simp only [matchingForced, mem_insert, mem_union, mem_image, mem_erase, mem_univ] at hb
  rcases hb with hplace | hrow | hcol
  · exact (Prod.mk.inj hplace).2
  · obtain ⟨j', ⟨hjne, _⟩, hpair⟩ := hrow
    have hpv : pvar n i j' = pvar n i j := (Prod.mk.inj hpair).1
    exact absurd (pvar_inj hpv).2 hjne
  · obtain ⟨i', ⟨hine, _⟩, hpair⟩ := hcol
    have hpv : pvar n i' j = pvar n i j := (Prod.mk.inj hpair).1
    exact absurd (pvar_inj hpv).1 hine

/-- Partial assignment lookup for a matching step. -/
noncomputable def matchingLookup (n : ℕ) (i : Fin (n + 1)) (j : Fin n)
    (v : ℕ) : Option Bool :=
  if h : ∃ b : Bool, (v, b) ∈ matchingForced n i j then
    some (Classical.choose h)
  else
    none

theorem matchingLookup_place {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    matchingLookup n i j (pvar n i j) = some true := by
  have h : ∃ b, (pvar n i j, b) ∈ matchingForced n i j :=
    ⟨true, mem_matchingForced_place i j⟩
  simp only [matchingLookup, h, ↓reduceDIte]
  rw [matchingForced_place_unique i j (Classical.choose_spec h)]

/-! ## Clause kill and restriction -/

/-- Clause `C` is killed by placing `i` in `j` when it contains `p_{i,j}`. -/
def killedByMatching (n : ℕ) (i : Fin (n + 1)) (j : Fin n) (C : Clause) : Prop :=
  (⟨pvar n i j, true⟩ : Literal) ∈ C

instance killedByMatching_decidable {n : ℕ} (i : Fin (n + 1)) (j : Fin n)
    (C : Clause) : Decidable (killedByMatching n i j C) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- Syntactic restriction of a clause by a partial assignment.
Returns `none` when the clause is satisfied (contains a forced true literal). -/
noncomputable def restrictClause (ρ : ℕ → Option Bool) (C : Clause) : Option Clause :=
  if ∃ l ∈ C, ρ l.var = some l.pos then
    none
  else
    some (C.filter fun l => ρ l.var = none)

theorem restrictClause_none_of_killed {n : ℕ} (i : Fin (n + 1)) (j : Fin n)
    (C : Clause) (h : killedByMatching n i j C) :
    restrictClause (matchingLookup n i j) C = none := by
  simp only [restrictClause, killedByMatching] at h ⊢
  exact if_pos ⟨⟨pvar n i j, true⟩, h, matchingLookup_place i j⟩

/-- Restrict a CNF: drop killed clauses; shrink survivors. -/
noncomputable def restrictCNF (ρ : ℕ → Option Bool) (F : CNF) : CNF :=
  F.biUnion fun C =>
    match restrictClause ρ C with
    | none => ∅
    | some C' => {C'}

/-! ## Averaging over wide positive clauses -/

/-- Incidence count: how many clauses of `Large` contain literal `l`. -/
noncomputable def hitCount (Large : Finset Clause) (l : Literal) : ℕ :=
  (Large.filter (fun C => l ∈ C)).card

theorem card_eq_sum_ite_mem {α : Type*} [DecidableEq α] (C S : Finset α)
    (h : C ⊆ S) :
    C.card = ∑ x ∈ S, (if x ∈ C then 1 else 0) := by
  have hfilter : S.filter (fun x => x ∈ C) = C := by
    ext x
    exact ⟨fun hx => (mem_filter.mp hx).2,
      fun hx => mem_filter.mpr ⟨h hx, hx⟩⟩
  rw [← sum_filter (p := fun x => x ∈ C) (f := fun _ => (1 : ℕ)), hfilter]
  simp

theorem sum_card_eq_sum_hitCount (n : ℕ) (Large : Finset Clause)
    (hsub : ∀ C ∈ Large, C ⊆ gridPosLits n) :
    ∑ C ∈ Large, C.card = ∑ l ∈ gridPosLits n, hitCount Large l := by
  classical
  have hleft :
      ∑ C ∈ Large, C.card =
        ∑ C ∈ Large, ∑ l ∈ gridPosLits n, (if l ∈ C then (1 : ℕ) else 0) := by
    refine sum_congr rfl ?_
    intro C hC
    exact card_eq_sum_ite_mem C (gridPosLits n) (hsub C hC)
  have hswap :
      ∑ C ∈ Large, ∑ l ∈ gridPosLits n, (if l ∈ C then (1 : ℕ) else 0) =
        ∑ l ∈ gridPosLits n, ∑ C ∈ Large, (if l ∈ C then (1 : ℕ) else 0) :=
    sum_comm
  have hright :
      ∑ l ∈ gridPosLits n, ∑ C ∈ Large, (if l ∈ C then (1 : ℕ) else 0) =
        ∑ l ∈ gridPosLits n, hitCount Large l := by
    refine sum_congr rfl ?_
    intro l _
    -- ∑_C 1_{l∈C} = |filter|
    have h1 :
        ∑ C ∈ Large, (if l ∈ C then (1 : ℕ) else 0) =
          ∑ C ∈ Large.filter (fun C => l ∈ C), (1 : ℕ) := by
      exact (sum_filter (p := fun C => l ∈ C) (f := fun _ => (1 : ℕ))).symm
    have h2 :
        ∑ C ∈ Large.filter (fun C => l ∈ C), (1 : ℕ) =
          (Large.filter (fun C => l ∈ C)).card := by
      simp
    exact h1.trans (h2.trans rfl)
  rw [hleft, hswap, hright]

/-- Double counting heart of BP96 Theorem 2: some positive grid literal hits
enough wide clauses that `|Large| * W ≤ V * hitCount`. -/
theorem exists_popular_grid_literal {n : ℕ} (hn : 0 < n)
    (Large : Finset Clause)
    (hwide : ∀ C ∈ Large, largeThreshold n ≤ C.card)
    (hsub : ∀ C ∈ Large, C ⊆ gridPosLits n) :
    ∃ i : Fin (n + 1), ∃ j : Fin n,
      Large.card * largeThreshold n ≤
        (n + 1) * n * (Large.filter (killedByMatching n i j)).card := by
  classical
  by_cases hL : Large = ∅
  · refine ⟨⟨0, by omega⟩, ⟨0, hn⟩, ?_⟩
    simp [hL]
  have hsum_ge :
      Large.card * largeThreshold n ≤ ∑ C ∈ Large, C.card := by
    have := card_nsmul_le_sum (s := Large) (f := fun C => C.card)
      (n := largeThreshold n) (fun C hC => hwide C hC)
    simpa [nsmul_eq_mul] using this
  have hsum_eq := sum_card_eq_sum_hitCount n Large hsub
  have hV : (gridPosLits n).card = (n + 1) * n := gridPosLits_card n
  have hne : (gridPosLits n).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hempty
    simp [hempty] at hV
    omega
  obtain ⟨l, hl, hsup⟩ :=
    exists_mem_eq_sup (gridPosLits n) hne (fun l => hitCount Large l)
  have hmax :
      ∑ t ∈ gridPosLits n, hitCount Large t ≤
        (gridPosLits n).card * hitCount Large l := by
    have := sum_le_card_nsmul (gridPosLits n) (fun t => hitCount Large t)
      (hitCount Large l) (fun t ht => hsup ▸ le_sup (f := fun u => hitCount Large u) ht)
    simpa [nsmul_eq_mul] using this
  have hbound :
      Large.card * largeThreshold n ≤
        (n + 1) * n * hitCount Large l := by
    calc Large.card * largeThreshold n
        ≤ ∑ C ∈ Large, C.card := hsum_ge
      _ = ∑ t ∈ gridPosLits n, hitCount Large t := hsum_eq
      _ ≤ (gridPosLits n).card * hitCount Large l := hmax
      _ = (n + 1) * n * hitCount Large l := by rw [hV]
  obtain ⟨i, j, rfl⟩ := (mem_gridPosLits_iff).mp hl
  refine ⟨i, j, ?_⟩
  simpa [hitCount, killedByMatching] using hbound

theorem filter_not_killed_card {n : ℕ} (i : Fin (n + 1)) (j : Fin n)
    (Large : Finset Clause) :
    (Large.filter (fun C => ¬ killedByMatching n i j C)).card =
      Large.card - (Large.filter (killedByMatching n i j)).card := by
  classical
  have hdisj : Disjoint
      (Large.filter (killedByMatching n i j))
      (Large.filter (fun C => ¬ killedByMatching n i j C)) := by
    rw [disjoint_filter]
    intro _ _ hk hnk
    exact hnk hk
  have hunion :
      Large.filter (killedByMatching n i j) ∪
        Large.filter (fun C => ¬ killedByMatching n i j C) = Large := by
    ext C
    simp only [mem_union, mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hC
      by_cases hk : killedByMatching n i j C
      · exact Or.inl ⟨hC, hk⟩
      · exact Or.inr ⟨hC, hk⟩
  have hcard := card_union_of_disjoint hdisj
  rw [hunion] at hcard
  omega

/-- One step shrink: after a popular matching, unkilled wide clauses are at most
`|Large| - (|Large| * W) / V`. -/
theorem large_survivors_le {n : ℕ} (hn : 0 < n)
    (Large : Finset Clause)
    (hwide : ∀ C ∈ Large, largeThreshold n ≤ C.card)
    (hsub : ∀ C ∈ Large, C ⊆ gridPosLits n) :
    ∃ i : Fin (n + 1), ∃ j : Fin n,
      (Large.filter (fun C => ¬ killedByMatching n i j C)).card ≤
        Large.card - (Large.card * largeThreshold n) / ((n + 1) * n) := by
  obtain ⟨i, j, hpop⟩ := exists_popular_grid_literal hn Large hwide hsub
  refine ⟨i, j, ?_⟩
  have hdiv :
      (Large.card * largeThreshold n) / ((n + 1) * n) ≤
        (Large.filter (killedByMatching n i j)).card :=
    Nat.div_le_of_le_mul hpop
  rw [filter_not_killed_card]
  exact Nat.sub_le_sub_left hdiv _

/-- An intermediate complexity clause is large after the monotone transform. -/
theorem monotoneClause_card_ge_largeThreshold {n : ℕ} (hn : 0 < n) (C : Clause)
    (hlo : (n + 1) / 3 < pigeonComplexity n C)
    (hhi : pigeonComplexity n C ≤ 2 * (n + 1) / 3) :
    largeThreshold n ≤ (monotoneClause n hn C).card := by
  simpa [largeThreshold] using monotoneClause_card_intermediate hn C hlo hhi

/-! ## Restriction helpers and semantic transport (G7b)

Syntactic size-nonincreasing derivation surgery (subclause induction) is the
next chunk. This chunk certifies the clause/CNF restriction API and the
semantic fact that unsatisfiability (hence refutability, via R0 completeness)
is preserved under restriction.
-/

theorem restrictClause_empty (ρ : ℕ → Option Bool) :
    restrictClause ρ (∅ : Clause) = some ∅ := by
  simp [restrictClause]

theorem restrictClause_eq_some_iff (ρ : ℕ → Option Bool) (C C' : Clause) :
    restrictClause ρ C = some C' ↔
      (∀ l ∈ C, ρ l.var ≠ some l.pos) ∧
        C' = C.filter fun l => ρ l.var = none := by
  simp only [restrictClause]
  constructor
  · intro h
    by_cases hsat : ∃ l ∈ C, ρ l.var = some l.pos
    · simp [hsat] at h
    · simp [hsat] at h
      refine ⟨?_, h.symm⟩
      intro l hl hρ
      exact hsat ⟨l, hl, hρ⟩
  · rintro ⟨hnsat, rfl⟩
    have hsat : ¬∃ l ∈ C, ρ l.var = some l.pos := fun ⟨l, hl, hρ⟩ => hnsat l hl hρ
    simp [hsat]

theorem restrictClause_subset {ρ : ℕ → Option Bool} {C C' : Clause}
    (h : restrictClause ρ C = some C') : C' ⊆ C := by
  have h' := (restrictClause_eq_some_iff ρ C C').mp h
  rw [h'.2]
  exact filter_subset _ _

theorem mem_restrictCNF_iff (ρ : ℕ → Option Bool) (F : CNF) (C' : Clause) :
    C' ∈ restrictCNF ρ F ↔ ∃ C ∈ F, restrictClause ρ C = some C' := by
  constructor
  · intro h
    simp only [restrictCNF, mem_biUnion] at h
    obtain ⟨C, hC, hmem⟩ := h
    cases hres : restrictClause ρ C with
    | none => simp [hres] at hmem
    | some C'' =>
      simp only [hres, mem_singleton] at hmem
      subst hmem
      exact ⟨C, hC, hres⟩
  · rintro ⟨C, hC, hres⟩
    simp only [restrictCNF, mem_biUnion]
    exact ⟨C, hC, by simp [hres]⟩

/-- Fill unset variables of `ρ` from a total assignment `a`. -/
def extendAssign (ρ : ℕ → Option Bool) (a : Assignment) : Assignment :=
  fun v => match ρ v with
    | some b => b
    | none => a v

theorem extendAssign_unassigned {ρ : ℕ → Option Bool} {a : Assignment} {v : ℕ}
    (h : ρ v = none) : extendAssign ρ a v = a v := by
  simp [extendAssign, h]

theorem extendAssign_assigned {ρ : ℕ → Option Bool} {a : Assignment} {v : ℕ}
    {b : Bool} (h : ρ v = some b) : extendAssign ρ a v = b := by
  simp [extendAssign, h]

theorem litSat_extend_of_mem_restrict {ρ : ℕ → Option Bool} {a : Assignment}
    {C C' : Clause} {l : Literal}
    (hC : restrictClause ρ C = some C') (hl : l ∈ C') (hla : litSat a l) :
    litSat (extendAssign ρ a) l := by
  have hiff := (restrictClause_eq_some_iff ρ C C').mp hC
  have hun : ρ l.var = none := by
    have : l ∈ C.filter fun t => ρ t.var = none := by
      simpa [hiff.2] using hl
    exact (mem_filter.mp this).2
  simp only [litSat, extendAssign_unassigned hun]
  exact hla

theorem clauseSat_extend_of_restrict {ρ : ℕ → Option Bool} {a : Assignment}
    {C C' : Clause}
    (hC : restrictClause ρ C = some C') (ha : clauseSat a C') :
    clauseSat (extendAssign ρ a) C := by
  obtain ⟨l, hl, hla⟩ := ha
  exact ⟨l, restrictClause_subset hC hl, litSat_extend_of_mem_restrict hC hl hla⟩

theorem clauseSat_extend_of_killed {ρ : ℕ → Option Bool} {a : Assignment}
    {C : Clause} (hC : restrictClause ρ C = none) :
    clauseSat (extendAssign ρ a) C := by
  simp only [restrictClause] at hC
  by_cases hsat : ∃ l ∈ C, ρ l.var = some l.pos
  · obtain ⟨l, hl, hρ⟩ := hsat
    refine ⟨l, hl, ?_⟩
    simp only [litSat, extendAssign, hρ]
  · simp [hsat] at hC

theorem cnfSat_extend_of_restrictCNF {ρ : ℕ → Option Bool} {a : Assignment}
    {F : CNF} (ha : cnfSat a (restrictCNF ρ F)) :
    cnfSat (extendAssign ρ a) F := by
  intro C hC
  cases hres : restrictClause ρ C with
  | none => exact clauseSat_extend_of_killed hres
  | some C' =>
    have hmem : C' ∈ restrictCNF ρ F :=
      (mem_restrictCNF_iff ρ F C').mpr ⟨C, hC, hres⟩
    exact clauseSat_extend_of_restrict hres (ha C' hmem)

/-- Satisfiability lifts along restriction (extend the model). -/
theorem Satisfiable_of_restrictCNF {ρ : ℕ → Option Bool} {F : CNF}
    (h : Satisfiable (restrictCNF ρ F)) : Satisfiable F := by
  obtain ⟨a, ha⟩ := h
  exact ⟨extendAssign ρ a, cnfSat_extend_of_restrictCNF ha⟩

theorem unsat_restrictCNF_of_unsat {ρ : ℕ → Option Bool} {F : CNF}
    (h : ¬Satisfiable F) : ¬Satisfiable (restrictCNF ρ F) :=
  fun hs => h (Satisfiable_of_restrictCNF hs)

/-- Refutability is preserved under restriction (via R0 completeness).
Size-nonincreasing syntactic transport is certified below (G7c). -/
theorem refutable_restrictCNF (ρ : ℕ → Option Bool) {F : CNF}
    (h : Refutable F) : Refutable (restrictCNF ρ F) :=
  resolution_complete (unsat_restrictCNF_of_unsat (resolution_sound h))

/-- Matching step preserves PHP refutability of the restricted CNF. -/
theorem refutable_matchingRestrict {n : ℕ} (i : Fin (n + 1)) (j : Fin n)
    (h : Refutable (phpCNF n)) :
    Refutable (restrictCNF (matchingLookup n i j) (phpCNF n)) :=
  refutable_restrictCNF (matchingLookup n i j) h

/-! ## Size-preserving syntactic transport (G7c) -/

theorem restrictClause_eq_none_iff (ρ : ℕ → Option Bool) (C : Clause) :
    restrictClause ρ C = none ↔ ∃ l ∈ C, ρ l.var = some l.pos := by
  simp only [restrictClause]
  constructor
  · intro h
    by_cases hsat : ∃ l ∈ C, ρ l.var = some l.pos
    · exact hsat
    · simp [hsat] at h
  · intro hsat
    simp [hsat]

theorem mem_of_mem_restrictClause {ρ : ℕ → Option Bool} {C C' : Clause}
    {l : Literal} (h : restrictClause ρ C = some C') (hl : l ∈ C') :
    l ∈ C ∧ ρ l.var = none := by
  have hiff := (restrictClause_eq_some_iff ρ C C').mp h
  have hl' : l ∈ C.filter fun t => ρ t.var = none := by simpa [hiff.2] using hl
  exact ⟨(mem_filter.mp hl').1, (mem_filter.mp hl').2⟩

/-- If both parents are killed, the resolvent is killed. -/
theorem restrictClause_resolvent_none_of_parents_none (ρ : ℕ → Option Bool)
    {C D : Clause} (x : ℕ)
    (hC : restrictClause ρ C = none) (hD : restrictClause ρ D = none) :
    restrictClause ρ (resolvent C D x) = none := by
  obtain ⟨lC, hlC, hρC⟩ := (restrictClause_eq_none_iff ρ C).mp hC
  obtain ⟨lD, hlD, hρD⟩ := (restrictClause_eq_none_iff ρ D).mp hD
  refine (restrictClause_eq_none_iff ρ _).mpr ?_
  by_cases hCx : lC = ⟨x, true⟩
  · subst hCx
    by_cases hDx : lD = ⟨x, false⟩
    · subst hDx
      -- ρ x cannot be both some true and some false
      cases hρC.symm.trans hρD
    · exact ⟨lD, mem_union_right _ (mem_erase.mpr ⟨hDx, hlD⟩), hρD⟩
  · exact ⟨lC, mem_union_left _ (mem_erase.mpr ⟨hCx, hlC⟩), hρC⟩

/-- Left parent killed (must be via +x); surviving right restriction embeds
into the restricted resolvent. -/
theorem restrict_sub_of_left_killed (ρ : ℕ → Option Bool) {C D D' R' : Clause}
    (x : ℕ) (_hx : (⟨x, true⟩ : Literal) ∈ C)
    (hC : restrictClause ρ C = none) (hD : restrictClause ρ D = some D')
    (hR : restrictClause ρ (resolvent C D x) = some R') :
    D' ⊆ R' := by
  obtain ⟨lC, hlC, hρC⟩ := (restrictClause_eq_none_iff ρ C).mp hC
  have hCx : lC = ⟨x, true⟩ := by
    by_contra hne
    have hlR : lC ∈ resolvent C D x :=
      mem_union_left _ (mem_erase.mpr ⟨hne, hlC⟩)
    have hnone : restrictClause ρ (resolvent C D x) = none :=
      (restrictClause_eq_none_iff ρ _).mpr ⟨lC, hlR, hρC⟩
    simp [hnone] at hR
  subst hCx
  -- ρ x = some true, so -x cannot appear in D'
  intro l hl
  obtain ⟨hlD, hun⟩ := mem_of_mem_restrictClause hD hl
  have hlne : l ≠ ⟨x, false⟩ := by
    intro heq
    subst heq
    simp [hρC] at hun
  have hlR : l ∈ resolvent C D x :=
    mem_union_right _ (mem_erase.mpr ⟨hlne, hlD⟩)
  have hiff := (restrictClause_eq_some_iff ρ (resolvent C D x) R').mp hR
  have : l ∈ (resolvent C D x).filter fun t => ρ t.var = none :=
    mem_filter.mpr ⟨hlR, hun⟩
  simpa [hiff.2] using this

theorem restrict_sub_of_right_killed (ρ : ℕ → Option Bool) {C C' D R' : Clause}
    (x : ℕ) (_hnx : (⟨x, false⟩ : Literal) ∈ D)
    (hC : restrictClause ρ C = some C') (hD : restrictClause ρ D = none)
    (hR : restrictClause ρ (resolvent C D x) = some R') :
    C' ⊆ R' := by
  obtain ⟨lD, hlD, hρD⟩ := (restrictClause_eq_none_iff ρ D).mp hD
  have hDx : lD = ⟨x, false⟩ := by
    by_contra hne
    have hlR : lD ∈ resolvent C D x :=
      mem_union_right _ (mem_erase.mpr ⟨hne, hlD⟩)
    have hnone : restrictClause ρ (resolvent C D x) = none :=
      (restrictClause_eq_none_iff ρ _).mpr ⟨lD, hlR, hρD⟩
    simp [hnone] at hR
  subst hDx
  intro l hl
  obtain ⟨hlC, hun⟩ := mem_of_mem_restrictClause hC hl
  have hlne : l ≠ ⟨x, true⟩ := by
    intro heq
    subst heq
    simp [hρD] at hun
  have hlR : l ∈ resolvent C D x :=
    mem_union_left _ (mem_erase.mpr ⟨hlne, hlC⟩)
  have hiff := (restrictClause_eq_some_iff ρ (resolvent C D x) R').mp hR
  have : l ∈ (resolvent C D x).filter fun t => ρ t.var = none :=
    mem_filter.mpr ⟨hlR, hun⟩
  simpa [hiff.2] using this

/-- Both parents survive only if the pivot is unassigned; then restriction
commutes with resolution. -/
theorem restrict_resolvent_of_both_some (ρ : ℕ → Option Bool) {C C' D D' : Clause}
    (x : ℕ) (hx : (⟨x, true⟩ : Literal) ∈ C) (hnx : (⟨x, false⟩ : Literal) ∈ D)
    (hC : restrictClause ρ C = some C') (hD : restrictClause ρ D = some D')
    (hxun : ρ x = none) :
    restrictClause ρ (resolvent C D x) = some (resolvent C' D' x) ∧
      (⟨x, true⟩ : Literal) ∈ C' ∧ (⟨x, false⟩ : Literal) ∈ D' := by
  have ⟨hCnsat, hCeq⟩ := (restrictClause_eq_some_iff ρ C C').mp hC
  have ⟨hDnsat, hDeq⟩ := (restrictClause_eq_some_iff ρ D D').mp hD
  have hxC' : (⟨x, true⟩ : Literal) ∈ C' := by
    simp [hCeq, mem_filter, hx, hxun]
  have hxD' : (⟨x, false⟩ : Literal) ∈ D' := by
    simp [hDeq, mem_filter, hnx, hxun]
  refine ⟨?_, hxC', hxD'⟩
  -- Prove by characterizing both sides as the unassigned lits of the resolvent.
  have hR :
      restrictClause ρ (resolvent C D x) =
        some ((resolvent C D x).filter fun l => ρ l.var = none) := by
    apply (restrictClause_eq_some_iff ρ (resolvent C D x) _).mpr
    refine ⟨?_, rfl⟩
    intro l hl hsat
    have hl' : l ∈ C.erase ⟨x, true⟩ ∨ l ∈ D.erase ⟨x, false⟩ :=
      (mem_union).mp (by simpa [resolvent] using hl)
    rcases hl' with hlC | hlD
    · exact hCnsat l (mem_of_mem_erase hlC) hsat
    · exact hDnsat l (mem_of_mem_erase hlD) hsat
  have hfilter :
      (resolvent C D x).filter (fun l => ρ l.var = none) = resolvent C' D' x := by
    ext l
    constructor
    · intro hl
      obtain ⟨hlR, hun⟩ := mem_filter.mp hl
      have hl' : l ∈ C.erase ⟨x, true⟩ ∨ l ∈ D.erase ⟨x, false⟩ :=
        (mem_union).mp (by simpa [resolvent] using hlR)
      simp only [resolvent, mem_union, mem_erase, hCeq, hDeq, mem_filter]
      rcases hl' with hlC | hlD
      · obtain ⟨hlne, hlC⟩ := mem_erase.mp hlC
        exact Or.inl ⟨hlne, hlC, hun⟩
      · obtain ⟨hlne, hlD⟩ := mem_erase.mp hlD
        exact Or.inr ⟨hlne, hlD, hun⟩
    · intro hl
      simp only [resolvent, mem_union, mem_erase, hCeq, hDeq, mem_filter] at hl
      apply mem_filter.mpr
      rcases hl with ⟨hlne, hlC, hun⟩ | ⟨hlne, hlD, hun⟩
      · exact ⟨mem_union_left _ (mem_erase.mpr ⟨hlne, hlC⟩), hun⟩
      · exact ⟨mem_union_right _ (mem_erase.mpr ⟨hlne, hlD⟩), hun⟩
  rw [hR, hfilter]

/-- Core G7c: if the conclusion survives restriction, some subclause of the
restricted conclusion has a derivation from `restrictCNF ρ F` of size at most
the original. -/
theorem derivation_restrict_sub (ρ : ℕ → Option Bool) {F : CNF} {C : Clause}
    (d : Derivation F C) {C' : Clause} (hC' : restrictClause ρ C = some C') :
    ∃ D : Clause, ∃ d' : Derivation (restrictCNF ρ F) D,
      D ⊆ C' ∧ d'.size ≤ d.size := by
  induction d generalizing C' with
  | hyp C hC =>
    refine ⟨C', Derivation.hyp C' ?_, Subset.rfl, ?_⟩
    · exact (mem_restrictCNF_iff ρ F C').mpr ⟨C, hC, hC'⟩
    · exact Nat.le_refl 1
  | res x dC dD hx hnx ihC ihD =>
    -- Parent conclusions are the binders C, D of this res step.
    change restrictClause ρ (resolvent dC.conclusion dD.conclusion x) = some C' at hC'
    cases hCrest : restrictClause ρ dC.conclusion with
    | none =>
      cases hDrest : restrictClause ρ dD.conclusion with
      | none =>
        have hnone :=
          restrictClause_resolvent_none_of_parents_none ρ x hCrest hDrest
        rw [hnone] at hC'
        cases hC'
      | some D' =>
        obtain ⟨E, dE, hEsub, hEsz⟩ := ihD (C' := D') hDrest
        have hDR : D' ⊆ C' :=
          restrict_sub_of_left_killed (C := dC.conclusion) (D := dD.conclusion)
            ρ x hx hCrest hDrest hC'
        refine ⟨E, dE, Subset.trans hEsub hDR, Nat.le_trans hEsz ?_⟩
        change dD.size ≤ dC.size + dD.size + 1
        omega
    | some Cparent =>
      cases hDrest : restrictClause ρ dD.conclusion with
      | none =>
        obtain ⟨E, dE, hEsub, hEsz⟩ := ihC (C' := Cparent) hCrest
        have hCR : Cparent ⊆ C' :=
          restrict_sub_of_right_killed (C := dC.conclusion) (D := dD.conclusion)
            ρ x hnx hCrest hDrest hC'
        refine ⟨E, dE, Subset.trans hEsub hCR, Nat.le_trans hEsz ?_⟩
        change dC.size ≤ dC.size + dD.size + 1
        omega
      | some Dparent =>
        have hxun : ρ x = none := by
          cases hρ : ρ x with
          | none => rfl
          | some b =>
            cases b
            · have : restrictClause ρ dD.conclusion = none :=
                (restrictClause_eq_none_iff ρ _).mpr
                  ⟨⟨x, false⟩, hnx, by simp [hρ]⟩
              rw [this] at hDrest
              cases hDrest
            · have : restrictClause ρ dC.conclusion = none :=
                (restrictClause_eq_none_iff ρ _).mpr
                  ⟨⟨x, true⟩, hx, by simp [hρ]⟩
              rw [this] at hCrest
              cases hCrest
        obtain ⟨hReq, _, _⟩ :=
          restrict_resolvent_of_both_some (C := dC.conclusion) (D := dD.conclusion)
            ρ x hx hnx hCrest hDrest hxun
        have hC'eq : C' = resolvent Cparent Dparent x :=
          Option.some.inj (hC'.symm.trans hReq)
        obtain ⟨E1, d1, h1, hs1⟩ := ihC (C' := Cparent) hCrest
        obtain ⟨E2, d2, h2, hs2⟩ := ihD (C' := Dparent) hDrest
        by_cases hE1x : (⟨x, true⟩ : Literal) ∈ E1
        · by_cases hE2x : (⟨x, false⟩ : Literal) ∈ E2
          · refine ⟨resolvent E1 E2 x, Derivation.res x d1 d2 hE1x hE2x, ?_, ?_⟩
            · intro l hl
              have hl' : l ∈ E1.erase ⟨x, true⟩ ∨ l ∈ E2.erase ⟨x, false⟩ :=
                (mem_union).mp (by simpa [resolvent] using hl)
              rw [hC'eq]
              simp only [resolvent, mem_union, mem_erase]
              rcases hl' with hl1 | hl2
              · obtain ⟨hlne, hl1⟩ := mem_erase.mp hl1
                exact Or.inl ⟨hlne, h1 hl1⟩
              · obtain ⟨hlne, hl2⟩ := mem_erase.mp hl2
                exact Or.inr ⟨hlne, h2 hl2⟩
            · change d1.size + d2.size + 1 ≤ dC.size + dD.size + 1
              omega
          · refine ⟨E2, d2, ?_, Nat.le_trans hs2 ?_⟩
            · intro l hl
              have hlD : l ∈ Dparent := h2 hl
              have hlne : l ≠ ⟨x, false⟩ := fun heq => hE2x (heq ▸ hl)
              rw [hC'eq]
              exact mem_union_right _ (mem_erase.mpr ⟨hlne, hlD⟩)
            · change dD.size ≤ dC.size + dD.size + 1
              omega
        · refine ⟨E1, d1, ?_, Nat.le_trans hs1 ?_⟩
          · intro l hl
            have hlC : l ∈ Cparent := h1 hl
            have hlne : l ≠ ⟨x, true⟩ := fun heq => hE1x (heq ▸ hl)
            rw [hC'eq]
            exact mem_union_left _ (mem_erase.mpr ⟨hlne, hlC⟩)
          · change dC.size ≤ dC.size + dD.size + 1
            omega

/-- Size-nonincreasing transport of a refutation under restriction. -/
theorem exists_restrict_refutation (ρ : ℕ → Option Bool) {F : CNF}
    (d : Derivation F (∅ : Clause)) :
    ∃ d' : Derivation (restrictCNF ρ F) (∅ : Clause), d'.size ≤ d.size := by
  obtain ⟨D, d', hsub, hsz⟩ := derivation_restrict_sub ρ d (restrictClause_empty ρ)
  have hD : D = ∅ := Subset.antisymm hsub (empty_subset _)
  subst hD
  exact ⟨d', hsz⟩

/-- Matching restriction of a PHP refutation yields a restricted refutation
of size at most the original. -/
theorem exists_matchingRestrict_refutation {n : ℕ} (i : Fin (n + 1)) (j : Fin n)
    (d : Derivation (phpCNF n) (∅ : Clause)) :
    ∃ d' : Derivation (restrictCNF (matchingLookup n i j) (phpCNF n)) (∅ : Clause),
      d'.size ≤ d.size :=
  exists_restrict_refutation (matchingLookup n i j) d

end SATurday.ProofComplexity
