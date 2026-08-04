import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Fin.Basic
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
derivation surgery. G7d: iterative large-clause kill progress. G7e: rename
embedding of `phpCNF k` into the matching restriction of `phpCNF (k+1)`.
Rate optimal iterative shrink and Frontier close remain deferred.

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

/-! ## Iterative large-clause kill and PHP restriction (G7d) -/

theorem matchingLookup_row {n : ℕ} (i : Fin (n + 1)) {j j' : Fin n}
    (hne : j' ≠ j) :
    matchingLookup n i j (pvar n i j') = some false := by
  have hex : ∃ b, (pvar n i j', b) ∈ matchingForced n i j :=
    ⟨false, mem_matchingForced_row i hne⟩
  simp only [matchingLookup, hex, ↓reduceDIte]
  have hb := Classical.choose_spec hex
  cases hbit : Classical.choose hex
  · rfl
  · have htrue : (pvar n i j', true) ∈ matchingForced n i j := by
      simpa [hbit] using hb
    simp only [matchingForced, mem_insert, mem_union, mem_image, mem_erase, mem_univ] at htrue
    rcases htrue with hplace | hrow | hcol
    · exact absurd (pvar_inj (Prod.mk.inj hplace).1).2 hne
    · obtain ⟨_, _, hpair⟩ := hrow
      exact Bool.noConfusion (Prod.mk.inj hpair).2
    · obtain ⟨_, _, hpair⟩ := hcol
      exact Bool.noConfusion (Prod.mk.inj hpair).2

theorem matchingLookup_col {n : ℕ} {i i' : Fin (n + 1)} (j : Fin n)
    (hne : i' ≠ i) :
    matchingLookup n i j (pvar n i' j) = some false := by
  have hex : ∃ b, (pvar n i' j, b) ∈ matchingForced n i j :=
    ⟨false, mem_matchingForced_col j hne⟩
  simp only [matchingLookup, hex, ↓reduceDIte]
  have hb := Classical.choose_spec hex
  cases hbit : Classical.choose hex
  · rfl
  · have htrue : (pvar n i' j, true) ∈ matchingForced n i j := by
      simpa [hbit] using hb
    simp only [matchingForced, mem_insert, mem_union, mem_image, mem_erase, mem_univ] at htrue
    rcases htrue with hplace | hrow | hcol
    · exact absurd (pvar_inj (Prod.mk.inj hplace).1).1 hne
    · obtain ⟨_, _, hpair⟩ := hrow
      exact Bool.noConfusion (Prod.mk.inj hpair).2
    · obtain ⟨_, _, hpair⟩ := hcol
      exact Bool.noConfusion (Prod.mk.inj hpair).2

theorem mem_pigeonClause {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (⟨pvar n i j, true⟩ : Literal) ∈ pigeonClause n i :=
  mem_image_of_mem _ (mem_univ j)

theorem pigeonClause_subset_gridPosLits (n : ℕ) (i : Fin (n + 1)) :
    pigeonClause n i ⊆ gridPosLits n := by
  intro l hl
  simp only [pigeonClause, mem_image] at hl
  obtain ⟨j, _, rfl⟩ := hl
  exact (mem_gridPosLits_iff).mpr ⟨i, j, rfl⟩

/-- Placing pigeon `i` kills its pigeon axiom. -/
theorem restrictClause_pigeonClause_place {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    restrictClause (matchingLookup n i j) (pigeonClause n i) = none :=
  restrictClause_none_of_killed i j (pigeonClause n i) (mem_pigeonClause i j)

private theorem matchingLookup_off_grid {n : ℕ} {i i' : Fin (n + 1)}
    {j j' : Fin n} (hi : i' ≠ i) (hj : j' ≠ j) :
    matchingLookup n i j (pvar n i' j') = none := by
  simp only [matchingLookup]
  split_ifs with hex
  · obtain ⟨b, hb⟩ := hex
    simp only [matchingForced, mem_insert, mem_union, mem_image, mem_erase, mem_univ] at hb
    rcases hb with hplace | hrow | hcol
    · exact (hi (pvar_inj (Prod.mk.inj hplace).1).1).elim
    · obtain ⟨_, _, hpair⟩ := hrow
      exact (hi (pvar_inj (Prod.mk.inj hpair).1).1.symm).elim
    · obtain ⟨_, _, hpair⟩ := hcol
      exact (hj (pvar_inj (Prod.mk.inj hpair).1).2.symm).elim
  · rfl

/-- A non-placed pigeon's axiom restricts to positive lits on holes other than `j`. -/
theorem restrictClause_pigeonClause_other {n : ℕ}
    {i i' : Fin (n + 1)} (j : Fin n) (hne : i' ≠ i) :
    restrictClause (matchingLookup n i j) (pigeonClause n i') =
      some (((Finset.univ : Finset (Fin n)).erase j).image fun j' =>
        (⟨pvar n i' j', true⟩ : Literal)) := by
  set ρ := matchingLookup n i j
  have hnsat : ∀ l ∈ pigeonClause n i', ρ l.var ≠ some l.pos := by
    intro l hl hρ
    obtain ⟨j', _, rfl⟩ := mem_image.mp (show l ∈ pigeonClause n i' from hl)
    by_cases hj : j' = j
    · -- Column force: other pigeon on hole j is set false, so not satisfied.
      have hcol := matchingLookup_col (i := i) (i' := i') j hne
      dsimp [ρ] at hρ
      rw [hj, hcol] at hρ
      exact Bool.noConfusion (Option.some.inj hρ)
    · have hoff := matchingLookup_off_grid hne hj
      dsimp [ρ] at hρ
      rw [hoff] at hρ
      exact (Option.some_ne_none true hρ.symm).elim
  have hfilter :
      (pigeonClause n i').filter (fun l => ρ l.var = none) =
        ((Finset.univ : Finset (Fin n)).erase j).image fun j' =>
          (⟨pvar n i' j', true⟩ : Literal) := by
    ext l
    constructor
    · intro hl
      obtain ⟨hlP, hun⟩ := mem_filter.mp hl
      obtain ⟨j', _, rfl⟩ := mem_image.mp hlP
      have hjne : j' ≠ j := by
        intro heq
        have hcol := matchingLookup_col (i := i) (i' := i') j hne
        dsimp [ρ] at hun
        rw [heq, hcol] at hun
        exact (Option.some_ne_none false hun).elim
      exact mem_image_of_mem _ (mem_erase.mpr ⟨hjne, mem_univ _⟩)
    · intro hl
      obtain ⟨j', hj, rfl⟩ := mem_image.mp hl
      have hjne := (mem_erase.mp hj).1
      exact mem_filter.mpr ⟨mem_pigeonClause i' j', matchingLookup_off_grid hne hjne⟩
  exact (restrictClause_eq_some_iff ρ _ _).mpr ⟨hnsat, hfilter.symm⟩

/-- Any nonempty Finset of nonempty positive grid clauses admits a matching
that kills at least one member. -/
theorem exists_matching_kills_one {n : ℕ} (_hn : 0 < n)
    (Large : Finset Clause) (hne : Large.Nonempty)
    (hsub : ∀ C ∈ Large, C ⊆ gridPosLits n)
    (hnC : ∀ C ∈ Large, C.Nonempty) :
    ∃ i : Fin (n + 1), ∃ j : Fin n,
      (Large.filter (killedByMatching n i j)).Nonempty := by
  obtain ⟨C, hC⟩ := hne
  obtain ⟨l, hl⟩ := hnC C hC
  obtain ⟨i, j, rfl⟩ := (mem_gridPosLits_iff).mp (hsub C hC hl)
  exact ⟨i, j, ⟨C, mem_filter.mpr ⟨hC, hl⟩⟩⟩

/-- One kill step strictly decreases the large-set cardinality. -/
theorem filter_not_killed_card_lt {n : ℕ} (i : Fin (n + 1)) (j : Fin n)
    (Large : Finset Clause)
    (hkill : (Large.filter (killedByMatching n i j)).Nonempty) :
    (Large.filter (fun C => ¬ killedByMatching n i j C)).card < Large.card := by
  have hpos : 0 < (Large.filter (killedByMatching n i j)).card :=
    card_pos.mpr hkill
  have hLpos : 0 < Large.card := lt_of_lt_of_le hpos (card_filter_le _ _)
  rw [filter_not_killed_card]
  exact Nat.sub_lt hLpos hpos

/-- Popular averaging gives a strict drop when `|Large| * W ≥ V`. -/
theorem large_survivors_lt {n : ℕ} (hn : 0 < n)
    (Large : Finset Clause)
    (hwide : ∀ C ∈ Large, largeThreshold n ≤ C.card)
    (hsub : ∀ C ∈ Large, C ⊆ gridPosLits n)
    (hbig : (n + 1) * n ≤ Large.card * largeThreshold n) :
    ∃ i : Fin (n + 1), ∃ j : Fin n,
      (Large.filter (fun C => ¬ killedByMatching n i j C)).card < Large.card := by
  obtain ⟨i, j, hle⟩ := large_survivors_le hn Large hwide hsub
  refine ⟨i, j, ?_⟩
  -- Averaging dividend is positive once |Large| * W ≥ V.
  have hV : 0 < (n + 1) * n := Nat.mul_pos (Nat.succ_pos n) hn
  have hdivPos : 0 < (Large.card * largeThreshold n) / ((n + 1) * n) :=
    Nat.div_pos hbig hV
  have hLpos : 0 < Large.card := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, Nat.zero_mul] at hbig
    exact (not_le_of_gt hV) hbig
  -- Survivors ≤ card − div < card.
  exact lt_of_le_of_lt hle (Nat.sub_lt hLpos hdivPos)

/-- Progress lemma for iteration: a nonempty positive grid set admits a matching
whose unkilled subset is strictly smaller. -/
theorem exists_matching_strict_progress {n : ℕ} (hn : 0 < n)
    (Large : Finset Clause) (hne : Large.Nonempty)
    (hsub : ∀ C ∈ Large, C ⊆ gridPosLits n)
    (hnC : ∀ C ∈ Large, C.Nonempty) :
    ∃ i : Fin (n + 1), ∃ j : Fin n,
      (Large.filter (fun C => ¬ killedByMatching n i j C)).card < Large.card := by
  obtain ⟨i, j, hkill⟩ := exists_matching_kills_one hn Large hne hsub hnC
  exact ⟨i, j, filter_not_killed_card_lt i j Large hkill⟩

/-! ## G7e: renaming iso foundation after a matching step

After placing pigeon `i` into hole `j` in PHP(k+2, k+1), surviving PHP axioms
are (after Fin.succAbove reindexing) exactly the axioms of PHP(k+1, k).
Variable indices still change (`pvar` width drops from k+1 to k), so we embed
rather than use identity on ℕ.
-/

/-- Dropping index `p` from `Fin (n+1)` is the image of `succAbove`. -/
theorem univ_erase_eq_image_succAbove {n : ℕ} (p : Fin (n + 1)) :
    (univ : Finset (Fin (n + 1))).erase p = univ.image p.succAbove := by
  rw [← compl_singleton, (Fin.image_succAbove_univ p).symm]

/-- Embed a PHP(k+1, k) grid variable into PHP(k+2, k+1) after removing `(i,j)`. -/
def matchingEmbedVar (k : ℕ) (i : Fin (k + 2)) (j : Fin (k + 1))
    (i' : Fin (k + 1)) (j' : Fin k) : ℕ :=
  pvar (k + 1) (i.succAbove i') (j.succAbove j')

/-- Renamed pigeon axiom of the smaller PHP, as a clause on the large grid. -/
noncomputable def matchingRenamePigeonClause (k : ℕ) (i : Fin (k + 2)) (j : Fin (k + 1))
    (i' : Fin (k + 1)) : Clause :=
  (univ : Finset (Fin k)).image fun j' =>
    (⟨matchingEmbedVar k i j i' j', true⟩ : Literal)

/-- Renamed hole axiom forbidding two remaining pigeons from sharing a remaining hole. -/
noncomputable def matchingRenameHoleClause (k : ℕ) (i : Fin (k + 2)) (j : Fin (k + 1))
    (j' : Fin k) (i1 i2 : Fin (k + 1)) : Clause :=
  ({⟨matchingEmbedVar k i j i1 j', false⟩,
      ⟨matchingEmbedVar k i j i2 j', false⟩} : Clause)

/-- Image of `phpCNF k` under the matching rename embedding. -/
noncomputable def matchingRenameCNF (k : ℕ) (i : Fin (k + 2)) (j : Fin (k + 1)) : CNF :=
  ((univ : Finset (Fin (k + 1))).image fun i' => matchingRenamePigeonClause k i j i') ∪
    ((univ : Finset (Fin k)).biUnion fun j' =>
      (univ : Finset (Fin (k + 1))).biUnion fun i1 =>
        ((univ : Finset (Fin (k + 1))).filter fun i2 => i1 < i2).image fun i2 =>
          matchingRenameHoleClause k i j j' i1 i2)

theorem matchingLookup_off_grid_succAbove {k : ℕ}
    (i : Fin (k + 2)) (j : Fin (k + 1)) (i' : Fin (k + 1)) (j' : Fin k) :
    matchingLookup (k + 1) i j (matchingEmbedVar k i j i' j') = none :=
  matchingLookup_off_grid (Fin.succAbove_ne i i') (Fin.succAbove_ne j j')

/-- Surviving pigeon axiom after matching equals the renamed smaller pigeon axiom. -/
theorem restrictClause_pigeonClause_succAbove {k : ℕ}
    (i : Fin (k + 2)) (j : Fin (k + 1)) (i' : Fin (k + 1)) :
    restrictClause (matchingLookup (k + 1) i j) (pigeonClause (k + 1) (i.succAbove i')) =
      some (matchingRenamePigeonClause k i j i') := by
  have h := restrictClause_pigeonClause_other (i := i) (i' := i.succAbove i') j
    (Fin.succAbove_ne i i')
  rw [h]
  congr 1
  -- erase j = image succAbove, then reindex literals.
  rw [matchingRenamePigeonClause, univ_erase_eq_image_succAbove, image_image]
  rfl

/-- Hole axiom on the matched column is killed (column forced false). -/
theorem restrictClause_hole_on_matched_col {k : ℕ}
    (i : Fin (k + 2)) (j : Fin (k + 1))
    {i1 i2 : Fin (k + 2)} (h1 : i1 ≠ i) (_h2 : i2 ≠ i) :
    restrictClause (matchingLookup (k + 1) i j)
      ({⟨pvar (k + 1) i1 j, false⟩, ⟨pvar (k + 1) i2 j, false⟩} : Clause) = none :=
  (restrictClause_eq_none_iff _ _).mpr
    ⟨⟨pvar (k + 1) i1 j, false⟩, mem_insert_self _ _,
      matchingLookup_col (i := i) (i' := i1) j h1⟩

/-- Hole axiom on the matched row is killed (row forced false). -/
theorem restrictClause_hole_on_matched_row {k : ℕ}
    (i : Fin (k + 2)) (j : Fin (k + 1))
    {j' : Fin (k + 1)} (hj : j' ≠ j) {i' : Fin (k + 2)} (_hi : i' ≠ i) :
    restrictClause (matchingLookup (k + 1) i j)
      ({⟨pvar (k + 1) i j', false⟩, ⟨pvar (k + 1) i' j', false⟩} : Clause) = none :=
  (restrictClause_eq_none_iff _ _).mpr
    ⟨⟨pvar (k + 1) i j', false⟩, mem_insert_self _ _, matchingLookup_row i hj⟩

/-- Hole axiom involving the placed cell polarity is killed by column force on the other pigeon. -/
theorem restrictClause_hole_with_place {k : ℕ}
    (i : Fin (k + 2)) (j : Fin (k + 1)) {i' : Fin (k + 2)} (hne : i' ≠ i) :
    restrictClause (matchingLookup (k + 1) i j)
      ({⟨pvar (k + 1) i j, false⟩, ⟨pvar (k + 1) i' j, false⟩} : Clause) = none :=
  (restrictClause_eq_none_iff _ _).mpr
    ⟨⟨pvar (k + 1) i' j, false⟩, mem_insert_of_mem (mem_singleton_self _),
      matchingLookup_col (i := i) (i' := i') j hne⟩

/-- Off-matching hole axiom restricts to the renamed smaller hole axiom. -/
theorem restrictClause_hole_succAbove {k : ℕ}
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (j' : Fin k) {i1 i2 : Fin (k + 1)} (_hlt : i1 < i2) :
    restrictClause (matchingLookup (k + 1) i j)
        ({⟨pvar (k + 1) (i.succAbove i1) (j.succAbove j'), false⟩,
          ⟨pvar (k + 1) (i.succAbove i2) (j.succAbove j'), false⟩} : Clause) =
      some (matchingRenameHoleClause k i j j' i1 i2) := by
  set ρ := matchingLookup (k + 1) i j
  set C : Clause :=
    {⟨pvar (k + 1) (i.succAbove i1) (j.succAbove j'), false⟩,
      ⟨pvar (k + 1) (i.succAbove i2) (j.succAbove j'), false⟩}
  have hoff1 :
      ρ (pvar (k + 1) (i.succAbove i1) (j.succAbove j')) = none :=
    matchingLookup_off_grid (Fin.succAbove_ne i i1) (Fin.succAbove_ne j j')
  have hoff2 :
      ρ (pvar (k + 1) (i.succAbove i2) (j.succAbove j')) = none :=
    matchingLookup_off_grid (Fin.succAbove_ne i i2) (Fin.succAbove_ne j j')
  have hnsat : ∀ l ∈ C, ρ l.var ≠ some l.pos := by
    intro l hl hρ
    have hl' : l = ⟨pvar (k + 1) (i.succAbove i1) (j.succAbove j'), false⟩ ∨
        l = ⟨pvar (k + 1) (i.succAbove i2) (j.succAbove j'), false⟩ := by
      simpa [C, mem_insert, mem_singleton] using hl
    rcases hl' with rfl | rfl
    · simp only at hρ
      rw [hoff1] at hρ
      exact (Option.some_ne_none false hρ.symm).elim
    · simp only at hρ
      rw [hoff2] at hρ
      exact (Option.some_ne_none false hρ.symm).elim
  have hfilter : C.filter (fun l => ρ l.var = none) = matchingRenameHoleClause k i j j' i1 i2 := by
    ext l
    constructor
    · intro hl
      obtain ⟨hlC, hun⟩ := mem_filter.mp hl
      have hl' : l = ⟨pvar (k + 1) (i.succAbove i1) (j.succAbove j'), false⟩ ∨
          l = ⟨pvar (k + 1) (i.succAbove i2) (j.succAbove j'), false⟩ := by
        simpa [C, mem_insert, mem_singleton] using hlC
      rcases hl' with rfl | rfl
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_singleton_self _)
    · intro hl
      have hl' : l = ⟨matchingEmbedVar k i j i1 j', false⟩ ∨
          l = ⟨matchingEmbedVar k i j i2 j', false⟩ := by
        simpa [matchingRenameHoleClause, mem_insert, mem_singleton] using hl
      rcases hl' with rfl | rfl
      · exact mem_filter.mpr ⟨by simp [C, matchingEmbedVar], hoff1⟩
      · exact mem_filter.mpr ⟨by simp [C, matchingEmbedVar], hoff2⟩
  exact (restrictClause_eq_some_iff ρ C _).mpr ⟨hnsat, hfilter.symm⟩

/-- Every renamed smaller PHP clause appears in the matching restriction. -/
theorem matchingRenameCNF_subset_restrict {k : ℕ}
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    matchingRenameCNF k i j ⊆
      restrictCNF (matchingLookup (k + 1) i j) (phpCNF (k + 1)) := by
  intro C hC
  simp only [matchingRenameCNF, mem_union, mem_image, mem_biUnion] at hC
  rcases hC with hpig | hhole
  · obtain ⟨i', _, rfl⟩ := hpig
    refine (mem_restrictCNF_iff _ _ _).mpr ?_
    refine ⟨pigeonClause (k + 1) (i.succAbove i'), ?_, ?_⟩
    · exact mem_union_left _ (mem_image_of_mem _ (mem_univ _))
    · exact restrictClause_pigeonClause_succAbove i j i'
  · obtain ⟨j', _, i1, _, i2, hi2, rfl⟩ := hhole
    have hlt : i1 < i2 := (mem_filter.mp hi2).2
    refine (mem_restrictCNF_iff _ _ _).mpr ?_
    refine ⟨({⟨pvar (k + 1) (i.succAbove i1) (j.succAbove j'), false⟩,
        ⟨pvar (k + 1) (i.succAbove i2) (j.succAbove j'), false⟩} : Clause), ?_, ?_⟩
    · refine mem_union_right _ ?_
      refine mem_biUnion.mpr ⟨j.succAbove j', mem_univ _, ?_⟩
      refine mem_biUnion.mpr ⟨i.succAbove i1, mem_univ _, ?_⟩
      refine mem_image.mpr ⟨i.succAbove i2, ?_, rfl⟩
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      exact (Fin.strictMono_succAbove i).lt_iff_lt.mpr hlt
    · exact restrictClause_hole_succAbove i j j' hlt

/-- Matching restriction of PHP produces only renamed smaller PHP clauses. -/
theorem restrict_subset_matchingRenameCNF {k : ℕ}
    (placed : Fin (k + 2)) (hole : Fin (k + 1)) :
    restrictCNF (matchingLookup (k + 1) placed hole) (phpCNF (k + 1)) ⊆
      matchingRenameCNF k placed hole := by
  intro C' hC'
  obtain ⟨C, hC, hres⟩ := (mem_restrictCNF_iff _ _ _).mp hC'
  rcases mem_union.mp hC with hpig | hhole
  · -- Surviving pigeon axioms are renamed smaller pigeon axioms.
    obtain ⟨i0, _, rfl⟩ := mem_image.mp hpig
    by_cases hi0 : i0 = placed
    · rw [hi0, restrictClause_pigeonClause_place placed hole] at hres
      exact (Option.some_ne_none _ hres.symm).elim
    · obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hi0
      rw [restrictClause_pigeonClause_succAbove placed hole i'] at hres
      have hC'eq : C' = matchingRenamePigeonClause k placed hole i' :=
        (Option.some.inj hres).symm
      rw [hC'eq]
      exact mem_union_left _ (mem_image_of_mem _ (mem_univ _))
  · -- Surviving hole axioms are renamed smaller hole axioms.
    obtain ⟨j0, _, hrest⟩ := mem_biUnion.mp hhole
    obtain ⟨i1, _, hrest2⟩ := mem_biUnion.mp hrest
    obtain ⟨i2, hi2f, rfl⟩ := mem_image.mp hrest2
    have hlt : i1 < i2 := (mem_filter.mp hi2f).2
    by_cases hj0 : j0 = hole
    · -- Matched column: hole axiom is killed.
      rw [hj0] at hres
      by_cases h1 : i1 = placed
      · rw [h1, restrictClause_hole_with_place placed hole (ne_of_gt (h1 ▸ hlt))] at hres
        exact (Option.some_ne_none _ hres.symm).elim
      · by_cases h2 : i2 = placed
        · have hnone :
              restrictClause (matchingLookup (k + 1) placed hole)
                ({⟨pvar (k + 1) i1 hole, false⟩, ⟨pvar (k + 1) placed hole, false⟩} : Clause) =
                  none :=
            (restrictClause_eq_none_iff _ _).mpr
              ⟨⟨pvar (k + 1) i1 hole, false⟩, mem_insert_self _ _,
                matchingLookup_col (i := placed) (i' := i1) hole h1⟩
          rw [h2, hnone] at hres
          exact (Option.some_ne_none _ hres.symm).elim
        · rw [restrictClause_hole_on_matched_col placed hole h1 h2] at hres
          exact (Option.some_ne_none _ hres.symm).elim
    · -- Off column: if either pigeon is the placed one, row force kills; else rename.
      by_cases h1 : i1 = placed
      · rw [h1, restrictClause_hole_on_matched_row placed hole hj0 (ne_of_gt (h1 ▸ hlt))] at hres
        exact (Option.some_ne_none _ hres.symm).elim
      · by_cases h2 : i2 = placed
        · have hnone :
              restrictClause (matchingLookup (k + 1) placed hole)
                ({⟨pvar (k + 1) i1 j0, false⟩, ⟨pvar (k + 1) placed j0, false⟩} : Clause) =
                  none :=
            (restrictClause_eq_none_iff _ _).mpr
              ⟨⟨pvar (k + 1) placed j0, false⟩, mem_insert_of_mem (mem_singleton_self _),
                matchingLookup_row placed hj0⟩
          rw [h2, hnone] at hres
          exact (Option.some_ne_none _ hres.symm).elim
        · obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj0
          obtain ⟨i1', rfl⟩ := Fin.exists_succAbove_eq h1
          obtain ⟨i2', rfl⟩ := Fin.exists_succAbove_eq h2
          have hlt' : i1' < i2' :=
            (Fin.strictMono_succAbove placed).lt_iff_lt.mp hlt
          rw [restrictClause_hole_succAbove placed hole j' hlt'] at hres
          have hC'eq : C' = matchingRenameHoleClause k placed hole j' i1' i2' :=
            (Option.some.inj hres).symm
          rw [hC'eq]
          refine mem_union_right _ ?_
          refine mem_biUnion.mpr ⟨j', mem_univ _, ?_⟩
          refine mem_biUnion.mpr ⟨i1', mem_univ _, ?_⟩
          exact mem_image.mpr
            ⟨i2', mem_filter.mpr ⟨mem_univ _, hlt'⟩, rfl⟩

/-- Matching restriction of `phpCNF (k+1)` equals the renamed `phpCNF k`. -/
theorem matchingRestrict_phpCNF_eq_rename {k : ℕ}
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    restrictCNF (matchingLookup (k + 1) i j) (phpCNF (k + 1)) =
      matchingRenameCNF k i j :=
  Subset.antisymm (restrict_subset_matchingRenameCNF i j)
    (matchingRenameCNF_subset_restrict i j)

/-! ## G7f: variable rename transport onto the smaller PHP

`matchingRenameCNF` is the pointwise image of `phpCNF k` under embedding its
grid variables. Derivations from `phpCNF k` transport into the rename CNF with
identical size. Combined with G7e and G7c this yields a same size refutation of
the matching restriction (hence of the rename image).
-/

/-- Rename a literal by acting on its variable index. -/
def renameLit (σ : ℕ → ℕ) (l : Literal) : Literal :=
  ⟨σ l.var, l.pos⟩

/-- Rename a clause pointwise. -/
noncomputable def renameClause (σ : ℕ → ℕ) (C : Clause) : Clause :=
  C.image (renameLit σ)

/-- Rename a CNF pointwise. -/
noncomputable def renameCNF (σ : ℕ → ℕ) (F : CNF) : CNF :=
  F.image (renameClause σ)

theorem renameClause_empty (σ : ℕ → ℕ) : renameClause σ (∅ : Clause) = ∅ := by
  simp [renameClause]

theorem mem_renameClause_iff (σ : ℕ → ℕ) (C : Clause) (l' : Literal) :
    l' ∈ renameClause σ C ↔ ∃ l ∈ C, renameLit σ l = l' :=
  mem_image

theorem matchingEmbedVar_inj {k : ℕ} {placed : Fin (k + 2)} {hole : Fin (k + 1)}
    {i₁ i₂ : Fin (k + 1)} {j₁ j₂ : Fin k}
    (h : matchingEmbedVar k placed hole i₁ j₁ = matchingEmbedVar k placed hole i₂ j₂) :
    i₁ = i₂ ∧ j₁ = j₂ := by
  have hinj := pvar_inj h
  exact ⟨Fin.succAbove_right_inj.mp hinj.1, Fin.succAbove_right_inj.mp hinj.2⟩

/-- Matching rename map: PHP(k+1, k) grid vars embed; all other indices stay put. -/
noncomputable def matchingRenameσ (k : ℕ) (placed : Fin (k + 2)) (hole : Fin (k + 1))
    (v : ℕ) : ℕ :=
  if h : ∃ p : Fin (k + 1) × Fin k, v = pvar k p.1 p.2 then
    let p := Classical.choose h
    matchingEmbedVar k placed hole p.1 p.2
  else
    v

theorem matchingRenameσ_pvar {k : ℕ} (placed : Fin (k + 2)) (hole : Fin (k + 1))
    (i' : Fin (k + 1)) (j' : Fin k) :
    matchingRenameσ k placed hole (pvar k i' j') =
      matchingEmbedVar k placed hole i' j' := by
  have hex : ∃ p : Fin (k + 1) × Fin k, pvar k i' j' = pvar k p.1 p.2 :=
    ⟨⟨i', j'⟩, rfl⟩
  simp only [matchingRenameσ, hex, ↓reduceDIte]
  have hspec := Classical.choose_spec hex
  have hinj := pvar_inj hspec.symm
  simp only [matchingEmbedVar]
  rw [hinj.1, hinj.2]

/-- Renamed pigeon axiom equals the pointwise rename of the small pigeon axiom. -/
theorem matchingRenamePigeonClause_eq_rename {k : ℕ}
    (placed : Fin (k + 2)) (hole : Fin (k + 1)) (i' : Fin (k + 1)) :
    matchingRenamePigeonClause k placed hole i' =
      renameClause (matchingRenameσ k placed hole) (pigeonClause k i') := by
  simp only [matchingRenamePigeonClause, renameClause, pigeonClause, image_image]
  refine image_congr fun j' _ => ?_
  change (⟨matchingEmbedVar k placed hole i' j', true⟩ : Literal) =
    ⟨matchingRenameσ k placed hole (pvar k i' j'), true⟩
  rw [matchingRenameσ_pvar]

/-- Renamed hole axiom equals the pointwise rename of the small hole axiom. -/
theorem matchingRenameHoleClause_eq_rename {k : ℕ}
    (placed : Fin (k + 2)) (hole : Fin (k + 1))
    (j' : Fin k) (i1 i2 : Fin (k + 1)) :
    matchingRenameHoleClause k placed hole j' i1 i2 =
      renameClause (matchingRenameσ k placed hole)
        ({⟨pvar k i1 j', false⟩, ⟨pvar k i2 j', false⟩} : Clause) := by
  ext l
  simp only [matchingRenameHoleClause, renameClause, mem_image, renameLit, mem_insert,
    mem_singleton]
  constructor
  · intro hl
    rcases hl with rfl | rfl
    · exact ⟨⟨pvar k i1 j', false⟩, Or.inl rfl, by simp [matchingRenameσ_pvar]⟩
    · exact ⟨⟨pvar k i2 j', false⟩, Or.inr rfl, by simp [matchingRenameσ_pvar]⟩
  · rintro ⟨l0, hl0, rfl⟩
    rcases hl0 with rfl | rfl
    · exact Or.inl (by simp [matchingRenameσ_pvar, matchingEmbedVar])
    · exact Or.inr (by simp [matchingRenameσ_pvar, matchingEmbedVar])

/-- The rename CNF is the pointwise image of `phpCNF k`. -/
theorem matchingRenameCNF_eq_renameCNF {k : ℕ}
    (placed : Fin (k + 2)) (hole : Fin (k + 1)) :
    matchingRenameCNF k placed hole =
      renameCNF (matchingRenameσ k placed hole) (phpCNF k) := by
  ext C
  constructor
  · intro hC
    simp only [renameCNF, mem_image]
    simp only [matchingRenameCNF, mem_union, mem_image, mem_biUnion] at hC
    rcases hC with hpig | hhole
    · obtain ⟨i', _, rfl⟩ := hpig
      refine ⟨pigeonClause k i', ?_,
        (matchingRenamePigeonClause_eq_rename placed hole i').symm⟩
      exact mem_union_left _ (mem_image_of_mem _ (mem_univ _))
    · obtain ⟨j', _, i1, _, i2, hi2, rfl⟩ := hhole
      have hlt : i1 < i2 := (mem_filter.mp hi2).2
      refine ⟨({⟨pvar k i1 j', false⟩, ⟨pvar k i2 j', false⟩} : Clause), ?_,
        (matchingRenameHoleClause_eq_rename placed hole j' i1 i2).symm⟩
      refine mem_union_right _ ?_
      refine mem_biUnion.mpr ⟨j', mem_univ _, ?_⟩
      refine mem_biUnion.mpr ⟨i1, mem_univ _, ?_⟩
      exact mem_image.mpr ⟨i2, mem_filter.mpr ⟨mem_univ _, hlt⟩, rfl⟩
  · intro hC
    obtain ⟨C0, hC0, rfl⟩ := mem_image.mp (show C ∈ renameCNF _ _ from hC)
    rcases mem_union.mp hC0 with hpig | hhole
    · obtain ⟨i', _, rfl⟩ := mem_image.mp hpig
      rw [← matchingRenamePigeonClause_eq_rename placed hole i']
      exact mem_union_left _ (mem_image_of_mem _ (mem_univ _))
    · obtain ⟨j', _, hrest⟩ := mem_biUnion.mp hhole
      obtain ⟨i1, _, hrest2⟩ := mem_biUnion.mp hrest
      obtain ⟨i2, hi2f, rfl⟩ := mem_image.mp hrest2
      have hlt : i1 < i2 := (mem_filter.mp hi2f).2
      rw [← matchingRenameHoleClause_eq_rename placed hole j' i1 i2]
      refine mem_union_right _ ?_
      refine mem_biUnion.mpr ⟨j', mem_univ _, ?_⟩
      refine mem_biUnion.mpr ⟨i1, mem_univ _, ?_⟩
      exact mem_image.mpr ⟨i2, mem_filter.mpr ⟨mem_univ _, hlt⟩, rfl⟩

/-- Injectivity of matching rename on PHP(k+1, k) grid variables. -/
theorem matchingRenameσ_inj_on_pvar {k : ℕ} (placed : Fin (k + 2)) (hole : Fin (k + 1))
    {i₁ i₂ : Fin (k + 1)} {j₁ j₂ : Fin k}
    (h : matchingRenameσ k placed hole (pvar k i₁ j₁) =
      matchingRenameσ k placed hole (pvar k i₂ j₂)) :
    i₁ = i₂ ∧ j₁ = j₂ := by
  rw [matchingRenameσ_pvar, matchingRenameσ_pvar] at h
  exact matchingEmbedVar_inj h

/-- Inverse rename: embedded large-grid vars decode back to PHP(k+1, k) vars. -/
noncomputable def matchingUnrenameσ (k : ℕ) (placed : Fin (k + 2)) (hole : Fin (k + 1))
    (v : ℕ) : ℕ :=
  if h : ∃ p : Fin (k + 1) × Fin k, v = matchingEmbedVar k placed hole p.1 p.2 then
    let p := Classical.choose h
    pvar k p.1 p.2
  else
    v

theorem matchingUnrenameσ_embed {k : ℕ} (placed : Fin (k + 2)) (hole : Fin (k + 1))
    (i' : Fin (k + 1)) (j' : Fin k) :
    matchingUnrenameσ k placed hole (matchingEmbedVar k placed hole i' j') =
      pvar k i' j' := by
  have hex : ∃ p : Fin (k + 1) × Fin k,
      matchingEmbedVar k placed hole i' j' = matchingEmbedVar k placed hole p.1 p.2 :=
    ⟨⟨i', j'⟩, rfl⟩
  simp only [matchingUnrenameσ, hex, ↓reduceDIte]
  have hspec := Classical.choose_spec hex
  have hinj := matchingEmbedVar_inj hspec.symm
  rw [hinj.1, hinj.2]

theorem matchingUnrenameσ_rename_pvar {k : ℕ} (placed : Fin (k + 2)) (hole : Fin (k + 1))
    (i' : Fin (k + 1)) (j' : Fin k) :
    matchingUnrenameσ k placed hole (matchingRenameσ k placed hole (pvar k i' j')) =
      pvar k i' j' := by
  rw [matchingRenameσ_pvar, matchingUnrenameσ_embed]

/-- Unrenaming a renamed pigeon axiom recovers the small pigeon axiom. -/
theorem unrename_matchingRenamePigeonClause {k : ℕ}
    (placed : Fin (k + 2)) (hole : Fin (k + 1)) (i' : Fin (k + 1)) :
    renameClause (matchingUnrenameσ k placed hole)
        (matchingRenamePigeonClause k placed hole i') =
      pigeonClause k i' := by
  rw [matchingRenamePigeonClause_eq_rename]
  simp only [renameClause, pigeonClause, image_image]
  refine image_congr fun j' _ => ?_
  change (⟨matchingUnrenameσ k placed hole
      (matchingRenameσ k placed hole (pvar k i' j')), true⟩ : Literal) =
    ⟨pvar k i' j', true⟩
  rw [matchingUnrenameσ_rename_pvar]

/-- Unrenaming a renamed hole axiom recovers the small hole axiom. -/
theorem unrename_matchingRenameHoleClause {k : ℕ}
    (placed : Fin (k + 2)) (hole : Fin (k + 1))
    (j' : Fin k) (i1 i2 : Fin (k + 1)) :
    renameClause (matchingUnrenameσ k placed hole)
        (matchingRenameHoleClause k placed hole j' i1 i2) =
      ({⟨pvar k i1 j', false⟩, ⟨pvar k i2 j', false⟩} : Clause) := by
  set H : Clause := {⟨pvar k i1 j', false⟩, ⟨pvar k i2 j', false⟩}
  set σ := matchingRenameσ k placed hole
  set τ := matchingUnrenameσ k placed hole
  have hren : matchingRenameHoleClause k placed hole j' i1 i2 = renameClause σ H :=
    matchingRenameHoleClause_eq_rename placed hole j' i1 i2
  rw [hren]
  have hback_lit (ia : Fin (k + 1)) :
      renameLit τ (renameLit σ ⟨pvar k ia j', false⟩) = ⟨pvar k ia j', false⟩ := by
    dsimp [σ, τ, renameLit]
    exact congrArg (fun v => (⟨v, false⟩ : Literal))
      (matchingUnrenameσ_rename_pvar placed hole ia j')
  ext l
  constructor
  · intro hl
    obtain ⟨l1, hl1, rfl⟩ := (mem_renameClause_iff τ _ _).mp hl
    obtain ⟨l0, hl0, rfl⟩ := (mem_renameClause_iff σ _ _).mp hl1
    have hl0' : l0 = ⟨pvar k i1 j', false⟩ ∨ l0 = ⟨pvar k i2 j', false⟩ := by
      simpa [H, mem_insert, mem_singleton] using hl0
    rcases hl0' with rfl | rfl
    · simpa [hback_lit i1] using (show ⟨pvar k i1 j', false⟩ ∈ H from hl0)
    · simpa [hback_lit i2] using (show ⟨pvar k i2 j', false⟩ ∈ H from hl0)
  · intro hl
    have hl' : l = ⟨pvar k i1 j', false⟩ ∨ l = ⟨pvar k i2 j', false⟩ := by
      simpa [H, mem_insert, mem_singleton] using hl
    rcases hl' with rfl | rfl
    · refine (mem_renameClause_iff τ _ _).mpr
        ⟨renameLit σ ⟨pvar k i1 j', false⟩, ?_, hback_lit i1⟩
      · exact (mem_renameClause_iff σ _ _).mpr ⟨⟨pvar k i1 j', false⟩, mem_insert_self _ _, rfl⟩
    · refine (mem_renameClause_iff τ _ _).mpr
        ⟨renameLit σ ⟨pvar k i2 j', false⟩, ?_, hback_lit i2⟩
      · exact (mem_renameClause_iff σ _ _).mpr
          ⟨⟨pvar k i2 j', false⟩, mem_insert_of_mem (mem_singleton_self _), rfl⟩

/-- Unrenaming the matching rename CNF recovers `phpCNF k`. -/
theorem unrename_matchingRenameCNF {k : ℕ}
    (placed : Fin (k + 2)) (hole : Fin (k + 1)) :
    renameCNF (matchingUnrenameσ k placed hole) (matchingRenameCNF k placed hole) =
      phpCNF k := by
  rw [matchingRenameCNF_eq_renameCNF]
  ext C
  simp only [renameCNF, mem_image]
  constructor
  · rintro ⟨C1, ⟨C0, hC0, rfl⟩, rfl⟩
    -- C1 = renameClause σ C0, and we unrename it back.
    -- Need renameClause τ (renameClause σ C0) = C0 for C0 ∈ phpCNF k.
    rcases mem_union.mp hC0 with hpig | hhole
    · obtain ⟨i', _, rfl⟩ := mem_image.mp hpig
      have hback := unrename_matchingRenamePigeonClause placed hole i'
      rw [matchingRenamePigeonClause_eq_rename] at hback
      rw [hback]
      exact mem_union_left _ (mem_image_of_mem _ (mem_univ _))
    · obtain ⟨j', _, hrest⟩ := mem_biUnion.mp hhole
      obtain ⟨i1, _, hrest2⟩ := mem_biUnion.mp hrest
      obtain ⟨i2, hi2f, rfl⟩ := mem_image.mp hrest2
      have hlt : i1 < i2 := (mem_filter.mp hi2f).2
      have hback := unrename_matchingRenameHoleClause placed hole j' i1 i2
      rw [matchingRenameHoleClause_eq_rename] at hback
      rw [hback]
      refine mem_union_right _ ?_
      refine mem_biUnion.mpr ⟨j', mem_univ _, ?_⟩
      refine mem_biUnion.mpr ⟨i1, mem_univ _, ?_⟩
      exact mem_image.mpr ⟨i2, mem_filter.mpr ⟨mem_univ _, hlt⟩, rfl⟩
  · intro hC
    rcases mem_union.mp hC with hpig | hhole
    · obtain ⟨i', _, rfl⟩ := mem_image.mp hpig
      refine ⟨matchingRenamePigeonClause k placed hole i', ?_, ?_⟩
      · exact ⟨pigeonClause k i', mem_union_left _ (mem_image_of_mem _ (mem_univ _)),
          (matchingRenamePigeonClause_eq_rename placed hole i').symm⟩
      · exact unrename_matchingRenamePigeonClause placed hole i'
    · obtain ⟨j', _, hrest⟩ := mem_biUnion.mp hhole
      obtain ⟨i1, _, hrest2⟩ := mem_biUnion.mp hrest
      obtain ⟨i2, hi2f, rfl⟩ := mem_image.mp hrest2
      have hlt : i1 < i2 := (mem_filter.mp hi2f).2
      refine ⟨matchingRenameHoleClause k placed hole j' i1 i2, ?_, ?_⟩
      · refine ⟨({⟨pvar k i1 j', false⟩, ⟨pvar k i2 j', false⟩} : Clause), ?_,
          (matchingRenameHoleClause_eq_rename placed hole j' i1 i2).symm⟩
        refine mem_union_right _ ?_
        refine mem_biUnion.mpr ⟨j', mem_univ _, ?_⟩
        refine mem_biUnion.mpr ⟨i1, mem_univ _, ?_⟩
        exact mem_image.mpr ⟨i2, mem_filter.mpr ⟨mem_univ _, hlt⟩, rfl⟩
      · exact unrename_matchingRenameHoleClause placed hole j' i1 i2

/-! ## G7g: size preserving derivation transport along injective renames

A rename that is injective on the variables of the hypothesis CNF transports
derivations clause by clause with identical size. Applied to
`matchingUnrenameσ` on `matchingRenameCNF` (whose variables are exactly the
embedded grid variables) this turns a restricted PHP(k+2, k+1) refutation into
a PHP(k+1, k) refutation of the same size, completing the shrink step.
-/

/-- Every clause in a derivation from `F` uses only variables of `F`. -/
theorem derivation_clauseVars_subset {F : CNF} {C : Clause}
    (d : Derivation F C) : clauseVars C ⊆ cnfVars F := by
  induction d with
  | hyp C hC => exact fun v hv => mem_biUnion.mpr ⟨C, hC, hv⟩
  | res x dC dD hx hnx ihC ihD =>
      intro v hv
      obtain ⟨l, hl, rfl⟩ := mem_image.mp hv
      rcases mem_union.mp hl with hlC | hlD
      · exact ihC (mem_image_of_mem _ (mem_of_mem_erase hlC))
      · exact ihD (mem_image_of_mem _ (mem_of_mem_erase hlD))

/-- Rename commutes with erasing the pivot literal when the rename cannot
identify a clause variable with the pivot without them being equal. -/
private theorem renameClause_erase_pivot {σ : ℕ → ℕ} {S : Clause} {x : ℕ}
    (b : Bool) (hS : ∀ l ∈ S, σ l.var = σ x → l.var = x) :
    renameClause σ (S.erase ⟨x, b⟩) = (renameClause σ S).erase ⟨σ x, b⟩ := by
  ext l'
  simp only [renameClause, mem_image, mem_erase]
  constructor
  · rintro ⟨l, ⟨hlne, hlS⟩, rfl⟩
    refine ⟨?_, ⟨l, hlS, rfl⟩⟩
    intro heq
    apply hlne
    have hvar : σ l.var = σ x := congrArg Literal.var heq
    have hpos : l.pos = b := congrArg Literal.pos heq
    have hlx : l.var = x := hS l hlS hvar
    calc l = ⟨l.var, l.pos⟩ := rfl
      _ = ⟨x, b⟩ := by rw [hlx, hpos]
  · rintro ⟨hne, l, hlS, rfl⟩
    refine ⟨l, ⟨?_, hlS⟩, rfl⟩
    rintro rfl
    exact hne rfl

/-- Rename commutes with resolvents under pivot local injectivity. -/
theorem renameClause_resolvent_of_pivot_inj {σ : ℕ → ℕ} {C D : Clause} {x : ℕ}
    (hCx : ∀ l ∈ C, σ l.var = σ x → l.var = x)
    (hDx : ∀ l ∈ D, σ l.var = σ x → l.var = x) :
    renameClause σ (resolvent C D x) =
      resolvent (renameClause σ C) (renameClause σ D) (σ x) := by
  show renameClause σ ((C.erase ⟨x, true⟩) ∪ (D.erase ⟨x, false⟩)) = _
  rw [show renameClause σ ((C.erase ⟨x, true⟩) ∪ (D.erase ⟨x, false⟩)) =
      renameClause σ (C.erase ⟨x, true⟩) ∪ renameClause σ (D.erase ⟨x, false⟩) from
    image_union _ _,
    renameClause_erase_pivot true hCx, renameClause_erase_pivot false hDx]
  rfl

/-- Derivations transport along renames injective on the hypothesis variables,
with identical size. -/
theorem exists_derivation_renameInj {σ : ℕ → ℕ} {F : CNF}
    (hσ : ∀ v ∈ cnfVars F, ∀ w ∈ cnfVars F, σ v = σ w → v = w) :
    ∀ {C : Clause} (d : Derivation F C),
      ∃ d' : Derivation (renameCNF σ F) (renameClause σ C), d'.size = d.size := by
  intro C d
  induction d with
  | hyp C hC => exact ⟨.hyp _ (mem_image_of_mem _ hC), rfl⟩
  | @res x Cp Dp dC dD hx hnx ihC ihD =>
      obtain ⟨dC', hsC⟩ := ihC
      obtain ⟨dD', hsD⟩ := ihD
      have hCsub := derivation_clauseVars_subset dC
      have hDsub := derivation_clauseVars_subset dD
      have hxF : x ∈ cnfVars F := hCsub (mem_image_of_mem _ hx)
      have hCx : ∀ l ∈ Cp, σ l.var = σ x → l.var = x := fun l hl h =>
        hσ l.var (hCsub (mem_image_of_mem _ hl)) x hxF h
      have hDx : ∀ l ∈ Dp, σ l.var = σ x → l.var = x := fun l hl h =>
        hσ l.var (hDsub (mem_image_of_mem _ hl)) x hxF h
      have hres := renameClause_resolvent_of_pivot_inj hCx hDx
      rw [hres]
      have hx' : (⟨σ x, true⟩ : Literal) ∈ renameClause σ _ :=
        mem_image_of_mem (renameLit σ) hx
      have hnx' : (⟨σ x, false⟩ : Literal) ∈ renameClause σ _ :=
        mem_image_of_mem (renameLit σ) hnx
      exact ⟨.res (σ x) dC' dD' hx' hnx', by
        simp [Derivation.size, hsC, hsD]⟩

/-- Transport a refutation across a CNF equality, preserving size. -/
theorem exists_refutation_of_cnf_eq {F G : CNF} (h : F = G)
    (d : Derivation F (∅ : Clause)) :
    ∃ d' : Derivation G (∅ : Clause), d'.size = d.size := by
  subst h
  exact ⟨d, rfl⟩

/-- Transport a derivation across a conclusion equality, preserving size. -/
theorem exists_derivation_of_concl_eq {F : CNF} {C C' : Clause} (h : C = C')
    (d : Derivation F C) :
    ∃ d' : Derivation F C', d'.size = d.size := by
  subst h
  exact ⟨d, rfl⟩

/-- Variables of the rename CNF are exactly embedded grid variables. -/
theorem mem_cnfVars_matchingRenameCNF {k : ℕ} {placed : Fin (k + 2)}
    {hole : Fin (k + 1)} {v : ℕ}
    (hv : v ∈ cnfVars (matchingRenameCNF k placed hole)) :
    ∃ i' : Fin (k + 1), ∃ j' : Fin k, v = matchingEmbedVar k placed hole i' j' := by
  obtain ⟨C, hC, hvC⟩ := mem_biUnion.mp hv
  obtain ⟨l, hl, rfl⟩ := mem_image.mp hvC
  rcases mem_union.mp hC with hpig | hhole
  · obtain ⟨i', _, rfl⟩ := mem_image.mp hpig
    obtain ⟨j', _, rfl⟩ := mem_image.mp hl
    exact ⟨i', j', rfl⟩
  · obtain ⟨j', _, hrest⟩ := mem_biUnion.mp hhole
    obtain ⟨i1, _, hrest2⟩ := mem_biUnion.mp hrest
    obtain ⟨i2, _, rfl⟩ := mem_image.mp hrest2
    have hl' : l = ⟨matchingEmbedVar k placed hole i1 j', false⟩ ∨
        l = ⟨matchingEmbedVar k placed hole i2 j', false⟩ := by
      simpa [matchingRenameHoleClause, mem_insert, mem_singleton] using hl
    rcases hl' with rfl | rfl
    · exact ⟨i1, j', rfl⟩
    · exact ⟨i2, j', rfl⟩

/-- The unrename map is injective on the variables of the rename CNF. -/
theorem matchingUnrenameσ_injOn {k : ℕ} (placed : Fin (k + 2)) (hole : Fin (k + 1)) :
    ∀ v ∈ cnfVars (matchingRenameCNF k placed hole),
      ∀ w ∈ cnfVars (matchingRenameCNF k placed hole),
        matchingUnrenameσ k placed hole v = matchingUnrenameσ k placed hole w →
          v = w := by
  intro v hv w hw h
  obtain ⟨i1, j1, rfl⟩ := mem_cnfVars_matchingRenameCNF hv
  obtain ⟨i2, j2, rfl⟩ := mem_cnfVars_matchingRenameCNF hw
  rw [matchingUnrenameσ_embed, matchingUnrenameσ_embed] at h
  have hinj := pvar_inj h
  rw [hinj.1, hinj.2]

/-- BP96 shrink step: a PHP(k+2, k+1) refutation yields a PHP(k+1, k)
refutation of at most the same size. -/
theorem php_shrink_step {k : ℕ} (d : Derivation (phpCNF (k + 1)) (∅ : Clause)) :
    ∃ d' : Derivation (phpCNF k) (∅ : Clause), d'.size ≤ d.size := by
  classical
  -- Restrict along the matching placing pigeon 0 in hole 0.
  obtain ⟨d1, hs1⟩ :=
    exists_matchingRestrict_refutation (0 : Fin (k + 2)) (0 : Fin (k + 1)) d
  -- Identify the restricted CNF with the renamed smaller PHP.
  obtain ⟨d2, hs2⟩ :=
    exists_refutation_of_cnf_eq (matchingRestrict_phpCNF_eq_rename 0 0) d1
  -- Unrename back onto the standard smaller PHP grid.
  obtain ⟨d3, hs3⟩ := exists_derivation_renameInj (matchingUnrenameσ_injOn 0 0) d2
  obtain ⟨d4, hs4⟩ := exists_derivation_of_concl_eq
    (renameClause_empty (matchingUnrenameσ k 0 0)) d3
  obtain ⟨d5, hs5⟩ :=
    exists_refutation_of_cnf_eq (unrename_matchingRenameCNF 0 0) d4
  exact ⟨d5, by omega⟩

/-- Iterated shrink: PHP refutations transfer down to any smaller instance. -/
theorem php_shrink_le (m : ℕ) :
    ∀ n, m ≤ n → ∀ d : Derivation (phpCNF n) (∅ : Clause),
      ∃ d' : Derivation (phpCNF m) (∅ : Clause), d'.size ≤ d.size := by
  intro n
  induction n with
  | zero =>
      intro h d
      obtain rfl := Nat.le_zero.mp h
      exact ⟨d, le_rfl⟩
  | succ q ih =>
      intro h d
      rcases eq_or_lt_of_le h with rfl | hlt
      · exact ⟨d, le_rfl⟩
      · obtain ⟨d1, hs1⟩ := php_shrink_step d
        obtain ⟨d2, hs2⟩ := ih (Nat.lt_succ_iff.mp hlt) d1
        exact ⟨d2, hs2.trans hs1⟩

end SATurday.ProofComplexity
