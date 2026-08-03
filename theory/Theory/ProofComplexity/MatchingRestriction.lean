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

Derivation transport, iterative shrink to a smaller PHP, and the final
contradiction assembly are deferred.

LOG: R1 matching restriction module (BP96 Theorem 2 / G7, partial)
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

end SATurday.ProofComplexity
