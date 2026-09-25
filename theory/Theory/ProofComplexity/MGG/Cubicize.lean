import Theory.ProofComplexity.MGG.Factor2Inv4
import Mathlib.Tactic

/-!
# Cycle cubicization of the factor-2 MGG graph (R2 Block A item 6)

Each vertex of `mggF2Graph` is replaced by an 8-cycle on the eight factor-2
ports. Port `s` is joined to port `mggF2Rev s` of the neighboring cell.
Inverse pairs are not cycle-adjacent, so a base loop becomes a chord and every
vertex has degree 3.

`HasExpansionInv` degrades from `mggInvK = 4` by the cloud size 8. Proper
subsets of the 8-cycle obey `card ≤ 4 * cycleBoundary` (7 vertices against 2
edges). Lost base edges are charged to in-ports of partial clouds. The resulting
constant is `mggF2CubK = 164`. Inverse constant 2 is false for this
construction: a full-cloud lift multiplies a positive base ratio by 8.

LOG: R2 Block A cycle cubicization, degree 3, connectivity, Inv 164
-/

namespace SATurday.ProofComplexity

open Classical
open Finset

/-! ## Locked cubic Inv constant

`164 = 8 * 4 + 33 * 4`, from cloud size 8, base `mggInvK = 4`, and the
cycle inequality `card ≤ 4 * boundary` on proper nonempty port sets.
`1968` is the least order at which `tseitinInvWidthFloor n 164 > 3`. -/

def mggF2CubK : ℕ := 164

def mggF2CubFloor : ℕ := 1968

/-! ## Port combinatorics -/

def mggF2Rev (s : Fin 8) : Fin 8 :=
  ⟨s.val ^^^ 1, by
    have hs : s.val < 8 := s.isLt
    interval_cases s.val <;> decide⟩

/-- Cycle `0 → 2 → 4 → 6 → 1 → 3 → 5 → 7 → 0`. -/
def mggF2CycNext (p : Fin 8) : Fin 8 :=
  ⟨match p.val with
    | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 5 | 4 => 6 | 5 => 7 | 6 => 1 | _ => 0, by
    have hp : p.val < 8 := p.isLt
    interval_cases p.val <;> decide⟩

def mggF2CycPrev (p : Fin 8) : Fin 8 :=
  ⟨match p.val with
    | 0 => 7 | 1 => 6 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 3 | 6 => 4 | _ => 5, by
    have hp : p.val < 8 := p.isLt
    interval_cases p.val <;> decide⟩

theorem mggF2Rev_ne : ∀ p : Fin 8, mggF2Rev p ≠ p := by decide
theorem mggF2Rev_rev : ∀ p : Fin 8, mggF2Rev (mggF2Rev p) = p := by decide
theorem mggF2Rev_ne_cycNext : ∀ p : Fin 8, mggF2Rev p ≠ mggF2CycNext p := by decide
theorem mggF2Rev_ne_cycPrev : ∀ p : Fin 8, mggF2Rev p ≠ mggF2CycPrev p := by decide
theorem mggF2CycNext_ne : ∀ p : Fin 8, mggF2CycNext p ≠ p := by decide
theorem mggF2CycPrev_ne : ∀ p : Fin 8, mggF2CycPrev p ≠ p := by decide
theorem mggF2CycNext_ne_prev : ∀ p : Fin 8, mggF2CycNext p ≠ mggF2CycPrev p := by decide
theorem mggF2CycPrev_next : ∀ p : Fin 8, mggF2CycPrev (mggF2CycNext p) = p := by decide
theorem mggF2CycNext_prev : ∀ p : Fin 8, mggF2CycNext (mggF2CycPrev p) = p := by decide
theorem mggF2CycNext_sq_ne : ∀ p : Fin 8, mggF2CycNext (mggF2CycNext p) ≠ p := by decide

theorem mggF2CycNext_orbit :
    ∀ p q : Fin 8, ∃ k : Fin 8, mggF2CycNext^[k.val] p = q := by
  decide

/-- Forward cycle steps that enter or leave `S`. Bool inequality keeps `decide` on. -/
def mggF2CycBoundary (S : Finset (Fin 8)) : Finset (Fin 8) :=
  (univ : Finset (Fin 8)).filter fun p =>
    decide (p ∈ S) != decide (mggF2CycNext p ∈ S)

theorem mggF2CycNext_iter8 : ∀ p : Fin 8, mggF2CycNext^[8] p = p := by
  decide

theorem mggF2CycBoundary_mem_iff (S : Finset (Fin 8)) (p : Fin 8) :
    p ∈ mggF2CycBoundary S ↔ (p ∈ S) ≠ (mggF2CycNext p ∈ S) := by
  simp only [mggF2CycBoundary, mem_filter, mem_univ, true_and]
  by_cases h1 : p ∈ S <;> by_cases h2 : mggF2CycNext p ∈ S <;> simp [h1, h2] 

/-! ## Encoding -/

def mggF2CubMk {m : ℕ} (v : Fin (m * m)) (p : Fin 8) : Fin (m * m * 8) :=
  ⟨v.val * 8 + p.val, by
    have hv : v.val < m * m := v.isLt
    have hp : p.val < 8 := p.isLt
    calc
      v.val * 8 + p.val < v.val * 8 + 8 := Nat.add_lt_add_left hp _
      _ = (v.val + 1) * 8 := by rw [Nat.succ_mul]
      _ ≤ (m * m) * 8 := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hv)⟩

def mggF2CubV {m : ℕ} (i : Fin (m * m * 8)) : Fin (m * m) :=
  ⟨i.val / 8, by
    have h : i.val < 8 * (m * m) := by
      calc
        i.val < (m * m) * 8 := i.isLt
        _ = 8 * (m * m) := Nat.mul_comm _ _
    exact Nat.div_lt_of_lt_mul h⟩

def mggF2CubP {m : ℕ} (i : Fin (m * m * 8)) : Fin 8 :=
  ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩

theorem mggF2CubMk_v {m : ℕ} (v : Fin (m * m)) (p : Fin 8) :
    mggF2CubV (mggF2CubMk v p) = v := by
  apply Fin.ext
  simp only [mggF2CubV, mggF2CubMk]
  rw [Nat.mul_comm (v.val) 8, Nat.mul_add_div (by decide : 0 < 8), Nat.div_eq_of_lt p.isLt]
  simp

theorem mggF2CubMk_p {m : ℕ} (v : Fin (m * m)) (p : Fin 8) :
    mggF2CubP (mggF2CubMk v p) = p := by
  apply Fin.ext
  simp only [mggF2CubP, mggF2CubMk]
  rw [Nat.mul_comm (v.val) 8, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt p.isLt

theorem mggF2CubMk_ext {m : ℕ} (i : Fin (m * m * 8)) :
    mggF2CubMk (mggF2CubV i) (mggF2CubP i) = i := by
  apply Fin.ext
  simp only [mggF2CubMk, mggF2CubV, mggF2CubP]
  rw [Nat.mul_comm]
  exact Nat.div_add_mod i.val 8

theorem mggF2CubMk_injective {m : ℕ} {v v' : Fin (m * m)} {p p' : Fin 8}
    (h : mggF2CubMk v p = mggF2CubMk v' p') : v = v' ∧ p = p' :=
  ⟨by simpa [mggF2CubMk_v] using congrArg mggF2CubV h,
    by simpa [mggF2CubMk_p] using congrArg mggF2CubP h⟩

/-! ## Generator inverse -/

def mggF2Step {m : ℕ} [NeZero m] (s : Fin 8) (xy : Fin m × Fin m) : Fin m × Fin m :=
  let x := xy.1
  let y := xy.2
  if s.val = 0 then (x + y + y, y)
  else if s.val = 1 then (x - y - y, y)
  else if s.val = 2 then (x, y + x + x)
  else if s.val = 3 then (x, y - x - x)
  else if s.val = 4 then (x + y + y + 1, y)
  else if s.val = 5 then (x - y - y - 1, y)
  else if s.val = 6 then (x, y + x + x + 1)
  else (x, y - x - x - 1)

theorem mggF2Neighbor_eq_step {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) (s : Fin 8) :
    haveI : NeZero m := ⟨ne_of_gt hm⟩
    mggF2Neighbor hm v s = mggEncode hm (mggF2Step s (mggDecode hm v)) := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  fin_cases s <;> rfl

theorem mggF2Step_rev {m : ℕ} [NeZero m] (s : Fin 8) (xy : Fin m × Fin m) :
    mggF2Step (mggF2Rev s) (mggF2Step s xy) = xy := by
  rcases xy with ⟨x, y⟩
  fin_cases s <;>
    simp [mggF2Step, mggF2Rev, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] <;>
    abel

theorem mggF2Neighbor_rev_left {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) (s : Fin 8) :
    mggF2Neighbor hm (mggF2Neighbor hm v s) (mggF2Rev s) = v := by
  letI : NeZero m := ⟨ne_of_gt hm⟩
  rw [mggF2Neighbor_eq_step, mggF2Neighbor_eq_step, mggDecode_encode, mggF2Step_rev,
    mggEncode_decode]

theorem mggF2_exists_label_of_adj {m : ℕ} (hm : 0 < m) {v w : Fin (m * m)}
    (h : (mggF2Graph m hm).Adj v w) :
    ∃ s : Fin 8, mggF2Neighbor hm v s = w := by
  obtain ⟨e, heG, hends⟩ := h
  simp only [mggF2Graph, mem_biUnion, mem_univ, true_and] at heG
  obtain ⟨v0, s, hs⟩ := heG
  have heOpt : mggF2EdgeOf hm v0 s = some e := by
    cases hopt : mggF2EdgeOf hm v0 s with
    | none => simp [hopt] at hs
    | some e' =>
      have hee' : e = e' := by simpa [hopt] using hs
      simpa [hee'] using hopt
  have hne0 : mggF2Neighbor hm v0 s ≠ v0 := by
    intro hloop
    simp [mggF2EdgeOf, hloop] at heOpt
  obtain ⟨e2, he2, hends2⟩ := mggF2EdgeOf_eq_some_of_ne hm v0 s hne0
  have hee : e = e2 := by
    have hsome : some e = some e2 := by rw [← heOpt, he2]
    exact Option.some_injective _ hsome
  subst hee
  rcases hends with ⟨hvE, hwE⟩ | ⟨hvE, hwE⟩
  · rcases hends2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hv0 : v0 = v := by rw [← hvE, h1]
      subst hv0
      exact ⟨s, by rw [← hwE, h2]⟩
    · have hv0 : v0 = w := by rw [← hwE, h2]
      have hvn : mggF2Neighbor hm v0 s = v := by rw [← hvE, h1]
      refine ⟨mggF2Rev s, ?_⟩
      rw [← hvn, mggF2Neighbor_rev_left hm v0 s]
      exact hv0
  · rcases hends2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hv0 : v0 = w := by rw [← hvE, h1]
      have hvn : mggF2Neighbor hm v0 s = v := by rw [← hwE, h2]
      refine ⟨mggF2Rev s, ?_⟩
      rw [← hvn, mggF2Neighbor_rev_left hm v0 s]
      exact hv0
    · have hv0 : v0 = v := by rw [← hwE, h2]
      subst hv0
      exact ⟨s, by rw [← hvE, h1]⟩

theorem mggF2CycNext_iter_ne :
    ∀ (d : Fin 8) (q : Fin 8), d ≠ 0 → mggF2CycNext^[d.val] q ≠ q := by
  decide

/-! ## Cycle isoperimetry

A proper nonempty subset of the 8-cycle has at least two boundary steps
(leave `S`, then re-enter before the period), hence `card ≤ 7 ≤ 4 * boundary`. -/

theorem mggF2CycBoundary_card_ge_two (S : Finset (Fin 8))
    (hne : S.Nonempty) (hnu : S ≠ univ) :
    2 ≤ (mggF2CycBoundary S).card := by
  obtain ⟨p, hp⟩ := hne
  have hnotall : ∃ j : Fin 8, mggF2CycNext^[j.val] p ∉ S := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hnu
    ext q
    refine ⟨fun _ => mem_univ _, fun _ => ?_⟩
    obtain ⟨j, hj⟩ := mggF2CycNext_orbit p q
    simpa [hj] using hall j
  have hex : ∃ j, j < 8 ∧ mggF2CycNext^[j] p ∉ S := by
    obtain ⟨j, hj⟩ := hnotall
    exact ⟨j.val, j.isLt, by simpa using hj⟩
  classical
  let k := Nat.find hex
  have hkSpec := Nat.find_spec hex
  have hklt : k < 8 := hkSpec.1
  have hkout : mggF2CycNext^[k] p ∉ S := hkSpec.2
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := by omega
    apply hkout
    simpa [hkzero] using hp
  have hprevIn : mggF2CycNext^[k - 1] p ∈ S := by
    by_contra hout
    exact Nat.find_min hex (show k - 1 < k by omega) ⟨by omega, hout⟩
  have h8in : mggF2CycNext^[8] p ∈ S := by
    simpa [mggF2CycNext_iter8 p] using hp
  have hex2 : ∃ j, k < j ∧ mggF2CycNext^[j] p ∈ S := ⟨8, by omega, h8in⟩
  let k2 := Nat.find hex2
  have hk2gt : k < k2 := (Nat.find_spec hex2).1
  have hk2in : mggF2CycNext^[k2] p ∈ S := (Nat.find_spec hex2).2
  have hk2le : k2 ≤ 8 := Nat.find_le (⟨by omega, h8in⟩ : k < 8 ∧ mggF2CycNext^[8] p ∈ S)
  have hpreOut : mggF2CycNext^[k2 - 1] p ∉ S := by
    by_cases heq : k2 - 1 = k
    · simpa [heq] using hkout
    · have hmin := Nat.find_min hex2 (show k2 - 1 < k2 by omega)
      exact fun hin => hmin ⟨by omega, hin⟩
  have hstep : ∀ n, mggF2CycNext^[n + 1] p = mggF2CycNext (mggF2CycNext^[n] p) := by
    intro n
    exact Function.iterate_succ_apply' mggF2CycNext n p
  let a : Fin 8 := mggF2CycNext^[k - 1] p
  let b : Fin 8 := mggF2CycNext^[k2 - 1] p
  have hnexta : mggF2CycNext a = mggF2CycNext^[k] p := by
    have hk : k - 1 + 1 = k := by omega
    have hs := hstep (k - 1)
    rw [hk] at hs
    simpa [a] using hs.symm
  have hnextb : mggF2CycNext b = mggF2CycNext^[k2] p := by
    have hk : k2 - 1 + 1 = k2 := by omega
    have hs := hstep (k2 - 1)
    rw [hk] at hs
    simpa [b] using hs.symm
  have haB : a ∈ mggF2CycBoundary S := by
    rw [mggF2CycBoundary_mem_iff, hnexta]
    simp [a, hprevIn, hkout]
  have hbB : b ∈ mggF2CycBoundary S := by
    rw [mggF2CycBoundary_mem_iff, hnextb]
    simp [b, hpreOut, hk2in]
  have hne : a ≠ b := by
    intro hab
    have hdiff : (k2 - 1) - (k - 1) ≠ 0 := by omega
    have hpos : 0 < (k2 - 1) - (k - 1) := by omega
    have hlt : (k2 - 1) - (k - 1) < 8 := by omega
    let d : Fin 8 := ⟨(k2 - 1) - (k - 1), hlt⟩
    have hd0 : d ≠ 0 := by
      intro hd
      have : d.val = 0 := by simpa using congrArg Fin.val hd
      simp [d] at this
      omega
    have hper := mggF2CycNext_iter_ne d a hd0
    have hadd : mggF2CycNext^[d.val] a = b := by
      have hsum : d.val + (k - 1) = k2 - 1 := by
        simp only [d]
        omega
      calc
        mggF2CycNext^[d.val] a
            = mggF2CycNext^[d.val] (mggF2CycNext^[k - 1] p) := by simp [a]
          _ = mggF2CycNext^[d.val + (k - 1)] p :=
              (Function.iterate_add_apply mggF2CycNext d.val (k - 1) p).symm
          _ = mggF2CycNext^[k2 - 1] p := by rw [hsum]
          _ = b := by simp [b]
    exact hper (hab.symm ▸ hadd)
  have hsub : ({a, b} : Finset (Fin 8)) ⊆ mggF2CycBoundary S := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact haB
    · exact hbB
  have hcard : ({a, b} : Finset (Fin 8)).card = 2 := by
    rw [card_insert_of_notMem, card_singleton]
    simpa using hne
  simpa [hcard] using card_le_card hsub

theorem mggF2Cyc_card_le_four_boundary (S : Finset (Fin 8))
    (hne : S.Nonempty) (hnu : S ≠ univ) :
    S.card ≤ 4 * (mggF2CycBoundary S).card := by
  have htwo := mggF2CycBoundary_card_ge_two S hne hnu
  have hcard : S.card ≤ 7 := by
    have hle : S.card ≤ 8 := by simpa using card_le_univ S
    have hne8 : S.card ≠ 8 := by
      intro h8
      apply hnu
      exact eq_of_subset_of_card_le (subset_univ S) (by simp [h8])
    omega
  have hmul : 8 ≤ 4 * (mggF2CycBoundary S).card := by
    have : 4 * 2 ≤ 4 * (mggF2CycBoundary S).card := Nat.mul_le_mul_left 4 htwo
    omega
  omega

/-! ## Cubic graph -/

def mggF2CubEdge {n : ℕ} (a b : Fin n) (h : a ≠ b) : FinEdge n :=
  if hlt : a.val < b.val then ⟨(a, b), hlt⟩
  else ⟨(b, a), by
    change b < a
    exact Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt)
      (fun heq => h (Fin.ext heq.symm))⟩

theorem mggF2CubEdge_ends {n : ℕ} (a b : Fin n) (h : a ≠ b) :
    ((mggF2CubEdge a b h).val.1 = a ∧ (mggF2CubEdge a b h).val.2 = b) ∨
      ((mggF2CubEdge a b h).val.1 = b ∧ (mggF2CubEdge a b h).val.2 = a) := by
  unfold mggF2CubEdge
  by_cases hlt : a.val < b.val <;> simp [hlt]

theorem mggF2CubEdge_eq_of_ends {n : ℕ} (e : FinEdge n) (a b : Fin n) (hab : a ≠ b)
    (he : (e.val.1 = a ∧ e.val.2 = b) ∨ (e.val.1 = b ∧ e.val.2 = a)) :
    e = mggF2CubEdge a b hab := by
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hlt : a.val < b.val := by
      rw [← h1, ← h2]
      exact e.property
    apply Subtype.ext
    simp only [mggF2CubEdge, hlt]
    exact Prod.ext h1 h2
  · have hlt : b.val < a.val := by
      rw [← h1, ← h2]
      exact e.property
    have hnot : ¬ a.val < b.val := Nat.not_lt.mpr (Nat.le_of_lt hlt)
    apply Subtype.ext
    simp only [mggF2CubEdge, hnot]
    exact Prod.ext h1 h2

def mggF2CubNext {m : ℕ} (i : Fin (m * m * 8)) : Fin (m * m * 8) :=
  mggF2CubMk (mggF2CubV i) (mggF2CycNext (mggF2CubP i))

def mggF2CubPrev {m : ℕ} (i : Fin (m * m * 8)) : Fin (m * m * 8) :=
  mggF2CubMk (mggF2CubV i) (mggF2CycPrev (mggF2CubP i))

def mggF2CubExt {m : ℕ} (hm : 0 < m) (i : Fin (m * m * 8)) : Fin (m * m * 8) :=
  mggF2CubMk (mggF2Neighbor hm (mggF2CubV i) (mggF2CubP i)) (mggF2Rev (mggF2CubP i))

theorem mggF2CubNext_ne {m : ℕ} (i : Fin (m * m * 8)) : mggF2CubNext i ≠ i := by
  intro h
  have hp := congrArg mggF2CubP h
  exact mggF2CycNext_ne _ (by simpa [mggF2CubNext, mggF2CubMk_p] using hp)

theorem mggF2CubPrev_ne {m : ℕ} (i : Fin (m * m * 8)) : mggF2CubPrev i ≠ i := by
  intro h
  have hp := congrArg mggF2CubP h
  exact mggF2CycPrev_ne _ (by simpa [mggF2CubPrev, mggF2CubMk_p] using hp)

theorem mggF2CubNext_ne_prev {m : ℕ} (i : Fin (m * m * 8)) :
    mggF2CubNext i ≠ mggF2CubPrev i := by
  intro h
  exact mggF2CycNext_ne_prev _ (mggF2CubMk_injective
    (by simpa [mggF2CubNext, mggF2CubPrev, mggF2CubMk_v, mggF2CubMk_p] using h)).2

theorem mggF2CubExt_ne {m : ℕ} (hm : 0 < m) (i : Fin (m * m * 8)) :
    mggF2CubExt hm i ≠ i := by
  intro h
  have hp := congrArg mggF2CubP h
  exact mggF2Rev_ne _ (by simpa [mggF2CubExt, mggF2CubMk_p] using hp)

theorem mggF2CubExt_ne_next {m : ℕ} (hm : 0 < m) (i : Fin (m * m * 8)) :
    mggF2CubExt hm i ≠ mggF2CubNext i := by
  intro h
  exact mggF2Rev_ne_cycNext _ (mggF2CubMk_injective
    (by simpa [mggF2CubExt, mggF2CubNext, mggF2CubMk_v, mggF2CubMk_p] using h)).2

theorem mggF2CubExt_ne_prev {m : ℕ} (hm : 0 < m) (i : Fin (m * m * 8)) :
    mggF2CubExt hm i ≠ mggF2CubPrev i := by
  intro h
  exact mggF2Rev_ne_cycPrev _ (mggF2CubMk_injective
    (by simpa [mggF2CubExt, mggF2CubPrev, mggF2CubMk_v, mggF2CubMk_p] using h)).2

def mggF2CubCycleEdge {m : ℕ} (v : Fin (m * m)) (p : Fin 8) : FinEdge (m * m * 8) :=
  mggF2CubEdge (mggF2CubMk v p) (mggF2CubMk v (mggF2CycNext p))
    (by
      intro h
      exact mggF2CycNext_ne p (mggF2CubMk_injective h).2.symm)

def mggF2CubExtEdge {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) (s : Fin 8) :
    FinEdge (m * m * 8) :=
  mggF2CubEdge (mggF2CubMk v s) (mggF2CubMk (mggF2Neighbor hm v s) (mggF2Rev s))
    (by
      intro h
      exact mggF2Rev_ne s (mggF2CubMk_injective h).2.symm)

def mggF2CubCycleEdges {m : ℕ} (_hm : 0 < m) : Finset (FinEdge (m * m * 8)) :=
  (univ : Finset (Fin (m * m))).biUnion fun v =>
    (univ : Finset (Fin 8)).image fun p => mggF2CubCycleEdge v p

def mggF2CubExtEdges {m : ℕ} (hm : 0 < m) : Finset (FinEdge (m * m * 8)) :=
  (univ : Finset (Fin (m * m))).biUnion fun v =>
    (univ : Finset (Fin 8)).image fun s => mggF2CubExtEdge hm v s

def mggF2CubGraph {m : ℕ} (hm : 0 < m) : FinGraph (m * m * 8) :=
  mggF2CubCycleEdges hm ∪ mggF2CubExtEdges hm

theorem mem_mggF2CubCycleEdges {m : ℕ} (hm : 0 < m) {e : FinEdge (m * m * 8)} :
    e ∈ mggF2CubCycleEdges hm ↔ ∃ v p, e = mggF2CubCycleEdge v p := by
  simp only [mggF2CubCycleEdges, mem_biUnion, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨v, p, h⟩
    exact ⟨v, p, h.symm⟩
  · rintro ⟨v, p, h⟩
    exact ⟨v, p, h.symm⟩

theorem mem_mggF2CubExtEdges {m : ℕ} (hm : 0 < m) {e : FinEdge (m * m * 8)} :
    e ∈ mggF2CubExtEdges hm ↔ ∃ v s, e = mggF2CubExtEdge hm v s := by
  simp only [mggF2CubExtEdges, mem_biUnion, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨v, s, h⟩
    exact ⟨v, s, h.symm⟩
  · rintro ⟨v, s, h⟩
    exact ⟨v, s, h.symm⟩

theorem mem_mggF2CubGraph {m : ℕ} (hm : 0 < m) {e : FinEdge (m * m * 8)} :
    e ∈ mggF2CubGraph hm ↔
      (∃ v p, e = mggF2CubCycleEdge v p) ∨ (∃ v s, e = mggF2CubExtEdge hm v s) := by
  simp only [mggF2CubGraph, mem_union, mem_mggF2CubCycleEdges, mem_mggF2CubExtEdges]

theorem mggF2Cub_adj_next {m : ℕ} (hm : 0 < m) (i : Fin (m * m * 8)) :
    (mggF2CubGraph hm).Adj i (mggF2CubNext i) := by
  let a := mggF2CubMk (mggF2CubV i) (mggF2CubP i)
  let b := mggF2CubMk (mggF2CubV i) (mggF2CycNext (mggF2CubP i))
  have hab : a ≠ b := by
    intro h
    exact mggF2CycNext_ne _ (mggF2CubMk_injective h).2.symm
  have ha : a = i := mggF2CubMk_ext i
  have hb : b = mggF2CubNext i := by simp [b, mggF2CubNext]
  let e := mggF2CubCycleEdge (mggF2CubV i) (mggF2CubP i)
  refine ⟨e, mem_union_left _ ((mem_mggF2CubCycleEdges hm).mpr ⟨_, _, rfl⟩), ?_⟩
  have he : e = mggF2CubEdge a b hab := by
    apply mggF2CubEdge_eq_of_ends
    simpa [e, a, b, mggF2CubCycleEdge] using mggF2CubEdge_ends a b hab
  rcases mggF2CubEdge_ends a b hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← he] at h1 h2
    exact Or.inl ⟨h1.trans ha, h2.trans hb⟩
  · rw [← he] at h1 h2
    exact Or.inr ⟨h1.trans hb, h2.trans ha⟩

theorem mggF2Cub_adj_ext {m : ℕ} (hm : 0 < m) (i : Fin (m * m * 8)) :
    (mggF2CubGraph hm).Adj i (mggF2CubExt hm i) := by
  let a := mggF2CubMk (mggF2CubV i) (mggF2CubP i)
  let b := mggF2CubMk (mggF2Neighbor hm (mggF2CubV i) (mggF2CubP i)) (mggF2Rev (mggF2CubP i))
  have hab : a ≠ b := by
    intro h
    exact mggF2Rev_ne _ (mggF2CubMk_injective h).2.symm
  have ha : a = i := mggF2CubMk_ext i
  have hb : b = mggF2CubExt hm i := by simp [b, mggF2CubExt]
  let e := mggF2CubExtEdge hm (mggF2CubV i) (mggF2CubP i)
  refine ⟨e, mem_union_right _ ((mem_mggF2CubExtEdges hm).mpr ⟨_, _, rfl⟩), ?_⟩
  have he : e = mggF2CubEdge a b hab := by
    apply mggF2CubEdge_eq_of_ends
    simpa [e, a, b, mggF2CubExtEdge] using mggF2CubEdge_ends a b hab
  rcases mggF2CubEdge_ends a b hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← he] at h1 h2
    exact Or.inl ⟨h1.trans ha, h2.trans hb⟩
  · rw [← he] at h1 h2
    exact Or.inr ⟨h1.trans hb, h2.trans ha⟩

theorem mggF2Cub_adj_symm {m : ℕ} (hm : 0 < m) {u v : Fin (m * m * 8)}
    (h : (mggF2CubGraph hm).Adj u v) : (mggF2CubGraph hm).Adj v u := by
  obtain ⟨e, he, hends⟩ := h
  refine ⟨e, he, ?_⟩
  rcases hends with hends | hends
  · exact Or.inr hends
  · exact Or.inl hends

theorem mggF2Cub_adj_prev {m : ℕ} (hm : 0 < m) (i : Fin (m * m * 8)) :
    (mggF2CubGraph hm).Adj i (mggF2CubPrev i) := by
  have hstep := mggF2Cub_adj_next hm (mggF2CubPrev i)
  have hback : mggF2CubNext (mggF2CubPrev i) = i := by
    simp [mggF2CubNext, mggF2CubPrev, mggF2CubMk_v, mggF2CubMk_p, mggF2CycNext_prev,
      mggF2CubMk_ext]
  rw [hback] at hstep
  exact mggF2Cub_adj_symm hm hstep

/-- Every neighbor in the cubic graph is the cycle successor, predecessor, or external port. -/
theorem mggF2Cub_adj_cases {m : ℕ} (hm : 0 < m) {i y : Fin (m * m * 8)}
    (h : (mggF2CubGraph hm).Adj i y) :
    y = mggF2CubNext i ∨ y = mggF2CubPrev i ∨ y = mggF2CubExt hm i := by
  obtain ⟨e, he, hends⟩ := h
  rcases (mem_mggF2CubGraph hm).mp he with ⟨v, p, rfl⟩ | ⟨v, s, rfl⟩
  · simp only [mggF2CubCycleEdge, mggF2CubEdge] at hends
    split_ifs at hends with hlt
    · rcases hends with ⟨hi, hy⟩ | ⟨hi, hy⟩
      · left
        simp [mggF2CubNext, ← hi, ← hy, mggF2CubMk_v, mggF2CubMk_p]
      · right; left
        simp [mggF2CubPrev, ← hi, ← hy, mggF2CubMk_v, mggF2CubMk_p, mggF2CycPrev_next]
    · rcases hends with ⟨hi, hy⟩ | ⟨hi, hy⟩
      · right; left
        simp [mggF2CubPrev, ← hi, ← hy, mggF2CubMk_v, mggF2CubMk_p, mggF2CycPrev_next]
      · left
        simp [mggF2CubNext, ← hi, ← hy, mggF2CubMk_v, mggF2CubMk_p]
  · simp only [mggF2CubExtEdge, mggF2CubEdge] at hends
    split_ifs at hends with hlt
    · rcases hends with ⟨hi, hy⟩ | ⟨hi, hy⟩
      · right; right
        simp [mggF2CubExt, ← hi, ← hy, mggF2CubMk_v, mggF2CubMk_p]
      · right; right
        simp [mggF2CubExt, ← hi, ← hy, mggF2CubMk_v, mggF2CubMk_p, mggF2Rev_rev,
          mggF2Neighbor_rev_left]
    · rcases hends with ⟨hi, hy⟩ | ⟨hi, hy⟩
      · right; right
        simp [mggF2CubExt, ← hi, ← hy, mggF2CubMk_v, mggF2CubMk_p, mggF2Rev_rev,
          mggF2Neighbor_rev_left]
      · right; right
        simp [mggF2CubExt, ← hi, ← hy, mggF2CubMk_v, mggF2CubMk_p]

theorem mggF2Cub_isRegular {m : ℕ} (hm : 0 < m) : IsRegular (mggF2CubGraph hm) 3 := by
  intro i
  let eN := mggF2CubEdge i (mggF2CubNext i) (Ne.symm (mggF2CubNext_ne i))
  let eP := mggF2CubEdge i (mggF2CubPrev i) (Ne.symm (mggF2CubPrev_ne i))
  let eE := mggF2CubEdge i (mggF2CubExt hm i) (Ne.symm (mggF2CubExt_ne hm i))
  have hNmem : eN ∈ incident (mggF2CubGraph hm) i := by
    refine (mem_incident_iff).mpr ⟨?_, ?_⟩
    · have hadj := mggF2Cub_adj_next hm i
      obtain ⟨e, he, hends⟩ := hadj
      have heq : e = eN := mggF2CubEdge_eq_of_ends e i (mggF2CubNext i) _
        (by simpa [eN] using hends)
      simpa [heq] using he
    · rcases mggF2CubEdge_ends i (mggF2CubNext i) _ with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1
      · exact Or.inr h2
  have hPmem : eP ∈ incident (mggF2CubGraph hm) i := by
    refine (mem_incident_iff).mpr ⟨?_, ?_⟩
    · have hadj := mggF2Cub_adj_prev hm i
      obtain ⟨e, he, hends⟩ := hadj
      have heq : e = eP := mggF2CubEdge_eq_of_ends e i (mggF2CubPrev i) _ hends
      simpa [heq] using he
    · rcases mggF2CubEdge_ends i (mggF2CubPrev i) _ with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1
      · exact Or.inr h2
  have hEmem : eE ∈ incident (mggF2CubGraph hm) i := by
    refine (mem_incident_iff).mpr ⟨?_, ?_⟩
    · have hadj := mggF2Cub_adj_ext hm i
      obtain ⟨e, he, hends⟩ := hadj
      have heq : e = eE := mggF2CubEdge_eq_of_ends e i (mggF2CubExt hm i) _ hends
      simpa [heq] using he
    · rcases mggF2CubEdge_ends i (mggF2CubExt hm i) _ with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1
      · exact Or.inr h2
  have hedge_other {a b : Fin (m * m * 8)} (ha : i ≠ a) (hb : i ≠ b)
      (h : mggF2CubEdge i a ha = mggF2CubEdge i b hb) : a = b := by
    have hv := congrArg Subtype.val h
    rcases mggF2CubEdge_ends i a ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;>
      rcases mggF2CubEdge_ends i b hb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
    · have : (i, a) = (i, b) :=
        (Prod.ext ha1.symm ha2.symm).trans (hv.trans (Prod.ext hb1.symm hb2.symm).symm)
      exact congrArg Prod.snd this
    · have : (i, a) = (b, i) :=
        (Prod.ext ha1.symm ha2.symm).trans (hv.trans (Prod.ext hb1.symm hb2.symm).symm)
      exact absurd (congrArg Prod.fst this) hb
    · have : (a, i) = (i, b) :=
        (Prod.ext ha1.symm ha2.symm).trans (hv.trans (Prod.ext hb1.symm hb2.symm).symm)
      exact absurd (congrArg Prod.fst this) ha.symm
    · have : (a, i) = (b, i) :=
        (Prod.ext ha1.symm ha2.symm).trans (hv.trans (Prod.ext hb1.symm hb2.symm).symm)
      exact congrArg Prod.fst this
  have hneNP : eN ≠ eP := fun h =>
    mggF2CubNext_ne_prev i (hedge_other (Ne.symm (mggF2CubNext_ne i))
      (Ne.symm (mggF2CubPrev_ne i)) h)
  have hneNE : eN ≠ eE := fun h =>
    mggF2CubExt_ne_next hm i (hedge_other (Ne.symm (mggF2CubExt_ne hm i))
      (Ne.symm (mggF2CubNext_ne i)) h.symm)
  have hnePE : eP ≠ eE := fun h =>
    mggF2CubExt_ne_prev hm i (hedge_other (Ne.symm (mggF2CubExt_ne hm i))
      (Ne.symm (mggF2CubPrev_ne i)) h.symm)
  have hsub : incident (mggF2CubGraph hm) i ⊆ {eN, eP, eE} := by
    intro e he
    obtain ⟨heG, htouch⟩ := (mem_incident_iff).mp he
    rcases htouch with h1 | h2
    · have hy := mggF2Cub_adj_cases hm ⟨e, heG, Or.inl ⟨h1, rfl⟩⟩
      have hi_ne : i ≠ e.val.2 := by
        intro hiy
        exact e.ne_endpoints (h1.trans hiy)
      rcases hy with hY | hY | hY
      · exact mem_insert.mpr (Or.inl (by
          simpa [eN] using
            mggF2CubEdge_eq_of_ends e i (mggF2CubNext i) (Ne.symm (mggF2CubNext_ne i))
              (Or.inl ⟨h1, hY⟩)))
      · exact mem_insert_of_mem (mem_insert.mpr (Or.inl (by
          simpa [eP] using
            mggF2CubEdge_eq_of_ends e i (mggF2CubPrev i) (Ne.symm (mggF2CubPrev_ne i))
              (Or.inl ⟨h1, hY⟩))))
      · exact mem_insert_of_mem (mem_insert_of_mem (mem_singleton.mpr (by
          simpa [eE] using
            mggF2CubEdge_eq_of_ends e i (mggF2CubExt hm i) (Ne.symm (mggF2CubExt_ne hm i))
              (Or.inl ⟨h1, hY⟩))))
    · have hy := mggF2Cub_adj_cases hm ⟨e, heG, Or.inr ⟨rfl, h2⟩⟩
      have hi_ne : i ≠ e.val.1 := by
        intro hiy
        exact e.ne_endpoints (hiy.symm.trans h2.symm)
      rcases hy with hY | hY | hY
      · exact mem_insert.mpr (Or.inl (by
          simpa [eN] using
            mggF2CubEdge_eq_of_ends e i (mggF2CubNext i) (Ne.symm (mggF2CubNext_ne i))
              (Or.inr ⟨hY, h2⟩)))
      · exact mem_insert_of_mem (mem_insert.mpr (Or.inl (by
          simpa [eP] using
            mggF2CubEdge_eq_of_ends e i (mggF2CubPrev i) (Ne.symm (mggF2CubPrev_ne i))
              (Or.inr ⟨hY, h2⟩))))
      · exact mem_insert_of_mem (mem_insert_of_mem (mem_singleton.mpr (by
          simpa [eE] using
            mggF2CubEdge_eq_of_ends e i (mggF2CubExt hm i) (Ne.symm (mggF2CubExt_ne hm i))
              (Or.inr ⟨hY, h2⟩))))
  have hsup : {eN, eP, eE} ⊆ incident (mggF2CubGraph hm) i := by
    intro e he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact hNmem
    · exact hPmem
    · exact hEmem
  have hcard : ({eN, eP, eE} : Finset (FinEdge (m * m * 8))).card = 3 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · simpa [eP, eE] using hnePE
    · simp [hneNP, hneNE]
  have heq : incident (mggF2CubGraph hm) i = {eN, eP, eE} :=
    subset_antisymm hsub hsup
  simp [degree, heq, hcard]

/-! ## Connectivity -/

theorem mggF2CubNext_mk {m : ℕ} (v : Fin (m * m)) (p : Fin 8) :
    mggF2CubNext (mggF2CubMk v p) = mggF2CubMk v (mggF2CycNext p) := by
  simp [mggF2CubNext, mggF2CubMk_v, mggF2CubMk_p]

theorem mggF2Cub_reachable_pow {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) (p : Fin 8)
    (k : ℕ) :
    (mggF2CubGraph hm).Reachable (mggF2CubMk v p)
      (mggF2CubMk v (mggF2CycNext^[k] p)) := by
  induction k with
  | zero =>
    rw [Function.iterate_zero]
    exact Relation.ReflTransGen.refl
  | succ k ih =>
    apply Relation.ReflTransGen.tail ih
    have hnext : mggF2CubNext (mggF2CubMk v (mggF2CycNext^[k] p)) =
        mggF2CubMk v (mggF2CycNext^[k + 1] p) := by
      simp [mggF2CubNext_mk, Function.iterate_succ_apply']
    rw [← hnext]
    exact mggF2Cub_adj_next hm _

theorem mggF2Cub_reachable_same {m : ℕ} (hm : 0 < m) (v : Fin (m * m))
    (p q : Fin 8) :
    (mggF2CubGraph hm).Reachable (mggF2CubMk v p) (mggF2CubMk v q) := by
  obtain ⟨k, hk⟩ := mggF2CycNext_orbit p q
  simpa [hk] using mggF2Cub_reachable_pow hm v p k.val

theorem mggF2Cub_reachable_base {m : ℕ} (hm : 0 < m) {v w : Fin (m * m)}
    (h : (mggF2Graph m hm).Reachable v w) (p q : Fin 8) :
    (mggF2CubGraph hm).Reachable (mggF2CubMk v p) (mggF2CubMk w q) := by
  exact Relation.ReflTransGen.head_induction_on
    (motive := fun a _ => ∀ r : Fin 8,
      (mggF2CubGraph hm).Reachable (mggF2CubMk a r) (mggF2CubMk w q))
    h
    (fun r => mggF2Cub_reachable_same hm w r q)
    (fun {a c} hadj _hrest ih r => by
      obtain ⟨s, hs⟩ := mggF2_exists_label_of_adj hm hadj
      exact ((mggF2Cub_reachable_same hm a r s).trans
          (Relation.ReflTransGen.single (by
            have := mggF2Cub_adj_ext hm (mggF2CubMk a s)
            simpa [mggF2CubExt, mggF2CubMk_v, mggF2CubMk_p, hs] using this))).trans
        (ih (mggF2Rev s)))
    p

theorem mggF2Cub_isConnected {m : ℕ} (hm : 0 < m) :
    (mggF2CubGraph hm).IsConnected := by
  intro a b
  simpa [mggF2CubMk_ext] using
    mggF2Cub_reachable_base hm
      (mggF2Graph_isConnected hm (mggF2CubV a) (mggF2CubV b))
      (mggF2CubP a) (mggF2CubP b)

/-! ## Cloud decomposition -/

def mggF2CubPorts {m : ℕ} (T : Finset (Fin (m * m * 8))) (v : Fin (m * m)) :
    Finset (Fin 8) :=
  (univ : Finset (Fin 8)).filter fun p => mggF2CubMk v p ∈ T

def mggF2CubCloudIn {m : ℕ} (T : Finset (Fin (m * m * 8))) (v : Fin (m * m)) :
    Finset (Fin (m * m * 8)) :=
  (mggF2CubPorts T v).image (mggF2CubMk v)

theorem mggF2Cub_card_eq_sum {m : ℕ} (T : Finset (Fin (m * m * 8))) :
    T.card = ∑ v : Fin (m * m), (mggF2CubPorts T v).card := by
  classical
  have hcover : T = (univ : Finset (Fin (m * m))).biUnion (mggF2CubCloudIn T) := by
    ext i
    simp only [mem_biUnion, mem_univ, true_and, mggF2CubCloudIn, mem_image,
      mggF2CubPorts, mem_filter]
    constructor
    · intro hi
      exact ⟨mggF2CubV i, mggF2CubP i, by simpa [mggF2CubMk_ext] using hi, mggF2CubMk_ext i⟩
    · rintro ⟨v, p, hp, rfl⟩
      exact hp
  have hdisj : ((univ : Finset (Fin (m * m))) : Set (Fin (m * m))).PairwiseDisjoint
      (mggF2CubCloudIn T) := by
    intro a _ b _ hne
    refine disjoint_left.mpr ?_
    intro i hi hj
    simp only [mggF2CubCloudIn, mem_image] at hi hj
    obtain ⟨p, _, rfl⟩ := hi
    obtain ⟨q, _, hq⟩ := hj
    exact hne (mggF2CubMk_injective hq).1.symm
  have hcard : T.card =
      ((univ : Finset (Fin (m * m))).biUnion (mggF2CubCloudIn T)).card :=
    congrArg Finset.card hcover
  rw [hcard, card_biUnion hdisj]
  refine sum_congr rfl fun v _ => ?_
  simpa [mggF2CubCloudIn] using
    (card_image_of_injective (mggF2CubPorts T v) fun p q h => (mggF2CubMk_injective h).2)

def mggF2CubFull {m : ℕ} (T : Finset (Fin (m * m * 8))) : Finset (Fin (m * m)) :=
  (univ : Finset (Fin (m * m))).filter fun v => mggF2CubPorts T v = univ

def mggF2CubPartial {m : ℕ} (T : Finset (Fin (m * m * 8))) : Finset (Fin (m * m)) :=
  (univ : Finset (Fin (m * m))).filter fun v =>
    (mggF2CubPorts T v).Nonempty ∧ mggF2CubPorts T v ≠ univ

theorem mggF2Cub_card_full_partial {m : ℕ} (T : Finset (Fin (m * m * 8))) :
    T.card = 8 * (mggF2CubFull T).card +
      ∑ v ∈ mggF2CubPartial T, (mggF2CubPorts T v).card := by
  have h8 : ((univ : Finset (Fin 8))).card = 8 := by simp [card_univ]
  rw [mggF2Cub_card_eq_sum]
  have hsplit := sum_filter_add_sum_filter_not (s := univ)
    (f := fun v : Fin (m * m) => (mggF2CubPorts T v).card)
    (p := fun v => mggF2CubPorts T v = univ)
  have hfull : ∑ v ∈ univ.filter (fun v => mggF2CubPorts T v = univ),
      (mggF2CubPorts T v).card = 8 * (mggF2CubFull T).card := by
    have hEq : mggF2CubFull T = univ.filter (fun v => mggF2CubPorts T v = univ) := rfl
    rw [← hEq]
    have hterm : ∑ v ∈ mggF2CubFull T, (mggF2CubPorts T v).card =
        ∑ v ∈ mggF2CubFull T, 8 := by
      refine sum_congr rfl fun v hv => ?_
      simp only [mggF2CubFull, mem_filter, mem_univ, true_and] at hv
      simp [hv, h8]
    rw [hterm, sum_const, smul_eq_mul, mul_comm]
  have hpart : ∑ v ∈ univ.filter (fun v => ¬ mggF2CubPorts T v = univ),
      (mggF2CubPorts T v).card =
      ∑ v ∈ mggF2CubPartial T, (mggF2CubPorts T v).card := by
    symm
    refine sum_subset ?hsub ?hzero
    · intro v hv
      simp only [mggF2CubPartial, mem_filter, mem_univ, true_and] at hv
      exact mem_filter.mpr ⟨mem_univ _, hv.2⟩
    · intro v hv hnot
      have hne : mggF2CubPorts T v ≠ univ := (mem_filter.mp hv).2
      have hempty : ¬ (mggF2CubPorts T v).Nonempty := by
        intro hN
        apply hnot
        exact mem_filter.mpr ⟨mem_univ _, hN, hne⟩
      simp [not_nonempty_iff_eq_empty.mp hempty]
  rw [← hsplit, hfull, hpart]

/-! ## Cycle cuts -/

def mggF2CubCycleCut {m : ℕ} (_hm : 0 < m) (T : Finset (Fin (m * m * 8))) :
    Finset (FinEdge (m * m * 8)) :=
  (univ : Finset (Fin (m * m))).biUnion fun v =>
    (mggF2CycBoundary (mggF2CubPorts T v)).image fun p => mggF2CubCycleEdge v p

theorem mggF2CubCycleEdge_ports {m : ℕ} (v : Fin (m * m)) (p : Fin 8) :
    ({mggF2CubP (mggF2CubCycleEdge v p).val.1,
      mggF2CubP (mggF2CubCycleEdge v p).val.2} : Finset (Fin 8)) =
      {p, mggF2CycNext p} ∧
    mggF2CubV (mggF2CubCycleEdge v p).val.1 = v ∧
    mggF2CubV (mggF2CubCycleEdge v p).val.2 = v := by
  unfold mggF2CubCycleEdge mggF2CubEdge
  by_cases hlt : (mggF2CubMk v p).val < (mggF2CubMk v (mggF2CycNext p)).val
  · simp [hlt, mggF2CubMk_v, mggF2CubMk_p]
  · rw [dif_neg hlt]
    simp only [mggF2CubMk_v, mggF2CubMk_p]
    refine ⟨?_, trivial, trivial⟩
    ext x
    simp [mem_insert, mem_singleton]
    tauto

theorem mggF2CycPair_eq : ∀ p q : Fin 8,
    ({p, mggF2CycNext p} : Finset (Fin 8)) = {q, mggF2CycNext q} → p = q := by
  decide

theorem mggF2CubCycleEdge_injective {m : ℕ} {v v' : Fin (m * m)} {p p' : Fin 8}
    (h : mggF2CubCycleEdge v p = mggF2CubCycleEdge v' p') : v = v' ∧ p = p' := by
  have hv := mggF2CubCycleEdge_ports v p
  have hv' := mggF2CubCycleEdge_ports v' p'
  have hV : v = v' := by
    have := congrArg (fun e : FinEdge (m * m * 8) => mggF2CubV e.val.1) h
    simpa [hv.2.1, hv'.2.1] using this
  refine ⟨hV, ?_⟩
  have hports := congrArg
    (fun e : FinEdge (m * m * 8) =>
      ({mggF2CubP e.val.1, mggF2CubP e.val.2} : Finset (Fin 8))) h
  have : ({p, mggF2CycNext p} : Finset (Fin 8)) = {p', mggF2CycNext p'} := by
    simpa [hv.1, hv'.1] using hports
  exact mggF2CycPair_eq p p' this

theorem mggF2CubCycleCut_card {m : ℕ} (hm : 0 < m) (T : Finset (Fin (m * m * 8))) :
    (mggF2CubCycleCut hm T).card =
      ∑ v : Fin (m * m), (mggF2CycBoundary (mggF2CubPorts T v)).card := by
  have hdisj : ((univ : Finset (Fin (m * m))) : Set (Fin (m * m))).PairwiseDisjoint
      (fun v => (mggF2CycBoundary (mggF2CubPorts T v)).image (mggF2CubCycleEdge v)) := by
    intro a _ b _ hne
    refine disjoint_left.mpr ?_
    intro e he hf
    simp only [mem_image] at he hf
    obtain ⟨p, _, rfl⟩ := he
    obtain ⟨q, _, hq⟩ := hf
    exact hne (mggF2CubCycleEdge_injective hq).1.symm
  rw [mggF2CubCycleCut, card_biUnion hdisj]
  refine sum_congr rfl fun v _ => ?_
  exact card_image_of_injective _ fun p q h => (mggF2CubCycleEdge_injective h).2

theorem mggF2CubCycleCut_subset_boundary {m : ℕ} (hm : 0 < m)
    (T : Finset (Fin (m * m * 8))) :
    mggF2CubCycleCut hm T ⊆ edgeBoundary (mggF2CubGraph hm) T := by
  intro e he
  simp only [mggF2CubCycleCut, mem_biUnion, mem_univ, true_and, mem_image] at he
  obtain ⟨v, p, hp, rfl⟩ := he
  rw [mggF2CycBoundary_mem_iff] at hp
  refine (mem_edgeBoundary_iff).mpr ⟨?_, ?_⟩
  · exact mem_union_left _ ((mem_mggF2CubCycleEdges hm).mpr ⟨v, p, rfl⟩)
  · have hends := mggF2CubCycleEdge_ports v p
    by_cases hin : mggF2CubMk v p ∈ T
    · have hout : mggF2CubMk v (mggF2CycNext p) ∉ T := by
        intro hmem
        exact hp (by simpa [mggF2CubPorts, hin, hmem] )
      -- endpoints are the two mks in either order
      unfold mggF2CubCycleEdge mggF2CubEdge
      by_cases hlt : (mggF2CubMk v p).val < (mggF2CubMk v (mggF2CycNext p)).val
      · simp [hlt, hin, hout]
      · simp [hlt, hin, hout]
    · have hother : mggF2CubMk v (mggF2CycNext p) ∈ T := by
        by_contra hnot
        apply hp
        simp [mggF2CubPorts, hin, hnot]
      unfold mggF2CubCycleEdge mggF2CubEdge
      by_cases hlt : (mggF2CubMk v p).val < (mggF2CubMk v (mggF2CycNext p)).val
      · simp [hlt, hin, hother]
      · simp [hlt, hin, hother]

theorem mggF2Cub_partial_le_boundary {m : ℕ} (hm : 0 < m)
    (T : Finset (Fin (m * m * 8))) :
    ∑ v ∈ mggF2CubPartial T, (mggF2CubPorts T v).card ≤
      4 * (edgeBoundary (mggF2CubGraph hm) T).card := by
  have hpt : ∀ v ∈ mggF2CubPartial T,
      (mggF2CubPorts T v).card ≤ 4 * (mggF2CycBoundary (mggF2CubPorts T v)).card := by
    intro v hv
    simp only [mggF2CubPartial, mem_filter, mem_univ, true_and] at hv
    exact mggF2Cyc_card_le_four_boundary _ hv.1 hv.2
  have hsum : ∑ v ∈ mggF2CubPartial T, (mggF2CubPorts T v).card ≤
      ∑ v ∈ mggF2CubPartial T, 4 * (mggF2CycBoundary (mggF2CubPorts T v)).card :=
    sum_le_sum hpt
  have hmul : ∑ v ∈ mggF2CubPartial T, 4 * (mggF2CycBoundary (mggF2CubPorts T v)).card =
      4 * ∑ v ∈ mggF2CubPartial T, (mggF2CycBoundary (mggF2CubPorts T v)).card := by
    simp [mul_sum]
  have hsub : ∑ v ∈ mggF2CubPartial T, (mggF2CycBoundary (mggF2CubPorts T v)).card ≤
      ∑ v : Fin (m * m), (mggF2CycBoundary (mggF2CubPorts T v)).card := by
    let f := fun v : Fin (m * m) => (mggF2CycBoundary (mggF2CubPorts T v)).card
    have hsplit := sum_filter_add_sum_filter_not (s := univ) (f := f)
      (p := fun v => v ∈ mggF2CubPartial T)
    have hf : univ.filter (fun v => v ∈ mggF2CubPartial T) = mggF2CubPartial T := by
      ext v
      simp [mggF2CubPartial, mem_filter]
    rw [hf] at hsplit
    have : ∑ v ∈ mggF2CubPartial T, f v ≤
        ∑ v ∈ mggF2CubPartial T, f v +
          ∑ v ∈ univ.filter (fun v => v ∉ mggF2CubPartial T), f v :=
      Nat.le_add_right _ _
    simpa [f, hsplit] using this
  have hcut : ∑ v : Fin (m * m), (mggF2CycBoundary (mggF2CubPorts T v)).card ≤
      (edgeBoundary (mggF2CubGraph hm) T).card := by
    rw [← mggF2CubCycleCut_card hm T]
    exact card_le_card (mggF2CubCycleCut_subset_boundary hm T)
  omega

/-! ## Base boundary lifts into the cubic cut -/

theorem mggF2Graph_proof_irrel {m : ℕ} (hm hm' : 0 < m) :
    mggF2Graph m hm = mggF2Graph m hm' :=
  congrArg (mggF2Graph m) (proof_irrel hm hm')

theorem mggF2CubExt_ext {m : ℕ} (hm : 0 < m) (i : Fin (m * m * 8)) :
    mggF2CubExt hm (mggF2CubExt hm i) = i := by
  simp [mggF2CubExt, mggF2CubMk_v, mggF2CubMk_p, mggF2Rev_rev,
    mggF2Neighbor_rev_left, mggF2CubMk_ext]

theorem mggF2CubExtEdge_orients {m : ℕ} (hm : 0 < m) (v : Fin (m * m)) (s : Fin 8) :
    ((mggF2CubExtEdge hm v s).val.1 = mggF2CubMk v s ∧
        (mggF2CubExtEdge hm v s).val.2 =
          mggF2CubMk (mggF2Neighbor hm v s) (mggF2Rev s)) ∨
      ((mggF2CubExtEdge hm v s).val.1 =
          mggF2CubMk (mggF2Neighbor hm v s) (mggF2Rev s) ∧
        (mggF2CubExtEdge hm v s).val.2 = mggF2CubMk v s) := by
  unfold mggF2CubExtEdge mggF2CubEdge
  by_cases hlt : (mggF2CubMk v s).val <
      (mggF2CubMk (mggF2Neighbor hm v s) (mggF2Rev s)).val
  · rw [dif_pos hlt]
    exact Or.inl ⟨rfl, rfl⟩
  · rw [dif_neg hlt]
    exact Or.inr ⟨rfl, rfl⟩

def mggF2CubPartialVerts {m : ℕ} (T : Finset (Fin (m * m * 8))) :
    Finset (Fin (m * m * 8)) :=
  (univ : Finset (Fin (m * m * 8))).filter fun i =>
    mggF2CubV i ∈ mggF2CubPartial T ∧ i ∈ T

theorem mggF2CubPartialVerts_card {m : ℕ} (T : Finset (Fin (m * m * 8))) :
    (mggF2CubPartialVerts T).card =
      ∑ v ∈ mggF2CubPartial T, (mggF2CubPorts T v).card := by
  classical
  have hcover : mggF2CubPartialVerts T =
      (mggF2CubPartial T).biUnion (mggF2CubCloudIn T) := by
    ext i
    simp only [mggF2CubPartialVerts, mem_filter, mem_univ, true_and, mem_biUnion,
      mggF2CubCloudIn, mem_image, mggF2CubPorts]
    constructor
    · intro ⟨hv, hi⟩
      refine ⟨mggF2CubV i, hv, mggF2CubP i, ?_, mggF2CubMk_ext i⟩
      simpa [mggF2CubPorts, mggF2CubMk_ext] using hi
    · rintro ⟨v, hv, p, hp, rfl⟩
      exact ⟨by simpa [mggF2CubMk_v] using hv, hp⟩
  have hdisj : ((mggF2CubPartial T) : Set (Fin (m * m))).PairwiseDisjoint
      (mggF2CubCloudIn T) := by
    intro a _ b _ hne
    refine disjoint_left.mpr ?_
    intro i hi hj
    simp only [mggF2CubCloudIn, mem_image] at hi hj
    obtain ⟨_, _, rfl⟩ := hi
    obtain ⟨_, _, hq⟩ := hj
    exact hne (mggF2CubMk_injective hq).1.symm
  have hcard : (mggF2CubPartialVerts T).card =
      ((mggF2CubPartial T).biUnion (mggF2CubCloudIn T)).card :=
    congrArg Finset.card hcover
  rw [hcard, card_biUnion hdisj]
  refine sum_congr rfl fun v _ => ?_
  simpa [mggF2CubCloudIn] using
    (card_image_of_injective (mggF2CubPorts T v) fun p q h => (mggF2CubMk_injective h).2)

theorem mggF2Cub_base_boundary_le {m : ℕ} (hm : 0 < m)
    (T : Finset (Fin (m * m * 8))) :
    (edgeBoundary (mggF2Graph m hm) (mggF2CubFull T)).card ≤
      (edgeBoundary (mggF2CubGraph hm) T).card +
        ∑ v ∈ mggF2CubPartial T, (mggF2CubPorts T v).card := by
  classical
  let F := mggF2CubFull T
  let B := edgeBoundary (mggF2Graph m hm) F
  let inn (e : FinEdge (m * m)) : Fin (m * m) :=
    if e.val.1 ∈ F then e.val.1 else e.val.2
  let out (e : FinEdge (m * m)) : Fin (m * m) :=
    if e.val.1 ∈ F then e.val.2 else e.val.1
  have hAdj : ∀ e, e ∈ B → (mggF2Graph m hm).Adj (inn e) (out e) := by
    intro e he
    obtain ⟨heG, hcut⟩ := (mem_edgeBoundary_iff).mp he
    refine ⟨e, heG, ?_⟩
    rcases hcut with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [inn, out, if_pos h1]
      exact Or.inl ⟨trivial, trivial⟩
    · simp only [inn, out, if_neg h1, if_pos h2]
      exact Or.inr ⟨trivial, trivial⟩
  have hIn : ∀ e, e ∈ B → inn e ∈ F := by
    intro e he
    obtain ⟨_, hcut⟩ := (mem_edgeBoundary_iff).mp he
    rcases hcut with ⟨h1, _⟩ | ⟨h1, h2⟩
    · simp only [inn, if_pos h1]
      exact h1
    · simp only [inn, if_neg h1, if_pos h2]
      exact h2
  have hOut : ∀ e, e ∈ B → out e ∉ F := by
    intro e he
    obtain ⟨_, hcut⟩ := (mem_edgeBoundary_iff).mp he
    rcases hcut with ⟨h1, h2⟩ | ⟨h1, _⟩
    · simp only [out, if_pos h1]
      exact h2
    · simp only [out, if_neg h1]
      exact h1
  let sOf (e : FinEdge (m * m)) (he : e ∈ B) : Fin 8 :=
    Classical.choose (mggF2_exists_label_of_adj hm (hAdj e he))
  have hsOf (e : FinEdge (m * m)) (he : e ∈ B) :
      mggF2Neighbor hm (inn e) (sOf e he) = out e :=
    Classical.choose_spec (mggF2_exists_label_of_adj hm (hAdj e he))
  let lift (e : {x // x ∈ B}) : FinEdge (m * m * 8) :=
    mggF2CubExtEdge hm (inn e.1) (sOf e.1 e.2)
  have hland (e : {x // x ∈ B}) :
      let y := mggF2CubMk (out e.1) (mggF2Rev (sOf e.1 e.2))
      (lift e).val.1 = mggF2CubMk (inn e.1) (sOf e.1 e.2) ∧ (lift e).val.2 = y ∨
        (lift e).val.1 = y ∧ (lift e).val.2 = mggF2CubMk (inn e.1) (sOf e.1 e.2) := by
    simpa [lift, hsOf e.1 e.2] using mggF2CubExtEdge_orients hm (inn e.1) (sOf e.1 e.2)
  have hInT (e : {x // x ∈ B}) : mggF2CubMk (inn e.1) (sOf e.1 e.2) ∈ T := by
    have hport : mggF2CubPorts T (inn e.1) = univ := by
      have hinF := hIn e.1 e.2
      simpa [F, mggF2CubFull, mem_filter] using hinF
    have : sOf e.1 e.2 ∈ mggF2CubPorts T (inn e.1) := by simp [hport]
    simpa [mggF2CubPorts] using this
  let img := B.attach.image lift
  have hbaseEnds (e : {x // x ∈ B}) :
      (e.1.val.1 = inn e.1 ∧ e.1.val.2 = out e.1) ∨
        (e.1.val.1 = out e.1 ∧ e.1.val.2 = inn e.1) := by
    obtain ⟨_, hcut⟩ := (mem_edgeBoundary_iff).mp e.2
    rcases hcut with ⟨h1, _h2⟩ | ⟨h1, h2⟩
    · left
      simp only [inn, out, if_pos h1]
      exact ⟨trivial, trivial⟩
    · right
      simp only [inn, out, if_neg h1, if_pos h2]
      exact ⟨trivial, trivial⟩
  let fullEnd (e : FinEdge (m * m * 8)) : Fin (m * m * 8) :=
    if mggF2CubV e.val.1 ∈ F then e.val.1 else e.val.2
  have hfull (e : {x // x ∈ B}) :
      fullEnd (lift e) = mggF2CubMk (inn e.1) (sOf e.1 e.2) := by
    rcases hland e with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hmem : mggF2CubV (lift e).val.1 ∈ F := by
        rw [ha, mggF2CubMk_v]
        exact hIn e.1 e.2
      simp only [fullEnd, if_pos hmem, ha]
    · have hmem : mggF2CubV (lift e).val.1 ∉ F := by
        rw [ha, mggF2CubMk_v]
        exact hOut e.1 e.2
      simp only [fullEnd, if_neg hmem, hb]
  have hinj : ∀ e1 e2 : {x // x ∈ B}, lift e1 = lift e2 → e1 = e2 := by
    intro e1 e2 h
    have hmk : mggF2CubMk (inn e1.1) (sOf e1.1 e1.2) =
        mggF2CubMk (inn e2.1) (sOf e2.1 e2.2) := by
      rw [← hfull e1, h, hfull e2]
    obtain ⟨hinn, hs⟩ := mggF2CubMk_injective hmk
    have houtE : out e1.1 = out e2.1 := by
      rw [← hsOf e1.1 e1.2, ← hsOf e2.1 e2.2, hinn, hs]
    apply Subtype.ext
    apply Subtype.ext
    rcases hbaseEnds e1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
      rcases hbaseEnds e2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
    · exact Prod.ext (a1.trans (hinn.trans a2.symm)) (b1.trans (houtE.trans b2.symm))
    · have hlt1 := e1.1.property
      have hlt2 := e2.1.property
      rw [a1, b1, hinn, houtE] at hlt1
      rw [a2, b2] at hlt2
      exact False.elim (lt_asymm hlt1 hlt2)
    · have hlt1 := e1.1.property
      have hlt2 := e2.1.property
      rw [a1, b1] at hlt1
      rw [a2, b2, ← hinn, ← houtE] at hlt2
      exact False.elim (lt_asymm hlt2 hlt1)
    · exact Prod.ext (a1.trans (houtE.trans a2.symm)) (b1.trans (hinn.trans b2.symm))
  have hcardB : B.card = img.card := by
    rw [← card_attach (s := B)]
    simpa [img] using (card_image_of_injective B.attach hinj).symm
  let land (e : FinEdge (m * m * 8)) : Fin (m * m * 8) :=
    if mggF2CubV e.val.1 ∈ F then e.val.2 else e.val.1
  have hland_out (e : {x // x ∈ B}) :
      land (lift e) = mggF2CubMk (out e.1) (mggF2Rev (sOf e.1 e.2)) := by
    rcases hland e with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hVin : mggF2CubV (lift e).val.1 ∈ F := by
        rw [ha, mggF2CubMk_v]
        exact hIn e.1 e.2
      simp only [land, if_pos hVin, hb]
    · have hVout : mggF2CubV (lift e).val.1 ∉ F := by
        rw [ha, mggF2CubMk_v]
        exact hOut e.1 e.2
      simp only [land, if_neg hVout, ha]
  let imgIn := img.filter fun e => land e ∈ T
  let imgOut := img.filter fun e => land e ∉ T
  have hsplit : img.card = imgIn.card + imgOut.card := by
    have hun : imgIn ∪ imgOut = img := filter_union_filter_not_eq (fun e => land e ∈ T) img
    have hdisj : Disjoint imgIn imgOut := by
      refine disjoint_left.mpr ?_
      intro e he hf
      exact (mem_filter.mp hf).2 (mem_filter.mp he).2
    rw [← hun, card_union_of_disjoint hdisj, add_comm]
  have hout_sub : imgOut ⊆ edgeBoundary (mggF2CubGraph hm) T := by
    intro e he
    obtain ⟨heimg, hnot⟩ := mem_filter.mp he
    obtain ⟨e0, _, rfl⟩ := mem_image.mp heimg
    refine (mem_edgeBoundary_iff).mpr ⟨?_, ?_⟩
    · exact mem_union_right _ ((mem_mggF2CubExtEdges hm).mpr ⟨inn e0.1, sOf e0.1 e0.2, rfl⟩)
    · rcases hland e0 with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl ⟨ha ▸ hInT e0, by simpa [hland_out e0, hb] using hnot⟩
      · exact Or.inr ⟨by simpa [hland_out e0, ha] using hnot, hb ▸ hInT e0⟩
  have hIn_sub (e : {x // x ∈ B}) (hTland : land (lift e) ∈ T) :
      land (lift e) ∈ mggF2CubPartialVerts T := by
    have hy := hland_out e
    rw [hy] at hTland ⊢
    refine mem_filter.mpr ⟨mem_univ _, ?_, hTland⟩
    rw [mggF2CubMk_v]
    have hout := hOut e.1 e.2
    have hneU : mggF2CubPorts T (out e.1) ≠ univ := by
      intro hU
      apply hout
      simpa [F, mggF2CubFull, mem_filter, hU]
    have hN : (mggF2CubPorts T (out e.1)).Nonempty :=
      ⟨mggF2Rev (sOf e.1 e.2), by simpa [mggF2CubPorts] using hTland⟩
    simpa [mggF2CubPartial, mem_filter] using ⟨hN, hneU⟩
  have hland_inj : ∀ e1 e2 : {x // x ∈ B},
      land (lift e1) = land (lift e2) → lift e1 = lift e2 := by
    intro e1 e2 hEq
    have hy : mggF2CubMk (out e1.1) (mggF2Rev (sOf e1.1 e1.2)) =
        mggF2CubMk (out e2.1) (mggF2Rev (sOf e2.1 e2.2)) := by
      rw [← hland_out e1, ← hland_out e2, hEq]
    have hf1 : mggF2CubExt hm (mggF2CubMk (out e1.1) (mggF2Rev (sOf e1.1 e1.2))) =
        mggF2CubMk (inn e1.1) (sOf e1.1 e1.2) := by
      have hback : mggF2Neighbor hm (out e1.1) (mggF2Rev (sOf e1.1 e1.2)) = inn e1.1 := by
        rw [← hsOf e1.1 e1.2]
        exact mggF2Neighbor_rev_left hm (inn e1.1) (sOf e1.1 e1.2)
      simp [mggF2CubExt, mggF2CubMk_v, mggF2CubMk_p, mggF2Rev_rev, hback]
    have hf2 : mggF2CubExt hm (mggF2CubMk (out e2.1) (mggF2Rev (sOf e2.1 e2.2))) =
        mggF2CubMk (inn e2.1) (sOf e2.1 e2.2) := by
      have hback : mggF2Neighbor hm (out e2.1) (mggF2Rev (sOf e2.1 e2.2)) = inn e2.1 := by
        rw [← hsOf e2.1 e2.2]
        exact mggF2Neighbor_rev_left hm (inn e2.1) (sOf e2.1 e2.2)
      simp [mggF2CubExt, mggF2CubMk_v, mggF2CubMk_p, mggF2Rev_rev, hback]
    have hfullMk : mggF2CubMk (inn e1.1) (sOf e1.1 e1.2) =
        mggF2CubMk (inn e2.1) (sOf e2.1 e2.2) := by
      rw [← hf1, ← hf2, hy]
    apply Subtype.ext
    rcases hland e1 with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩ <;>
      rcases hland e2 with ⟨ha2, hb2⟩ | ⟨ha2, hb2⟩
    · exact Prod.ext (ha1.trans (hfullMk.trans ha2.symm)) (hb1.trans (hy.trans hb2.symm))
    · have hlt1 := (lift e1).property
      have hlt2 := (lift e2).property
      rw [ha1, hb1, hfullMk, hy] at hlt1
      rw [ha2, hb2] at hlt2
      exact False.elim (lt_asymm hlt1 hlt2)
    · have hlt1 := (lift e1).property
      have hlt2 := (lift e2).property
      rw [ha1, hb1] at hlt1
      rw [ha2, hb2, ← hfullMk, ← hy] at hlt2
      exact False.elim (lt_asymm hlt2 hlt1)
    · exact Prod.ext (ha1.trans (hy.trans ha2.symm)) (hb1.trans (hfullMk.trans hb2.symm))
  have hInCard : imgIn.card ≤ (mggF2CubPartialVerts T).card := by
    have hsub : imgIn.image land ⊆ mggF2CubPartialVerts T := by
      intro y hy
      obtain ⟨e, he, rfl⟩ := mem_image.mp hy
      obtain ⟨heimg, hT⟩ := mem_filter.mp he
      obtain ⟨e0, _, rfl⟩ := mem_image.mp heimg
      exact hIn_sub e0 hT
    have hcard : (imgIn.image land).card = imgIn.card := by
      refine card_image_of_injOn ?_
      intro e1 he1 e2 he2 hEq
      obtain ⟨he1, _⟩ := mem_filter.mp he1
      obtain ⟨he2, _⟩ := mem_filter.mp he2
      obtain ⟨a, _, rfl⟩ := mem_image.mp he1
      obtain ⟨b, _, rfl⟩ := mem_image.mp he2
      exact hland_inj a b hEq
    rw [← hcard]
    exact card_le_card hsub
  have hOutCard : imgOut.card ≤ (edgeBoundary (mggF2CubGraph hm) T).card :=
    card_le_card hout_sub
  have hpartial : (mggF2CubPartialVerts T).card =
      ∑ v ∈ mggF2CubPartial T, (mggF2CubPorts T v).card :=
    mggF2CubPartialVerts_card T
  calc
    (edgeBoundary (mggF2Graph m hm) F).card = B.card := rfl
    _ = img.card := hcardB
    _ = imgIn.card + imgOut.card := hsplit
    _ ≤ (mggF2CubPartialVerts T).card + imgOut.card := Nat.add_le_add_right hInCard _
    _ = (∑ v ∈ mggF2CubPartial T, (mggF2CubPorts T v).card) + imgOut.card := by
      rw [hpartial]
    _ ≤ (∑ v ∈ mggF2CubPartial T, (mggF2CubPorts T v).card) +
        (edgeBoundary (mggF2CubGraph hm) T).card := Nat.add_le_add_left hOutCard _
    _ = (edgeBoundary (mggF2CubGraph hm) T).card +
        ∑ v ∈ mggF2CubPartial T, (mggF2CubPorts T v).card := Nat.add_comm _ _

theorem mggF2Cub_hasExpansionInv {m : ℕ} (hm0 : 0 < m) (hmI : mggInformativeFloor ≤ m) :
    HasExpansionInv (mggF2CubGraph hm0) mggF2CubK := by
  intro T hT hhalf
  have hbase : HasExpansionInv (mggF2Graph m hm0) mggInvK := by
    have h := mggF2Graph_hasExpansionInv hmI
    rw [mggF2Graph_proof_irrel
      (lt_of_lt_of_le (by decide : 0 < mggInformativeFloor) hmI) hm0] at h
    exact h
  have hcard := mggF2Cub_card_full_partial T
  have hpart := mggF2Cub_partial_le_boundary hm0 T
  have hbaseLe := mggF2Cub_base_boundary_le hm0 T
  let F := mggF2CubFull T
  by_cases hF : F.Nonempty
  · have hhalfF : 2 * F.card ≤ m * m := by
      have h8 : 8 * F.card ≤ T.card := by
        rw [hcard]
        exact Nat.le_add_right _ _
      have hmul : 8 * (2 * F.card) ≤ 8 * (m * m) := by
        calc
          8 * (2 * F.card) = 2 * (8 * F.card) := by ring
          _ ≤ 2 * T.card := Nat.mul_le_mul_left 2 h8
          _ ≤ m * m * 8 := hhalf
          _ = 8 * (m * m) := by ring
      exact Nat.le_of_mul_le_mul_left hmul (by decide)
    have hFcard : F.card ≤ mggInvK * (edgeBoundary (mggF2Graph m hm0) F).card :=
      hbase F hF hhalfF
    simp only [mggF2CubK, mggInvK, F] at hFcard hcard hpart hbaseLe ⊢
    omega
  · have h0 : F.card = 0 := by
      simpa [card_eq_zero, not_nonempty_iff_eq_empty] using hF
    rw [h0] at hcard
    simp only [mggF2CubK] at hcard hpart ⊢
    omega

theorem exists_mggF2Cub_hasExpansionInv_family :
    ∀ N : ℕ, ∃ (n : ℕ) (G : FinGraph n),
      max N mggF2CubFloor ≤ n ∧
        IsRegular G 3 ∧ G.IsConnected ∧ HasExpansionInv G mggF2CubK := by
  intro N
  let m := max mggInformativeFloor (max N mggF2CubFloor)
  have hmI : mggInformativeFloor ≤ m := le_max_left _ _
  have hm0 : 0 < m := lt_of_lt_of_le (by decide : 0 < mggInformativeFloor) hmI
  refine ⟨m * m * 8, mggF2CubGraph hm0, ?_, mggF2Cub_isRegular hm0,
      mggF2Cub_isConnected hm0, mggF2Cub_hasExpansionInv hm0 hmI⟩
  have hm : max N mggF2CubFloor ≤ m := le_max_right _ _
  have hone : 1 ≤ m := Nat.succ_le_of_lt hm0
  have hsq : m ≤ m * m := by
    simpa using Nat.mul_le_mul_left m hone
  have h8 : m * m ≤ m * m * 8 := by
    simpa using Nat.mul_le_mul_left (m * m) (by decide : 1 ≤ 8)
  omega

end SATurday.ProofComplexity
