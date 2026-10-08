import Theory.ProofComplexity.Matching
import Mathlib.Data.List.GetD
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# The switching lemma for matching restrictions (Ladder Rung R4, 1B.3)

Razborov style encoding for matching restrictions. A restriction `ρ` whose canonical matching
tree has depth at least `s` is sent to an extension `ρ'` with `s` more edges (the term edges
along the leftmost deep branch, truncated) plus a code: for each block, the positions of the
term edges inside the term, and for each of their vertices a code for its partner along the
branch (a position inside the term, or an index among the free vertices of `ρ'`).
`mdec` recovers `ρ` from `ρ'` and the code, so

  `#{ρ ∈ R_m : mdepth ρ ≥ s} ≤ #R_{m+s} · (2 w C²)^s`

where `w` bounds the term width and `C` bounds `w` plus the free vertex counts of `R_{m+s}`.

LOG: R4 MatchingSwitch module (PHP switching lemma)
-/

namespace SATurday.ProofComplexity

open Finset

noncomputable section

open Classical

/-! ## Positions inside a term -/

def mpos (t : Mt) (e : ℕ × ℕ) : ℕ := t.toList.idxOf e

def edgeAt (t : Mt) (p : ℕ) : ℕ × ℕ := t.toList.getD p (0, 0)

theorem getD_idxOf {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a d : α} (h : a ∈ l) :
    l.getD (l.idxOf a) d = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem h),
    Option.getD_some, List.getElem_idxOf]

theorem mpos_lt {t : Mt} {e : ℕ × ℕ} (h : e ∈ t) : mpos t e < t.card := by
  unfold mpos; rw [← length_toList]
  exact List.idxOf_lt_length_of_mem (mem_toList.2 h)

theorem edgeAt_mpos {t : Mt} {e : ℕ × ℕ} (h : e ∈ t) : edgeAt t (mpos t e) = e := by
  unfold edgeAt mpos
  exact getD_idxOf (mem_toList.2 h)

theorem mpos_inj {t : Mt} {e f : ℕ × ℕ} (he : e ∈ t) (hf : f ∈ t) (h : mpos t e = mpos t f) :
    e = f := by
  rw [← edgeAt_mpos he, ← edgeAt_mpos hf, h]

/-- Edges of `t` at the positions `β`. -/
def selE (t : Mt) (β : Finset ℕ) : Mt := t.filter fun e => mpos t e ∈ β

/-- Positions of the edges of `τ` inside `t`. -/
def posOf (t τ : Mt) : Finset ℕ := τ.image (mpos t)

theorem selE_posOf {t τ : Mt} (h : τ ⊆ t) : selE t (posOf t τ) = τ := by
  ext e
  simp only [selE, posOf, mem_filter, mem_image]
  constructor
  · rintro ⟨het, f, hf, hfe⟩; rwa [← mpos_inj (h hf) het hfe]
  · intro he; exact ⟨h he, e, he, rfl⟩

theorem posOf_card {t τ : Mt} (h : τ ⊆ t) : (posOf t τ).card = τ.card :=
  card_image_of_injOn fun e he f hf hef => mpos_inj (h he) (h hf) hef

theorem posOf_sub {t τ : Mt} {w : ℕ} (h : τ ⊆ t) (hw : t.card ≤ w) :
    posOf t τ ⊆ range w := by
  intro p hp
  obtain ⟨e, he, rfl⟩ := mem_image.1 hp
  exact mem_range.2 (lt_of_lt_of_le (mpos_lt (h he)) hw)

/-! ## Partner codes -/

def decHole (H : Finset ℕ) (w : ℕ) (t ρ' : Mt) (a : ℕ) : ℕ :=
  if a < w then (edgeAt t a).2 else (fH H ρ').toList.getD (a - w) 0

def decPig (P : Finset ℕ) (w : ℕ) (t ρ' : Mt) (b : ℕ) : ℕ :=
  if b < w then (edgeAt t b).1 else (fP P ρ').toList.getD (b - w) 0

def encHole (H : Finset ℕ) (w : ℕ) (t τ ρ' : Mt) (h : ℕ) : ℕ :=
  if hh : ∃ e ∈ τ, e.2 = h then mpos t (Classical.choose hh)
  else w + (fH H ρ').toList.idxOf h

def encPig (P : Finset ℕ) (w : ℕ) (t τ ρ' : Mt) (i : ℕ) : ℕ :=
  if hh : ∃ e ∈ τ, e.1 = i then mpos t (Classical.choose hh)
  else w + (fP P ρ').toList.idxOf i

def partnerH (σ : Mt) (i : ℕ) : ℕ := if h : ∃ e ∈ σ, e.1 = i then (Classical.choose h).2 else 0
def partnerP (σ : Mt) (j : ℕ) : ℕ := if h : ∃ e ∈ σ, e.2 = j then (Classical.choose h).1 else 0

theorem partnerH_mem {σ : Mt} {i : ℕ} (h : i ∈ pigs σ) : (i, partnerH σ i) ∈ σ := by
  have hh : ∃ e ∈ σ, e.1 = i := mem_pigs.1 h
  unfold partnerH; rw [dif_pos hh]
  have e := Classical.choose_spec hh
  convert e.1 using 1; exact Prod.ext e.2.symm rfl

theorem partnerP_mem {σ : Mt} {j : ℕ} (h : j ∈ hols σ) : (partnerP σ j, j) ∈ σ := by
  have hh : ∃ e ∈ σ, e.2 = j := mem_hols.1 h
  unfold partnerP; rw [dif_pos hh]
  have e := Classical.choose_spec hh
  convert e.1 using 1; exact Prod.ext rfl e.2.symm

theorem partnerH_eq {σ : Mt} (hm : IsMatch σ) {e : ℕ × ℕ} (he : e ∈ σ) : partnerH σ e.1 = e.2 := by
  have := partnerH_mem (mem_pigs.2 ⟨e, he, rfl⟩)
  exact congrArg Prod.snd (hm _ this e he (Or.inl rfl))

theorem partnerP_eq {σ : Mt} (hm : IsMatch σ) {e : ℕ × ℕ} (he : e ∈ σ) : partnerP σ e.2 = e.1 := by
  have := partnerP_mem (mem_hols.2 ⟨e, he, rfl⟩)
  exact congrArg Prod.fst (hm _ this e he (Or.inr rfl))

theorem dec_encHole {H : Finset ℕ} {w : ℕ} {t τ ρ' : Mt} (hτt : τ ⊆ t) (htw : t.card ≤ w)
    {h : ℕ} (hh : h ∈ hols τ ∨ h ∈ fH H ρ') :
    decHole H w t ρ' (encHole H w t τ ρ' h) = h ∧ encHole H w t τ ρ' h < w + (fH H ρ').card := by
  unfold encHole
  split_ifs with hx
  · have hs := Classical.choose_spec hx
    have hlt := lt_of_lt_of_le (mpos_lt (hτt hs.1)) htw
    refine ⟨?_, by omega⟩
    unfold decHole; rw [if_pos hlt, edgeAt_mpos (hτt hs.1), hs.2]
  · have hf : h ∈ fH H ρ' := hh.resolve_left fun h' => hx (mem_hols.1 h')
    have hl : (fH H ρ').toList.idxOf h < (fH H ρ').toList.length :=
      List.idxOf_lt_length_of_mem (mem_toList.2 hf)
    rw [length_toList] at hl
    refine ⟨?_, by omega⟩
    unfold decHole
    rw [if_neg (by omega), show w + (fH H ρ').toList.idxOf h - w = (fH H ρ').toList.idxOf h
      by omega]
    exact getD_idxOf (mem_toList.2 hf)

theorem dec_encPig {P : Finset ℕ} {w : ℕ} {t τ ρ' : Mt} (hτt : τ ⊆ t) (htw : t.card ≤ w)
    {i : ℕ} (hi : i ∈ pigs τ ∨ i ∈ fP P ρ') :
    decPig P w t ρ' (encPig P w t τ ρ' i) = i ∧ encPig P w t τ ρ' i < w + (fP P ρ').card := by
  unfold encPig
  split_ifs with hx
  · have hs := Classical.choose_spec hx
    have hlt := lt_of_lt_of_le (mpos_lt (hτt hs.1)) htw
    refine ⟨?_, by omega⟩
    unfold decPig; rw [if_pos hlt, edgeAt_mpos (hτt hs.1), hs.2]
  · have hf : i ∈ fP P ρ' := hi.resolve_left fun h' => hx (mem_pigs.1 h')
    have hl : (fP P ρ').toList.idxOf i < (fP P ρ').toList.length :=
      List.idxOf_lt_length_of_mem (mem_toList.2 hf)
    rw [length_toList] at hl
    refine ⟨?_, by omega⟩
    unfold decPig
    rw [if_neg (by omega), show w + (fP P ρ').toList.idxOf i - w = (fP P ρ').toList.idxOf i
      by omega]
    exact getD_idxOf (mem_toList.2 hf)

/-- The partner code of a block. -/
def encG (P H : Finset ℕ) (w : ℕ) (t τ σ ρ' : Mt) : ℕ → ℕ × ℕ := fun p =>
  if p ∈ posOf t τ then
    (encHole H w t τ ρ' (partnerH σ (edgeAt t p).1), encPig P w t τ ρ' (partnerP σ (edgeAt t p).2))
  else (0, 0)

theorem encG_at {P H : Finset ℕ} {w : ℕ} {t τ σ ρ' : Mt} {p : ℕ} (h : p ∈ posOf t τ) :
    encG P H w t τ σ ρ' p = (encHole H w t τ ρ' (partnerH σ (edgeAt t p).1),
      encPig P w t τ ρ' (partnerP σ (edgeAt t p).2)) := by
  unfold encG; rw [if_pos h]

/-- The branch edges decoded from a block code. -/
def decS (P H : Finset ℕ) (w : ℕ) (t : Mt) (β : Finset ℕ) (γ : ℕ → ℕ × ℕ) (ρ' : Mt) : Mt :=
  (β.image fun p => ((edgeAt t p).1, decHole H w t ρ' (γ p).1)) ∪
    (β.image fun p => (decPig P w t ρ' (γ p).2, (edgeAt t p).2))

/-- A cover of `τ` whose outside vertices are free in `ρ'`. -/
structure GoodCover (P H : Finset ℕ) (τ σ ρ' : Mt) : Prop where
  match_ : IsMatch σ
  pc : pigs τ ⊆ pigs σ
  hc : hols τ ⊆ hols σ
  touch : ∀ e ∈ σ, e.1 ∈ pigs τ ∨ e.2 ∈ hols τ
  freeH : ∀ e ∈ σ, e.2 ∉ hols τ → e.2 ∈ fH H ρ'
  freeP : ∀ e ∈ σ, e.1 ∉ pigs τ → e.1 ∈ fP P ρ'

theorem decS_encG {P H : Finset ℕ} {w : ℕ} {t τ σ ρ' : Mt} (hτt : τ ⊆ t) (htw : t.card ≤ w)
    (hg : GoodCover P H τ σ ρ') : decS P H w t (posOf t τ) (encG P H w t τ σ ρ') ρ' = σ := by
  have hHole : ∀ i ∈ pigs τ, decHole H w t ρ' (encHole H w t τ ρ' (partnerH σ i)) =
      partnerH σ i := by
    intro i hi
    have hm := partnerH_mem (hg.pc hi)
    refine (dec_encHole hτt htw ?_).1
    by_cases h : partnerH σ i ∈ hols τ
    · exact Or.inl h
    · exact Or.inr (hg.freeH _ hm h)
  have hPig : ∀ j ∈ hols τ, decPig P w t ρ' (encPig P w t τ ρ' (partnerP σ j)) =
      partnerP σ j := by
    intro j hj
    have hm := partnerP_mem (hg.hc hj)
    refine (dec_encPig hτt htw ?_).1
    by_cases h : partnerP σ j ∈ pigs τ
    · exact Or.inl h
    · exact Or.inr (hg.freeP _ hm h)
  ext e
  simp only [decS, mem_union, mem_image]
  constructor
  · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · obtain ⟨f, hf, rfl⟩ := mem_image.1 hp
      rw [encG_at hp, edgeAt_mpos (hτt hf)]
      have hi : f.1 ∈ pigs τ := mem_pigs.2 ⟨f, hf, rfl⟩
      rw [hHole _ hi]; exact partnerH_mem (hg.pc hi)
    · obtain ⟨f, hf, rfl⟩ := mem_image.1 hp
      rw [encG_at hp, edgeAt_mpos (hτt hf)]
      have hj : f.2 ∈ hols τ := mem_hols.2 ⟨f, hf, rfl⟩
      rw [hPig _ hj]; exact partnerP_mem (hg.hc hj)
  · intro he
    rcases hg.touch e he with hi | hj
    · obtain ⟨f, hf, hfe⟩ := mem_pigs.1 hi
      refine Or.inl ⟨mpos t f, mem_image.2 ⟨f, hf, rfl⟩, ?_⟩
      rw [encG_at (mem_image.2 ⟨f, hf, rfl⟩), edgeAt_mpos (hτt hf)]
      rw [hHole _ (mem_pigs.2 ⟨f, hf, rfl⟩), hfe, partnerH_eq hg.match_ he]
    · obtain ⟨f, hf, hfe⟩ := mem_hols.1 hj
      refine Or.inr ⟨mpos t f, mem_image.2 ⟨f, hf, rfl⟩, ?_⟩
      rw [encG_at (mem_image.2 ⟨f, hf, rfl⟩), edgeAt_mpos (hτt hf)]
      rw [hPig _ (mem_hols.2 ⟨f, hf, rfl⟩), hfe, partnerP_eq hg.match_ he]

/-! ## Codes -/

/-- Block codes for the positions `β`, values below `C`, normalized outside `β`. -/
def gcodes (β : Finset ℕ) (C : ℕ) : Finset (ℕ → ℕ × ℕ) :=
  (β.pi fun _ => range C ×ˢ range C).image fun f p => if h : p ∈ β then f p h else (0, 0)

theorem gcodes_card (β : Finset ℕ) (C : ℕ) : (gcodes β C).card ≤ (C * C) ^ β.card := by
  refine card_image_le.trans ?_
  rw [card_pi, prod_const, card_product, card_range]

theorem mem_gcodes {β : Finset ℕ} {C : ℕ} {γ : ℕ → ℕ × ℕ} (h0 : ∀ p ∉ β, γ p = (0, 0))
    (hC : ∀ p ∈ β, (γ p).1 < C ∧ (γ p).2 < C) : γ ∈ gcodes β C := by
  refine mem_image.2 ⟨fun p _ => γ p, mem_pi.2 fun p hp => ?_, ?_⟩
  · exact mem_product.2 ⟨mem_range.2 (hC p hp).1, mem_range.2 (hC p hp).2⟩
  · funext p; by_cases hp : p ∈ β <;> simp [hp, h0]

abbrev MCode := List (Finset ℕ × (ℕ → ℕ × ℕ))

/-- Codes for depth `s`. -/
def mcodes (w C : ℕ) : ℕ → Finset MCode
  | 0 => {[]}
  | s + 1 => (range (s + 1)).biUnion fun m =>
      ((range w).powersetCard (m + 1)).biUnion fun β =>
        (gcodes β C).biUnion fun γ => (mcodes w C (s - m)).image (List.cons (β, γ))
termination_by s => s
decreasing_by omega

theorem mcodes_ne_nil {w C s : ℕ} {c : MCode} (h : c ∈ mcodes w C (s + 1)) : c ≠ [] := by
  rw [mcodes] at h
  simp only [mem_biUnion, mem_image] at h
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := h
  simp

theorem geom_two' (k : ℕ) : ∑ j ∈ range k, 2 ^ j + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, pow_succ]; omega

theorem mcodes_card (w C s : ℕ) : (mcodes w C s).card ≤ (2 * (w * (C * C))) ^ s := by
  set Y := w * (C * C)
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  cases s with
  | zero => simp [mcodes]
  | succ s =>
    rw [mcodes]
    calc _ ≤ ∑ m ∈ range (s + 1), Y ^ (m + 1) * (2 * Y) ^ (s - m) := by
          refine card_biUnion_le.trans (sum_le_sum fun m hm => ?_)
          refine card_biUnion_le.trans ?_
          calc _ ≤ ∑ β ∈ (range w).powersetCard (m + 1), (C * C) ^ (m + 1) * (2 * Y) ^ (s - m) := by
                refine sum_le_sum fun β hβ => ?_
                refine card_biUnion_le.trans ?_
                have hβc := (mem_powersetCard.1 hβ).2
                calc _ ≤ ∑ γ ∈ gcodes β C, (2 * Y) ^ (s - m) :=
                      sum_le_sum fun γ _ => card_image_le.trans (ih _ (by omega))
                  _ = (gcodes β C).card * (2 * Y) ^ (s - m) := by rw [sum_const, smul_eq_mul]
                  _ ≤ _ := Nat.mul_le_mul_right _ (hβc ▸ gcodes_card β C)
            _ = w.choose (m + 1) * ((C * C) ^ (m + 1) * (2 * Y) ^ (s - m)) := by
                rw [sum_const, card_powersetCard, card_range, smul_eq_mul]
            _ ≤ w ^ (m + 1) * ((C * C) ^ (m + 1) * (2 * Y) ^ (s - m)) :=
                Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)
            _ = _ := by rw [← mul_assoc, ← mul_pow]
      _ = ∑ m ∈ range (s + 1), Y ^ (s + 1) * 2 ^ (s - m) := by
          refine sum_congr rfl fun m hm => ?_
          have hm := mem_range.1 hm
          obtain ⟨k, rfl⟩ : ∃ k, s = m + k := ⟨s - m, by omega⟩
          rw [show m + k - m = k by omega, mul_pow]; ring
      _ = Y ^ (s + 1) * ∑ j ∈ range (s + 1), 2 ^ j := by
          rw [← mul_sum, ← sum_range_reflect]
          refine congrArg _ (sum_congr rfl fun j hj => ?_)
          have := mem_range.1 hj
          congr 1; omega
      _ ≤ Y ^ (s + 1) * 2 ^ (s + 1) := by
          have := geom_two' (s + 1); exact Nat.mul_le_mul_left _ (by omega)
      _ = (2 * Y) ^ (s + 1) := by rw [mul_pow]; ring

/-! ## Decoding -/

/-- Decoding. The last block only removes its term edges; earlier blocks swap their term edges
for the decoded branch edges, decode the rest, and remove the branch edges. -/
def mdec (P H : Finset ℕ) (D : MDNF) (w : ℕ) : Mt → MCode → Mt
  | ρ', [] => ρ'
  | ρ', [(β, _)] => match mfirst ρ' D with
    | none => ρ'
    | some t => ρ' \ selE t β
  | ρ', (β, γ) :: c => match mfirst ρ' D with
    | none => ρ'
    | some t =>
        (mdec P H D w ((ρ' \ selE t β) ∪ decS P H w t β γ ρ') c) \ decS P H w t β γ ρ'

theorem mfirst_ext {ρ ρ' : Mt} {D : MDNF} {t : Mt} (h : mfirst ρ D = some t) (hsub : ρ ⊆ ρ')
    (hc : Compat ρ' t) : mfirst ρ' D = some t := by
  unfold mfirst at h ⊢
  rw [List.find?_eq_some_iff_append] at h ⊢
  obtain ⟨_, as, bs, hF, has⟩ := h
  refine ⟨by simpa using hc, as, bs, hF, fun a ha => ?_⟩
  have := has a ha
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this ⊢
  exact fun h' => this (compat_mono h' hsub subset_rfl)

/-- Edges added on top of a sub matching avoid its vertices. -/
theorem disj_ext {A B : Mt} (hB : IsMatch B) (hAB : A ⊆ B) :
    ∀ e ∈ B \ A, ∀ f ∈ A, e.1 ≠ f.1 ∧ e.2 ≠ f.2 := by
  intro e he f hf
  obtain ⟨heB, heA⟩ := mem_sdiff.1 he
  exact ⟨fun h => heA (hB e heB f (hAB hf) (Or.inl h) ▸ hf),
    fun h => heA (hB e heB f (hAB hf) (Or.inr h) ▸ hf)⟩

/-! ## The encoding lemma -/

theorem mencode {P H : Finset ℕ} {D : MDNF} (hU : ∀ t ∈ D, InU P H t) {w : ℕ}
    (hw : ∀ t ∈ D, t.card ≤ w) :
    ∀ s (ρ : Mt), IsMatch ρ → InU P H ρ → s ≤ mdepth P H D ρ →
    ∃ ρ' c, IsMatch ρ' ∧ InU P H ρ' ∧ ρ ⊆ ρ' ∧ ρ'.card = ρ.card + s ∧
      (∀ C, w + (fP P ρ').card ≤ C → w + (fH H ρ').card ≤ C → c ∈ mcodes w C s) ∧
      mdec P H D w ρ' c = ρ := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro ρ hρ hρU hs
  cases s with
  | zero => exact ⟨ρ, [], hρ, hρU, subset_rfl, rfl, fun C _ _ => by simp [mcodes], rfl⟩
  | succ s =>
  cases hF : mfirst ρ D with
  | none => rw [mdepth_none hF] at hs; omega
  | some t =>
  have htD := mfirst_mem hF
  have hct := mfirst_compat hF
  have hts : ¬ t ⊆ ρ := by
    intro h; rw [mdepth_some hF, if_pos h] at hs; omega
  have htw := hw t htD
  have htm : IsMatch t := isMatch_mono hct subset_union_right
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = t \ ρ := ⟨_, rfl⟩
  have hτf : τ ⊆ freeE P H ρ := hτdef ▸ sdiff_free hct (hU t htD)
  have hτt : τ ⊆ t := hτdef ▸ sdiff_subset
  have hτm : IsMatch τ := isMatch_mono htm hτt
  have hτρ : ∀ e ∈ τ, e ∉ ρ := fun e he => (mem_sdiff.1 (hτdef ▸ he)).2
  have hdepth := mdepth_some (P := P) (H := H) hF
  rw [if_neg hts, ← hτdef] at hdepth
  rw [hdepth] at hs
  by_cases hA : s + 1 ≤ τ.card
  · obtain ⟨τ', hτ'τ, hτ'c⟩ := exists_subset_card_eq hA
    have hτ'f : τ' ⊆ freeE P H ρ := hτ'τ.trans hτf
    have hτ'm := isMatch_mono hτm hτ'τ
    have hτ't : τ' ⊆ t := hτ'τ.trans hτt
    have hρ'm : IsMatch (ρ ∪ τ') := by
      have := compat_free hρ hτ'm hτ'f; unfold Compat at this; rwa [union_comm]
    have hdisj : Disjoint ρ τ' := disjoint_left.2 fun e he he' => hτρ e (hτ'τ he') he
    have hw1 : 1 ≤ w := by
      have := card_le_card hτt; omega
    refine ⟨ρ ∪ τ', [(posOf t τ', fun _ => (0, 0))], hρ'm,
      union_subset hρU (hτ'f.trans freeE_sub), subset_union_left,
      by rw [card_union_of_disjoint hdisj, hτ'c], ?_, ?_⟩
    · intro C hC1 _
      rw [mcodes]
      simp only [mem_biUnion, mem_range, mem_powersetCard, mem_image]
      refine ⟨s, by omega, posOf t τ', ⟨posOf_sub hτ't htw, by rw [posOf_card hτ't, hτ'c]⟩,
        fun _ => (0, 0), mem_gcodes (fun _ _ => rfl) (fun _ _ => ⟨by omega, by omega⟩), [], ?_, rfl⟩
      rw [Nat.sub_self]; simp [mcodes]
    · have hc' : Compat (ρ ∪ τ') t := by
        refine isMatch_mono hct ?_
        intro e he
        simp only [mem_union] at he ⊢
        rcases he with (he | he) | he
        · exact Or.inl he
        · exact Or.inr (hτ't he)
        · exact Or.inr he
      have hfl := mfirst_ext hF subset_union_left hc'
      simp only [mdec, hfl, selE_posOf hτ't]
      rw [union_sdiff_right, sdiff_eq_self_of_disjoint hdisj]
  · push Not at hA
    have hτne : τ.Nonempty := by
      obtain ⟨e, he⟩ := not_subset.1 hts; exact ⟨e, hτdef ▸ mem_sdiff.2 he⟩
    obtain ⟨m, hm⟩ : ∃ m, τ.card = m + 1 := ⟨τ.card - 1, by have := hτne.card_pos; omega⟩
    have hsup := Nat.sub_le_iff_le_add'.2 hs
    have hsup' := le_trans (show s - m ≤ s + 1 - τ.card by omega) hsup
    obtain ⟨⟨σ1, hσ1⟩, -, hσ1d⟩ := (Finset.le_sup_iff (by simp; omega)).1 hsup'
    simp only at hσ1d
    obtain ⟨hσ1p, hσ1m, hpc, hhc, htouch⟩ := mem_filter.1 hσ1
    have hσ1f : σ1 ⊆ freeE P H ρ := mem_powerset.1 hσ1p
    have hρ1m : IsMatch (ρ ∪ σ1) := by
      have := compat_free hρ hσ1m hσ1f; unfold Compat at this; rwa [union_comm]
    have hρ1U : InU P H (ρ ∪ σ1) := union_subset hρU (hσ1f.trans freeE_sub)
    obtain ⟨ρ1', c1, h1m, h1U, h1sub, h1card, h1codes, h1dec⟩ :=
      ih (s - m) (by omega) (ρ ∪ σ1) hρ1m hρ1U hσ1d
    have hc1ne : c1 ≠ [] := by
      have := h1codes (w + (fP P ρ1').card + (fH H ρ1').card) (by omega) (by omega)
      rw [show s - m = (s - m - 1) + 1 by omega] at this
      exact mcodes_ne_nil this
    obtain ⟨x, c1', rfl⟩ := List.exists_cons_of_ne_nil hc1ne
    have hσρ : ∀ e ∈ σ1, e ∉ ρ := fun e he he' =>
      (disj_free hσ1f e he e he').1 rfl
    have hdisjρσ : Disjoint ρ σ1 := disjoint_left.2 fun e he he' => hσρ e he' he
    have hσ1sub : σ1 ⊆ ρ1' := subset_union_right.trans h1sub
    have hρsub : ρ ⊆ ρ1' := subset_union_left.trans h1sub
    have F1 := disj_ext h1m h1sub
    -- edges of `ρ1'` outside `σ1` cross `t` properly
    have hX : Cross (ρ1' \ σ1) t := by
      intro e he f hf hef
      obtain ⟨he1, heσ⟩ := mem_sdiff.1 he
      by_cases heρ : e ∈ ρ
      · exact (compat_iff.1 hct).2.2 e heρ f hf hef
      · have heN : e ∈ ρ1' \ (ρ ∪ σ1) := mem_sdiff.2 ⟨he1, by simp [heρ, heσ]⟩
        by_cases hfρ : f ∈ ρ
        · have := F1 e heN f (mem_union.2 (Or.inl hfρ))
          rcases hef with h | h
          · exact absurd h this.1
          · exact absurd h this.2
        · have hfτ : f ∈ τ := hτdef ▸ mem_sdiff.2 ⟨hf, hfρ⟩
          rcases hef with h | h
          · obtain ⟨g, hg, hgf⟩ := mem_pigs.1 (hpc (mem_pigs.2 ⟨f, hfτ, rfl⟩))
            exact absurd (h.trans hgf.symm) (F1 e heN g (mem_union.2 (Or.inr hg))).1
          · obtain ⟨g, hg, hgf⟩ := mem_hols.1 (hhc (mem_hols.2 ⟨f, hfτ, rfl⟩))
            exact absurd (h.trans hgf.symm) (F1 e heN g (mem_union.2 (Or.inr hg))).2
    have F3 : ∀ e ∈ τ, e ∉ ρ1' \ σ1 := by
      intro e he he'
      have := hX e he' e (hτt he)
      obtain ⟨he1, heσ⟩ := mem_sdiff.1 he'
      have heN : e ∈ ρ1' \ (ρ ∪ σ1) := mem_sdiff.2 ⟨he1, by simp [hτρ e he, heσ]⟩
      obtain ⟨g, hg, hgf⟩ := mem_pigs.1 (hpc (mem_pigs.2 ⟨e, he, rfl⟩))
      exact (F1 e heN g (mem_union.2 (Or.inr hg))).1 hgf.symm
    set ρ' := (ρ1' \ σ1) ∪ τ with hρ'def
    have hρ'm : IsMatch ρ' :=
      isMatch_union.2 ⟨isMatch_mono h1m sdiff_subset, hτm, cross_mono hX subset_rfl hτt⟩
    have hρ'U : InU P H ρ' := union_subset (sdiff_subset.trans h1U) (hτf.trans freeE_sub)
    have hρρ' : ρ ⊆ ρ' := fun e he =>
      mem_union.2 (Or.inl (mem_sdiff.2 ⟨hρsub he, fun h => hσρ e h he⟩))
    have hcardρ1 : (ρ ∪ σ1).card = ρ.card + σ1.card := card_union_of_disjoint hdisjρσ
    have hσ1τ : τ.card ≤ σ1.card := by
      rw [← card_pigs hτm, ← card_pigs hσ1m]; exact card_le_card hpc
    have hcard' : ρ'.card = ρ.card + (s + 1) := by
      rw [hρ'def, card_union_of_disjoint (disjoint_left.2 fun e he he' => F3 e he' he),
        card_sdiff_of_subset hσ1sub, h1card, hcardρ1]
      omega
    have hgood : GoodCover P H τ σ1 ρ' := by
      refine ⟨hσ1m, hpc, hhc, htouch, fun e he hn => ?_, fun e he hn => ?_⟩
      · have hfree := mem_freeE.1 (hσ1f he)
        refine mem_sdiff.2 ⟨hfree.2.1, fun hj => ?_⟩
        obtain ⟨f, hf, hfe⟩ := mem_hols.1 hj
        rcases mem_union.1 hf with hf | hf
        · obtain ⟨hf1, hfσ⟩ := mem_sdiff.1 hf
          by_cases hfρ : f ∈ ρ
          · exact hfree.2.2 (mem_hols.2 ⟨f, hfρ, hfe⟩)
          · have hfN : f ∈ ρ1' \ (ρ ∪ σ1) := mem_sdiff.2 ⟨hf1, by simp [hfρ, hfσ]⟩
            exact (F1 f hfN e (mem_union.2 (Or.inr he))).2 hfe
        · exact hn (mem_hols.2 ⟨f, hf, hfe⟩)
      · have hfree := mem_freeE.1 (hσ1f he)
        refine mem_sdiff.2 ⟨hfree.1.1, fun hj => ?_⟩
        obtain ⟨f, hf, hfe⟩ := mem_pigs.1 hj
        rcases mem_union.1 hf with hf | hf
        · obtain ⟨hf1, hfσ⟩ := mem_sdiff.1 hf
          by_cases hfρ : f ∈ ρ
          · exact hfree.1.2 (mem_pigs.2 ⟨f, hfρ, hfe⟩)
          · have hfN : f ∈ ρ1' \ (ρ ∪ σ1) := mem_sdiff.2 ⟨hf1, by simp [hfρ, hfσ]⟩
            exact (F1 f hfN e (mem_union.2 (Or.inr he))).1 hfe
        · exact hn (mem_pigs.2 ⟨f, hf, hfe⟩)
    refine ⟨ρ', (posOf t τ, encG P H w t τ σ1 ρ') :: x :: c1', hρ'm, hρ'U, hρρ', hcard', ?_, ?_⟩
    · intro C hC1 hC2
      rw [mcodes]
      simp only [mem_biUnion, mem_range, mem_powersetCard, mem_image]
      refine ⟨m, by omega, posOf t τ, ⟨posOf_sub hτt htw, by rw [posOf_card hτt, hm]⟩,
        encG P H w t τ σ1 ρ', ?_, x :: c1', ?_, rfl⟩
      · refine mem_gcodes (fun p hp => by unfold encG; rw [if_neg hp]) fun p hp => ?_
        rw [encG_at hp]
        obtain ⟨f, hf, rfl⟩ := mem_image.1 hp
        rw [edgeAt_mpos (hτt hf)]
        have hi : f.1 ∈ pigs τ := mem_pigs.2 ⟨f, hf, rfl⟩
        have hj : f.2 ∈ hols τ := mem_hols.2 ⟨f, hf, rfl⟩
        have e1 := partnerH_mem (hpc hi)
        have e2 := partnerP_mem (hhc hj)
        have k1 := (dec_encHole (H := H) (ρ' := ρ') hτt htw
          (h := partnerH σ1 f.1) (by
            by_cases h : partnerH σ1 f.1 ∈ hols τ
            · exact Or.inl h
            · exact Or.inr (hgood.freeH _ e1 h))).2
        have k2 := (dec_encPig (P := P) (ρ' := ρ') hτt htw
          (i := partnerP σ1 f.2) (by
            by_cases h : partnerP σ1 f.2 ∈ pigs τ
            · exact Or.inl h
            · exact Or.inr (hgood.freeP _ e2 h))).2
        exact ⟨by omega, by omega⟩
      · have hle : ρ'.card ≤ ρ1'.card := by rw [hcard', h1card, hcardρ1]; omega
        refine h1codes C ?_ ?_
        · rw [fP_card h1m (pigs_sub h1U)]; rw [fP_card hρ'm (pigs_sub hρ'U)] at hC1; omega
        · rw [fH_card h1m (hols_sub h1U)]; rw [fH_card hρ'm (hols_sub hρ'U)] at hC2; omega
    · have hc' : Compat ρ' t := by
        refine isMatch_mono (isMatch_union.2 ⟨isMatch_mono h1m sdiff_subset, htm, hX⟩) ?_
        intro e he
        simp only [hρ'def, mem_union] at he ⊢
        rcases he with (he | he) | he
        · exact Or.inl he
        · exact Or.inr (hτt he)
        · exact Or.inr he
      have hfl := mfirst_ext hF hρρ' hc'
      have hback : (ρ' \ τ) ∪ σ1 = ρ1' := by
        rw [hρ'def, union_sdiff_right, sdiff_eq_self_of_disjoint
          (disjoint_left.2 fun e he he' => F3 e he' he), sdiff_union_of_subset hσ1sub]
      simp only [mdec, hfl, selE_posOf hτt, decS_encG hτt htw hgood, hback, h1dec]
      rw [union_sdiff_right, sdiff_eq_self_of_disjoint hdisjρσ]

/-! ## The switching lemma for matching restrictions -/

/-- Matchings of size `m` in the universe extending `ρ0`. -/
def Rm (P H : Finset ℕ) (ρ0 : Mt) (m : ℕ) : Finset Mt :=
  (P ×ˢ H).powerset.filter fun ρ => IsMatch ρ ∧ ρ0 ⊆ ρ ∧ ρ.card = m

/-- **PHP switching lemma** (counting form). -/
theorem mswitching {P H : Finset ℕ} {D : MDNF} (hU : ∀ t ∈ D, InU P H t) {w : ℕ}
    (hw : ∀ t ∈ D, t.card ≤ w) (ρ0 : Mt) (m s C : ℕ) (hC1 : w + (P.card - (m + s)) ≤ C)
    (hC2 : w + (H.card - (m + s)) ≤ C) :
    ((Rm P H ρ0 m).filter fun ρ => s ≤ mdepth P H D ρ).card ≤
      (Rm P H ρ0 (m + s)).card * (2 * (w * (C * C))) ^ s := by
  calc _ ≤ ((Rm P H ρ0 (m + s) ×ˢ mcodes w C s).image fun p => mdec P H D w p.1 p.2).card := by
        apply card_le_card
        intro ρ hρ
        simp only [Rm, mem_filter, mem_powerset] at hρ
        obtain ⟨⟨hρU, hρm, hρ0, hρc⟩, hs⟩ := hρ
        obtain ⟨ρ', c, hm', hU', hsub, hcard, hcodes, hdec⟩ := mencode hU hw s ρ hρm hρU hs
        refine mem_image.2 ⟨(ρ', c), mem_product.2 ⟨?_, hcodes C ?_ ?_⟩, hdec⟩
        · simp only [Rm, mem_filter, mem_powerset]
          exact ⟨hU', hm', hρ0.trans hsub, by rw [hcard, hρc]⟩
        · rw [fP_card hm' (pigs_sub hU'), hcard, hρc]; exact hC1
        · rw [fH_card hm' (hols_sub hU'), hcard, hρc]; exact hC2
    _ ≤ (Rm P H ρ0 (m + s) ×ˢ mcodes w C s).card := card_image_le
    _ ≤ _ := by rw [card_product]; exact Nat.mul_le_mul_left _ (mcodes_card w C s)

/-! ## Ratio of restriction counts (double counting) -/

theorem Rm_succ {P H : Finset ℕ} {ρ0 : Mt} (m : ℕ) :
    (Rm P H ρ0 (m + 1)).card * (m + 1 - ρ0.card) ≤
      (Rm P H ρ0 m).card * ((P.card - m) * (H.card - m)) := by
  refine card_mul_le_card_mul (fun ρ' ρ => ρ ⊆ ρ') (fun ρ' hρ' => ?_) (fun ρ hρ => ?_)
  · simp only [Rm, mem_filter, mem_powerset] at hρ'
    obtain ⟨hU, hm, h0, hc⟩ := hρ'
    calc m + 1 - ρ0.card = (ρ' \ ρ0).card := by rw [card_sdiff_of_subset h0, hc]
      _ = ((ρ' \ ρ0).image fun e => ρ'.erase e).card := by
          refine (card_image_of_injOn fun e he f hf hef => ?_).symm
          have he' := (mem_sdiff.1 he).1
          by_contra hne
          have : f ∈ ρ'.erase e := mem_erase.2 ⟨Ne.symm hne, (mem_sdiff.1 hf).1⟩
          simp only at hef
          rw [hef] at this; simp at this
      _ ≤ _ := by
          refine card_le_card fun ρ hρ => ?_
          obtain ⟨e, he, rfl⟩ := mem_image.1 hρ
          have he' := mem_sdiff.1 he
          simp only [bipartiteAbove, Rm, mem_filter, mem_powerset]
          refine ⟨⟨(erase_subset _ _).trans hU, isMatch_mono hm (erase_subset _ _),
            fun x hx => mem_erase.2 ⟨fun h => he'.2 (h ▸ hx), h0 hx⟩, ?_⟩, erase_subset _ _⟩
          rw [card_erase_of_mem he'.1, hc]; rfl
  · simp only [Rm, mem_filter, mem_powerset] at hρ
    obtain ⟨hU, hm, h0, hc⟩ := hρ
    calc _ ≤ ((freeE P H ρ).image fun e => insert e ρ).card := by
          refine card_le_card fun ρ' hρ' => ?_
          simp only [bipartiteBelow, Rm, mem_filter, mem_powerset] at hρ'
          obtain ⟨⟨hU', hm', -, hc'⟩, hsub⟩ := hρ'
          have hlt : ρ.card < ρ'.card := by omega
          obtain ⟨e, he, heρ⟩ := exists_mem_notMem_of_card_lt_card hlt
          have heq : ρ' = insert e ρ := by
            symm; apply eq_of_subset_of_card_le (insert_subset he hsub)
            rw [card_insert_of_notMem heρ]; omega
          refine mem_image.2 ⟨e, ?_, heq.symm⟩
          have hd := disj_ext hm' hsub e (mem_sdiff.2 ⟨he, heρ⟩)
          have hu := mem_product.1 (hU' he)
          refine mem_freeE.2 ⟨⟨hu.1, fun hi => ?_⟩, ⟨hu.2, fun hj => ?_⟩⟩
          · obtain ⟨f, hf, hfe⟩ := mem_pigs.1 hi; exact (hd f hf).1 hfe.symm
          · obtain ⟨f, hf, hfe⟩ := mem_hols.1 hj; exact (hd f hf).2 hfe.symm
      _ ≤ (freeE P H ρ).card := card_image_le
      _ = _ := by
          rw [freeE, card_product, fP_card hm (pigs_sub hU), fH_card hm (hols_sub hU), hc]

theorem Rm_add {P H : Finset ℕ} {ρ0 : Mt} (m : ℕ) : ∀ s,
    (Rm P H ρ0 (m + s)).card * (m + 1 - ρ0.card) ^ s ≤
      (Rm P H ρ0 m).card * ((P.card - m) * (H.card - m)) ^ s := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 := Rm_succ (P := P) (H := H) (ρ0 := ρ0) (m + s)
    calc (Rm P H ρ0 (m + (s + 1))).card * (m + 1 - ρ0.card) ^ (s + 1)
        = ((Rm P H ρ0 (m + s + 1)).card * (m + 1 - ρ0.card)) * (m + 1 - ρ0.card) ^ s := by
          rw [← add_assoc, pow_succ]; ring
      _ ≤ ((Rm P H ρ0 (m + s + 1)).card * (m + s + 1 - ρ0.card)) *
            (m + 1 - ρ0.card) ^ s := by gcongr; omega
      _ ≤ ((Rm P H ρ0 (m + s)).card * ((P.card - (m + s)) * (H.card - (m + s)))) *
            (m + 1 - ρ0.card) ^ s := Nat.mul_le_mul_right _ h1
      _ ≤ ((Rm P H ρ0 (m + s)).card * ((P.card - m) * (H.card - m))) *
            (m + 1 - ρ0.card) ^ s := by gcongr <;> omega
      _ = ((Rm P H ρ0 (m + s)).card * (m + 1 - ρ0.card) ^ s) * ((P.card - m) * (H.card - m)) := by
          ring
      _ ≤ ((Rm P H ρ0 m).card * ((P.card - m) * (H.card - m)) ^ s) *
            ((P.card - m) * (H.card - m)) := Nat.mul_le_mul_right _ ih
      _ = _ := by rw [pow_succ]; ring

/-- **PHP switching lemma** (probability form, cleared of denominators): among the matchings of
size `m` extending `ρ0`, those whose canonical tree has depth at least `s` satisfy
`#bad · (m + 1 - |ρ0|)^s ≤ #R_m · ((|P| - m)(|H| - m) · 2 w C²)^s`. -/
theorem mswitching_ratio {P H : Finset ℕ} {D : MDNF} (hU : ∀ t ∈ D, InU P H t) {w : ℕ}
    (hw : ∀ t ∈ D, t.card ≤ w) (ρ0 : Mt) (m s C : ℕ) (hC1 : w + (P.card - (m + s)) ≤ C)
    (hC2 : w + (H.card - (m + s)) ≤ C) :
    ((Rm P H ρ0 m).filter fun ρ => s ≤ mdepth P H D ρ).card * (m + 1 - ρ0.card) ^ s ≤
      (Rm P H ρ0 m).card * ((P.card - m) * (H.card - m) * (2 * (w * (C * C)))) ^ s := by
  calc _ ≤ (Rm P H ρ0 (m + s)).card * (2 * (w * (C * C))) ^ s * (m + 1 - ρ0.card) ^ s :=
        Nat.mul_le_mul_right _ (mswitching hU hw ρ0 m s C hC1 hC2)
    _ = ((Rm P H ρ0 (m + s)).card * (m + 1 - ρ0.card) ^ s) * (2 * (w * (C * C))) ^ s := by ring
    _ ≤ ((Rm P H ρ0 m).card * ((P.card - m) * (H.card - m)) ^ s) * (2 * (w * (C * C))) ^ s :=
        Nat.mul_le_mul_right _ (Rm_add m s)
    _ = _ := by rw [mul_pow]; ring

end

end SATurday.ProofComplexity
