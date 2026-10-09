import Theory.ProofComplexity.CountMass
import Theory.ProofComplexity.MatchingSwitch

/-!
# The switching lemma for q-partition restrictions (Ladder Rung R4, 1D.2)

Razborov style encoding for partial q-partition restrictions (the q-analog of
`MatchingSwitch`). A DNF is a list of partial q-partitions (terms). The canonical depth `cdepth`
of a restriction `ρ` queries the first term compatible with `ρ`: its blocks outside `ρ` are
paid for, every point they cover is answered by a cover `c` (blocks of free points, each meeting
the term, together covering it) and the depth continues at `ρ ∪ c`.

A restriction of canonical depth at least `s` is sent to an extension with `s` more blocks (the
term blocks along a deep branch, truncated) plus a code: per round, the positions of the term
blocks inside the term and, for each point of each term block, the cover block through it given
as a set of indices into the term points and the free points of the extension. Decoding
recovers the restriction, so

  `#{ρ ∈ R_m : cdepth ρ ≥ s} ≤ #R_{m+s} · (2 w C^{q q})^s`.

LOG: R4 QSwitch module (q-partition switching lemma)
-/

namespace SATurday.ProofComplexity

namespace QP

open Finset

noncomputable section

open Classical

variable {q : ℕ}

/-! ## Free points, first compatible term, covers -/

/-- Free points of a restriction. -/
def free (U : Finset ℕ) (ρ : Finset (Finset ℕ)) : Finset ℕ := U \ cov ρ

/-- Blocks inside the universe. -/
def InU (U : Finset ℕ) (E : Finset (Finset ℕ)) : Prop := ∀ e ∈ E, e ⊆ U

/-- First term compatible with the restriction. -/
def qfirst (q : ℕ) (ρ : Finset (Finset ℕ)) (D : List (Finset (Finset ℕ))) :
    Option (Finset (Finset ℕ)) :=
  D.find? fun t => Compat q ρ t

/-- Covers of the points of `τ` by blocks of free points, each meeting `τ`. -/
def qcovers (q : ℕ) (U : Finset ℕ) (ρ τ : Finset (Finset ℕ)) : Finset (Finset (Finset ℕ)) :=
  ((free U ρ).powersetCard q).powerset.filter fun c => c.Nonempty ∧ PP q c ∧ cov τ ⊆ cov c ∧
    ∀ e ∈ c, ¬ Disjoint e (cov τ)

theorem free_union (U : Finset ℕ) (ρ c : Finset (Finset ℕ)) :
    free U (ρ ∪ c) = free U ρ \ cov c := by
  ext x; simp only [free, cov_union, mem_sdiff, mem_union]; tauto

theorem mem_qcovers {U : Finset ℕ} {ρ τ c : Finset (Finset ℕ)} :
    c ∈ qcovers q U ρ τ ↔ (∀ e ∈ c, e ⊆ free U ρ) ∧ c.Nonempty ∧ PP q c ∧ cov τ ⊆ cov c ∧
      ∀ e ∈ c, ¬ Disjoint e (cov τ) := by
  simp only [qcovers, mem_filter, mem_powerset]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨fun e he => (mem_powersetCard.1 (h1 he)).1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨fun e he => mem_powersetCard.2 ⟨h1 e he, h3.1 e he⟩, h2, h3, h4, h5⟩

theorem free_union_lt {U : Finset ℕ} {ρ τ c : Finset (Finset ℕ)} (hc : c ∈ qcovers q U ρ τ) :
    (free U (ρ ∪ c)).card < (free U ρ).card := by
  obtain ⟨hsub, ⟨e, he⟩, -, -, htouch⟩ := mem_qcovers.1 hc
  obtain ⟨x, hxe, -⟩ := not_disjoint_iff.1 (htouch e he)
  apply card_lt_card
  rw [free_union]
  refine ⟨sdiff_subset, fun h => ?_⟩
  have := h (hsub e he hxe)
  exact (mem_sdiff.1 this).2 (sub_cov he hxe)

/-- Canonical depth: term blocks paid along the deepest branch. -/
def cdepth (q : ℕ) (U : Finset ℕ) (D : List (Finset (Finset ℕ))) : Finset (Finset ℕ) → ℕ
  | ρ => match h : qfirst q ρ D with
    | none => 0
    | some t =>
        if hs : t ⊆ ρ then 0
        else (t \ ρ).card + (qcovers q U ρ (t \ ρ)).attach.sup fun c =>
          cdepth q U D (ρ ∪ c.1)
termination_by ρ => (free U ρ).card
decreasing_by exact free_union_lt c.2

theorem qfirst_compat {ρ : Finset (Finset ℕ)} {D : List (Finset (Finset ℕ))}
    {t : Finset (Finset ℕ)} (h : qfirst q ρ D = some t) : Compat q ρ t := by
  have := List.find?_some h
  simpa using this

theorem qfirst_mem {ρ : Finset (Finset ℕ)} {D : List (Finset (Finset ℕ))} {t : Finset (Finset ℕ)}
    (h : qfirst q ρ D = some t) : t ∈ D :=
  List.mem_of_find?_eq_some h

theorem qfirst_none {ρ : Finset (Finset ℕ)} {D : List (Finset (Finset ℕ))}
    (h : qfirst q ρ D = none) : ∀ t ∈ D, ¬ Compat q ρ t := by
  intro t ht hc
  have := List.find?_eq_none.1 h t ht
  simp_all

theorem compat_mono {A B A' B' : Finset (Finset ℕ)} (h : Compat q A B) (hA : A' ⊆ A)
    (hB : B' ⊆ B) : Compat q A' B' :=
  pp_mono h (union_subset_union hA hB)

theorem qfirst_ext {ρ ρ' : Finset (Finset ℕ)} {D : List (Finset (Finset ℕ))}
    {t : Finset (Finset ℕ)} (h : qfirst q ρ D = some t) (hsub : ρ ⊆ ρ')
    (hc : Compat q ρ' t) : qfirst q ρ' D = some t := by
  unfold qfirst at h ⊢
  rw [List.find?_eq_some_iff_append] at h ⊢
  obtain ⟨_, as, bs, hF, has⟩ := h
  refine ⟨by simpa using hc, as, bs, hF, fun a ha => ?_⟩
  have := has a ha
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this ⊢
  exact fun h' => this (compat_mono h' hsub subset_rfl)

theorem cdepth_none {U : Finset ℕ} {D : List (Finset (Finset ℕ))} {ρ : Finset (Finset ℕ)}
    (h : qfirst q ρ D = none) : cdepth q U D ρ = 0 := by
  rw [cdepth]; split <;> simp_all

theorem cdepth_some {U : Finset ℕ} {D : List (Finset (Finset ℕ))} {ρ t : Finset (Finset ℕ)}
    (h : qfirst q ρ D = some t) :
    cdepth q U D ρ = if t ⊆ ρ then 0 else (t \ ρ).card +
      (qcovers q U ρ (t \ ρ)).attach.sup fun c => cdepth q U D (ρ ∪ c.1) := by
  rw [cdepth]; split
  · simp_all
  · rename_i t' h'
    rw [h] at h'; cases h'
    by_cases hs : t ⊆ ρ <;> simp [hs]

theorem le_cdepth_cover {U : Finset ℕ} {D : List (Finset (Finset ℕ))} {ρ t c : Finset (Finset ℕ)}
    (h : qfirst q ρ D = some t) (hs : ¬ t ⊆ ρ) (hc : c ∈ qcovers q U ρ (t \ ρ)) :
    (t \ ρ).card + cdepth q U D (ρ ∪ c) ≤ cdepth q U D ρ := by
  rw [cdepth_some h, if_neg hs]
  exact Nat.add_le_add_left (le_sup (f := fun c : {x // x ∈ qcovers q U ρ (t \ ρ)} =>
    cdepth q U D (ρ ∪ c.1)) (mem_attach _ ⟨c, hc⟩)) _

/-! ## Cardinalities -/

theorem card_cov {E : Finset (Finset ℕ)} (hE : PP q E) : (cov E).card = q * E.card := by
  unfold cov
  rw [card_biUnion (fun e he f hf hef => by simpa using hE.2 e he f hf hef)]
  simp only [id]
  rw [sum_congr rfl fun e he => hE.1 e he, sum_const, smul_eq_mul, Nat.mul_comm]

theorem card_free {U : Finset ℕ} {E : Finset (Finset ℕ)} (hE : PP q E) (hEU : InU U E) :
    (free U E).card = U.card - q * E.card := by
  rw [free, card_sdiff_of_subset (fun x hx => by
    obtain ⟨e, he, hxe⟩ := mem_cov.1 hx; exact hEU e he hxe), card_cov hE]

/-- A cover has at least as many blocks as the covered partial partition. -/
theorem card_le_cover {U : Finset ℕ} {ρ τ c : Finset (Finset ℕ)} (hq : 1 ≤ q) (hτ : PP q τ)
    (hc : c ∈ qcovers q U ρ τ) : τ.card ≤ c.card := by
  obtain ⟨-, -, hcp, hcov, -⟩ := mem_qcovers.1 hc
  have := card_le_card hcov
  rw [card_cov hτ, card_cov hcp] at this
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- ... and at most as many blocks as the covered points. -/
theorem card_cover_le {U : Finset ℕ} {ρ τ c : Finset (Finset ℕ)} (hc : c ∈ qcovers q U ρ τ) :
    c.card ≤ (cov τ).card := by
  obtain ⟨-, -, hcp, -, htouch⟩ := mem_qcovers.1 hc
  have : ∀ e ∈ c, ∃ x ∈ cov τ, x ∈ e := fun e he => by
    obtain ⟨x, h1, h2⟩ := not_disjoint_iff.1 (htouch e he); exact ⟨x, h2, h1⟩
  choose f hf1 hf2 using this
  refine card_le_card_of_injOn (fun e => if h : e ∈ c then f e h else 0) (fun e he => ?_)
    (fun e he e' he' hee => ?_)
  · simp only [dif_pos (mem_coe.1 he)]; exact hf1 e he
  · simp only [dif_pos (mem_coe.1 he), dif_pos (mem_coe.1 he')] at hee
    exact pp_eq_of_mem hcp he he' (hf2 e he) (hee ▸ hf2 e' he')

/-! ## Positions inside a term -/

def qpos (t : Finset (Finset ℕ)) (e : Finset ℕ) : ℕ := t.toList.idxOf e

def qat (t : Finset (Finset ℕ)) (p : ℕ) : Finset ℕ := t.toList.getD p ∅

theorem qpos_lt {t : Finset (Finset ℕ)} {e : Finset ℕ} (h : e ∈ t) : qpos t e < t.card := by
  unfold qpos; rw [← length_toList]
  exact List.idxOf_lt_length_of_mem (mem_toList.2 h)

theorem qat_qpos {t : Finset (Finset ℕ)} {e : Finset ℕ} (h : e ∈ t) : qat t (qpos t e) = e := by
  unfold qat qpos
  exact getD_idxOf (mem_toList.2 h)

theorem qpos_inj {t : Finset (Finset ℕ)} {e f : Finset ℕ} (he : e ∈ t) (hf : f ∈ t)
    (h : qpos t e = qpos t f) : e = f := by
  rw [← qat_qpos he, ← qat_qpos hf, h]

/-- Blocks of `t` at the positions `β`. -/
def qsel (t : Finset (Finset ℕ)) (β : Finset ℕ) : Finset (Finset ℕ) :=
  t.filter fun e => qpos t e ∈ β

/-- Positions of the blocks of `τ` inside `t`. -/
def qposOf (t τ : Finset (Finset ℕ)) : Finset ℕ := τ.image (qpos t)

theorem qsel_qposOf {t τ : Finset (Finset ℕ)} (h : τ ⊆ t) : qsel t (qposOf t τ) = τ := by
  ext e
  simp only [qsel, qposOf, mem_filter, mem_image]
  constructor
  · rintro ⟨het, f, hf, hfe⟩; rwa [← qpos_inj (h hf) het hfe]
  · intro he; exact ⟨h he, e, he, rfl⟩

theorem qposOf_card {t τ : Finset (Finset ℕ)} (h : τ ⊆ t) : (qposOf t τ).card = τ.card :=
  card_image_of_injOn fun e he f hf hef => qpos_inj (h he) (h hf) hef

theorem qposOf_sub {t τ : Finset (Finset ℕ)} {w : ℕ} (h : τ ⊆ t) (hw : t.card ≤ w) :
    qposOf t τ ⊆ range w := by
  intro p hp
  obtain ⟨e, he, rfl⟩ := mem_image.1 hp
  exact mem_range.2 (lt_of_lt_of_le (qpos_lt (h he)) hw)

/-! ## Cover codes -/

/-- Reference points: the term points and the free points of the extension. -/
def refL (U : Finset ℕ) (ρ' τ : Finset (Finset ℕ)) : List ℕ := (cov τ ∪ free U ρ').sort (· ≤ ·)

/-- The block of `c` through `x`. -/
def blockOf (c : Finset (Finset ℕ)) (x : ℕ) : Finset ℕ :=
  if h : ∃ b ∈ c, x ∈ b then Classical.choose h else ∅

/-- The `r`-th point of a block. -/
def ptAt (b : Finset ℕ) (r : ℕ) : ℕ := (b.sort (· ≤ ·)).getD r 0

theorem blockOf_spec {c : Finset (Finset ℕ)} {x : ℕ} (h : x ∈ cov c) :
    blockOf c x ∈ c ∧ x ∈ blockOf c x := by
  have hh : ∃ b ∈ c, x ∈ b := mem_cov.1 h
  unfold blockOf; rw [dif_pos hh]
  exact Classical.choose_spec hh

theorem blockOf_eq {c : Finset (Finset ℕ)} (hc : PP q c) {b : Finset ℕ} (hb : b ∈ c) {x : ℕ}
    (hx : x ∈ b) : blockOf c x = b := by
  have := blockOf_spec (mem_cov.2 ⟨b, hb, hx⟩)
  exact pp_eq_of_mem hc this.1 hb this.2 hx

theorem ptAt_mem {b : Finset ℕ} {r : ℕ} (hr : r < b.card) : ptAt b r ∈ b := by
  unfold ptAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [length_sort]; exact hr),
    Option.getD_some]
  exact (mem_sort _).1 (List.getElem_mem _)

theorem ptAt_idx {b : Finset ℕ} {x : ℕ} (hx : x ∈ b) :
    ptAt b ((b.sort (· ≤ ·)).idxOf x) = x ∧ (b.sort (· ≤ ·)).idxOf x < b.card := by
  have hm : x ∈ b.sort (· ≤ ·) := (mem_sort _).2 hx
  refine ⟨getD_idxOf hm, ?_⟩
  rw [← length_sort (· ≤ ·)]
  exact List.idxOf_lt_length_of_mem hm

/-- The code of a cover: for each position and each point of the term block there, the cover
block through the point as indices into the reference points. -/
def encC (q : ℕ) (U : Finset ℕ) (ρ' t τ c : Finset (Finset ℕ)) : ℕ → ℕ → Finset ℕ :=
  fun p r => if p ∈ qposOf t τ ∧ r < q then
    (blockOf c (ptAt (qat t p) r)).image fun x => (refL U ρ' τ).idxOf x else ∅

/-- Decoding a cover. -/
def decC (q : ℕ) (U : Finset ℕ) (ρ' t : Finset (Finset ℕ)) (β : Finset ℕ)
    (γ : ℕ → ℕ → Finset ℕ) : Finset (Finset ℕ) :=
  (β ×ˢ range q).image fun pr => (γ pr.1 pr.2).image fun i => (refL U ρ' (qsel t β)).getD i 0

/-- A cover of `τ` whose points outside `τ` are free in `ρ'`. -/
structure GoodC (q : ℕ) (U : Finset ℕ) (τ c ρ' : Finset (Finset ℕ)) : Prop where
  pp : PP q c
  covers : cov τ ⊆ cov c
  touch : ∀ b ∈ c, ¬ Disjoint b (cov τ)
  inside : ∀ b ∈ c, b ⊆ cov τ ∪ free U ρ'

theorem mem_refL {U : Finset ℕ} {ρ' τ : Finset (Finset ℕ)} {x : ℕ} :
    x ∈ refL U ρ' τ ↔ x ∈ cov τ ∪ free U ρ' := mem_sort _

theorem decC_encC {U : Finset ℕ} {ρ' t τ c : Finset (Finset ℕ)} (hτt : τ ⊆ t) (hτ : PP q τ)
    (hg : GoodC q U τ c ρ') : decC q U ρ' t (qposOf t τ) (encC q U ρ' t τ c) = c := by
  have hsel := qsel_qposOf hτt
  have hround : ∀ b ∈ c, (b.image fun x => (refL U ρ' τ).idxOf x).image
      (fun i => (refL U ρ' τ).getD i 0) = b := by
    intro b hb
    rw [image_image]
    conv_rhs => rw [← image_id (s := b)]
    refine image_congr fun x hx => ?_
    exact getD_idxOf (mem_refL.2 (hg.inside b hb hx))
  ext b
  simp only [decC, hsel, mem_image, mem_product, mem_range]
  constructor
  · rintro ⟨⟨p, r⟩, ⟨hp, hr⟩, rfl⟩
    simp only at hp hr ⊢
    obtain ⟨b', hb', rfl⟩ := mem_image.1 hp
    have hx : ptAt (qat t (qpos t b')) r ∈ cov τ := by
      rw [qat_qpos (hτt hb')]
      exact sub_cov hb' (ptAt_mem (by rw [hτ.1 b' hb']; exact hr))
    have hb0 := blockOf_spec (hg.covers hx)
    simp only [encC, if_pos (show qpos t b' ∈ qposOf t τ ∧ r < q from ⟨hp, hr⟩)]
    rw [hround _ hb0.1]; exact hb0.1
  · intro hb
    obtain ⟨x, hxb, hxτ⟩ := not_disjoint_iff.1 (hg.touch b hb)
    obtain ⟨b', hb', hxb'⟩ := mem_cov.1 hxτ
    obtain ⟨hpt, hlt⟩ := ptAt_idx hxb'
    refine ⟨(qpos t b', (b'.sort (· ≤ ·)).idxOf x), ⟨mem_image.2 ⟨b', hb', rfl⟩,
      by rw [← hτ.1 b' hb']; exact hlt⟩, ?_⟩
    simp only [encC, if_pos (show qpos t b' ∈ qposOf t τ ∧ _ < q from
      ⟨mem_image.2 ⟨b', hb', rfl⟩, by rw [← hτ.1 b' hb']; exact hlt⟩), qat_qpos (hτt hb'), hpt,
      blockOf_eq hg.pp hb hxb]
    exact hround b hb

/-! ## Codes -/

/-- Cover codes for the positions `β`, index sets below `C`, normalized outside `β`. -/
def gcodesQ (q : ℕ) (β : Finset ℕ) (C : ℕ) : Finset (ℕ → ℕ → Finset ℕ) :=
  ((β ×ˢ range q).pi fun _ => (range C).powersetCard q).image fun f p r =>
    if h : (p, r) ∈ β ×ˢ range q then f (p, r) h else ∅

theorem gcodesQ_card (β : Finset ℕ) (C : ℕ) :
    (gcodesQ q β C).card ≤ (C ^ (q * q)) ^ β.card := by
  refine card_image_le.trans ?_
  rw [card_pi, prod_const, card_powersetCard, card_range, card_product, card_range]
  calc C.choose q ^ (β.card * q) ≤ (C ^ q) ^ (β.card * q) :=
        Nat.pow_le_pow_left (Nat.choose_le_pow _ _) _
    _ = _ := by rw [← pow_mul, ← pow_mul]; ring_nf

theorem mem_gcodesQ {β : Finset ℕ} {C : ℕ} {γ : ℕ → ℕ → Finset ℕ}
    (h0 : ∀ p r, ¬ (p ∈ β ∧ r < q) → γ p r = ∅)
    (hC : ∀ p ∈ β, ∀ r < q, γ p r ∈ (range C).powersetCard q) : γ ∈ gcodesQ q β C := by
  refine mem_image.2 ⟨fun pr _ => γ pr.1 pr.2, mem_pi.2 fun pr hpr => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := mem_product.1 hpr
    exact hC pr.1 h1 pr.2 (mem_range.1 h2)
  · funext p r
    by_cases h : (p, r) ∈ β ×ˢ range q
    · rw [dif_pos h]
    · rw [dif_neg h, h0 p r (fun h' => h (mem_product.2 ⟨h'.1, mem_range.2 h'.2⟩))]

abbrev QCode := List (Finset ℕ × (ℕ → ℕ → Finset ℕ))

/-- Codes for depth `s`. -/
def qcodes (q w C : ℕ) : ℕ → Finset QCode
  | 0 => {[]}
  | s + 1 => (range (s + 1)).biUnion fun m =>
      ((range w).powersetCard (m + 1)).biUnion fun β =>
        (gcodesQ q β C).biUnion fun γ => (qcodes q w C (s - m)).image (List.cons (β, γ))
termination_by s => s
decreasing_by omega

theorem qcodes_ne_nil {w C s : ℕ} {c : QCode} (h : c ∈ qcodes q w C (s + 1)) : c ≠ [] := by
  rw [qcodes] at h
  simp only [mem_biUnion, mem_image] at h
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := h
  simp

theorem qcodes_card (w C s : ℕ) : (qcodes q w C s).card ≤ (2 * (w * C ^ (q * q))) ^ s := by
  set Y := w * C ^ (q * q)
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  cases s with
  | zero => simp [qcodes]
  | succ s =>
    rw [qcodes]
    calc _ ≤ ∑ m ∈ range (s + 1), Y ^ (m + 1) * (2 * Y) ^ (s - m) := by
          refine card_biUnion_le.trans (sum_le_sum fun m hm => ?_)
          refine card_biUnion_le.trans ?_
          calc _ ≤ ∑ β ∈ (range w).powersetCard (m + 1),
                  (C ^ (q * q)) ^ (m + 1) * (2 * Y) ^ (s - m) := by
                refine sum_le_sum fun β hβ => ?_
                refine card_biUnion_le.trans ?_
                have hβc := (mem_powersetCard.1 hβ).2
                calc _ ≤ ∑ γ ∈ gcodesQ q β C, (2 * Y) ^ (s - m) :=
                      sum_le_sum fun γ _ => card_image_le.trans (ih _ (by omega))
                  _ = (gcodesQ q β C).card * (2 * Y) ^ (s - m) := by rw [sum_const, smul_eq_mul]
                  _ ≤ _ := Nat.mul_le_mul_right _ (hβc ▸ gcodesQ_card β C)
            _ = w.choose (m + 1) * ((C ^ (q * q)) ^ (m + 1) * (2 * Y) ^ (s - m)) := by
                rw [sum_const, card_powersetCard, card_range, smul_eq_mul]
            _ ≤ w ^ (m + 1) * ((C ^ (q * q)) ^ (m + 1) * (2 * Y) ^ (s - m)) :=
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

/-- Decoding. The last round only removes its term blocks; earlier rounds swap their term blocks
for the decoded cover, decode the rest, and remove the cover. -/
def qdec (q : ℕ) (U : Finset ℕ) (D : List (Finset (Finset ℕ))) :
    Finset (Finset ℕ) → QCode → Finset (Finset ℕ)
  | ρ', [] => ρ'
  | ρ', [(β, _)] => match qfirst q ρ' D with
    | none => ρ'
    | some t => ρ' \ qsel t β
  | ρ', (β, γ) :: c => match qfirst q ρ' D with
    | none => ρ'
    | some t => (qdec q U D ((ρ' \ qsel t β) ∪ decC q U ρ' t β γ) c) \ decC q U ρ' t β γ

/-! ## Partial partitions -/

theorem pp_union {E F : Finset (Finset ℕ)} (hE : PP q E) (hF : PP q F)
    (h : ∀ e ∈ E, ∀ f ∈ F, e ≠ f → Disjoint e f) : PP q (E ∪ F) := by
  refine ⟨fun e he => ?_, fun e he f hf hef => ?_⟩
  · rcases mem_union.1 he with he | he
    · exact hE.1 e he
    · exact hF.1 e he
  · rcases mem_union.1 he with he | he <;> rcases mem_union.1 hf with hf | hf
    · exact hE.2 e he f hf hef
    · exact h e he f hf hef
    · exact (h f hf e he (Ne.symm hef)).symm
    · exact hF.2 e he f hf hef

theorem blocks_free_of_compat {U : Finset ℕ} {ρ t : Finset (Finset ℕ)} (hc : Compat q ρ t)
    (htU : InU U t) : ∀ b ∈ t \ ρ, b ⊆ free U ρ := by
  intro b hb x hx
  obtain ⟨hbt, hbρ⟩ := mem_sdiff.1 hb
  refine mem_sdiff.2 ⟨htU b hbt hx, fun hxρ => ?_⟩
  obtain ⟨f, hf, hxf⟩ := mem_cov.1 hxρ
  have := pp_eq_of_mem hc (mem_union.2 (Or.inr hbt)) (mem_union.2 (Or.inl hf)) hx hxf
  exact hbρ (this ▸ hf)

theorem disj_free_blocks {U : Finset ℕ} {ρ : Finset (Finset ℕ)} {e : Finset ℕ}
    (he : e ⊆ free U ρ) : ∀ f ∈ ρ, Disjoint e f := by
  intro f hf
  exact disjoint_left.2 fun x hxe hxf => (mem_sdiff.1 (he hxe)).2 (sub_cov hf hxf)

theorem notMem_of_free {U : Finset ℕ} {ρ : Finset (Finset ℕ)} {e : Finset ℕ}
    (he : e ⊆ free U ρ) (hne : e.Nonempty) : e ∉ ρ := by
  intro h
  obtain ⟨x, hx⟩ := hne
  exact (mem_sdiff.1 (he hx)).2 (sub_cov h hx)

/-- New blocks of an extension avoid the points of the old ones. -/
theorem disj_ext {A B : Finset (Finset ℕ)} (hB : PP q B) (hAB : A ⊆ B) :
    ∀ e ∈ B \ A, ∀ f ∈ A, Disjoint e f := by
  intro e he f hf
  obtain ⟨heB, heA⟩ := mem_sdiff.1 he
  exact hB.2 e heB f (hAB hf) (fun h => heA (h ▸ hf))

theorem disj_ext_cov {A B : Finset (Finset ℕ)} (hB : PP q B) (hAB : A ⊆ B) :
    ∀ e ∈ B \ A, Disjoint e (cov A) := by
  intro e he
  refine disjoint_left.2 fun x hxe hxA => ?_
  obtain ⟨f, hf, hxf⟩ := mem_cov.1 hxA
  exact disjoint_left.1 (disj_ext hB hAB e he f hf) hxe hxf

/-! ## The encoding lemma -/

theorem qencode {U : Finset ℕ} {D : List (Finset (Finset ℕ))} (hU : ∀ t ∈ D, InU U t) {w : ℕ}
    (hw : ∀ t ∈ D, t.card ≤ w) (hq : 1 ≤ q) :
    ∀ s (ρ : Finset (Finset ℕ)), PP q ρ → InU U ρ → s ≤ cdepth q U D ρ →
    ∃ ρ' c, PP q ρ' ∧ InU U ρ' ∧ ρ ⊆ ρ' ∧ ρ'.card = ρ.card + s ∧
      (∀ C, q * w + (free U ρ').card ≤ C → c ∈ qcodes q w C s) ∧ qdec q U D ρ' c = ρ := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro ρ hρ hρU hs
  cases s with
  | zero => exact ⟨ρ, [], hρ, hρU, subset_rfl, rfl, fun C _ => by simp [qcodes], rfl⟩
  | succ s =>
  cases hF : qfirst q ρ D with
  | none => rw [cdepth_none hF] at hs; omega
  | some t =>
  have htD := qfirst_mem hF
  have hct := qfirst_compat hF
  have hts : ¬ t ⊆ ρ := by
    intro h; rw [cdepth_some hF, if_pos h] at hs; omega
  have htw := hw t htD
  have htp : PP q t := pp_mono hct subset_union_right
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = t \ ρ := ⟨_, rfl⟩
  have hτf : ∀ b ∈ τ, b ⊆ free U ρ := hτdef ▸ blocks_free_of_compat hct (hU t htD)
  have hτt : τ ⊆ t := hτdef ▸ sdiff_subset
  have hτp : PP q τ := pp_mono htp hτt
  have hτρ : ∀ e ∈ τ, e ∉ ρ := fun e he => (mem_sdiff.1 (hτdef ▸ he)).2
  have hdepth := cdepth_some (U := U) hF
  rw [if_neg hts, ← hτdef] at hdepth
  rw [hdepth] at hs
  have hτne : τ.Nonempty := by
    obtain ⟨e, he⟩ := not_subset.1 hts; exact ⟨e, hτdef ▸ mem_sdiff.2 he⟩
  have hw1 : 1 ≤ w := by have := card_le_card hτt; have := hτne.card_pos; omega
  by_cases hA : s + 1 ≤ τ.card
  · obtain ⟨τ', hτ'τ, hτ'c⟩ := exists_subset_card_eq hA
    have hτ't : τ' ⊆ t := hτ'τ.trans hτt
    have hρ'p : PP q (ρ ∪ τ') := pp_mono hct (union_subset_union subset_rfl hτ't)
    have hdisj : Disjoint ρ τ' := disjoint_left.2 fun e he he' => hτρ e (hτ'τ he') he
    let γ0 : ℕ → ℕ → Finset ℕ := fun p r => if p ∈ qposOf t τ' ∧ r < q then range q else ∅
    refine ⟨ρ ∪ τ', [(qposOf t τ', γ0)], hρ'p,
      fun e he => by
        rcases mem_union.1 he with he | he
        · exact hρU e he
        · exact (hτf e (hτ'τ he)).trans sdiff_subset,
      subset_union_left, by rw [card_union_of_disjoint hdisj, hτ'c], ?_, ?_⟩
    · intro C hC
      rw [qcodes]
      simp only [mem_biUnion, mem_range, mem_powersetCard, mem_image]
      refine ⟨s, by omega, qposOf t τ', ⟨qposOf_sub hτ't htw, by rw [qposOf_card hτ't, hτ'c]⟩,
        γ0, mem_gcodesQ (fun p r h => by simp only [γ0]; rw [if_neg h]) (fun p hp r hr => ?_),
        [], ?_, rfl⟩
      · simp only [γ0]; rw [if_pos ⟨hp, hr⟩]
        refine mem_powersetCard.2 ⟨range_subset.2 ?_, card_range q⟩
        have : q * 1 ≤ q * w := Nat.mul_le_mul_left _ hw1
        rw [mul_one] at this
        have hqC := le_trans this (le_trans (Nat.le_add_right _ _) hC)
        exact fun x hx => mem_range.2 (by omega)
      · rw [Nat.sub_self]; simp [qcodes]
    · have hc' : Compat q (ρ ∪ τ') t := by
        refine pp_mono hct ?_
        intro e he
        simp only [mem_union] at he ⊢
        rcases he with (he | he) | he
        · exact Or.inl he
        · exact Or.inr (hτ't he)
        · exact Or.inr he
      have hfl := qfirst_ext hF subset_union_left hc'
      simp only [qdec, hfl, qsel_qposOf hτ't]
      rw [union_sdiff_right, sdiff_eq_self_of_disjoint hdisj]
  · push Not at hA
    obtain ⟨m, hm⟩ : ∃ m, τ.card = m + 1 := ⟨τ.card - 1, by have := hτne.card_pos; omega⟩
    have hsup := Nat.sub_le_iff_le_add'.2 hs
    have hsup' := le_trans (show s - m ≤ s + 1 - τ.card by omega) hsup
    obtain ⟨⟨c1, hc1⟩, -, hc1d⟩ := (Finset.le_sup_iff (by simp; omega)).1 hsup'
    simp only at hc1d
    obtain ⟨hc1f, hc1ne, hc1p, hc1cov, hc1touch⟩ := mem_qcovers.1 hc1
    have hc1nonempty : ∀ e ∈ c1, e.Nonempty := fun e he => by
      obtain ⟨x, hx, -⟩ := not_disjoint_iff.1 (hc1touch e he); exact ⟨x, hx⟩
    have hρ1p : PP q (ρ ∪ c1) := pp_union hρ hc1p fun e he f hf _ =>
      (disj_free_blocks (hc1f f hf) e he).symm
    have hρ1U : InU U (ρ ∪ c1) := fun e he => by
      rcases mem_union.1 he with he | he
      · exact hρU e he
      · exact (hc1f e he).trans sdiff_subset
    obtain ⟨ρ1', cc, h1p, h1U, h1sub, h1card, h1codes, h1dec⟩ :=
      ih (s - m) (by omega) (ρ ∪ c1) hρ1p hρ1U hc1d
    have hcne : cc ≠ [] := by
      have := h1codes (q * w + (free U ρ1').card) le_rfl
      rw [show s - m = (s - m - 1) + 1 by omega] at this
      exact qcodes_ne_nil this
    obtain ⟨x, cc', rfl⟩ := List.exists_cons_of_ne_nil hcne
    have hcρ : ∀ e ∈ c1, e ∉ ρ := fun e he => notMem_of_free (hc1f e he) (hc1nonempty e he)
    have hdisjρc : Disjoint ρ c1 := disjoint_left.2 fun e he he' => hcρ e he' he
    have hc1sub : c1 ⊆ ρ1' := subset_union_right.trans h1sub
    have hρsub : ρ ⊆ ρ1' := subset_union_left.trans h1sub
    have F1 := disj_ext_cov h1p h1sub
    have hτnon : ∀ e ∈ τ, e.Nonempty := fun e he => by
      rw [← card_pos, hτp.1 e he]; omega
    -- new blocks avoid the term
    have hX : PP q ((ρ1' \ c1) ∪ t) := by
      refine pp_union (pp_mono h1p sdiff_subset) htp fun e he f hf hef => ?_
      obtain ⟨he1, hec⟩ := mem_sdiff.1 he
      by_cases heρ : e ∈ ρ
      · exact hct.2 e (mem_union.2 (Or.inl heρ)) f (mem_union.2 (Or.inr hf)) hef
      · have heN : e ∈ ρ1' \ (ρ ∪ c1) := mem_sdiff.2 ⟨he1, by simp [heρ, hec]⟩
        by_cases hfρ : f ∈ ρ
        · exact disjoint_left.2 fun y hye hyf =>
            disjoint_left.1 (F1 e heN) hye (sub_cov (mem_union.2 (Or.inl hfρ)) hyf)
        · have hfτ : f ∈ τ := hτdef ▸ mem_sdiff.2 ⟨hf, hfρ⟩
          exact disjoint_left.2 fun y hye hyf =>
            disjoint_left.1 (F1 e heN) hye (by
              rw [cov_union]; exact mem_union.2 (Or.inr (hc1cov (sub_cov hfτ hyf))))
    have F3 : ∀ e ∈ τ, e ∉ ρ1' \ c1 := by
      intro e he he'
      obtain ⟨he1, hec⟩ := mem_sdiff.1 he'
      have heN : e ∈ ρ1' \ (ρ ∪ c1) := mem_sdiff.2 ⟨he1, by simp [hτρ e he, hec]⟩
      obtain ⟨y, hy⟩ := hτnon e he
      exact disjoint_left.1 (F1 e heN) hy (by
        rw [cov_union]; exact mem_union.2 (Or.inr (hc1cov (sub_cov he hy))))
    set ρ' := (ρ1' \ c1) ∪ τ with hρ'def
    have hρ'p : PP q ρ' := pp_mono hX (union_subset_union subset_rfl hτt)
    have hρ'U : InU U ρ' := by
      intro e he
      rcases mem_union.1 he with he | he
      · exact h1U e (mem_sdiff.1 he).1
      · exact (hτf e he).trans sdiff_subset
    have hρρ' : ρ ⊆ ρ' := fun e he =>
      mem_union.2 (Or.inl (mem_sdiff.2 ⟨hρsub he, fun h => hcρ e h he⟩))
    have hcardρ1 : (ρ ∪ c1).card = ρ.card + c1.card := card_union_of_disjoint hdisjρc
    have hc1τ : τ.card ≤ c1.card := card_le_cover hq hτp hc1
    have hcard' : ρ'.card = ρ.card + (s + 1) := by
      rw [hρ'def, card_union_of_disjoint (disjoint_left.2 fun e he he' => F3 e he' he),
        card_sdiff_of_subset hc1sub, h1card, hcardρ1]
      omega
    have hgood : GoodC q U τ c1 ρ' := by
      refine ⟨hc1p, hc1cov, hc1touch, fun b hb y hy => ?_⟩
      by_cases hyτ : y ∈ cov τ
      · exact mem_union.2 (Or.inl hyτ)
      · refine mem_union.2 (Or.inr (mem_sdiff.2 ⟨(mem_sdiff.1 (hc1f b hb hy)).1, fun hyρ' => ?_⟩))
        obtain ⟨f, hf, hyf⟩ := mem_cov.1 hyρ'
        rcases mem_union.1 hf with hf | hf
        · obtain ⟨hf1, hfc⟩ := mem_sdiff.1 hf
          by_cases hfρ : f ∈ ρ
          · exact (mem_sdiff.1 (hc1f b hb hy)).2 (sub_cov hfρ hyf)
          · have hfN : f ∈ ρ1' \ (ρ ∪ c1) := mem_sdiff.2 ⟨hf1, by simp [hfρ, hfc]⟩
            exact disjoint_left.1 (F1 f hfN) hyf (by
              rw [cov_union]; exact mem_union.2 (Or.inr (sub_cov hb hy)))
        · exact hyτ (sub_cov hf hyf)
    have hfreeρ' := card_free hρ'p hρ'U
    have hfreeρ1 := card_free h1p h1U
    refine ⟨ρ', (qposOf t τ, encC q U ρ' t τ c1) :: x :: cc', hρ'p, hρ'U, hρρ', hcard', ?_, ?_⟩
    · intro C hC
      rw [qcodes]
      simp only [mem_biUnion, mem_range, mem_powersetCard, mem_image]
      refine ⟨m, by omega, qposOf t τ, ⟨qposOf_sub hτt htw, by rw [qposOf_card hτt, hm]⟩,
        encC q U ρ' t τ c1, ?_, x :: cc', ?_, rfl⟩
      · refine mem_gcodesQ (fun p r h => by simp only [encC]; rw [if_neg h]) fun p hp r hr => ?_
        simp only [encC, if_pos (show p ∈ qposOf t τ ∧ r < q from ⟨hp, hr⟩)]
        obtain ⟨b', hb', rfl⟩ := mem_image.1 hp
        have hy : ptAt (qat t (qpos t b')) r ∈ cov τ := by
          rw [qat_qpos (hτt hb')]
          exact sub_cov hb' (ptAt_mem (by rw [hτp.1 b' hb']; exact hr))
        obtain ⟨hb0, -⟩ := blockOf_spec (hc1cov hy)
        set b0 := blockOf c1 (ptAt (qat t (qpos t b')) r)
        have hb0R : ∀ z ∈ b0, z ∈ refL U ρ' τ := fun z hz => mem_refL.2 (hgood.inside b0 hb0 hz)
        have hRlen : (refL U ρ' τ).length ≤ q * w + (free U ρ').card := by
          rw [refL, length_sort]
          refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
          rw [card_cov hτp]
          exact Nat.mul_le_mul_left _ ((card_le_card hτt).trans htw)
        refine mem_powersetCard.2 ⟨fun i hi => ?_, ?_⟩
        · obtain ⟨z, hz, rfl⟩ := mem_image.1 hi
          exact mem_range.2 (lt_of_lt_of_le (List.idxOf_lt_length_of_mem (hb0R z hz))
            (hRlen.trans hC))
        · rw [card_image_of_injOn, hc1p.1 b0 hb0]
          intro z hz z' hz' hzz
          rw [← getD_idxOf (d := 0) (hb0R z hz), ← getD_idxOf (d := 0) (hb0R z' hz')]
          simp only at hzz
          rw [hzz]
      · refine h1codes C ?_
        have hle : ρ'.card ≤ ρ1'.card := by rw [hcard', h1card, hcardρ1]; omega
        have : q * ρ'.card ≤ q * ρ1'.card := Nat.mul_le_mul_left _ hle
        omega
    · have hc' : Compat q ρ' t := pp_mono hX (union_subset_union
        (union_subset subset_union_left (hτt.trans subset_union_right)) subset_rfl |>.trans
          (by rw [union_assoc, union_self]))
      have hfl := qfirst_ext hF hρρ' hc'
      have hback : (ρ' \ τ) ∪ c1 = ρ1' := by
        rw [hρ'def, union_sdiff_right, sdiff_eq_self_of_disjoint
          (disjoint_left.2 fun e he he' => F3 e he' he), sdiff_union_of_subset hc1sub]
      simp only [qdec, hfl, qsel_qposOf hτt, decC_encC hτt hτp hgood, hback, h1dec]
      rw [union_sdiff_right, sdiff_eq_self_of_disjoint hdisjρc]

/-! ## The switching lemma for q-partition restrictions -/

/-- Partial q-partitions of size `m` in the universe extending `ρ0`. -/
def Rq (q : ℕ) (U : Finset ℕ) (ρ0 : Finset (Finset ℕ)) (m : ℕ) : Finset (Finset (Finset ℕ)) :=
  (U.powersetCard q).powerset.filter fun ρ => PP q ρ ∧ ρ0 ⊆ ρ ∧ ρ.card = m

theorem mem_Rq {U : Finset ℕ} {ρ0 ρ : Finset (Finset ℕ)} {m : ℕ} :
    ρ ∈ Rq q U ρ0 m ↔ InU U ρ ∧ PP q ρ ∧ ρ0 ⊆ ρ ∧ ρ.card = m := by
  simp only [Rq, mem_filter, mem_powerset]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun e he => (mem_powersetCard.1 (h1 he)).1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun e he => mem_powersetCard.2 ⟨h1 e he, h2.1 e he⟩, h2, h3, h4⟩

/-- **q-partition switching lemma** (counting form). -/
theorem qswitching {U : Finset ℕ} {D : List (Finset (Finset ℕ))} (hU : ∀ t ∈ D, InU U t)
    {w : ℕ} (hw : ∀ t ∈ D, t.card ≤ w) (hq : 1 ≤ q) (ρ0 : Finset (Finset ℕ)) (m s C : ℕ)
    (hC : q * w + (U.card - q * (m + s)) ≤ C) :
    ((Rq q U ρ0 m).filter fun ρ => s ≤ cdepth q U D ρ).card ≤
      (Rq q U ρ0 (m + s)).card * (2 * (w * C ^ (q * q))) ^ s := by
  calc _ ≤ ((Rq q U ρ0 (m + s) ×ˢ qcodes q w C s).image fun pc => qdec q U D pc.1 pc.2).card := by
        apply card_le_card
        intro ρ hρ
        obtain ⟨hρR, hs⟩ := mem_filter.1 hρ
        obtain ⟨hρU, hρp, hρ0, hρc⟩ := mem_Rq.1 hρR
        obtain ⟨ρ', c, hp', hU', hsub, hcard, hcodes, hdec⟩ := qencode hU hw hq s ρ hρp hρU hs
        refine mem_image.2 ⟨(ρ', c), mem_product.2 ⟨?_, hcodes C ?_⟩, hdec⟩
        · exact mem_Rq.2 ⟨hU', hp', hρ0.trans hsub, by rw [hcard, hρc]⟩
        · rw [card_free hp' hU', hcard, hρc]; exact hC
    _ ≤ (Rq q U ρ0 (m + s) ×ˢ qcodes q w C s).card := card_image_le
    _ ≤ _ := by rw [card_product]; exact Nat.mul_le_mul_left _ (qcodes_card w C s)

/-! ## Ratio of restriction counts (double counting) -/

theorem Rq_succ {U : Finset ℕ} {ρ0 : Finset (Finset ℕ)} (m : ℕ) :
    (Rq q U ρ0 (m + 1)).card * (m + 1 - ρ0.card) ≤
      (Rq q U ρ0 m).card * (U.card - q * m).choose q := by
  refine card_mul_le_card_mul (fun ρ' ρ => ρ ⊆ ρ') (fun ρ' hρ' => ?_) (fun ρ hρ => ?_)
  · obtain ⟨hU, hp, h0, hc⟩ := mem_Rq.1 hρ'
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
          simp only [bipartiteAbove, mem_filter]
          refine ⟨mem_Rq.2 ⟨fun f hf => hU f (mem_of_mem_erase hf), pp_mono hp (erase_subset _ _),
            fun x hx => mem_erase.2 ⟨fun h => he'.2 (h ▸ hx), h0 hx⟩, ?_⟩, erase_subset _ _⟩
          rw [card_erase_of_mem he'.1, hc]; rfl
  · obtain ⟨hU, hp, h0, hc⟩ := mem_Rq.1 hρ
    calc _ ≤ (((free U ρ).powersetCard q).image fun e => insert e ρ).card := by
          refine card_le_card fun ρ' hρ' => ?_
          simp only [bipartiteBelow, mem_filter] at hρ'
          obtain ⟨hR', hsub⟩ := hρ'
          obtain ⟨hU', hp', -, hc'⟩ := mem_Rq.1 hR'
          have hlt : ρ.card < ρ'.card := by omega
          obtain ⟨e, he, heρ⟩ := exists_mem_notMem_of_card_lt_card hlt
          have heq : ρ' = insert e ρ := by
            symm; apply eq_of_subset_of_card_le (insert_subset he hsub)
            rw [card_insert_of_notMem heρ]; omega
          refine mem_image.2 ⟨e, mem_powersetCard.2 ⟨fun x hx => mem_sdiff.2 ⟨hU' e he hx,
            fun hxρ => ?_⟩, hp'.1 e he⟩, heq.symm⟩
          obtain ⟨f, hf, hxf⟩ := mem_cov.1 hxρ
          exact disjoint_left.1 (disj_ext hp' hsub e (mem_sdiff.2 ⟨he, heρ⟩) f hf) hx hxf
      _ ≤ ((free U ρ).powersetCard q).card := card_image_le
      _ = _ := by rw [card_powersetCard, card_free hp hU, hc]

theorem Rq_add {U : Finset ℕ} {ρ0 : Finset (Finset ℕ)} (m : ℕ) : ∀ s,
    (Rq q U ρ0 (m + s)).card * (m + 1 - ρ0.card) ^ s ≤
      (Rq q U ρ0 m).card * ((U.card - q * m).choose q) ^ s := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 := Rq_succ (q := q) (U := U) (ρ0 := ρ0) (m + s)
    have hch : (U.card - q * (m + s)).choose q ≤ (U.card - q * m).choose q :=
      Nat.choose_le_choose _ (by have : q * m ≤ q * (m + s) := Nat.mul_le_mul_left _ (by omega)
                                 omega)
    calc (Rq q U ρ0 (m + (s + 1))).card * (m + 1 - ρ0.card) ^ (s + 1)
        = ((Rq q U ρ0 (m + s + 1)).card * (m + 1 - ρ0.card)) * (m + 1 - ρ0.card) ^ s := by
          rw [← add_assoc, pow_succ]; ring
      _ ≤ ((Rq q U ρ0 (m + s + 1)).card * (m + s + 1 - ρ0.card)) *
            (m + 1 - ρ0.card) ^ s := by gcongr; omega
      _ ≤ ((Rq q U ρ0 (m + s)).card * (U.card - q * (m + s)).choose q) *
            (m + 1 - ρ0.card) ^ s := Nat.mul_le_mul_right _ h1
      _ ≤ ((Rq q U ρ0 (m + s)).card * (U.card - q * m).choose q) *
            (m + 1 - ρ0.card) ^ s := by gcongr
      _ = ((Rq q U ρ0 (m + s)).card * (m + 1 - ρ0.card) ^ s) * (U.card - q * m).choose q := by
          ring
      _ ≤ ((Rq q U ρ0 m).card * ((U.card - q * m).choose q) ^ s) *
            (U.card - q * m).choose q := Nat.mul_le_mul_right _ ih
      _ = _ := by rw [pow_succ]; ring

/-- **q-partition switching lemma** (probability form, cleared of denominators): among the
partial q-partitions of size `m` extending `ρ0`, those of canonical depth at least `s` satisfy
`#bad · (m + 1 - |ρ0|)^s ≤ #R_m · (C(|U| - q m, q) · 2 w C^{q q})^s`. -/
theorem qswitching_ratio {U : Finset ℕ} {D : List (Finset (Finset ℕ))} (hU : ∀ t ∈ D, InU U t)
    {w : ℕ} (hw : ∀ t ∈ D, t.card ≤ w) (hq : 1 ≤ q) (ρ0 : Finset (Finset ℕ)) (m s C : ℕ)
    (hC : q * w + (U.card - q * (m + s)) ≤ C) :
    ((Rq q U ρ0 m).filter fun ρ => s ≤ cdepth q U D ρ).card * (m + 1 - ρ0.card) ^ s ≤
      (Rq q U ρ0 m).card * ((U.card - q * m).choose q * (2 * (w * C ^ (q * q)))) ^ s := by
  calc _ ≤ (Rq q U ρ0 (m + s)).card * (2 * (w * C ^ (q * q))) ^ s * (m + 1 - ρ0.card) ^ s :=
        Nat.mul_le_mul_right _ (qswitching hU hw hq ρ0 m s C hC)
    _ = ((Rq q U ρ0 (m + s)).card * (m + 1 - ρ0.card) ^ s) * (2 * (w * C ^ (q * q))) ^ s := by
        ring
    _ ≤ ((Rq q U ρ0 m).card * ((U.card - q * m).choose q) ^ s) * (2 * (w * C ^ (q * q))) ^ s :=
        Nat.mul_le_mul_right _ (Rq_add m s)
    _ = _ := by rw [mul_pow]; ring

end

end QP

end SATurday.ProofComplexity
