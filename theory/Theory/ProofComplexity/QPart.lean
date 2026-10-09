import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Partial q-partitions, q-decision trees and designs (Ladder Rung R4, 1D.2)

Infrastructure for the Count_q lower bound (Beame–Impagliazzo–Krajíček–Pitassi–Pudlák 1994,
Buss–Impagliazzo–Krajíček–Pudlák–Razborov–Sgall 1997).

* Partial q-partitions: finite sets of pairwise disjoint `q`-element blocks (`PP`).
* q-decision trees (`QT`): a node queries a point `v`; its children are indexed by the blocks
  containing `v` inside the current free set. Branches (`br`) are the partial partitions read
  along paths, with their leaf labels.
* Coverage: a tree of height `h` has a branch compatible with any partial partition leaving
  room (`exists_branch`); distinct branches are incompatible (`branch_incompat`).
* Designs: `s(∅) = 1` and `s(E) = Σ_{e ∋ v} s(E ∪ {e})` for `|E| < d` and `v` uncovered. The
  branches of a tree of height `≤ d - |E|` carry total design mass `s(E)` (`mass`).

LOG: R4 QPart module (q-partitions, q-decision trees, designs)
-/

namespace SATurday.ProofComplexity

namespace QP

open Finset

noncomputable section

open Classical

variable (q : ℕ)

/-- Partial q-partitions: blocks of size `q`, pairwise disjoint. -/
def PP (E : Finset (Finset ℕ)) : Prop :=
  (∀ e ∈ E, e.card = q) ∧ ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint e f

/-- Points covered. -/
def cov (E : Finset (Finset ℕ)) : Finset ℕ := E.biUnion id

/-- Compatibility: the union is a partial partition. -/
def Compat (E F : Finset (Finset ℕ)) : Prop := PP q (E ∪ F)

/-- Blocks inside `W` containing `v`. -/
def blocks (W : Finset ℕ) (v : ℕ) : Finset (Finset ℕ) := (W.powersetCard q).filter fun e => v ∈ e

/-- q-decision trees with labels in `α`. -/
inductive QT (α : Type) where
  | leaf (a : α)
  | node (v : ℕ) (ch : Finset ℕ → QT α)

variable {q}
variable {α : Type}

namespace QT

/-- Branches over the free set `W`: partial partitions read along the paths, with labels. -/
def br (q : ℕ) : QT α → Finset ℕ → Finset (Finset (Finset ℕ) × α)
  | leaf a, _ => {(∅, a)}
  | node v ch, W => (blocks q W v).biUnion fun e =>
      (br q (ch e) (W \ e)).image fun B => (insert e B.1, B.2)

/-- Well formed over `W`: every query is a free point. -/
def WF (q : ℕ) : QT α → Finset ℕ → Prop
  | leaf _, _ => True
  | node v ch, W => v ∈ W ∧ ∀ e ∈ blocks q W v, WF q (ch e) (W \ e)

/-- Height over `W`. -/
def ht (q : ℕ) : QT α → Finset ℕ → ℕ
  | leaf _, _ => 0
  | node v ch, W => ((blocks q W v).sup fun e => ht q (ch e) (W \ e)) + 1

end QT

open QT

theorem mem_blocks {W : Finset ℕ} {v : ℕ} {e : Finset ℕ} :
    e ∈ blocks q W v ↔ e ⊆ W ∧ e.card = q ∧ v ∈ e := by
  simp [blocks, mem_powersetCard, and_assoc]

theorem mem_br_node {v : ℕ} {ch : Finset ℕ → QT α} {W : Finset ℕ}
    {B : Finset (Finset ℕ) × α} :
    B ∈ br q (node v ch) W ↔ ∃ e ∈ blocks q W v, ∃ B' ∈ br q (ch e) (W \ e),
      B = (insert e B'.1, B'.2) := by
  simp only [br, mem_biUnion, mem_image]
  constructor
  · rintro ⟨e, he, B', hB', rfl⟩; exact ⟨e, he, B', hB', rfl⟩
  · rintro ⟨e, he, B', hB', rfl⟩; exact ⟨e, he, B', hB', rfl⟩

/-- Branch blocks are blocks of the free set, pairwise disjoint, at most the height many. -/
theorem br_props : ∀ (T : QT α) (W : Finset ℕ) (B : Finset (Finset ℕ) × α),
    B ∈ br q T W → PP q B.1 ∧ (∀ f ∈ B.1, f ⊆ W) ∧ B.1.card ≤ ht q T W
  | leaf a, W, B, h => by
    simp [br] at h; subst h; refine ⟨⟨by simp, by simp⟩, by simp, by simp [ht]⟩
  | node v ch, W, B, h => by
    obtain ⟨e, he, B', hB', rfl⟩ := mem_br_node.1 h
    obtain ⟨heW, hec, hve⟩ := mem_blocks.1 he
    obtain ⟨hPP, hsub, hcard⟩ := br_props (ch e) (W \ e) B' hB'
    have hnot : e ∉ B'.1 := by
      intro hm
      have := hsub e hm
      exact (mem_sdiff.1 (this hve)).2 hve
    refine ⟨⟨fun f hf => ?_, fun f hf g hg hfg => ?_⟩, fun f hf => ?_, ?_⟩
    · rcases mem_insert.1 hf with rfl | hf
      · exact hec
      · exact hPP.1 f hf
    · rcases mem_insert.1 hf with hf1 | hf1 <;> rcases mem_insert.1 hg with hg1 | hg1
      · exact absurd (hf1.trans hg1.symm) hfg
      · subst hf1
        exact disjoint_left.2 fun x hx hx' => (mem_sdiff.1 (hsub g hg1 hx')).2 hx
      · subst hg1
        exact disjoint_left.2 fun x hx hx' => (mem_sdiff.1 (hsub f hf1 hx)).2 hx'
      · exact hPP.2 f hf1 g hg1 hfg
    · rcases mem_insert.1 hf with rfl | hf
      · exact heW
      · exact (hsub f hf).trans sdiff_subset
    · rw [card_insert_of_notMem hnot]
      simp only [ht]
      exact Nat.add_le_add_right (hcard.trans (le_sup (f := fun e => ht q (ch e) (W \ e)) he)) 1

theorem ht_child {v : ℕ} {ch : Finset ℕ → QT α} {W : Finset ℕ} {e : Finset ℕ}
    (he : e ∈ blocks q W v) : ht q (ch e) (W \ e) + 1 ≤ ht q (node v ch) W := by
  simp only [ht]
  exact Nat.add_le_add_right (le_sup (f := fun e => ht q (ch e) (W \ e)) he) 1

/-! ## Weighted sums over branches -/

section WSum

variable {R : Type} [CommRing R]

/-- Sum of a weight over the branches of a tree (by recursion, so no injectivity is needed). -/
def wsum (q : ℕ) : QT α → Finset ℕ → (Finset (Finset ℕ) × α → R) → R
  | leaf a, _, w => w (∅, a)
  | node v ch, W, w => ∑ e ∈ blocks q W v, wsum q (ch e) (W \ e) fun B => w (insert e B.1, B.2)

theorem wsum_congr : ∀ (T : QT α) (W : Finset ℕ) (w w' : Finset (Finset ℕ) × α → R),
    (∀ B ∈ br q T W, w B = w' B) → wsum q T W w = wsum q T W w'
  | leaf a, W, w, w', h => by simp only [wsum]; exact h _ (by simp [br])
  | node v ch, W, w, w', h => by
    simp only [wsum]
    refine sum_congr rfl fun e he => wsum_congr (ch e) (W \ e) _ _ fun B hB => ?_
    exact h _ (mem_br_node.2 ⟨e, he, B, hB, rfl⟩)

theorem wsum_zero' : ∀ (T : QT α) (W : Finset ℕ), wsum q T W (fun _ => (0 : R)) = 0
  | leaf a, W => rfl
  | node v ch, W => by simp only [wsum]; exact sum_eq_zero fun e _ => wsum_zero' (ch e) (W \ e)

theorem wsum_zero {T : QT α} {W : Finset ℕ} {w : Finset (Finset ℕ) × α → R}
    (h : ∀ B ∈ br q T W, w B = 0) : wsum q T W w = 0 :=
  (wsum_congr T W w _ h).trans (wsum_zero' T W)

theorem wsum_sum {ι : Type} (X : Finset ι) : ∀ (T : QT α) (W : Finset ℕ)
    (f : ι → Finset (Finset ℕ) × α → R),
    wsum q T W (fun B => ∑ x ∈ X, f x B) = ∑ x ∈ X, wsum q T W (f x)
  | leaf a, W, f => rfl
  | node v ch, W, f => by
    simp only [wsum]
    rw [sum_comm]
    exact sum_congr rfl fun e _ => wsum_sum X (ch e) (W \ e) _

end WSum

/-! ## Designs and the mass lemma -/

theorem compat_iff_pp {E F : Finset (Finset ℕ)} : Compat q E F ↔ PP q (E ∪ F) := Iff.rfl

theorem mem_cov {E : Finset (Finset ℕ)} {v : ℕ} : v ∈ cov E ↔ ∃ e ∈ E, v ∈ e := by
  simp [cov]

theorem sub_cov {E : Finset (Finset ℕ)} {e : Finset ℕ} (he : e ∈ E) : e ⊆ cov E :=
  fun v hv => mem_cov.2 ⟨e, he, hv⟩

theorem cov_insert (e : Finset ℕ) (E : Finset (Finset ℕ)) : cov (insert e E) = e ∪ cov E := by
  ext v; simp [mem_cov]

theorem cov_union (E F : Finset (Finset ℕ)) : cov (E ∪ F) = cov E ∪ cov F := by
  ext v; simp only [mem_cov, mem_union]
  constructor
  · rintro ⟨e, he | he, hv⟩
    · exact Or.inl ⟨e, he, hv⟩
    · exact Or.inr ⟨e, he, hv⟩
  · rintro (⟨e, he, hv⟩ | ⟨e, he, hv⟩)
    · exact ⟨e, Or.inl he, hv⟩
    · exact ⟨e, Or.inr he, hv⟩

/-- A design of degree `D` on the universe `U` with values in `R`. -/
structure Design (q : ℕ) (R : Type) [CommRing R] (U : Finset ℕ) (D : ℕ) where
  s : Finset (Finset ℕ) → R
  empty : s ∅ = 1
  ext : ∀ E, PP q E → (∀ e ∈ E, e ⊆ U) → E.card < D → ∀ v ∈ U, v ∉ cov E →
    s E = ∑ e ∈ blocks q (U \ cov E) v, s (insert e E)

theorem pp_insert {E : Finset (Finset ℕ)} {e : Finset ℕ} (hE : PP q E) (he : e.card = q)
    (hd : Disjoint e (cov E)) : PP q (insert e E) := by
  refine ⟨fun f hf => ?_, fun f hf g hg hfg => ?_⟩
  · rcases mem_insert.1 hf with rfl | hf
    · exact he
    · exact hE.1 f hf
  · rcases mem_insert.1 hf with hf1 | hf1 <;> rcases mem_insert.1 hg with hg1 | hg1
    · exact absurd (hf1.trans hg1.symm) hfg
    · rw [hf1]; exact hd.mono_right (sub_cov hg1)
    · rw [hg1]; exact (hd.mono_right (sub_cov hf1)).symm
    · exact hE.2 f hf1 g hg1 hfg

/-- Blocks containing a common point coincide in a partial partition. -/
theorem pp_eq_of_mem {E : Finset (Finset ℕ)} (hE : PP q E) {e f : Finset ℕ} (he : e ∈ E)
    (hf : f ∈ E) {v : ℕ} (hve : v ∈ e) (hvf : v ∈ f) : e = f := by
  by_contra h
  exact disjoint_left.1 (hE.2 e he f hf h) hve hvf

section Mass

variable {R : Type} [CommRing R]

/-- **Mass lemma**: the branches of a well formed tree compatible with a partial partition `F`
carry total design mass `s F`, provided `|F|` plus the height stays within the degree. -/
theorem mass {U : Finset ℕ} {D : ℕ} (ds : Design q R U D) : ∀ (T : QT α) (W : Finset ℕ)
    (F : Finset (Finset ℕ)), WF q T W → W ⊆ U → PP q F → (∀ f ∈ F, f ⊆ U) →
    U ⊆ W ∪ cov F → (∀ f ∈ F, f ⊆ W ∨ Disjoint f W) → F.card + ht q T W ≤ D →
    wsum q T W (fun B => if Compat q F B.1 then ds.s (F ∪ B.1) else 0) = ds.s F
  | leaf a, W, F, _, _, hF, _, _, _, _ => by
    simp only [wsum, Compat, union_empty, if_pos hF]
  | node v ch, W, F, hWF, hWU, hF, hFU, hcov, hFW, hdeg => by
    obtain ⟨hvW, hch⟩ := hWF
    simp only [wsum]
    by_cases hvF : v ∈ cov F
    · obtain ⟨f, hf, hvf⟩ := mem_cov.1 hvF
      have hfW : f ⊆ W := by
        rcases hFW f hf with h | h
        · exact h
        · exact absurd hvW (disjoint_left.1 h hvf)
      have hfb : f ∈ blocks q W v := mem_blocks.2 ⟨hfW, hF.1 f hf, hvf⟩
      rw [sum_eq_single f]
      · have hht := ht_child (ch := ch) hfb
        have key := mass ds (ch f) (W \ f) F (hch f hfb) (sdiff_subset.trans hWU) hF hFU
          (fun x hx => by
            rcases mem_union.1 (hcov hx) with h | h
            · by_cases hxf : x ∈ f
              · exact mem_union.2 (Or.inr (sub_cov hf hxf))
              · exact mem_union.2 (Or.inl (mem_sdiff.2 ⟨h, hxf⟩))
            · exact mem_union.2 (Or.inr h))
          (fun g hg => by
            by_cases hgf : g = f
            · subst hgf; exact Or.inr disjoint_sdiff
            · rcases hFW g hg with h | h
              · exact Or.inl fun x hx => mem_sdiff.2 ⟨h hx,
                  fun hxf => disjoint_left.1 (hF.2 g hg f hf hgf) hx hxf⟩
              · exact Or.inr (h.mono_right sdiff_subset))
          (by omega)
        rw [← key]
        refine wsum_congr _ _ _ _ fun B _ => ?_
        have h1 : F ∪ insert f B.1 = F ∪ B.1 := by
          ext x; simp only [mem_union, mem_insert]
          constructor
          · rintro (h | rfl | h)
            · exact Or.inl h
            · exact Or.inl hf
            · exact Or.inr h
          · rintro (h | h)
            · exact Or.inl h
            · exact Or.inr (Or.inr h)
        exact if_congr (by unfold Compat; rw [h1]) (by rw [h1]) rfl
      · intro e he hef
        refine wsum_zero fun B _ => ?_
        rw [if_neg]
        intro hc
        have he' := mem_blocks.1 he
        exact hef (pp_eq_of_mem hc (mem_union.2 (Or.inr (mem_insert_self _ _)))
          (mem_union.2 (Or.inl hf)) he'.2.2 hvf)
      · intro h; exact absurd hfb h
    · -- `v` is not covered: the design condition
      have hlt : F.card < D := by
        have : 1 ≤ ht q (node v ch) W := by simp [ht]
        omega
      rw [ds.ext F hF hFU hlt v (hWU hvW) hvF]
      have hidx : blocks q (U \ cov F) v = (blocks q W v).filter fun e => Disjoint e (cov F) := by
        ext e
        simp only [mem_filter, mem_blocks]
        constructor
        · rintro ⟨hsub, hc, hv⟩
          refine ⟨⟨fun x hx => ?_, hc, hv⟩, disjoint_left.2 fun x hx => (mem_sdiff.1 (hsub hx)).2⟩
          rcases mem_union.1 (hcov (mem_sdiff.1 (hsub hx)).1) with h | h
          · exact h
          · exact absurd h (mem_sdiff.1 (hsub hx)).2
        · rintro ⟨⟨hsub, hc, hv⟩, hd⟩
          exact ⟨fun x hx => mem_sdiff.2 ⟨hWU (hsub hx), disjoint_left.1 hd hx⟩, hc, hv⟩
      rw [hidx, sum_filter]
      refine sum_congr rfl fun e he => ?_
      have he' := mem_blocks.1 he
      split_ifs with hd
      · have hht := ht_child (ch := ch) he
        have heF : e ∉ F := fun h => hvF (sub_cov h he'.2.2)
        have key := mass ds (ch e) (W \ e) (insert e F) (hch e he) (sdiff_subset.trans hWU)
          (pp_insert hF he'.2.1 hd)
          (fun g hg => by
            rcases mem_insert.1 hg with rfl | hg
            · exact he'.1.trans hWU
            · exact hFU g hg)
          (fun x hx => by
            rw [cov_insert]
            rcases mem_union.1 (hcov hx) with h | h
            · by_cases hxe : x ∈ e
              · exact mem_union.2 (Or.inr (mem_union.2 (Or.inl hxe)))
              · exact mem_union.2 (Or.inl (mem_sdiff.2 ⟨h, hxe⟩))
            · exact mem_union.2 (Or.inr (mem_union.2 (Or.inr h))))
          (fun g hg => by
            rcases mem_insert.1 hg with rfl | hg
            · exact Or.inr disjoint_sdiff
            · rcases hFW g hg with h | h
              · exact Or.inl fun x hx => mem_sdiff.2 ⟨h hx,
                  fun hxe => disjoint_left.1 hd hxe (sub_cov hg hx)⟩
              · exact Or.inr (h.mono_right sdiff_subset))
          (by rw [card_insert_of_notMem heF]; omega)
        rw [← key]
        refine wsum_congr _ _ _ _ fun B _ => ?_
        have h1 : F ∪ insert e B.1 = insert e F ∪ B.1 := by
          ext x; simp only [mem_union, mem_insert]; tauto
        exact if_congr (by unfold Compat; rw [h1]) (by rw [h1]) rfl
      · refine wsum_zero fun B _ => ?_
        rw [if_neg]
        intro hc
        obtain ⟨x, hxe, hxF⟩ := not_disjoint_iff.1 hd
        obtain ⟨g, hg, hxg⟩ := mem_cov.1 hxF
        have := pp_eq_of_mem hc (mem_union.2 (Or.inr (mem_insert_self _ _)))
          (mem_union.2 (Or.inl hg)) hxe hxg
        subst this
        exact hvF (sub_cov hg he'.2.2)

end Mass

/-! ## Padding a design by a fixed partial partition -/

section Pad

variable {R : Type} [CommRing R]

/-- Blocks of `E` either avoid the points of `α` or belong to `α`. -/
def Fits (α E : Finset (Finset ℕ)) : Prop := ∀ e ∈ E, Disjoint e (cov α) ∨ e ∈ α

/-- A design on `U \ cov α` padded by `α` to a design on `U`. -/
def pad (α : Finset (Finset ℕ)) (s : Finset (Finset ℕ) → R) (E : Finset (Finset ℕ)) : R :=
  if Fits α E then s (E \ α) else 0

theorem pad_self {α : Finset (Finset ℕ)} (s : Finset (Finset ℕ) → R) :
    pad α s α = s ∅ := by
  rw [pad, if_pos (show Fits α α from fun e he => Or.inr he), sdiff_self]; rfl

/-- The padded design. -/
def padD {U : Finset ℕ} {D : ℕ} {α : Finset (Finset ℕ)} (hα : PP q α) (hαU : ∀ a ∈ α, a ⊆ U)
    (ds : Design q R (U \ cov α) D) : Design q R U D where
  s := pad α ds.s
  empty := by
    rw [pad, if_pos (show Fits α ∅ from fun e he => by simp at he), empty_sdiff, ds.empty]
  ext := by
    intro E hE hEU hEc v hvU hvE
    by_cases hfit : Fits α E
    · simp only [pad, if_pos hfit]
      by_cases hvα : v ∈ cov α
      · obtain ⟨a, ha, hva⟩ := mem_cov.1 hvα
        have haE : a ∉ E := fun h => hvE (sub_cov h hva)
        have hab : a ∈ blocks q (U \ cov E) v := by
          refine mem_blocks.2 ⟨fun x hx => mem_sdiff.2 ⟨hαU a ha hx, fun hxE => ?_⟩, hα.1 a ha, hva⟩
          obtain ⟨e, he, hxe⟩ := mem_cov.1 hxE
          rcases hfit e he with h | h
          · exact disjoint_left.1 h hxe (sub_cov ha hx)
          · have := pp_eq_of_mem hα h ha hxe hx; subst this; exact haE he
        rw [sum_eq_single a]
        · rw [if_pos]
          · congr 1; ext x; simp only [mem_sdiff, mem_insert]
            constructor
            · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
            · rintro ⟨rfl | h1, h2⟩
              · exact absurd ha h2
              · exact ⟨h1, h2⟩
          · intro e he
            rcases mem_insert.1 he with rfl | he
            · exact Or.inr ha
            · exact hfit e he
        · intro e he hea
          rw [if_neg]
          intro hf
          rcases hf e (mem_insert_self _ _) with h | h
          · exact disjoint_left.1 h (mem_blocks.1 he).2.2 hvα
          · exact hea (pp_eq_of_mem hα h ha (mem_blocks.1 he).2.2 hva)
        · intro h; exact absurd hab h
      · -- `v` is a point of the inner universe
        have hE'pp : PP q (E \ α) :=
          ⟨fun e he => hE.1 e (mem_sdiff.1 he).1,
            fun e he f hf hef => hE.2 e (mem_sdiff.1 he).1 f (mem_sdiff.1 hf).1 hef⟩
        have hE'U : ∀ e ∈ E \ α, e ⊆ U \ cov α := by
          intro e he
          obtain ⟨heE, heα⟩ := mem_sdiff.1 he
          rcases hfit e heE with h | h
          · exact fun x hx => mem_sdiff.2 ⟨hEU e heE hx, disjoint_left.1 h hx⟩
          · exact absurd h heα
        have hcovE' : cov (E \ α) ⊆ cov E := fun x hx => by
          obtain ⟨e, he, hxe⟩ := mem_cov.1 hx; exact mem_cov.2 ⟨e, (mem_sdiff.1 he).1, hxe⟩
        rw [ds.ext (E \ α) hE'pp hE'U (lt_of_le_of_lt (card_le_card sdiff_subset) hEc) v
          (mem_sdiff.2 ⟨hvU, hvα⟩) (fun h => hvE (hcovE' h))]
        have hidx : blocks q ((U \ cov α) \ cov (E \ α)) v =
            (blocks q (U \ cov E) v).filter fun e => Disjoint e (cov α) := by
          ext e
          simp only [mem_filter, mem_blocks]
          constructor
          · rintro ⟨hsub, hc, hv⟩
            refine ⟨⟨fun x hx => ?_, hc, hv⟩, disjoint_left.2 fun x hx =>
              (mem_sdiff.1 (mem_sdiff.1 (hsub hx)).1).2⟩
            obtain ⟨hx1, hx2⟩ := mem_sdiff.1 (hsub hx)
            obtain ⟨hxU, hxα⟩ := mem_sdiff.1 hx1
            refine mem_sdiff.2 ⟨hxU, fun hxE => ?_⟩
            obtain ⟨f, hf, hxf⟩ := mem_cov.1 hxE
            by_cases hfα : f ∈ α
            · exact hxα (sub_cov hfα hxf)
            · exact hx2 (mem_cov.2 ⟨f, mem_sdiff.2 ⟨hf, hfα⟩, hxf⟩)
          · rintro ⟨⟨hsub, hc, hv⟩, hd⟩
            refine ⟨fun x hx => ?_, hc, hv⟩
            obtain ⟨hxU, hxE⟩ := mem_sdiff.1 (hsub hx)
            exact mem_sdiff.2 ⟨mem_sdiff.2 ⟨hxU, disjoint_left.1 hd hx⟩, fun h => hxE (hcovE' h)⟩
        rw [hidx, ← sum_filter_add_sum_filter_not (blocks q (U \ cov E) v)
          (fun e => Disjoint e (cov α))]
        have hz : ∑ e ∈ (blocks q (U \ cov E) v).filter (fun e => ¬ Disjoint e (cov α)),
            (if Fits α (insert e E) then ds.s (insert e E \ α) else 0) = 0 := by
          refine sum_eq_zero fun e he => ?_
          rw [if_neg]
          intro hf
          obtain ⟨he1, he2⟩ := mem_filter.1 he
          rcases hf e (mem_insert_self _ _) with h | h
          · exact he2 h
          · exact hvα (sub_cov h (mem_blocks.1 he1).2.2)
        rw [hz, add_zero]
        refine sum_congr rfl fun e he => ?_
        obtain ⟨he1, hd⟩ := mem_filter.1 he
        have heα : e ∉ α := fun h => hvα (sub_cov h (mem_blocks.1 he1).2.2)
        rw [if_pos]
        · congr 1; ext x; simp only [mem_sdiff, mem_insert]
          constructor
          · rintro (rfl | ⟨h1, h2⟩)
            · exact ⟨Or.inl rfl, heα⟩
            · exact ⟨Or.inr h1, h2⟩
          · rintro ⟨rfl | h1, h2⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨h1, h2⟩
        · intro f hf
          rcases mem_insert.1 hf with rfl | hf
          · exact Or.inl hd
          · exact hfit f hf
    · simp only [pad, if_neg hfit]
      symm
      refine sum_eq_zero fun e _ => ?_
      rw [if_neg]
      intro hf
      exact hfit fun f hf' => hf f (mem_insert_of_mem hf')

end Pad

/-! ## Monotonicity and transport of designs -/

section Map

variable {R : Type} [CommRing R]

/-- A design of degree `D` is a design of every smaller degree. -/
def monoD {U : Finset ℕ} {D D' : ℕ} (h : D' ≤ D) (ds : Design q R U D) : Design q R U D' where
  s := ds.s
  empty := ds.empty
  ext E hE hEU hEc v hv hvE := ds.ext E hE hEU (by omega) v hv hvE

/-- Preimage of a block. -/
def pre (U : Finset ℕ) (φ : ℕ → ℕ) (e : Finset ℕ) : Finset ℕ := U.filter fun x => φ x ∈ e

theorem image_pre {U : Finset ℕ} {φ : ℕ → ℕ} {e : Finset ℕ} (he : e ⊆ U.image φ) :
    (pre U φ e).image φ = e := by
  ext y
  simp only [mem_image, pre, mem_filter]
  constructor
  · rintro ⟨x, ⟨-, hx⟩, rfl⟩; exact hx
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_image.1 (he hy)
    exact ⟨x, ⟨hx, hy⟩, rfl⟩

theorem pre_image {U : Finset ℕ} {φ : ℕ → ℕ} (hφ : Set.InjOn φ U) {b : Finset ℕ} (hb : b ⊆ U) :
    pre U φ (b.image φ) = b := by
  ext x
  simp only [pre, mem_filter, mem_image]
  constructor
  · rintro ⟨hx, y, hy, hyx⟩
    rwa [← hφ (hb hy) hx hyx]
  · intro hx; exact ⟨hb hx, x, hx, rfl⟩

theorem card_pre {U : Finset ℕ} {φ : ℕ → ℕ} (hφ : Set.InjOn φ U) {e : Finset ℕ}
    (he : e ⊆ U.image φ) : (pre U φ e).card = e.card := by
  conv_rhs => rw [← image_pre he]
  exact (card_image_of_injOn fun x hx y hy h =>
    hφ (mem_filter.1 hx).1 (mem_filter.1 hy).1 h).symm

theorem mem_cov_pre {U : Finset ℕ} {φ : ℕ → ℕ} {E : Finset (Finset ℕ)} {x : ℕ} (hx : x ∈ U) :
    x ∈ cov (E.image (pre U φ)) ↔ φ x ∈ cov E := by
  simp only [mem_cov, mem_image, pre]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, hxe⟩; exact ⟨e, he, (mem_filter.1 hxe).2⟩
  · rintro ⟨e, he, hxe⟩; exact ⟨_, ⟨e, he, rfl⟩, mem_filter.2 ⟨hx, hxe⟩⟩

/-- Transport of a design along a map injective on the universe. -/
def mapD {U : Finset ℕ} {D : ℕ} (ds : Design q R U D) (φ : ℕ → ℕ) (hφ : Set.InjOn φ U) :
    Design q R (U.image φ) D where
  s E := ds.s (E.image (pre U φ))
  empty := by rw [image_empty, ds.empty]
  ext := by
    intro E hE hEU hEc v' hv' hvE
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hv'
    have hE' : PP q (E.image (pre U φ)) := by
      refine ⟨fun b hb => ?_, fun b hb c hc hbc => ?_⟩
      · obtain ⟨e, he, rfl⟩ := mem_image.1 hb
        rw [card_pre hφ (hEU e he), hE.1 e he]
      · obtain ⟨e, he, rfl⟩ := mem_image.1 hb
        obtain ⟨f, hf, rfl⟩ := mem_image.1 hc
        have hef : e ≠ f := fun h => hbc (h ▸ rfl)
        refine disjoint_left.2 fun x hx hx' => ?_
        exact disjoint_left.1 (hE.2 e he f hf hef) (mem_filter.1 hx).2 (mem_filter.1 hx').2
    have hE'U : ∀ b ∈ E.image (pre U φ), b ⊆ U := by
      intro b hb; obtain ⟨e, -, rfl⟩ := mem_image.1 hb; exact filter_subset _ _
    rw [ds.ext _ hE' hE'U (lt_of_le_of_lt card_image_le hEc) v hv
      (fun h => hvE ((mem_cov_pre hv).1 h))]
    symm
    refine sum_nbij' (pre U φ) (fun b => b.image φ) ?_ ?_ ?_ ?_ ?_
    · intro e he
      obtain ⟨hsub, hc, hve⟩ := mem_blocks.1 he
      have hsub' : e ⊆ U.image φ := fun y hy => (mem_sdiff.1 (hsub hy)).1
      refine mem_blocks.2 ⟨fun x hx => ?_, by rw [card_pre hφ hsub', hc], mem_filter.2 ⟨hv, hve⟩⟩
      obtain ⟨hxU, hxe⟩ := mem_filter.1 hx
      exact mem_sdiff.2 ⟨hxU, fun h => (mem_sdiff.1 (hsub hxe)).2 ((mem_cov_pre hxU).1 h)⟩
    · intro b hb
      obtain ⟨hsub, hc, hvb⟩ := mem_blocks.1 hb
      refine mem_blocks.2 ⟨fun y hy => ?_, ?_, mem_image_of_mem φ hvb⟩
      · obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
        obtain ⟨hxU, hxE⟩ := mem_sdiff.1 (hsub hx)
        exact mem_sdiff.2 ⟨mem_image_of_mem φ hxU, fun h => hxE ((mem_cov_pre hxU).2 h)⟩
      · rw [card_image_of_injOn (fun x hx y hy h =>
          hφ (mem_sdiff.1 (hsub hx)).1 (mem_sdiff.1 (hsub hy)).1 h), hc]
    · intro e he
      exact image_pre fun y hy => (mem_sdiff.1 ((mem_blocks.1 he).1 hy)).1
    · intro b hb
      exact pre_image hφ fun x hx => (mem_sdiff.1 ((mem_blocks.1 hb).1 hx)).1
    · intro e _
      rw [image_insert]

end Map

end

end QP

end SATurday.ProofComplexity
