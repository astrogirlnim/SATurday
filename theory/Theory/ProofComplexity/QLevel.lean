import Theory.ProofComplexity.QKEval
import Theory.ProofComplexity.KEvalBuild

/-!
# Tree valued k-evaluations over q-partition restrictions (Ladder Rung R4, 1D.2)

A tree evaluation assigns a q-decision tree to every formula; its branch sets
(`setsOf`: `1`-branches, `0`-branches) form a set level evaluation. `TGood` (well formed, height
at most `k`, local conditions on the branch sets) implies `SGood` (`tgood_sgood`). One level up:
restricting the trees of the old formulas (`tgood_restrict`) and taking canonical trees of the
DNFs of their branches for the new `OR` / `AND` formulas (`tgood_canon_or`, `tgood_canon_and`)
keeps `TGood`.

LOG: R4 QLevel module (tree valued q k-evaluations)
-/

namespace SATurday.ProofComplexity

namespace QP

open Finset

noncomputable section

open Classical

variable {q : ℕ}

open QT

/-! ## Branch sets of trees -/

/-- `1`-branches. -/
def ones (q : ℕ) (T : QT Bool) (W : Finset ℕ) : Finset (Finset (Finset ℕ)) :=
  ((br q T W).filter fun B => B.2 = true).image Prod.fst

/-- `0`-branches. -/
def zeros (q : ℕ) (T : QT Bool) (W : Finset ℕ) : Finset (Finset (Finset ℕ)) :=
  ((br q T W).filter fun B => B.2 = false).image Prod.fst

theorem mem_ones {T : QT Bool} {W : Finset ℕ} {α : Finset (Finset ℕ)} :
    α ∈ ones q T W ↔ (α, true) ∈ br q T W := by
  simp only [ones, mem_image, mem_filter]
  constructor
  · rintro ⟨B, ⟨hB, h2⟩, rfl⟩; rwa [show B = (B.1, true) from Prod.ext rfl h2] at hB
  · intro h; exact ⟨_, ⟨h, rfl⟩, rfl⟩

theorem mem_zeros {T : QT Bool} {W : Finset ℕ} {α : Finset (Finset ℕ)} :
    α ∈ zeros q T W ↔ (α, false) ∈ br q T W := by
  simp only [zeros, mem_image, mem_filter]
  constructor
  · rintro ⟨B, ⟨hB, h2⟩, rfl⟩; rwa [show B = (B.1, false) from Prod.ext rfl h2] at hB
  · intro h; exact ⟨_, ⟨h, rfl⟩, rfl⟩

theorem ones_flip {T : QT Bool} {W : Finset ℕ} : ones q (flipT T) W = zeros q T W := by
  ext α
  rw [mem_ones, mem_zeros, (flip_props T W).2.2, mem_image]
  constructor
  · rintro ⟨B, hB, hBe⟩
    have h1 : B.1 = α := congrArg Prod.fst hBe
    have h2 : B.2 = false := by have := congrArg Prod.snd hBe; simpa using this
    rwa [show B = (α, false) from Prod.ext h1 h2] at hB
  · intro h; exact ⟨_, h, rfl⟩

theorem zeros_flip {T : QT Bool} {W : Finset ℕ} : zeros q (flipT T) W = ones q T W := by
  ext α
  rw [mem_ones, mem_zeros, (flip_props T W).2.2, mem_image]
  constructor
  · rintro ⟨B, hB, hBe⟩
    have h1 : B.1 = α := congrArg Prod.fst hBe
    have h2 : B.2 = true := by have := congrArg Prod.snd hBe; simpa using this
    rwa [show B = (α, true) from Prod.ext h1 h2] at hB
  · intro h; exact ⟨_, h, rfl⟩

/-- The set level evaluation of a tree evaluation. -/
def setsOf (q : ℕ) (U : Finset ℕ) (ρ : Finset (Finset ℕ)) (ET : Fm → QT Bool) : QSet :=
  fun φ => (ones q (ET φ) (free U ρ), zeros q (ET φ) (free U ρ))

/-- A formula well evaluated by trees of height at most `k`. -/
structure TGood (q : ℕ) (U : Finset ℕ) (vx : ℕ → Finset ℕ) (ρ : Finset (Finset ℕ)) (k : ℕ)
    (ET : Fm → QT Bool) (φ : Fm) : Prop where
  wf : WF q (ET φ) (free U ρ)
  ht : ht q (ET φ) (free U ρ) ≤ k
  loc : QLoc q U vx ρ (setsOf q U ρ ET) φ

theorem tgood_sgood (hq : 1 ≤ q) {U : Finset ℕ} {vx : ℕ → Finset ℕ} {ρ : Finset (Finset ℕ)}
    {k : ℕ} {ET : Fm → QT Bool} {φ : Fm} (h : TGood q U vx ρ k ET φ) :
    SGood q U vx ρ k (setsOf q U ρ ET) φ := by
  refine ⟨fun α hα => ?_, fun α hα β hβ hc => ?_, fun π hπ hπm hroom => ?_, h.loc⟩
  · have hB : ∃ b, (α, b) ∈ br q (ET φ) (free U ρ) := by
      rcases mem_union.1 hα with hα | hα
      · exact ⟨true, mem_ones.1 hα⟩
      · exact ⟨false, mem_zeros.1 hα⟩
    obtain ⟨b, hb⟩ := hB
    obtain ⟨hp, hf, hc⟩ := br_props _ _ _ hb
    exact ⟨hf, hp, hc.trans h.ht⟩
  · have := branch_eq _ _ _ _ (mem_ones.1 hα) (mem_zeros.1 hβ) hc
    simp at this
  · obtain ⟨B, hB, hc⟩ := exists_branch hq (ET φ) (free U ρ) π h.wf hπm hπ
      (le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left h.ht _)) hroom)
    refine ⟨B.1, ?_, qcompat_symm hc⟩
    cases hb : B.2
    · exact mem_union.2 (Or.inr (mem_zeros.2 (by rw [← hb]; exact hB)))
    · exact mem_union.2 (Or.inl (mem_ones.2 (by rw [← hb]; exact hB)))

/-! ## Restriction -/

/-- Restriction of a branch set by `τ`. -/
def resS (q : ℕ) (τ : Finset (Finset ℕ)) (S : Finset (Finset (Finset ℕ))) :
    Finset (Finset (Finset ℕ)) :=
  (S.filter fun α => Compat q τ α).image (· \ τ)

theorem mem_resS {τ : Finset (Finset ℕ)} {S : Finset (Finset (Finset ℕ))} {β : Finset (Finset ℕ)} :
    β ∈ resS q τ S ↔ ∃ α ∈ S, Compat q τ α ∧ β = α \ τ := by
  simp only [resS, mem_image, mem_filter]
  constructor
  · rintro ⟨α, ⟨hα, hc⟩, rfl⟩; exact ⟨α, hα, hc, rfl⟩
  · rintro ⟨α, hα, hc, rfl⟩; exact ⟨α, ⟨hα, hc⟩, rfl⟩

theorem free_ext {U : Finset ℕ} {ρ τ : Finset (Finset ℕ)} :
    free U ρ \ cov τ = free U (ρ ∪ τ) := (free_union U ρ τ).symm

/-- Blocks of an extension are blocks of free points. -/
theorem sep_ext {U : Finset ℕ} {ρ τ : Finset (Finset ℕ)} (hp : PP q (ρ ∪ τ)) (hτU : InU U τ)
    (hd : Disjoint ρ τ) : ∀ f ∈ τ, f ⊆ free U ρ := by
  intro f hf x hx
  refine mem_sdiff.2 ⟨hτU f hf hx, fun hxρ => ?_⟩
  obtain ⟨g, hg, hxg⟩ := mem_cov.1 hxρ
  have := pp_eq_of_mem hp (mem_union.2 (Or.inr hf)) (mem_union.2 (Or.inl hg)) hx hxg
  exact disjoint_left.1 hd hg (this ▸ hf)

theorem ones_restrict (hq : 1 ≤ q) {U : Finset ℕ} {ρ τ : Finset (Finset ℕ)} (hτ : PP q τ)
    (hτf : ∀ f ∈ τ, f ⊆ free U ρ) {T : QT Bool} (hT : WF q T (free U ρ)) :
    ones q (restrictT τ T) (free U (ρ ∪ τ)) = resS q τ (ones q T (free U ρ)) ∧
      zeros q (restrictT τ T) (free U (ρ ∪ τ)) = resS q τ (zeros q T (free U ρ)) := by
  obtain ⟨-, -, r1, r2⟩ := restrict_props hq hτ T (free U ρ) hT (fun f hf => Or.inl (hτf f hf))
  rw [free_ext] at r1 r2
  constructor
  · ext β
    rw [mem_ones, mem_resS]
    constructor
    · intro h
      obtain ⟨B, hB, hc, he, hl⟩ := r1 _ h
      refine ⟨B.1, mem_ones.2 ?_, hc, he.symm⟩
      rwa [show B = (B.1, true) from Prod.ext rfl hl] at hB
    · rintro ⟨α, hα, hc, rfl⟩; exact r2 _ (mem_ones.1 hα) hc
  · ext β
    rw [mem_zeros, mem_resS]
    constructor
    · intro h
      obtain ⟨B, hB, hc, he, hl⟩ := r1 _ h
      refine ⟨B.1, mem_zeros.2 ?_, hc, he.symm⟩
      rwa [show B = (B.1, false) from Prod.ext rfl hl] at hB
    · rintro ⟨α, hα, hc, rfl⟩; exact r2 _ (mem_zeros.1 hα) hc

theorem compat_back {τ α β : Finset (Finset ℕ)} (ha : Compat q τ α) (hb : Compat q τ β)
    (h : Compat q (α \ τ) (β \ τ)) : Compat q α β := by
  have hτ : PP q τ := pp_mono ha subset_union_left
  have h3 : PP q (α \ τ ∪ β \ τ ∪ τ) := by
    refine pp_union h hτ fun e he f hf hef => ?_
    rcases mem_union.1 he with he | he
    · exact ha.2 e (mem_union.2 (Or.inr (mem_sdiff.1 he).1)) f (mem_union.2 (Or.inl hf)) hef
    · exact hb.2 e (mem_union.2 (Or.inr (mem_sdiff.1 he).1)) f (mem_union.2 (Or.inl hf)) hef
  refine pp_mono h3 fun e he => ?_
  simp only [mem_union, mem_sdiff] at he ⊢
  by_cases heτ : e ∈ τ <;> tauto

/-- **Restriction keeps `TGood`.** -/
theorem tgood_restrict (hq : 1 ≤ q) {U : Finset ℕ} {vx : ℕ → Finset ℕ} {ρ τ : Finset (Finset ℕ)}
    (hτ : PP q τ) (hτf : ∀ f ∈ τ, f ⊆ free U ρ) {k : ℕ} {ET : Fm → QT Bool} {φ : Fm}
    (hwf : ∀ χ ∈ subs φ, WF q (ET χ) (free U ρ)) (hG : TGood q U vx ρ k ET φ) :
    TGood q U vx (ρ ∪ τ) k (fun χ => restrictT τ (ET χ)) φ := by
  obtain ⟨i1, i2, -, -⟩ := restrict_props hq hτ (ET φ) (free U ρ) hG.wf
    (fun f hf => Or.inl (hτf f hf))
  rw [free_ext] at i1 i2
  have hS : ∀ χ ∈ subs φ, setsOf q U (ρ ∪ τ) (fun χ => restrictT τ (ET χ)) χ =
      (resS q τ (setsOf q U ρ ET χ).1, resS q τ (setsOf q U ρ ET χ).2) := by
    intro χ hχ
    obtain ⟨h1, h2⟩ := ones_restrict hq hτ hτf (hwf χ hχ)
    simp only [setsOf, h1, h2]
  refine ⟨i1, i2.trans hG.ht, ?_⟩
  have hl := hG.loc
  have hself := hS φ (self_mem_subs φ)
  cases φ with
  | var v =>
    simp only [QLoc] at hl ⊢
    intro hu
    obtain ⟨h1, h0⟩ := hl hu
    rw [hself]
    refine ⟨fun β hβ => ?_, fun β hβ hm => ?_⟩
    · obtain ⟨α, hα, hc, rfl⟩ := mem_resS.1 hβ
      have := h1 α hα
      simp only [mem_union, mem_sdiff] at this ⊢
      by_cases hx : vx v ∈ τ <;> tauto
    · obtain ⟨α, hα, hc, rfl⟩ := mem_resS.1 hβ
      refine h0 α hα (pp_mono hm ?_)
      intro e he
      simp only [mem_insert, mem_union, mem_sdiff] at he ⊢
      by_cases heτ : e ∈ τ <;> tauto
  | neg ψ =>
    simp only [QLoc] at hl ⊢
    rw [hself, hS ψ (by rw [subs]; exact List.mem_cons_of_mem _ (self_mem_subs ψ)), hl]
  | and l =>
    simp only [QLoc] at hl ⊢
    have hc' : ∀ ψ ∈ l, ψ ∈ subs (Fm.and l) := fun ψ hψ => sub_and (self_mem_subs _) hψ
    rw [hself]
    refine ⟨fun β hβ => ?_, fun β hβ ψ hψ γ hγ hc => ?_⟩
    · obtain ⟨α, hα, hcα, rfl⟩ := mem_resS.1 hβ
      obtain ⟨ψ, hψ, γ, hγ, hγα⟩ := hl.1 α hα
      refine ⟨ψ, hψ, γ \ τ, ?_, sdiff_subset_sdiff hγα subset_rfl⟩
      rw [hS ψ (hc' ψ hψ)]
      exact mem_resS.2 ⟨γ, hγ, compat_mono hcα subset_rfl hγα, rfl⟩
    · obtain ⟨α, hα, hcα, rfl⟩ := mem_resS.1 hβ
      rw [hS ψ (hc' ψ hψ)] at hγ
      obtain ⟨γ', hγ', hcγ, rfl⟩ := mem_resS.1 hγ
      exact hl.2 α hα ψ hψ γ' hγ' (compat_back hcα hcγ hc)
  | or l =>
    simp only [QLoc] at hl ⊢
    have hc' : ∀ ψ ∈ l, ψ ∈ subs (Fm.or l) := fun ψ hψ => sub_or (self_mem_subs _) hψ
    rw [hself]
    refine ⟨fun β hβ => ?_, fun β hβ ψ hψ γ hγ hc => ?_⟩
    · obtain ⟨α, hα, hcα, rfl⟩ := mem_resS.1 hβ
      obtain ⟨ψ, hψ, γ, hγ, hγα⟩ := hl.1 α hα
      refine ⟨ψ, hψ, γ \ τ, ?_, sdiff_subset_sdiff hγα subset_rfl⟩
      rw [hS ψ (hc' ψ hψ)]
      exact mem_resS.2 ⟨γ, hγ, compat_mono hcα subset_rfl hγα, rfl⟩
    · obtain ⟨α, hα, hcα, rfl⟩ := mem_resS.1 hβ
      rw [hS ψ (hc' ψ hψ)] at hγ
      obtain ⟨γ', hγ', hcγ, rfl⟩ := mem_resS.1 hγ
      exact hl.2 α hα ψ hψ γ' hγ' (compat_back hcα hcγ hc)
  | mod r l => trivial

/-! ## Canonical trees one level up -/

theorem canon_C1 (hq : 1 ≤ q) {U : Finset ℕ} {ρ τ : Finset (Finset ℕ)} {D : List (Finset (Finset ℕ))}
    (hD : ∀ x ∈ D, (∀ f ∈ x, f ⊆ free U ρ) ∧ PP q x) {α : Finset (Finset ℕ)}
    (hα : α ∈ ones q (canonT q U D (ρ ∪ τ)) (free U (ρ ∪ τ))) :
    ∃ x ∈ D, Compat q τ x ∧ x \ τ ⊆ α := by
  obtain ⟨x, hx, hc, hsub⟩ := canonT_one hq (mem_ones.1 hα) rfl
  refine ⟨x, hx, compat_mono hc subset_union_right subset_rfl, fun e he => hsub ?_⟩
  obtain ⟨hex, heτ⟩ := mem_sdiff.1 he
  refine mem_sdiff.2 ⟨hex, fun h => ?_⟩
  rcases mem_union.1 h with h | h
  · have hne : e.Nonempty := by rw [← card_pos, (hD x hx).2.1 e hex]; omega
    exact notMem_of_free ((hD x hx).1 e hex) hne h
  · exact heτ h

theorem canon_C0 (hq : 1 ≤ q) {U : Finset ℕ} {ρ τ : Finset (Finset ℕ)} (hρτ : PP q (ρ ∪ τ))
    (hρτU : InU U (ρ ∪ τ)) {D : List (Finset (Finset ℕ))}
    (hD : ∀ x ∈ D, (∀ f ∈ x, f ⊆ free U ρ) ∧ PP q x) {α : Finset (Finset ℕ)}
    (hα : α ∈ zeros q (canonT q U D (ρ ∪ τ)) (free U (ρ ∪ τ))) :
    ∀ x ∈ D, Compat q τ x → ¬ Compat q α (x \ τ) := by
  intro x hx hc hcα
  have hDU : ∀ t ∈ D, InU U t := fun t ht f hf => ((hD t ht).1 f hf).trans sdiff_subset
  have hcx : Compat q (ρ ∪ τ) x := by
    refine pp_union hρτ (hD x hx).2 fun e he f hf hef => ?_
    rcases mem_union.1 he with he | he
    · exact (disj_free_blocks ((hD x hx).1 f hf) e he).symm
    · exact hc.2 e (mem_union.2 (Or.inl he)) f (mem_union.2 (Or.inr hf)) hef
  have hxe : x \ (ρ ∪ τ) = x \ τ := by
    ext e; simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (Or.inr h)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun h => h.elim (fun h => ?_) h2⟩
      have hne : e.Nonempty := by rw [← card_pos, (hD x hx).2.1 e h1]; omega
      exact notMem_of_free ((hD x hx).1 e h1) hne h
  exact canonT_zero hq hDU hρτ hρτU (mem_zeros.1 hα) rfl x hx hcx (by rw [hxe]; exact hcα)

/-- DNF of the `1`-branches of the disjuncts. -/
def DorT (q : ℕ) (U : Finset ℕ) (ρ : Finset (Finset ℕ)) (ET : Fm → QT Bool) (l : List Fm) :
    List (Finset (Finset ℕ)) :=
  (l.map fun ψ => (ones q (ET ψ) (free U ρ)).toList).flatten

/-- DNF of the `0`-branches of the conjuncts. -/
def DandT (q : ℕ) (U : Finset ℕ) (ρ : Finset (Finset ℕ)) (ET : Fm → QT Bool) (l : List Fm) :
    List (Finset (Finset ℕ)) :=
  (l.map fun ψ => (zeros q (ET ψ) (free U ρ)).toList).flatten

theorem mem_DorT {U : Finset ℕ} {ρ : Finset (Finset ℕ)} {ET : Fm → QT Bool} {l : List Fm}
    {x : Finset (Finset ℕ)} : x ∈ DorT q U ρ ET l ↔ ∃ ψ ∈ l, x ∈ ones q (ET ψ) (free U ρ) := by
  simp [DorT, List.mem_flatten, List.mem_map]

theorem mem_DandT {U : Finset ℕ} {ρ : Finset (Finset ℕ)} {ET : Fm → QT Bool} {l : List Fm}
    {x : Finset (Finset ℕ)} : x ∈ DandT q U ρ ET l ↔ ∃ ψ ∈ l, x ∈ zeros q (ET ψ) (free U ρ) := by
  simp [DandT, List.mem_flatten, List.mem_map]

/-- The tree evaluation one level up: old formulas restricted, new ones canonical. -/
def canonF (q : ℕ) (U : Finset ℕ) (ρ τ : Finset (Finset ℕ)) (ET : Fm → QT Bool) : Fm → QT Bool
  | .or l => canonT q U (DorT q U ρ ET l) (ρ ∪ τ)
  | .and l => flipT (canonT q U (DandT q U ρ ET l) (ρ ∪ τ))
  | .neg ψ => flipT (canonF q U ρ τ ET ψ)
  | _ => leaf false

def nextT (q : ℕ) (U : Finset ℕ) (ρ τ : Finset (Finset ℕ)) (t : ℕ) (ET : Fm → QT Bool) :
    Fm → QT Bool :=
  fun φ => if φ.depth ≤ t then restrictT τ (ET φ) else canonF q U ρ τ ET φ

/-! ## Congruence and negation -/

theorem tgood_congr {U : Finset ℕ} {vx : ℕ → Finset ℕ} {ρ : Finset (Finset ℕ)} {k : ℕ}
    {ET1 ET2 : Fm → QT Bool} {φ : Fm} (h : ∀ χ ∈ subs φ, ET1 χ = ET2 χ)
    (hG : TGood q U vx ρ k ET1 φ) : TGood q U vx ρ k ET2 φ := by
  have e := h φ (self_mem_subs φ)
  have hs : ∀ χ ∈ subs φ, setsOf q U ρ ET1 χ = setsOf q U ρ ET2 χ := fun χ hχ => by
    simp only [setsOf, h χ hχ]
  obtain ⟨hw, hh, hl⟩ := hG
  refine ⟨by rw [← e]; exact hw, by rw [← e]; exact hh, ?_⟩
  have e' := hs φ (self_mem_subs φ)
  cases φ with
  | var v => simp only [QLoc] at hl ⊢; rw [← e']; exact hl
  | neg ψ =>
    simp only [QLoc] at hl ⊢
    rw [← e', hl, hs ψ (by rw [subs]; exact List.mem_cons_of_mem _ (self_mem_subs ψ))]
  | and l =>
    simp only [QLoc] at hl ⊢
    have hc' : ∀ ψ ∈ l, setsOf q U ρ ET1 ψ = setsOf q U ρ ET2 ψ := fun ψ hψ =>
      hs ψ (sub_and (self_mem_subs _) hψ)
    rw [← e']
    refine ⟨fun α hα => ?_, fun α hα ψ hψ β hβ => ?_⟩
    · obtain ⟨ψ, hψ, β, hβ, hβα⟩ := hl.1 α hα
      exact ⟨ψ, hψ, β, by rw [← hc' ψ hψ]; exact hβ, hβα⟩
    · exact hl.2 α hα ψ hψ β (by rw [hc' ψ hψ]; exact hβ)
  | or l =>
    simp only [QLoc] at hl ⊢
    have hc' : ∀ ψ ∈ l, setsOf q U ρ ET1 ψ = setsOf q U ρ ET2 ψ := fun ψ hψ =>
      hs ψ (sub_or (self_mem_subs _) hψ)
    rw [← e']
    refine ⟨fun α hα => ?_, fun α hα ψ hψ β hβ => ?_⟩
    · obtain ⟨ψ, hψ, β, hβ, hβα⟩ := hl.1 α hα
      exact ⟨ψ, hψ, β, by rw [← hc' ψ hψ]; exact hβ, hβα⟩
    · exact hl.2 α hα ψ hψ β (by rw [hc' ψ hψ]; exact hβ)
  | mod r l => trivial

theorem tgood_neg {U : Finset ℕ} {vx : ℕ → Finset ℕ} {ρ : Finset (Finset ℕ)} {k : ℕ}
    {ET : Fm → QT Bool} {ψ : Fm} (hG : TGood q U vx ρ k ET ψ) (hE : ET (.neg ψ) = flipT (ET ψ)) :
    TGood q U vx ρ k ET (.neg ψ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hE, (flip_props _ _).1]; exact hG.wf
  · rw [hE, (flip_props _ _).2.1]; exact hG.ht
  · simp only [QLoc, setsOf, hE, ones_flip, zeros_flip]

/-! ## Depth zero -/

/-- The tree of a variable: query a point of its block. -/
def varT (q : ℕ) (U : Finset ℕ) (e : Finset ℕ) : QT Bool :=
  if e ∈ U.powersetCard q then
    node (if h : e.Nonempty then e.min' h else 0) fun f => leaf (decide (f = e))
  else leaf false

def ET0 (q : ℕ) (U : Finset ℕ) (vx : ℕ → Finset ℕ) : Fm → QT Bool
  | .var v => varT q U (vx v)
  | .neg ψ => flipT (ET0 q U vx ψ)
  | _ => leaf false

theorem tgood_ET0 (hq : 1 ≤ q) {U : Finset ℕ} {vx : ℕ → Finset ℕ} {k : ℕ} (hk : 1 ≤ k) :
    ∀ φ : Fm, φ.depth = 0 → TGood q U vx ∅ k (ET0 q U vx) φ
  | .var v, _ => by
    have hfree : free U ∅ = U := by simp [free, cov]
    by_cases he : vx v ∈ U.powersetCard q
    · obtain ⟨heU, hec⟩ := mem_powersetCard.1 he
      have hne : (vx v).Nonempty := by rw [← card_pos, hec]; omega
      set v0 := (vx v).min' hne
      have hv0 : v0 ∈ vx v := min'_mem _ _
      have hT : ET0 q U vx (.var v) = node v0 fun f => leaf (decide (f = vx v)) := by
        simp only [ET0, varT, if_pos he, dif_pos hne]; rfl
      have hbr : ∀ B ∈ br q (ET0 q U vx (.var v)) (free U ∅),
          ∃ f ∈ blocks q U v0, B = ({f}, decide (f = vx v)) := by
        intro B hB
        rw [hT] at hB
        obtain ⟨f, hf, B', hB', rfl⟩ := mem_br_node.1 hB
        simp [br] at hB'
        rw [hfree] at hf
        exact ⟨f, hf, by rw [hB']; rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [hT, hfree]; exact ⟨heU hv0, fun _ _ => trivial⟩
      · rw [hT]; simp only [ht]
        have : ((blocks q (free U ∅) v0).sup fun _ => (0 : ℕ)) = 0 := by simp
        omega
      · simp only [QLoc, setsOf]
        intro _
        refine ⟨fun α hα => ?_, fun α hα hm => ?_⟩
        · obtain ⟨f, hf, hBe⟩ := hbr _ (mem_ones.1 hα)
          have h1 : α = {f} := congrArg Prod.fst hBe
          have h2 : decide (f = vx v) = true := (congrArg Prod.snd hBe).symm
          rw [h1, of_decide_eq_true h2]; simp
        · obtain ⟨f, hf, hBe⟩ := hbr _ (mem_zeros.1 hα)
          have h1 : α = {f} := congrArg Prod.fst hBe
          have h2 : decide (f = vx v) = false := (congrArg Prod.snd hBe).symm
          have hfe : f ≠ vx v := of_decide_eq_false h2
          rw [h1] at hm
          exact hfe (pp_eq_of_mem hm (by simp) (by simp) (mem_blocks.1 hf).2.2 hv0)
    · have hT : ET0 q U vx (.var v) = leaf false := by simp only [ET0, varT, if_neg he]
      refine ⟨by rw [hT]; trivial, by rw [hT]; simp [ht], ?_⟩
      simp only [QLoc]; intro hu; exact absurd hu he
  | .neg ψ, h => by
    rw [depth_neg] at h
    exact tgood_neg (tgood_ET0 hq hk ψ h) rfl
  | .and l, h => by rw [depth_and] at h; omega
  | .or l, h => by rw [depth_or] at h; omega
  | .mod r l, h => by rw [depth_mod] at h; omega

/-! ## The level step -/

theorem subs_closed {Φ : List Fm}
    (hcl : ∀ φ ∈ Φ, (∀ ψ, φ = .neg ψ → ψ ∈ Φ) ∧ (∀ l, φ = .or l → ∀ ψ ∈ l, ψ ∈ Φ) ∧
      (∀ l, φ = .and l → ∀ ψ ∈ l, ψ ∈ Φ)) (hmod : ∀ φ ∈ Φ, isMod φ = false) :
    ∀ (φ : Fm), φ ∈ Φ → ∀ χ ∈ subs φ, χ ∈ Φ
  | .var i, h, χ, hχ => by simp [subs] at hχ; rw [hχ]; exact h
  | .neg ψ, h, χ, hχ => by
      rw [subs, List.mem_cons] at hχ
      rcases hχ with rfl | hχ
      · exact h
      · exact subs_closed hcl hmod ψ ((hcl _ h).1 ψ rfl) χ hχ
  | .and l, h, χ, hχ => by
      rw [subs_and, List.mem_cons] at hχ
      rcases hχ with rfl | hχ
      · exact h
      · obtain ⟨_, ⟨ψ, hψ, rfl⟩, hχψ⟩ := List.mem_flatten.1 hχ |>.imp fun _ =>
          And.imp_left List.mem_map.1
        have : sizeOf ψ < sizeOf (Fm.and l) := by
          have := List.sizeOf_lt_of_mem hψ; simp only [Fm.and.sizeOf_spec]; omega
        exact subs_closed hcl hmod ψ ((hcl _ h).2.2 l rfl ψ hψ) χ hχψ
  | .or l, h, χ, hχ => by
      rw [subs_or, List.mem_cons] at hχ
      rcases hχ with rfl | hχ
      · exact h
      · obtain ⟨_, ⟨ψ, hψ, rfl⟩, hχψ⟩ := List.mem_flatten.1 hχ |>.imp fun _ =>
          And.imp_left List.mem_map.1
        have : sizeOf ψ < sizeOf (Fm.or l) := by
          have := List.sizeOf_lt_of_mem hψ; simp only [Fm.or.sizeOf_spec]; omega
        exact subs_closed hcl hmod ψ ((hcl _ h).2.1 l rfl ψ hψ) χ hχψ
  | .mod r l, h, χ, hχ => by have := hmod _ h; simp [isMod] at this

theorem branches_free {T : QT Bool} {W : Finset ℕ} (hT : WF q T W)
    {x : Finset (Finset ℕ)} (hx : x ∈ ones q T W ∨ x ∈ zeros q T W) :
    (∀ f ∈ x, f ⊆ W) ∧ PP q x := by
  rcases hx with hx | hx
  · have := br_props _ _ _ (mem_ones.1 hx); exact ⟨this.2.1, this.1⟩
  · have := br_props _ _ _ (mem_zeros.1 hx); exact ⟨this.2.1, this.1⟩

/-- **Level step**: from a tree evaluation over `ρ` up to depth `t` to one over `ρ ∪ τ` up to
depth `t + 1`, when the DNFs of the new `OR` / `AND` formulas have small canonical depth. -/
theorem level_step_q (hq : 1 ≤ q) {U : Finset ℕ} {vx : ℕ → Finset ℕ} {Φ : List Fm}
    (hcl : ∀ φ ∈ Φ, (∀ ψ, φ = .neg ψ → ψ ∈ Φ) ∧ (∀ l, φ = .or l → ∀ ψ ∈ l, ψ ∈ Φ) ∧
      (∀ l, φ = .and l → ∀ ψ ∈ l, ψ ∈ Φ))
    (hmod : ∀ φ ∈ Φ, isMod φ = false) {t k : ℕ} {ρ τ : Finset (Finset ℕ)} {ET : Fm → QT Bool}
    (hG : ∀ φ ∈ Φ, φ.depth ≤ t → TGood q U vx ρ k ET φ)
    (hρτ : PP q (ρ ∪ τ)) (hρτU : InU U (ρ ∪ τ)) (hd : Disjoint ρ τ)
    (hsh1 : ∀ l, Fm.or l ∈ Φ → (Fm.or l).depth = t + 1 →
      q * cdepth q U (DorT q U ρ ET l) (ρ ∪ τ) ≤ k)
    (hsh2 : ∀ l, Fm.and l ∈ Φ → (Fm.and l).depth = t + 1 →
      q * cdepth q U (DandT q U ρ ET l) (ρ ∪ τ) ≤ k) :
    ∀ φ ∈ Φ, φ.depth ≤ t + 1 → TGood q U vx (ρ ∪ τ) k (nextT q U ρ τ t ET) φ := by
  have hτ : PP q τ := pp_mono hρτ subset_union_right
  have hτU : InU U τ := fun f hf => hρτU f (mem_union.2 (Or.inr hf))
  have hτf := sep_ext hρτ hτU hd
  have hlow : ∀ φ ∈ Φ, φ.depth ≤ t → TGood q U vx (ρ ∪ τ) k (nextT q U ρ τ t ET) φ := by
    intro φ hφ hdφ
    have hwf : ∀ χ ∈ subs φ, WF q (ET χ) (free U ρ) := fun χ hχ =>
      (hG χ (subs_closed hcl hmod φ hφ χ hχ) ((depth_subs φ hχ).trans hdφ)).wf
    refine tgood_congr (fun χ hχ => ?_) (tgood_restrict hq hτ hτf hwf (hG φ hφ hdφ))
    have := depth_subs φ hχ
    simp only [nextT, if_pos (show χ.depth ≤ t by omega)]
  have hchild : ∀ ψ ∈ Φ, ψ.depth ≤ t → nextT q U ρ τ t ET ψ = restrictT τ (ET ψ) := by
    intro ψ _ hd'; simp only [nextT, if_pos hd']
  have hcan : ∀ φ, φ.depth = t + 1 → nextT q U ρ τ t ET φ = canonF q U ρ τ ET φ := by
    intro φ hd'; simp only [nextT, if_neg (show ¬ φ.depth ≤ t by omega)]
  have hDfree : ∀ ψ ∈ Φ, ψ.depth ≤ t → ∀ x, x ∈ ones q (ET ψ) (free U ρ) ∨
      x ∈ zeros q (ET ψ) (free U ρ) → (∀ f ∈ x, f ⊆ free U ρ) ∧ PP q x :=
    fun ψ hψ hd' x hx => branches_free (hG ψ hψ hd').wf hx
  have htop : ∀ φ : Fm, φ ∈ Φ → φ.depth = t + 1 → TGood q U vx (ρ ∪ τ) k (nextT q U ρ τ t ET) φ := by
    intro φ
    induction φ using Fm.rec (motive_2 := fun _ => True) with
    | var v => intro _ h; simp [Fm.depth] at h
    | neg ψ ih =>
      intro hφ hd'
      rw [depth_neg] at hd'
      have hψ := (hcl _ hφ).1 ψ rfl
      refine tgood_neg (ih hψ hd') ?_
      rw [hcan _ (by rw [depth_neg]; exact hd'), hcan _ hd']; rfl
    | or l _ =>
      intro hφ hd'
      have hch : ∀ ψ ∈ l, ψ ∈ Φ ∧ ψ.depth ≤ t := fun ψ hψ =>
        ⟨(hcl _ hφ).2.1 l rfl ψ hψ, by have := depth_child_or hψ; omega⟩
      have hE : nextT q U ρ τ t ET (.or l) = canonT q U (DorT q U ρ ET l) (ρ ∪ τ) := hcan _ hd'
      have hD : ∀ x ∈ DorT q U ρ ET l, (∀ f ∈ x, f ⊆ free U ρ) ∧ PP q x := by
        intro x hx
        obtain ⟨ψ, hψ, hxψ⟩ := mem_DorT.1 hx
        exact hDfree ψ (hch ψ hψ).1 (hch ψ hψ).2 x (Or.inl hxψ)
      have hDU : ∀ x ∈ DorT q U ρ ET l, InU U x := fun x hx f hf =>
        ((hD x hx).1 f hf).trans sdiff_subset
      refine ⟨by rw [hE]; exact wf_canonT _ _ _, ?_, ?_⟩
      · rw [hE]; exact (ht_canonT hq hDU hρτ hρτU).trans (hsh1 l hφ hd')
      · simp only [QLoc, setsOf]
        refine ⟨fun α hα => ?_, fun α hα ψ hψ β hβ hc => ?_⟩
        · rw [hE] at hα
          obtain ⟨x, hx, hcx, hsub⟩ := canon_C1 hq hD hα
          obtain ⟨ψ, hψ, hxψ⟩ := mem_DorT.1 hx
          refine ⟨ψ, hψ, x \ τ, ?_, hsub⟩
          rw [hchild ψ (hch ψ hψ).1 (hch ψ hψ).2,
            (ones_restrict hq hτ hτf (hG ψ (hch ψ hψ).1 (hch ψ hψ).2).wf).1]
          exact mem_resS.2 ⟨x, hxψ, hcx, rfl⟩
        · rw [hE] at hα
          rw [hchild ψ (hch ψ hψ).1 (hch ψ hψ).2,
            (ones_restrict hq hτ hτf (hG ψ (hch ψ hψ).1 (hch ψ hψ).2).wf).1] at hβ
          obtain ⟨x, hx, hcx, rfl⟩ := mem_resS.1 hβ
          exact canon_C0 hq hρτ hρτU hD hα x (mem_DorT.2 ⟨ψ, hψ, hx⟩) hcx hc
    | and l _ =>
      intro hφ hd'
      have hch : ∀ ψ ∈ l, ψ ∈ Φ ∧ ψ.depth ≤ t := fun ψ hψ =>
        ⟨(hcl _ hφ).2.2 l rfl ψ hψ, by have := depth_child_and hψ; omega⟩
      have hE : nextT q U ρ τ t ET (.and l) =
          flipT (canonT q U (DandT q U ρ ET l) (ρ ∪ τ)) := hcan _ hd'
      have hD : ∀ x ∈ DandT q U ρ ET l, (∀ f ∈ x, f ⊆ free U ρ) ∧ PP q x := by
        intro x hx
        obtain ⟨ψ, hψ, hxψ⟩ := mem_DandT.1 hx
        exact hDfree ψ (hch ψ hψ).1 (hch ψ hψ).2 x (Or.inr hxψ)
      have hDU : ∀ x ∈ DandT q U ρ ET l, InU U x := fun x hx f hf =>
        ((hD x hx).1 f hf).trans sdiff_subset
      refine ⟨by rw [hE, (flip_props _ _).1]; exact wf_canonT _ _ _, ?_, ?_⟩
      · rw [hE, (flip_props _ _).2.1]; exact (ht_canonT hq hDU hρτ hρτU).trans (hsh2 l hφ hd')
      · simp only [QLoc, setsOf, hE, ones_flip, zeros_flip]
        refine ⟨fun α hα => ?_, fun α hα ψ hψ β hβ hc => ?_⟩
        · obtain ⟨x, hx, hcx, hsub⟩ := canon_C1 hq hD hα
          obtain ⟨ψ, hψ, hxψ⟩ := mem_DandT.1 hx
          refine ⟨ψ, hψ, x \ τ, ?_, hsub⟩
          rw [hchild ψ (hch ψ hψ).1 (hch ψ hψ).2,
            (ones_restrict hq hτ hτf (hG ψ (hch ψ hψ).1 (hch ψ hψ).2).wf).2]
          exact mem_resS.2 ⟨x, hxψ, hcx, rfl⟩
        · rw [hchild ψ (hch ψ hψ).1 (hch ψ hψ).2,
            (ones_restrict hq hτ hτf (hG ψ (hch ψ hψ).1 (hch ψ hψ).2).wf).2] at hβ
          obtain ⟨x, hx, hcx, rfl⟩ := mem_resS.1 hβ
          exact canon_C0 hq hρτ hρτU hD hα x (mem_DandT.2 ⟨ψ, hψ, hx⟩) hcx hc
    | mod r l _ =>
      intro hφ _
      have := hmod _ hφ; simp [isMod] at this
    | nil => trivial
    | cons _ _ _ _ => trivial
  intro φ hφ hd'
  by_cases h : φ.depth ≤ t
  · exact hlow φ hφ h
  · exact htop φ hφ (by omega)

end

end QP

end SATurday.ProofComplexity
