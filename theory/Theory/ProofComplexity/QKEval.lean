import Theory.ProofComplexity.QTree
import Theory.ProofComplexity.KEval

/-!
# k-evaluations over q-partition restrictions, with Count_p axioms (Ladder Rung R4, 1D.2)

The q-analog of `KEval`. Branches are partial q-partitions of the free points of a restriction
`ρ` of the universe `U`. A set level evaluation `E φ = (true branches, false branches)` is
`SGood` when its branches are small partial partitions of free points, the two sides are
incompatible, every partial partition leaving room is compatible with a branch, and the local
connective conditions hold (`QLoc`). The proof system `FProofC` is the mod free sequent calculus
plus all instances of the Count_p axiom schema (`countSeq p M ψ` with `p ∤ M`: the formulas
`ψ g`, `g` a `p`-subset of `[M]`, do not define a `p`-partition of `[M]`), which are valid
(`countSeq_valid`).

Soundness (`qkeval_sound`): if every hypothesis clause is hit and every Count_p instance line
has no false branch, no line of the proof has a false branch.

LOG: R4 QKEval module (q k-evaluations and Count_p axioms)
-/

namespace SATurday.ProofComplexity

namespace QP

open Finset

noncomputable section

open Classical

/-! ## Count_p axioms -/

/-- The `p`-subsets of `[M]`. -/
def cntG (p M : ℕ) : Finset (Finset ℕ) := powersetCard p (range M)

/-- Point `i` is covered. -/
def covF (p M : ℕ) (ψ : Finset ℕ → Fm) (i : ℕ) : Fm :=
  .or (((cntG p M).filter (i ∈ ·)).toList.map ψ)

/-- Overlapping classes are not both chosen. -/
def confF (ψ : Finset ℕ → Fm) (g g' : Finset ℕ) : Fm := .or [.neg (ψ g), .neg (ψ g')]

def confPairs (p M : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((cntG p M) ×ˢ (cntG p M)).filter fun gg => gg.1 ≠ gg.2 ∧ ¬ Disjoint gg.1 gg.2

/-- The Count_p^M axiom instance: `covF` for every point and `confF` for every overlapping pair
cannot all hold. -/
def countSeq (p M : ℕ) (ψ : Finset ℕ → Fm) : Seq :=
  ((range M).toList.map (covF p M ψ) ++ (confPairs p M).toList.map (fun gg => confF ψ gg.1 gg.2),
    [])

/-- Instances of the Count_p axiom schema. -/
def CountInst (p : ℕ) (S : Seq) : Prop := ∃ M ψ, ¬ p ∣ M ∧ S = countSeq p M ψ

/-- One inference of bounded depth Frege with Count_p axioms. -/
def FStepC (p : ℕ) (F : CNF) (prev : List Seq) (S : Seq) : Prop :=
  FStep p F prev S ∨ CountInst p S

def FProofC (p : ℕ) (F : CNF) (L : List Seq) : Prop :=
  ∀ k (hk : k < L.length), FStepC p F (L.take k) (L.get ⟨k, hk⟩)

/-- A depth `d` refutation of `F` with Count_p axioms. -/
def FRefutesC (p d : ℕ) (F : CNF) (L : List Seq) : Prop :=
  FProofC p F L ∧ FDepthLe d L ∧ ([], []) ∈ L

/-! ## Set level k-evaluations -/

abbrev QSet := Fm → Finset (Finset (Finset ℕ)) × Finset (Finset (Finset ℕ))

/-- Local conditions tying an evaluation to the connectives. -/
def QLoc (q : ℕ) (U : Finset ℕ) (vx : ℕ → Finset ℕ) (ρ : Finset (Finset ℕ)) (E : QSet) :
    Fm → Prop
  | .var v => vx v ∈ U.powersetCard q →
      (∀ α ∈ (E (.var v)).1, vx v ∈ α ∪ ρ) ∧
      (∀ α ∈ (E (.var v)).2, ¬ PP q (insert (vx v) (α ∪ ρ)))
  | .neg ψ => E (.neg ψ) = ((E ψ).2, (E ψ).1)
  | .and l => (∀ α ∈ (E (.and l)).2, ∃ ψ ∈ l, ∃ β ∈ (E ψ).2, β ⊆ α) ∧
      (∀ α ∈ (E (.and l)).1, ∀ ψ ∈ l, ∀ β ∈ (E ψ).2, ¬ Compat q α β)
  | .or l => (∀ α ∈ (E (.or l)).1, ∃ ψ ∈ l, ∃ β ∈ (E ψ).1, β ⊆ α) ∧
      (∀ α ∈ (E (.or l)).2, ∀ ψ ∈ l, ∀ β ∈ (E ψ).1, ¬ Compat q α β)
  | .mod _ _ => True

/-- A formula well evaluated at depth `k` over `ρ`. -/
structure SGood (q : ℕ) (U : Finset ℕ) (vx : ℕ → Finset ℕ) (ρ : Finset (Finset ℕ)) (k : ℕ)
    (E : QSet) (φ : Fm) : Prop where
  mem : ∀ α ∈ (E φ).1 ∪ (E φ).2, (∀ f ∈ α, f ⊆ free U ρ) ∧ PP q α ∧ α.card ≤ k
  inc : ∀ α ∈ (E φ).1, ∀ β ∈ (E φ).2, ¬ Compat q α β
  cov : ∀ π, (∀ f ∈ π, f ⊆ free U ρ) → PP q π → q * (π.card + k) ≤ (free U ρ).card →
    ∃ α ∈ (E φ).1 ∪ (E φ).2, Compat q α π
  loc : QLoc q U vx ρ E φ

/-- Every clause of `F` is hit, against any small partial partition, by a true branch of one of
its literals. -/
def SClauseHit (q : ℕ) (U : Finset ℕ) (vx : ℕ → Finset ℕ) (ρ : Finset (Finset ℕ)) (k : ℕ)
    (E : QSet) (F : CNF) : Prop :=
  ∀ C ∈ F, (∀ φ ∈ subs (clauseFm C), SGood q U vx ρ k E φ) → ∀ β, (∀ f ∈ β, f ⊆ free U ρ) →
    PP q β → β.card ≤ k → ∃ l ∈ C, ∃ γ ∈ (E (litFm l)).1, Compat q γ β

/-- All subformulas of the line formula of `T` are well evaluated. -/
def SGoodLine (q : ℕ) (U : Finset ℕ) (vx : ℕ → Finset ℕ) (ρ : Finset (Finset ℕ)) (k : ℕ)
    (E : QSet) (T : Seq) : Prop :=
  ∀ φ ∈ subs (lineF T), SGood q U vx ρ k E φ

section Sound

variable {q : ℕ} {U : Finset ℕ} {vx : ℕ → Finset ℕ} {ρ : Finset (Finset ℕ)} {k : ℕ} {E : QSet}

theorem qcompat_symm {A B : Finset (Finset ℕ)} (h : Compat q A B) : Compat q B A := by
  unfold Compat at h ⊢; rwa [union_comm]

theorem qcompat_left {γ α β : Finset (Finset ℕ)} (h : Compat q γ (α ∪ β)) : Compat q γ α :=
  compat_mono h subset_rfl subset_union_left

theorem qcompat_right {γ α β : Finset (Finset ℕ)} (h : Compat q γ (α ∪ β)) : Compat q γ β :=
  compat_mono h subset_rfl subset_union_right

theorem sgood_neg {ψ : Fm} (h : SGood q U vx ρ k E (.neg ψ)) :
    (E (.neg ψ)).1 = (E ψ).2 ∧ (E (.neg ψ)).2 = (E ψ).1 := by
  have := h.loc; simp only [QLoc] at this; rw [this]; exact ⟨rfl, rfl⟩

theorem qunion_small {α β : Finset (Finset ℕ)} (hα : ∀ f ∈ α, f ⊆ free U ρ)
    (hβ : ∀ f ∈ β, f ⊆ free U ρ) (hc : Compat q α β) (hαk : α.card ≤ k) (hβk : β.card ≤ k) :
    (∀ f ∈ α ∪ β, f ⊆ free U ρ) ∧ PP q (α ∪ β) ∧ (α ∪ β).card ≤ 2 * k :=
  ⟨fun f hf => by
    rcases mem_union.1 hf with h | h
    · exact hα f h
    · exact hβ f h, hc, (card_union_le _ _).trans (by omega)⟩

/-- Coverage for partial partitions of at most `2 k` blocks. -/
theorem qcov2 {φ : Fm} (hG : SGood q U vx ρ k E φ) (hroom : q * (3 * k) ≤ (free U ρ).card)
    {π : Finset (Finset ℕ)} (hπ : ∀ f ∈ π, f ⊆ free U ρ) (hπm : PP q π) (hπk : π.card ≤ 2 * k) :
    ∃ α ∈ (E φ).1 ∪ (E φ).2, Compat q α π :=
  hG.cov π hπ hπm (le_trans (Nat.mul_le_mul_left _ (by omega)) hroom)

/-- A line with no false branch is hit by a true branch of a disjunct. -/
theorem qpremise_hit {T : Seq} (hG : SGood q U vx ρ k E (lineF T)) (hT : (E (lineF T)).2 = ∅)
    (hroom : q * (3 * k) ≤ (free U ρ).card) {π : Finset (Finset ℕ)} (hπ : ∀ f ∈ π, f ⊆ free U ρ)
    (hπm : PP q π) (hπk : π.card ≤ 2 * k) : ∃ ψ ∈ dsOf T, ∃ γ ∈ (E ψ).1, Compat q γ π := by
  obtain ⟨ε, hε, hc⟩ := qcov2 hG hroom hπ hπm hπk
  rw [hT, union_empty] at hε
  have hl := hG.loc; simp only [lineF, QLoc] at hl
  obtain ⟨ψ, hψ, γ, hγ, hγε⟩ := hl.1 ε hε
  exact ⟨ψ, hψ, γ, hγ, compat_mono hc hγε subset_rfl⟩

theorem qfalse_branch {S : Seq} (hG : SGood q U vx ρ k E (lineF S)) {α : Finset (Finset ℕ)}
    (hα : α ∈ (E (lineF S)).2) :
    ((∀ f ∈ α, f ⊆ free U ρ) ∧ PP q α ∧ α.card ≤ k) ∧
      ∀ ψ ∈ dsOf S, ∀ γ ∈ (E ψ).1, ¬ Compat q α γ := by
  refine ⟨hG.mem α (mem_union.2 (Or.inr hα)), ?_⟩
  have hl := hG.loc; simp only [lineF, QLoc] at hl
  exact hl.2 α hα

theorem sgoodLine_line {T : Seq} (h : SGoodLine q U vx ρ k E T) : SGood q U vx ρ k E (lineF T) :=
  h _ (self_mem_subs _)

theorem sgoodLine_ds {T : Seq} (h : SGoodLine q U vx ρ k E T) {ψ : Fm} (hψ : ψ ∈ dsOf T) :
    ψ ∈ subs (lineF T) := sub_or (self_mem_subs _) hψ

/-- One inference preserves "no false branch". -/
theorem qstep_sound {p : ℕ} {F : CNF} {prev : List Seq} {S : Seq} (hstep : FStep p F prev S)
    (hroom : q * (3 * k) ≤ (free U ρ).card)
    (hprev : ∀ T ∈ prev, (E (lineF T)).2 = ∅) (hGprev : ∀ T ∈ prev, SGoodLine q U vx ρ k E T)
    (hGS : SGoodLine q U vx ρ k E S) (hmf : ∀ φ ∈ S.1 ++ S.2, ∀ ψ ∈ subs φ, isMod ψ = false)
    (hF : SClauseHit q U vx ρ k E F) : (E (lineF S)).2 = ∅ := by
  have hLS := sgoodLine_line hGS
  ext α
  simp only [Finset.notMem_empty, iff_false]
  intro hα
  obtain ⟨⟨hαf, hαm, hαk⟩, hαx⟩ := qfalse_branch hLS hα
  have hdS : ∀ ψ ∈ dsOf S, SGood q U vx ρ k E ψ := fun ψ hψ => hGS ψ (sgoodLine_ds hGS hψ)
  have hαk2 : α.card ≤ 2 * k := by omega
  -- the mod free hypothesis rules out the MOD axioms
  have hnm : ∀ φ ∈ S.1 ++ S.2, isMod φ = false := fun φ hφ => hmf φ hφ φ (self_mem_subs φ)
  rcases hstep with ⟨C, hC, rfl⟩ | ⟨φ, rfl⟩ | rfl | rfl | rfl | ⟨r, -, rfl⟩ |
    ⟨r, φ, l, rfl⟩ | ⟨r, φ, l, rfl⟩ | ⟨r, φ, l, rfl⟩ | ⟨r, φ, l, rfl⟩ |
    ⟨T, hT, h1, h2⟩ | ⟨φ, h1, h2⟩ | ⟨φ, Γ, Δ, rfl, h1⟩ | ⟨φ, Γ, Δ, rfl, h1⟩ |
    ⟨l, Γ, Δ, φ, hφl, rfl, h1⟩ | ⟨l, Γ, Δ, rfl, h1⟩ | ⟨l, Γ, Δ, rfl, h1⟩ |
    ⟨l, Γ, Δ, φ, hφl, rfl, h1⟩
  · -- hypothesis clause
    have hds : clauseFm C ∈ dsOf ([], [clauseFm C]) := by simp [dsOf]
    have hG := hdS _ hds
    obtain ⟨ε, hε, hc⟩ := qcov2 hG hroom hαf hαm hαk2
    rcases mem_union.1 hε with hε | hε
    · exact hαx _ hds ε hε (qcompat_symm hc)
    · have hl := hG.loc; simp only [clauseFm, QLoc] at hl
      obtain ⟨hεf, hεm, hεk⟩ := hG.mem ε (mem_union.2 (Or.inr hε))
      obtain ⟨lit, hlit, γ, hγ, hγε⟩ := hF C hC
        (fun φ hφ => hGS φ (subs_trans _ (sgoodLine_ds hGS hds) hφ)) ε hεf hεm hεk
      exact hl.2 ε hε (litFm lit) (List.mem_map.2 ⟨lit, mem_toList.2 hlit, rfl⟩) γ hγ
        (qcompat_symm hγε)
  · -- axiom φ ⊢ φ
    have hd1 : Fm.neg φ ∈ dsOf ([φ], [φ]) := by simp [dsOf]
    have hd2 : φ ∈ dsOf ([φ], [φ]) := by simp [dsOf]
    have hGn := hdS _ hd1
    have hG : SGood q U vx ρ k E φ := hGS φ (sub_neg (sgoodLine_ds hGS hd1))
    obtain ⟨β, hβ, hc⟩ := qcov2 hG hroom hαf hαm hαk2
    rcases mem_union.1 hβ with hβ | hβ
    · exact hαx φ hd2 β hβ (qcompat_symm hc)
    · exact hαx _ hd1 β (by rw [(sgood_neg hGn).1]; exact hβ) (qcompat_symm hc)
  · -- ⊢ AND []
    have hd : Fm.and [] ∈ dsOf ([], [.and []]) := by simp [dsOf]
    have hG := hdS _ hd
    obtain ⟨β, hβ, hc⟩ := qcov2 hG hroom hαf hαm hαk2
    have hl := hG.loc; simp only [QLoc] at hl
    rcases mem_union.1 hβ with hβ | hβ
    · exact hαx _ hd β hβ (qcompat_symm hc)
    · obtain ⟨ψ, hψ, -⟩ := hl.1 β hβ; simp at hψ
  · -- OR [] ⊢
    have hd : Fm.neg (.or []) ∈ dsOf ([.or []], []) := by simp [dsOf]
    have hGn := hdS _ hd
    have hG : SGood q U vx ρ k E (.or []) := hGS _ (sub_neg (sgoodLine_ds hGS hd))
    obtain ⟨β, hβ, hc⟩ := qcov2 hG hroom hαf hαm hαk2
    have hl := hG.loc; simp only [QLoc] at hl
    rcases mem_union.1 hβ with hβ | hβ
    · obtain ⟨ψ, hψ, -⟩ := hl.1 β hβ; simp at hψ
    · exact hαx _ hd β (by rw [(sgood_neg hGn).1]; exact hβ) (qcompat_symm hc)
  · exact absurd (hnm (.mod 0 []) (by simp)) (by simp [isMod])
  · exact absurd (hnm (.mod r []) (by simp)) (by simp [isMod])
  · exact absurd (hnm (.mod r (φ :: l)) (by simp)) (by simp [isMod])
  · exact absurd (hnm (.mod r (φ :: l)) (by simp)) (by simp [isMod])
  · exact absurd (hnm (.mod r (φ :: l)) (by simp)) (by simp [isMod])
  · exact absurd (hnm (.mod r l) (by simp)) (by simp [isMod])
  · -- weakening
    obtain ⟨ψ, hψ, γ, hγ, hc⟩ := qpremise_hit (sgoodLine_line (hGprev T hT)) (hprev T hT) hroom
      hαf hαm hαk2
    refine hαx ψ ?_ γ hγ (qcompat_symm hc)
    rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
    · exact mem_dsOf.2 (Or.inl ⟨χ, h1 hχ, rfl⟩)
    · exact mem_dsOf.2 (Or.inr (h2 hψ))
  · -- cut
    have hGφ : SGood q U vx ρ k E φ := hGprev _ h1 φ (sgoodLine_ds (hGprev _ h1) (by simp [dsOf]))
    obtain ⟨β, hβ, hc⟩ := qcov2 hGφ hroom hαf hαm hαk2
    obtain ⟨hβf, hβm, hβk⟩ := hGφ.mem β hβ
    obtain ⟨huf, hum, huk⟩ := qunion_small hβf hαf hc hβk hαk
    rcases mem_union.1 hβ with hβ | hβ
    · obtain ⟨ψ, hψ, γ, hγ, hcγ⟩ := qpremise_hit (sgoodLine_line (hGprev _ h2)) (hprev _ h2)
        hroom huf hum huk
      rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
      · rcases List.mem_cons.1 hχ with rfl | hχ
        · have hGn : SGood q U vx ρ k E (.neg χ) := hGprev _ h2 _ (sgoodLine_ds (hGprev _ h2) hψ)
          rw [(sgood_neg hGn).1] at hγ
          exact hGφ.inc β hβ γ hγ (qcompat_symm (qcompat_left hcγ))
        · exact hαx _ (mem_dsOf.2 (Or.inl ⟨χ, hχ, rfl⟩)) γ hγ (qcompat_symm (qcompat_right hcγ))
      · exact hαx _ (mem_dsOf.2 (Or.inr hψ)) γ hγ (qcompat_symm (qcompat_right hcγ))
    · obtain ⟨ψ, hψ, γ, hγ, hcγ⟩ := qpremise_hit (sgoodLine_line (hGprev _ h1)) (hprev _ h1)
        hroom huf hum huk
      rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
      · exact hαx _ (mem_dsOf.2 (Or.inl ⟨χ, hχ, rfl⟩)) γ hγ (qcompat_symm (qcompat_right hcγ))
      · rcases List.mem_cons.1 hψ with rfl | hψ
        · exact hGφ.inc γ hγ β hβ (qcompat_left hcγ)
        · exact hαx _ (mem_dsOf.2 (Or.inr hψ)) γ hγ (qcompat_symm (qcompat_right hcγ))
  · -- ¬ left
    obtain ⟨ψ, hψ, γ, hγ, hc⟩ := qpremise_hit (sgoodLine_line (hGprev _ h1)) (hprev _ h1) hroom
      hαf hαm hαk2
    rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
    · exact hαx _ (mem_dsOf.2 (Or.inl ⟨χ, List.mem_cons_of_mem _ hχ, rfl⟩)) γ hγ (qcompat_symm hc)
    · rcases List.mem_cons.1 hψ with rfl | hψ
      · have hd : Fm.neg (.neg ψ) ∈ dsOf (.neg ψ :: Γ, Δ) := by simp [dsOf]
        have hGnn := hdS _ hd
        have hGn : SGood q U vx ρ k E (.neg ψ) := hGS _ (sub_neg (sgoodLine_ds hGS hd))
        refine hαx _ hd γ ?_ (qcompat_symm hc)
        rw [(sgood_neg hGnn).1, (sgood_neg hGn).2]; exact hγ
      · exact hαx _ (mem_dsOf.2 (Or.inr hψ)) γ hγ (qcompat_symm hc)
  · -- ¬ right
    obtain ⟨ψ, hψ, γ, hγ, hc⟩ := qpremise_hit (sgoodLine_line (hGprev _ h1)) (hprev _ h1) hroom
      hαf hαm hαk2
    rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
    · rcases List.mem_cons.1 hχ with rfl | hχ
      · exact hαx _ (mem_dsOf.2 (Or.inr (List.mem_cons_self))) γ hγ (qcompat_symm hc)
      · exact hαx _ (mem_dsOf.2 (Or.inl ⟨χ, hχ, rfl⟩)) γ hγ (qcompat_symm hc)
    · exact hαx _ (mem_dsOf.2 (Or.inr (List.mem_cons_of_mem _ hψ))) γ hγ (qcompat_symm hc)
  · -- AND left
    have hd : Fm.neg (.and l) ∈ dsOf (.and l :: Γ, Δ) := by simp [dsOf]
    have hGna := hdS _ hd
    have hGa : SGood q U vx ρ k E (.and l) := hGS _ (sub_neg (sgoodLine_ds hGS hd))
    obtain ⟨ψ, hψ, γ, hγ, hc⟩ := qpremise_hit (sgoodLine_line (hGprev _ h1)) (hprev _ h1) hroom
      hαf hαm hαk2
    rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
    · rcases List.mem_cons.1 hχ with rfl | hχ
      · have hGn : SGood q U vx ρ k E (.neg χ) := hGprev _ h1 _ (sgoodLine_ds (hGprev _ h1) hψ)
        have hγ' : γ ∈ (E χ).2 := by rw [← (sgood_neg hGn).1]; exact hγ
        obtain ⟨hγf, hγm, hγk⟩ := hGn.mem γ (mem_union.2 (Or.inl hγ))
        obtain ⟨huf, hum, huk⟩ := qunion_small hγf hαf hc hγk hαk
        obtain ⟨ε, hε, hcε⟩ := qcov2 hGa hroom huf hum huk
        have hl := hGa.loc; simp only [QLoc] at hl
        rcases mem_union.1 hε with hε | hε
        · exact hl.2 ε hε χ hφl γ hγ' (qcompat_left hcε)
        · exact hαx _ hd ε (by rw [(sgood_neg hGna).1]; exact hε) (qcompat_symm (qcompat_right hcε))
      · exact hαx _ (mem_dsOf.2 (Or.inl ⟨χ, List.mem_cons_of_mem _ hχ, rfl⟩)) γ hγ
          (qcompat_symm hc)
    · exact hαx _ (mem_dsOf.2 (Or.inr hψ)) γ hγ (qcompat_symm hc)
  · -- AND right
    have hd : Fm.and l ∈ dsOf (Γ, .and l :: Δ) := by simp [dsOf]
    have hGa := hdS _ hd
    obtain ⟨ε, hε, hcε⟩ := qcov2 hGa hroom hαf hαm hαk2
    rcases mem_union.1 hε with hε | hε
    · exact hαx _ hd ε hε (qcompat_symm hcε)
    · have hl := hGa.loc; simp only [QLoc] at hl
      obtain ⟨φ, hφl, δ, hδ, hδε⟩ := hl.1 ε hε
      have hGφ : SGood q U vx ρ k E φ := hGS _ (sub_and (sgoodLine_ds hGS hd) hφl)
      obtain ⟨hεf, hεm, hεk⟩ := hGa.mem ε (mem_union.2 (Or.inr hε))
      obtain ⟨huf, hum, huk⟩ := qunion_small hεf hαf hcε hεk hαk
      obtain ⟨ψ, hψ, η, hη, hc⟩ := qpremise_hit (sgoodLine_line (hGprev _ (h1 φ hφl)))
        (hprev _ (h1 φ hφl)) hroom huf hum huk
      rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
      · exact hαx _ (mem_dsOf.2 (Or.inl ⟨χ, hχ, rfl⟩)) η hη (qcompat_symm (qcompat_right hc))
      · rcases List.mem_cons.1 hψ with rfl | hψ
        · exact hGφ.inc η hη δ hδ (compat_mono (qcompat_left hc) subset_rfl hδε)
        · exact hαx _ (mem_dsOf.2 (Or.inr (List.mem_cons_of_mem _ hψ))) η hη
            (qcompat_symm (qcompat_right hc))
  · -- OR left
    have hd : Fm.neg (.or l) ∈ dsOf (.or l :: Γ, Δ) := by simp [dsOf]
    have hGno := hdS _ hd
    have hGo : SGood q U vx ρ k E (.or l) := hGS _ (sub_neg (sgoodLine_ds hGS hd))
    obtain ⟨ε, hε, hcε⟩ := qcov2 hGo hroom hαf hαm hαk2
    rcases mem_union.1 hε with hε | hε
    · have hl := hGo.loc; simp only [QLoc] at hl
      obtain ⟨φ, hφl, δ, hδ, hδε⟩ := hl.1 ε hε
      have hGφ : SGood q U vx ρ k E φ := hGS _ (sub_or (sub_neg (sgoodLine_ds hGS hd)) hφl)
      obtain ⟨hεf, hεm, hεk⟩ := hGo.mem ε (mem_union.2 (Or.inl hε))
      obtain ⟨huf, hum, huk⟩ := qunion_small hεf hαf hcε hεk hαk
      obtain ⟨ψ, hψ, η, hη, hc⟩ := qpremise_hit (sgoodLine_line (hGprev _ (h1 φ hφl)))
        (hprev _ (h1 φ hφl)) hroom huf hum huk
      rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
      · rcases List.mem_cons.1 hχ with rfl | hχ
        · have hGn : SGood q U vx ρ k E (.neg χ) :=
            hGprev _ (h1 χ hφl) _ (sgoodLine_ds (hGprev _ (h1 χ hφl)) hψ)
          rw [(sgood_neg hGn).1] at hη
          exact hGφ.inc δ hδ η hη (qcompat_symm (compat_mono (qcompat_left hc) subset_rfl hδε))
        · exact hαx _ (mem_dsOf.2 (Or.inl ⟨χ, List.mem_cons_of_mem _ hχ, rfl⟩)) η hη
            (qcompat_symm (qcompat_right hc))
      · exact hαx _ (mem_dsOf.2 (Or.inr hψ)) η hη (qcompat_symm (qcompat_right hc))
    · exact hαx _ hd ε (by rw [(sgood_neg hGno).1]; exact hε) (qcompat_symm hcε)
  · -- OR right
    have hd : Fm.or l ∈ dsOf (Γ, .or l :: Δ) := by simp [dsOf]
    have hGo := hdS _ hd
    obtain ⟨ψ, hψ, γ, hγ, hc⟩ := qpremise_hit (sgoodLine_line (hGprev _ h1)) (hprev _ h1) hroom
      hαf hαm hαk2
    rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
    · exact hαx _ (mem_dsOf.2 (Or.inl ⟨χ, hχ, rfl⟩)) γ hγ (qcompat_symm hc)
    · rcases List.mem_cons.1 hψ with rfl | hψ
      · have hGψ : SGood q U vx ρ k E ψ := hGprev _ h1 _ (sgoodLine_ds (hGprev _ h1) (by simp [dsOf]))
        obtain ⟨hγf, hγm, hγk⟩ := hGψ.mem γ (mem_union.2 (Or.inl hγ))
        obtain ⟨huf, hum, huk⟩ := qunion_small hγf hαf hc hγk hαk
        obtain ⟨ε, hε, hcε⟩ := qcov2 hGo hroom huf hum huk
        have hl := hGo.loc; simp only [QLoc] at hl
        rcases mem_union.1 hε with hε | hε
        · exact hαx _ hd ε hε (qcompat_symm (qcompat_right hcε))
        · exact hl.2 ε hε ψ hφl γ hγ (qcompat_left hcε)
      · exact hαx _ (mem_dsOf.2 (Or.inr (List.mem_cons_of_mem _ hψ))) γ hγ (qcompat_symm hc)


/-- **k-evaluation soundness with Count_p axioms**: if every hypothesis clause is hit and every
Count_p instance line has no false branch, then no line of a mod free proof has a false branch. -/
theorem qkeval_sound {p : ℕ} {F : CNF} {L : List Seq} (hL : FProofC p F L) (hmf : ModFree L)
    (hE : ∀ S ∈ L, SGoodLine q U vx ρ k E S) (hF : SClauseHit q U vx ρ k E F)
    (hroom : q * (3 * k) ≤ (free U ρ).card)
    (hAx : ∀ S ∈ L, CountInst p S → (E (lineF S)).2 = ∅) : ∀ S ∈ L, (E (lineF S)).2 = ∅ := by
  have key : ∀ j (hj : j < L.length), (E (lineF (L.get ⟨j, hj⟩))).2 = ∅ := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    intro hj
    have hmem : L.get ⟨j, hj⟩ ∈ L := List.get_mem _ _
    rcases hL j hj with hstep | hcnt
    · refine qstep_sound hstep hroom (fun T hT => ?_) (fun T hT => hE T (List.mem_of_mem_take hT))
        (hE _ hmem) (hmf _ hmem) hF
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hT
      have hij : i < j := by simp at hi; omega
      have := ih i hij (by simp at hi; omega)
      simp only [List.getElem_take]
      simpa using this
    · exact hAx _ hmem hcnt
  intro S hS
  obtain ⟨⟨j, hj⟩, rfl⟩ := List.mem_iff_get.1 hS
  exact key j hj

end Sound

end

end QP

end SATurday.ProofComplexity
