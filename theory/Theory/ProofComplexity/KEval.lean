import Theory.ProofComplexity.AC0pFrege
import Theory.ProofComplexity.Matching

/-!
# k-evaluations for bounded depth Frege (Ladder Rung R4, 1B.4)

A `k`-evaluation over a matching restriction `ρ` assigns to each formula `φ` two sets of free
partial matchings of size at most `k`: `(E φ).1` (branches forcing `φ` true) and `(E φ).2`
(branches forcing it false), such that the two sides are pairwise incompatible, every free
partial matching leaving room is compatible with some member (coverage), and the sets respect
the connectives (negation swaps the sides; a true branch of an `OR` extends a true branch of a
disjunct, a false branch is incompatible with every true branch of a disjunct; dually for `AND`;
a variable `x_{ij}` is forced by containing the edge `(i, j)` or contradicting it).

Each sequent `Γ ⊢ Δ` of a proof is represented by its line formula `OR (¬Γ, Δ)`. If every
hypothesis clause is hit by a true branch of one of its literals, then every line of a mod free
proof has no false branch (`keval_sound`), so the empty sequent never occurs.

LOG: R4 KEval module (k-evaluations and their soundness)
-/

namespace SATurday.ProofComplexity

open Finset

noncomputable section

open Classical

/-! ## Subformulas -/

/-- All subformulas (with repetitions). -/
def subs : Fm → List Fm
  | .var i => [.var i]
  | .neg φ => .neg φ :: subs φ
  | .and l => .and l :: (l.attach.map fun ⟨φ, _⟩ => subs φ).flatten
  | .or l => .or l :: (l.attach.map fun ⟨φ, _⟩ => subs φ).flatten
  | .mod r l => .mod r l :: (l.attach.map fun ⟨φ, _⟩ => subs φ).flatten

theorem subs_and (l : List Fm) : subs (.and l) = .and l :: (l.map subs).flatten := by
  rw [subs]; have := Fm.attach_map l subs; simp only at this; rw [this]

theorem subs_or (l : List Fm) : subs (.or l) = .or l :: (l.map subs).flatten := by
  rw [subs]; have := Fm.attach_map l subs; simp only at this; rw [this]

theorem subs_mod (r : ℕ) (l : List Fm) : subs (.mod r l) = .mod r l :: (l.map subs).flatten := by
  rw [subs]; have := Fm.attach_map l subs; simp only at this; rw [this]

theorem self_mem_subs (φ : Fm) : φ ∈ subs φ := by
  cases φ with
  | var i => simp [subs]
  | neg φ => simp [subs]
  | and l => rw [subs_and]; simp
  | or l => rw [subs_or]; simp
  | mod r l => rw [subs_mod]; simp

theorem subs_trans : ∀ (ψ : Fm) {φ : Fm}, φ ∈ subs ψ → subs φ ⊆ subs ψ
  | .var i, φ, h => by simp [subs] at h; subst h; exact List.Subset.refl _
  | .neg χ, φ, h => by
      rw [subs, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.Subset.refl _
      · rw [subs]; exact (subs_trans χ h).trans (List.subset_cons_self _ _)
  | .and l, φ, h => by
      rw [subs_and, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.Subset.refl _
      · obtain ⟨_, ⟨χ, hχ, rfl⟩, hφ⟩ := List.mem_flatten.1 h |>.imp fun _ => And.imp_left List.mem_map.1
        have : sizeOf χ < sizeOf (Fm.and l) := by
          have := List.sizeOf_lt_of_mem hχ; simp only [Fm.and.sizeOf_spec]; omega
        rw [subs_and]
        refine (subs_trans χ hφ).trans ?_
        intro x hx
        exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨subs χ, List.mem_map.2 ⟨χ, hχ, rfl⟩, hx⟩)
  | .or l, φ, h => by
      rw [subs_or, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.Subset.refl _
      · obtain ⟨_, ⟨χ, hχ, rfl⟩, hφ⟩ := List.mem_flatten.1 h |>.imp fun _ => And.imp_left List.mem_map.1
        have : sizeOf χ < sizeOf (Fm.or l) := by
          have := List.sizeOf_lt_of_mem hχ; simp only [Fm.or.sizeOf_spec]; omega
        rw [subs_or]
        refine (subs_trans χ hφ).trans ?_
        intro x hx
        exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨subs χ, List.mem_map.2 ⟨χ, hχ, rfl⟩, hx⟩)
  | .mod r l, φ, h => by
      rw [subs_mod, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.Subset.refl _
      · obtain ⟨_, ⟨χ, hχ, rfl⟩, hφ⟩ := List.mem_flatten.1 h |>.imp fun _ => And.imp_left List.mem_map.1
        have : sizeOf χ < sizeOf (Fm.mod r l) := by
          have := List.sizeOf_lt_of_mem hχ; simp only [Fm.mod.sizeOf_spec]; omega
        rw [subs_mod]
        refine (subs_trans χ hφ).trans ?_
        intro x hx
        exact List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨subs χ, List.mem_map.2 ⟨χ, hχ, rfl⟩, hx⟩)

theorem sub_neg {ψ χ : Fm} (h : .neg χ ∈ subs ψ) : χ ∈ subs ψ :=
  subs_trans ψ h (by rw [subs]; exact List.mem_cons_of_mem _ (self_mem_subs χ))

theorem sub_and {ψ χ : Fm} {l : List Fm} (h : .and l ∈ subs ψ) (hχ : χ ∈ l) : χ ∈ subs ψ :=
  subs_trans ψ h (by
    rw [subs_and]
    exact List.mem_cons_of_mem _ (List.mem_flatten.2
      ⟨subs χ, List.mem_map.2 ⟨χ, hχ, rfl⟩, self_mem_subs χ⟩))

theorem sub_or {ψ χ : Fm} {l : List Fm} (h : .or l ∈ subs ψ) (hχ : χ ∈ l) : χ ∈ subs ψ :=
  subs_trans ψ h (by
    rw [subs_or]
    exact List.mem_cons_of_mem _ (List.mem_flatten.2
      ⟨subs χ, List.mem_map.2 ⟨χ, hχ, rfl⟩, self_mem_subs χ⟩))

/-- A formula without `MOD` connectives. -/
def isMod : Fm → Bool
  | .mod _ _ => true
  | _ => false

/-- Mod free proofs: no `MOD` subformula anywhere. -/
def ModFree (L : List Seq) : Prop := ∀ S ∈ L, ∀ φ ∈ S.1 ++ S.2, ∀ ψ ∈ subs φ, isMod ψ = false

/-! ## Line formulas -/

/-- Disjuncts of the line formula of a sequent. -/
def dsOf (S : Seq) : List Fm := S.1.map .neg ++ S.2

/-- The line formula `OR (¬Γ, Δ)`. -/
def lineF (S : Seq) : Fm := .or (dsOf S)

theorem mem_dsOf {S : Seq} {ψ : Fm} : ψ ∈ dsOf S ↔ (∃ φ ∈ S.1, ψ = .neg φ) ∨ ψ ∈ S.2 := by
  simp [dsOf, List.mem_append, List.mem_map, eq_comm]

/-! ## k-evaluations -/

/-- An evaluation: true branches and false branches of each formula. -/
abbrev Eval := Fm → Finset Mt × Finset Mt

/-- Local conditions tying an evaluation to the connectives. -/
def Local (P H : Finset ℕ) (vx : ℕ → ℕ × ℕ) (ρ : Mt) (E : Eval) : Fm → Prop
  | .var v => vx v ∈ P ×ˢ H →
      (∀ α ∈ (E (.var v)).1, vx v ∈ α ∪ ρ) ∧
      (∀ α ∈ (E (.var v)).2, ¬ IsMatch (insert (vx v) (α ∪ ρ)))
  | .neg ψ => E (.neg ψ) = ((E ψ).2, (E ψ).1)
  | .and l => (∀ α ∈ (E (.and l)).2, ∃ ψ ∈ l, ∃ β ∈ (E ψ).2, β ⊆ α) ∧
      (∀ α ∈ (E (.and l)).1, ∀ ψ ∈ l, ∀ β ∈ (E ψ).2, ¬ Compat α β)
  | .or l => (∀ α ∈ (E (.or l)).1, ∃ ψ ∈ l, ∃ β ∈ (E ψ).1, β ⊆ α) ∧
      (∀ α ∈ (E (.or l)).2, ∀ ψ ∈ l, ∀ β ∈ (E ψ).1, ¬ Compat α β)
  | .mod _ _ => True

/-- A formula well evaluated at depth `k` over `ρ`. -/
structure Good (P H : Finset ℕ) (vx : ℕ → ℕ × ℕ) (ρ : Mt) (k : ℕ) (E : Eval) (φ : Fm) : Prop where
  mem : ∀ α ∈ (E φ).1 ∪ (E φ).2, α ⊆ freeE P H ρ ∧ IsMatch α ∧ α.card ≤ k
  inc : ∀ α ∈ (E φ).1, ∀ β ∈ (E φ).2, ¬ Compat α β
  cov : ∀ π, π ⊆ freeE P H ρ → IsMatch π → π.card + 3 * k ≤ (fH H ρ).card →
    ∃ α ∈ (E φ).1 ∪ (E φ).2, Compat α π
  loc : Local P H vx ρ E φ

/-- Every clause of `F` is hit, against any small free matching, by a true branch of one of its
literals. -/
def ClauseHit (P H : Finset ℕ) (vx : ℕ → ℕ × ℕ) (ρ : Mt) (k : ℕ) (E : Eval) (F : CNF) : Prop :=
  ∀ C ∈ F, (∀ φ ∈ subs (clauseFm C), Good P H vx ρ k E φ) → ∀ β, β ⊆ freeE P H ρ → IsMatch β → β.card ≤ k →
    ∃ l ∈ C, ∃ γ ∈ (E (litFm l)).1, Compat γ β

section Sound

variable {P H : Finset ℕ} {vx : ℕ → ℕ × ℕ} {ρ : Mt} {k : ℕ} {E : Eval}

theorem good_neg {ψ : Fm} (h : Good P H vx ρ k E (.neg ψ)) :
    (E (.neg ψ)).1 = (E ψ).2 ∧ (E (.neg ψ)).2 = (E ψ).1 := by
  have := h.loc; simp only [Local] at this; rw [this]; exact ⟨rfl, rfl⟩

theorem union_small {α β : Mt} (hα : α ⊆ freeE P H ρ) (hβ : β ⊆ freeE P H ρ) (hc : Compat α β)
    (hαk : α.card ≤ k) (hβk : β.card ≤ k) :
    α ∪ β ⊆ freeE P H ρ ∧ IsMatch (α ∪ β) ∧ (α ∪ β).card ≤ 2 * k :=
  ⟨union_subset hα hβ, hc, (card_union_le _ _).trans (by omega)⟩

/-- Coverage for matchings of at most `2 k` edges. -/
theorem cov2 {φ : Fm} (hG : Good P H vx ρ k E φ) (hroom : 5 * k ≤ (fH H ρ).card) {π : Mt}
    (hπ : π ⊆ freeE P H ρ) (hπm : IsMatch π) (hπk : π.card ≤ 2 * k) :
    ∃ α ∈ (E φ).1 ∪ (E φ).2, Compat α π :=
  hG.cov π hπ hπm (by omega)

/-- A line with no false branch is hit by a true branch of a disjunct. -/
theorem premise_hit {T : Seq} (hG : Good P H vx ρ k E (lineF T)) (hT : (E (lineF T)).2 = ∅)
    (hroom : 5 * k ≤ (fH H ρ).card) {π : Mt} (hπ : π ⊆ freeE P H ρ) (hπm : IsMatch π)
    (hπk : π.card ≤ 2 * k) : ∃ ψ ∈ dsOf T, ∃ γ ∈ (E ψ).1, Compat γ π := by
  obtain ⟨ε, hε, hc⟩ := cov2 hG hroom hπ hπm hπk
  rw [hT, union_empty] at hε
  have hl := hG.loc; simp only [lineF, Local] at hl
  obtain ⟨ψ, hψ, γ, hγ, hγε⟩ := hl.1 ε hε
  exact ⟨ψ, hψ, γ, hγ, compat_mono hc hγε subset_rfl⟩

theorem false_branch {S : Seq} (hG : Good P H vx ρ k E (lineF S)) {α : Mt}
    (hα : α ∈ (E (lineF S)).2) :
    (α ⊆ freeE P H ρ ∧ IsMatch α ∧ α.card ≤ k) ∧
      ∀ ψ ∈ dsOf S, ∀ γ ∈ (E ψ).1, ¬ Compat α γ := by
  refine ⟨hG.mem α (mem_union.2 (Or.inr hα)), ?_⟩
  have hl := hG.loc; simp only [lineF, Local] at hl
  exact hl.2 α hα

/-- All subformulas of the line formula of `T` are well evaluated. -/
def GoodLine (P H : Finset ℕ) (vx : ℕ → ℕ × ℕ) (ρ : Mt) (k : ℕ) (E : Eval) (T : Seq) : Prop :=
  ∀ φ ∈ subs (lineF T), Good P H vx ρ k E φ

theorem goodLine_line {T : Seq} (h : GoodLine P H vx ρ k E T) : Good P H vx ρ k E (lineF T) :=
  h _ (self_mem_subs _)

theorem goodLine_ds {T : Seq} (h : GoodLine P H vx ρ k E T) {ψ : Fm} (hψ : ψ ∈ dsOf T) :
    ψ ∈ subs (lineF T) := sub_or (self_mem_subs _) hψ

theorem compat_left {γ α β : Mt} (h : Compat γ (α ∪ β)) : Compat γ α :=
  compat_mono h subset_rfl subset_union_left

theorem compat_right {γ α β : Mt} (h : Compat γ (α ∪ β)) : Compat γ β :=
  compat_mono h subset_rfl subset_union_right

/-- One inference preserves "no false branch". -/
theorem step_sound {p : ℕ} {F : CNF} {prev : List Seq} {S : Seq} (hstep : FStep p F prev S)
    (hroom : 5 * k ≤ (fH H ρ).card)
    (hprev : ∀ T ∈ prev, (E (lineF T)).2 = ∅) (hGprev : ∀ T ∈ prev, GoodLine P H vx ρ k E T)
    (hGS : GoodLine P H vx ρ k E S) (hmf : ∀ φ ∈ S.1 ++ S.2, ∀ ψ ∈ subs φ, isMod ψ = false)
    (hF : ClauseHit P H vx ρ k E F) : (E (lineF S)).2 = ∅ := by
  have hLS := goodLine_line hGS
  ext α
  simp only [Finset.notMem_empty, iff_false]
  intro hα
  obtain ⟨⟨hαf, hαm, hαk⟩, hαx⟩ := false_branch hLS hα
  have hdS : ∀ ψ ∈ dsOf S, Good P H vx ρ k E ψ := fun ψ hψ => hGS ψ (goodLine_ds hGS hψ)
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
    obtain ⟨ε, hε, hc⟩ := cov2 hG hroom hαf hαm hαk2
    rcases mem_union.1 hε with hε | hε
    · exact hαx _ hds ε hε (compat_symm hc)
    · have hl := hG.loc; simp only [clauseFm, Local] at hl
      obtain ⟨hεf, hεm, hεk⟩ := hG.mem ε (mem_union.2 (Or.inr hε))
      obtain ⟨lit, hlit, γ, hγ, hγε⟩ := hF C hC
        (fun φ hφ => hGS φ (subs_trans _ (goodLine_ds hGS hds) hφ)) ε hεf hεm hεk
      exact hl.2 ε hε (litFm lit) (List.mem_map.2 ⟨lit, mem_toList.2 hlit, rfl⟩) γ hγ
        (compat_symm hγε)
  · -- axiom φ ⊢ φ
    have hd1 : Fm.neg φ ∈ dsOf ([φ], [φ]) := by simp [dsOf]
    have hd2 : φ ∈ dsOf ([φ], [φ]) := by simp [dsOf]
    have hGn := hdS _ hd1
    have hG : Good P H vx ρ k E φ := hGS φ (sub_neg (goodLine_ds hGS hd1))
    obtain ⟨β, hβ, hc⟩ := cov2 hG hroom hαf hαm hαk2
    rcases mem_union.1 hβ with hβ | hβ
    · exact hαx φ hd2 β hβ (compat_symm hc)
    · exact hαx _ hd1 β (by rw [(good_neg hGn).1]; exact hβ) (compat_symm hc)
  · -- ⊢ AND []
    have hd : Fm.and [] ∈ dsOf ([], [.and []]) := by simp [dsOf]
    have hG := hdS _ hd
    obtain ⟨β, hβ, hc⟩ := cov2 hG hroom hαf hαm hαk2
    have hl := hG.loc; simp only [Local] at hl
    rcases mem_union.1 hβ with hβ | hβ
    · exact hαx _ hd β hβ (compat_symm hc)
    · obtain ⟨ψ, hψ, -⟩ := hl.1 β hβ; simp at hψ
  · -- OR [] ⊢
    have hd : Fm.neg (.or []) ∈ dsOf ([.or []], []) := by simp [dsOf]
    have hGn := hdS _ hd
    have hG : Good P H vx ρ k E (.or []) := hGS _ (sub_neg (goodLine_ds hGS hd))
    obtain ⟨β, hβ, hc⟩ := cov2 hG hroom hαf hαm hαk2
    have hl := hG.loc; simp only [Local] at hl
    rcases mem_union.1 hβ with hβ | hβ
    · obtain ⟨ψ, hψ, -⟩ := hl.1 β hβ; simp at hψ
    · exact hαx _ hd β (by rw [(good_neg hGn).1]; exact hβ) (compat_symm hc)
  · exact absurd (hnm (.mod 0 []) (by simp)) (by simp [isMod])
  · exact absurd (hnm (.mod r []) (by simp)) (by simp [isMod])
  · exact absurd (hnm (.mod r (φ :: l)) (by simp)) (by simp [isMod])
  · exact absurd (hnm (.mod r (φ :: l)) (by simp)) (by simp [isMod])
  · exact absurd (hnm (.mod r (φ :: l)) (by simp)) (by simp [isMod])
  · exact absurd (hnm (.mod r l) (by simp)) (by simp [isMod])
  · -- weakening
    obtain ⟨ψ, hψ, γ, hγ, hc⟩ := premise_hit (goodLine_line (hGprev T hT)) (hprev T hT) hroom
      hαf hαm hαk2
    refine hαx ψ ?_ γ hγ (compat_symm hc)
    rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
    · exact mem_dsOf.2 (Or.inl ⟨χ, h1 hχ, rfl⟩)
    · exact mem_dsOf.2 (Or.inr (h2 hψ))
  · -- cut
    have hGφ : Good P H vx ρ k E φ := hGprev _ h1 φ (goodLine_ds (hGprev _ h1) (by simp [dsOf]))
    obtain ⟨β, hβ, hc⟩ := cov2 hGφ hroom hαf hαm hαk2
    obtain ⟨hβf, hβm, hβk⟩ := hGφ.mem β hβ
    obtain ⟨huf, hum, huk⟩ := union_small hβf hαf hc hβk hαk
    rcases mem_union.1 hβ with hβ | hβ
    · obtain ⟨ψ, hψ, γ, hγ, hcγ⟩ := premise_hit (goodLine_line (hGprev _ h2)) (hprev _ h2)
        hroom huf hum huk
      rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
      · rcases List.mem_cons.1 hχ with rfl | hχ
        · have hGn : Good P H vx ρ k E (.neg χ) := hGprev _ h2 _ (goodLine_ds (hGprev _ h2) hψ)
          rw [(good_neg hGn).1] at hγ
          exact hGφ.inc β hβ γ hγ (compat_symm (compat_left hcγ))
        · exact hαx _ (mem_dsOf.2 (Or.inl ⟨χ, hχ, rfl⟩)) γ hγ (compat_symm (compat_right hcγ))
      · exact hαx _ (mem_dsOf.2 (Or.inr hψ)) γ hγ (compat_symm (compat_right hcγ))
    · obtain ⟨ψ, hψ, γ, hγ, hcγ⟩ := premise_hit (goodLine_line (hGprev _ h1)) (hprev _ h1)
        hroom huf hum huk
      rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
      · exact hαx _ (mem_dsOf.2 (Or.inl ⟨χ, hχ, rfl⟩)) γ hγ (compat_symm (compat_right hcγ))
      · rcases List.mem_cons.1 hψ with rfl | hψ
        · exact hGφ.inc γ hγ β hβ (compat_left hcγ)
        · exact hαx _ (mem_dsOf.2 (Or.inr hψ)) γ hγ (compat_symm (compat_right hcγ))
  · -- ¬ left
    obtain ⟨ψ, hψ, γ, hγ, hc⟩ := premise_hit (goodLine_line (hGprev _ h1)) (hprev _ h1) hroom
      hαf hαm hαk2
    rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
    · exact hαx _ (mem_dsOf.2 (Or.inl ⟨χ, List.mem_cons_of_mem _ hχ, rfl⟩)) γ hγ (compat_symm hc)
    · rcases List.mem_cons.1 hψ with rfl | hψ
      · have hd : Fm.neg (.neg ψ) ∈ dsOf (.neg ψ :: Γ, Δ) := by simp [dsOf]
        have hGnn := hdS _ hd
        have hGn : Good P H vx ρ k E (.neg ψ) := hGS _ (sub_neg (goodLine_ds hGS hd))
        refine hαx _ hd γ ?_ (compat_symm hc)
        rw [(good_neg hGnn).1, (good_neg hGn).2]; exact hγ
      · exact hαx _ (mem_dsOf.2 (Or.inr hψ)) γ hγ (compat_symm hc)
  · -- ¬ right
    obtain ⟨ψ, hψ, γ, hγ, hc⟩ := premise_hit (goodLine_line (hGprev _ h1)) (hprev _ h1) hroom
      hαf hαm hαk2
    rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
    · rcases List.mem_cons.1 hχ with rfl | hχ
      · exact hαx _ (mem_dsOf.2 (Or.inr (List.mem_cons_self))) γ hγ (compat_symm hc)
      · exact hαx _ (mem_dsOf.2 (Or.inl ⟨χ, hχ, rfl⟩)) γ hγ (compat_symm hc)
    · exact hαx _ (mem_dsOf.2 (Or.inr (List.mem_cons_of_mem _ hψ))) γ hγ (compat_symm hc)
  · -- AND left
    have hd : Fm.neg (.and l) ∈ dsOf (.and l :: Γ, Δ) := by simp [dsOf]
    have hGna := hdS _ hd
    have hGa : Good P H vx ρ k E (.and l) := hGS _ (sub_neg (goodLine_ds hGS hd))
    obtain ⟨ψ, hψ, γ, hγ, hc⟩ := premise_hit (goodLine_line (hGprev _ h1)) (hprev _ h1) hroom
      hαf hαm hαk2
    rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
    · rcases List.mem_cons.1 hχ with rfl | hχ
      · have hGn : Good P H vx ρ k E (.neg χ) := hGprev _ h1 _ (goodLine_ds (hGprev _ h1) hψ)
        have hγ' : γ ∈ (E χ).2 := by rw [← (good_neg hGn).1]; exact hγ
        obtain ⟨hγf, hγm, hγk⟩ := hGn.mem γ (mem_union.2 (Or.inl hγ))
        obtain ⟨huf, hum, huk⟩ := union_small hγf hαf hc hγk hαk
        obtain ⟨ε, hε, hcε⟩ := cov2 hGa hroom huf hum huk
        have hl := hGa.loc; simp only [Local] at hl
        rcases mem_union.1 hε with hε | hε
        · exact hl.2 ε hε χ hφl γ hγ' (compat_left hcε)
        · exact hαx _ hd ε (by rw [(good_neg hGna).1]; exact hε) (compat_symm (compat_right hcε))
      · exact hαx _ (mem_dsOf.2 (Or.inl ⟨χ, List.mem_cons_of_mem _ hχ, rfl⟩)) γ hγ
          (compat_symm hc)
    · exact hαx _ (mem_dsOf.2 (Or.inr hψ)) γ hγ (compat_symm hc)
  · -- AND right
    have hd : Fm.and l ∈ dsOf (Γ, .and l :: Δ) := by simp [dsOf]
    have hGa := hdS _ hd
    obtain ⟨ε, hε, hcε⟩ := cov2 hGa hroom hαf hαm hαk2
    rcases mem_union.1 hε with hε | hε
    · exact hαx _ hd ε hε (compat_symm hcε)
    · have hl := hGa.loc; simp only [Local] at hl
      obtain ⟨φ, hφl, δ, hδ, hδε⟩ := hl.1 ε hε
      have hGφ : Good P H vx ρ k E φ := hGS _ (sub_and (goodLine_ds hGS hd) hφl)
      obtain ⟨hεf, hεm, hεk⟩ := hGa.mem ε (mem_union.2 (Or.inr hε))
      obtain ⟨huf, hum, huk⟩ := union_small hεf hαf hcε hεk hαk
      obtain ⟨ψ, hψ, η, hη, hc⟩ := premise_hit (goodLine_line (hGprev _ (h1 φ hφl)))
        (hprev _ (h1 φ hφl)) hroom huf hum huk
      rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
      · exact hαx _ (mem_dsOf.2 (Or.inl ⟨χ, hχ, rfl⟩)) η hη (compat_symm (compat_right hc))
      · rcases List.mem_cons.1 hψ with rfl | hψ
        · exact hGφ.inc η hη δ hδ (compat_mono (compat_left hc) subset_rfl hδε)
        · exact hαx _ (mem_dsOf.2 (Or.inr (List.mem_cons_of_mem _ hψ))) η hη
            (compat_symm (compat_right hc))
  · -- OR left
    have hd : Fm.neg (.or l) ∈ dsOf (.or l :: Γ, Δ) := by simp [dsOf]
    have hGno := hdS _ hd
    have hGo : Good P H vx ρ k E (.or l) := hGS _ (sub_neg (goodLine_ds hGS hd))
    obtain ⟨ε, hε, hcε⟩ := cov2 hGo hroom hαf hαm hαk2
    rcases mem_union.1 hε with hε | hε
    · have hl := hGo.loc; simp only [Local] at hl
      obtain ⟨φ, hφl, δ, hδ, hδε⟩ := hl.1 ε hε
      have hGφ : Good P H vx ρ k E φ := hGS _ (sub_or (sub_neg (goodLine_ds hGS hd)) hφl)
      obtain ⟨hεf, hεm, hεk⟩ := hGo.mem ε (mem_union.2 (Or.inl hε))
      obtain ⟨huf, hum, huk⟩ := union_small hεf hαf hcε hεk hαk
      obtain ⟨ψ, hψ, η, hη, hc⟩ := premise_hit (goodLine_line (hGprev _ (h1 φ hφl)))
        (hprev _ (h1 φ hφl)) hroom huf hum huk
      rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
      · rcases List.mem_cons.1 hχ with rfl | hχ
        · have hGn : Good P H vx ρ k E (.neg χ) :=
            hGprev _ (h1 χ hφl) _ (goodLine_ds (hGprev _ (h1 χ hφl)) hψ)
          rw [(good_neg hGn).1] at hη
          exact hGφ.inc δ hδ η hη (compat_symm (compat_mono (compat_left hc) subset_rfl hδε))
        · exact hαx _ (mem_dsOf.2 (Or.inl ⟨χ, List.mem_cons_of_mem _ hχ, rfl⟩)) η hη
            (compat_symm (compat_right hc))
      · exact hαx _ (mem_dsOf.2 (Or.inr hψ)) η hη (compat_symm (compat_right hc))
    · exact hαx _ hd ε (by rw [(good_neg hGno).1]; exact hε) (compat_symm hcε)
  · -- OR right
    have hd : Fm.or l ∈ dsOf (Γ, .or l :: Δ) := by simp [dsOf]
    have hGo := hdS _ hd
    obtain ⟨ψ, hψ, γ, hγ, hc⟩ := premise_hit (goodLine_line (hGprev _ h1)) (hprev _ h1) hroom
      hαf hαm hαk2
    rcases mem_dsOf.1 hψ with ⟨χ, hχ, rfl⟩ | hψ
    · exact hαx _ (mem_dsOf.2 (Or.inl ⟨χ, hχ, rfl⟩)) γ hγ (compat_symm hc)
    · rcases List.mem_cons.1 hψ with rfl | hψ
      · have hGψ : Good P H vx ρ k E ψ := hGprev _ h1 _ (goodLine_ds (hGprev _ h1) (by simp [dsOf]))
        obtain ⟨hγf, hγm, hγk⟩ := hGψ.mem γ (mem_union.2 (Or.inl hγ))
        obtain ⟨huf, hum, huk⟩ := union_small hγf hαf hc hγk hαk
        obtain ⟨ε, hε, hcε⟩ := cov2 hGo hroom huf hum huk
        have hl := hGo.loc; simp only [Local] at hl
        rcases mem_union.1 hε with hε | hε
        · exact hαx _ hd ε hε (compat_symm (compat_right hcε))
        · exact hl.2 ε hε ψ hφl γ hγ (compat_left hcε)
      · exact hαx _ (mem_dsOf.2 (Or.inr (List.mem_cons_of_mem _ hψ))) γ hγ (compat_symm hc)

/-- **k-evaluation soundness**: every line of a mod free proof has no false branch. -/
theorem keval_sound {p : ℕ} {F : CNF} {L : List Seq} (hL : FProof p F L) (hmf : ModFree L)
    (hE : ∀ S ∈ L, GoodLine P H vx ρ k E S) (hF : ClauseHit P H vx ρ k E F)
    (hroom : 5 * k ≤ (fH H ρ).card) : ∀ S ∈ L, (E (lineF S)).2 = ∅ := by
  have key : ∀ j (hj : j < L.length), (E (lineF (L.get ⟨j, hj⟩))).2 = ∅ := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    intro hj
    have hmem : L.get ⟨j, hj⟩ ∈ L := List.get_mem _ _
    refine step_sound (hL j hj) hroom (fun T hT => ?_) (fun T hT => hE T (List.mem_of_mem_take hT))
      (hE _ hmem) (hmf _ hmem) hF
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hT
    have hij : i < j := by simp at hi; omega
    have := ih i hij (by simp at hi; omega)
    simp only [List.getElem_take]
    simpa using this
  intro S hS
  obtain ⟨⟨j, hj⟩, rfl⟩ := List.mem_iff_get.1 hS
  exact key j hj

/-- No mod free proof with a `k`-evaluation contains the empty sequent. -/
theorem keval_no_refutation {p : ℕ} {F : CNF} {L : List Seq} (hL : FProof p F L)
    (hmf : ModFree L) (hE : ∀ S ∈ L, GoodLine P H vx ρ k E S) (hF : ClauseHit P H vx ρ k E F)
    (hroom : 5 * k ≤ (fH H ρ).card) : ([], []) ∉ L := by
  intro h
  have h0 := keval_sound hL hmf hE hF hroom _ h
  have hG := goodLine_line (hE _ h)
  obtain ⟨α, hα, -⟩ := hG.cov ∅ (empty_subset _) isMatch_empty (by simp; omega)
  rw [h0, union_empty] at hα
  have hl := hG.loc; simp only [lineF, Local] at hl
  obtain ⟨ψ, hψ, -⟩ := hl.1 α hα
  simp [dsOf] at hψ

end Sound

end

end SATurday.ProofComplexity
