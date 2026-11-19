import Theory.ProofComplexity.C1Final
import Theory.ProofComplexity.AC0pFrege

/-!
# A bridge from a fragment of the AC0[p] Frege sequent calculus into `R_ρ^p`

`FProof p F L` (file `AC0pFrege.lean`) is the sequent calculus of the R4 pin.  This file
translates the proofs of a syntactic fragment of it into the bounded rank calculus `R_ρ^p` of
`C1Rank.lean`, with a polynomial bound on the number of nodes, so that `C1.c1_main` gives a size
lower bound for that fragment.

The fragment (`Flat`): every formula in every sequent is, after stripping negations, a variable
or an `AND`, `OR` or `MOD_p` gate whose members are literals (so formula depth at most one in the
sense of `Fm.depth`), all variables lie in a fixed set `V`, and the translation of every sequent
has rank at most `ρ`.  The last condition holds when every `AND` in positive position and every
`OR` in negative position has at most `ρ` members; `MOD_p` gates may have any fan in.

This is NOT a lower bound for depth one or depth two AC0[p] Frege: `AND` gates in positive
position (and `OR` gates in negative position) of fan in above `ρ ≤ ε log n` are excluded, and no
gate may have a gate as a member.

LOG: R4 depth-2 fable session, bridge file
-/

open SATurday.ProofComplexity C1

namespace FBridge

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime] {Φ : CNF} {V : Finset ℕ} {ρ : ℕ}

/-! ## Good terms and list derivations in `R_ρ^p` -/

/-- A term of rank at most `ρ` with all variables in `V`. -/
def GoodT (V : Finset ℕ) (ρ : ℕ) (T : Term p) : Prop :=
  rank T ≤ ρ ∧ ∀ l ∈ T, l.1.support ⊆ V

/-- A line all of whose terms are good. -/
def GoodL (V : Finset ℕ) (ρ : ℕ) (L : RLine p) : Prop := ∀ T ∈ L, GoodT V ρ T

theorem rank_le_card (T : Term p) : rank T ≤ T.card :=
  finrank_span_finset_le_card (R := ZMod p) T

theorem rank_mono {T T' : Term p} (h : T ⊆ T') : rank T ≤ rank T' := by
  unfold rank
  exact Submodule.finrank_mono (Submodule.span_mono (by exact_mod_cast h))

theorem GoodT.mono {T T' : Term p} (h : T ⊆ T') (hT : GoodT V ρ T') : GoodT V ρ T :=
  ⟨(rank_mono h).trans hT.1, fun l hl => hT.2 l (h hl)⟩

theorem goodT_empty : GoodT V ρ (∅ : Term p) :=
  ⟨by have := rank_le_card (∅ : Term p); simp at this; omega, by simp⟩

theorem goodT_singleton (hρ : 1 ≤ ρ) {f : AffForm p} (hf : f.1.support ⊆ V) :
    GoodT V ρ ({f} : Term p) :=
  ⟨(rank_le_card _).trans (by simpa using hρ), by simpa using hf⟩

/-- A list of lines in which every line follows by a rule of `R_ρ^p` from lines of the list
built so far, every line being good. -/
inductive Der (Φ : CNF) (V : Finset ℕ) (ρ : ℕ) : List (RLine p) → Prop
  | nil : Der Φ V ρ []
  | snoc {Ls : List (RLine p)} {L : RLine p} (prems : List (RLine p)) (h : Der Φ V ρ Ls)
      (hp : ∀ M ∈ prems, M ∈ Ls) (hi : RInfer Φ ρ prems L) (hg : GoodL V ρ L) :
      Der Φ V ρ (Ls ++ [L])

theorem Der.good {Ls : List (RLine p)} (h : Der Φ V ρ Ls) : ∀ L ∈ Ls, GoodL V ρ L := by
  induction h with
  | nil => intro L hL; simp at hL
  | snoc prems h hp hi hg ih =>
    intro L hL
    rcases List.mem_append.1 hL with hL | hL
    · exact ih L hL
    · rw [List.mem_singleton] at hL; subst hL; exact hg

/-- `Ls₂` is a derivation containing all lines of `Ls` and at most `c` lines longer. -/
def Ext (Φ : CNF) (V : Finset ℕ) (ρ : ℕ) (Ls Ls₂ : List (RLine p)) (c : ℕ) : Prop :=
  Der Φ V ρ Ls₂ ∧ (∀ M ∈ Ls, M ∈ Ls₂) ∧ Ls₂.length ≤ Ls.length + c

theorem Ext.refl {Ls : List (RLine p)} (h : Der Φ V ρ Ls) : Ext Φ V ρ Ls Ls 0 :=
  ⟨h, fun _ hM => hM, le_rfl⟩

theorem Ext.trans {Ls Ls₂ Ls₃ : List (RLine p)} {c c' : ℕ} (h : Ext Φ V ρ Ls Ls₂ c)
    (h' : Ext Φ V ρ Ls₂ Ls₃ c') : Ext Φ V ρ Ls Ls₃ (c + c') :=
  ⟨h'.1, fun M hM => h'.2.1 M (h.2.1 M hM), by have := h.2.2; have := h'.2.2; omega⟩

theorem Ext.mono {Ls Ls₂ : List (RLine p)} {c c' : ℕ} (h : Ext Φ V ρ Ls Ls₂ c) (hc : c ≤ c') :
    Ext Φ V ρ Ls Ls₂ c' :=
  ⟨h.1, h.2.1, h.2.2.trans (by omega)⟩

/-- One rule application. -/
theorem reach_step {Ls : List (RLine p)} (h : Der Φ V ρ Ls) {prems : List (RLine p)}
    {L : RLine p} (hp : ∀ M ∈ prems, M ∈ Ls) (hi : RInfer Φ ρ prems L) (hg : GoodL V ρ L) :
    ∃ Ls₂, Ext Φ V ρ Ls Ls₂ 1 ∧ L ∈ Ls₂ :=
  ⟨Ls ++ [L], ⟨Der.snoc prems h hp hi hg, fun M hM => List.mem_append_left _ hM, by simp⟩,
    by simp⟩

theorem reach_weak {Ls : List (RLine p)} (h : Der Φ V ρ Ls) {L L' : RLine p} (hL : L ∈ Ls)
    (hsub : L ⊆ L') (hg : GoodL V ρ L') : ∃ Ls₂, Ext Φ V ρ Ls Ls₂ 1 ∧ L' ∈ Ls₂ :=
  reach_step h (prems := [L]) (by simpa using hL) (RInfer.weak L' hsub) hg

/-- Axiom lines. -/
theorem reach_axioms (Ms : List (RLine p)) :
    ∀ {Ls : List (RLine p)}, Der Φ V ρ Ls → (∀ M ∈ Ms, RInfer Φ ρ [] M ∧ GoodL V ρ M) →
      ∃ Ls₂, Ext Φ V ρ Ls Ls₂ Ms.length ∧ ∀ M ∈ Ms, M ∈ Ls₂ := by
  induction Ms with
  | nil => intro Ls h _; exact ⟨Ls, Ext.refl h, by simp⟩
  | cons M Ms ih =>
    intro Ls h hMs
    obtain ⟨Ls₂, hE, hmem⟩ := ih h (fun M' hM' => hMs M' (List.mem_cons_of_mem _ hM'))
    obtain ⟨hi, hg⟩ := hMs M (List.mem_cons_self ..)
    obtain ⟨Ls₃, hE', hM⟩ := reach_step hE.1 (prems := []) (by simp) hi hg
    refine ⟨Ls₃, (hE.trans hE').mono (by simp), fun M' hM' => ?_⟩
    rcases List.mem_cons.1 hM' with rfl | hM'
    · exact hM
    · exact hE'.2.1 _ (hmem M' hM')

/-- A line containing a term that holds on the whole cube. -/
theorem reach_true {v₀ : ℕ} (hv : v₀ ∈ V) (hρ : 1 ≤ ρ) {Ls : List (RLine p)}
    (h : Der Φ V ρ Ls) {T : Term p} (hT : ∀ a : Assignment, TrueAt (boolPt (F := ZMod p) a) T)
    {Y : RLine p} (hY : GoodL V ρ Y) (hTY : T ∈ Y) : ∃ Ls₂, Ext Φ V ρ Ls Ls₂ 3 ∧ Y ∈ Ls₂ := by
  have hsV : ((formVar v₀ : AffForm p)).1.support ⊆ V := by
    intro x hx
    have : x = v₀ := by
      by_contra hne
      simp [formVar, Ne.symm hne] at hx
    rw [this]; exact hv
  have hsV' : ((formVarSub v₀ : AffForm p)).1.support ⊆ V := hsV
  have g0 : GoodL V ρ ({{formVar v₀}, {formVarSub v₀}} : RLine p) := by
    intro T hT
    rcases Finset.mem_insert.1 hT with rfl | hT
    · exact goodT_singleton hρ hsV
    · rw [Finset.mem_singleton] at hT; subst hT; exact goodT_singleton hρ hsV'
  obtain ⟨Ls₁, hE₁, hm₁⟩ := reach_step h (prems := []) (by simp) (RInfer.taut v₀) g0
  have g1 : GoodL V ρ ({T, {formVarSub v₀}} : RLine p) := by
    intro T' hT'
    rcases Finset.mem_insert.1 hT' with rfl | hT'
    · exact hY _ hTY
    · rw [Finset.mem_singleton] at hT'; subst hT'; exact goodT_singleton hρ hsV'
  obtain ⟨Ls₂, hE₂, hm₂⟩ := reach_step hE₁.1 (prems := [{{formVar v₀}, {formVarSub v₀}}])
    (by simpa using hm₁)
    (RInfer.sem1 (T₁ := {formVar v₀}) (T₃ := some T) (by simp)
      (fun a _ _ => ⟨T, rfl, hT a⟩) ({T, {formVarSub v₀}})
      (by
        intro x hx
        obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact absurd rfl hne
        · exact Finset.mem_insert_of_mem hx)
      (by intro T' hT'; cases hT'; simp)
      (by intro T' hT'; cases hT'; exact (hY _ hTY).1)) g1
  obtain ⟨Ls₃, hE₃, hm₃⟩ := reach_step hE₂.1 (prems := [{T, {formVarSub v₀}}])
    (by simpa using hm₂)
    (RInfer.sem1 (T₁ := {formVarSub v₀}) (T₃ := some T) (by simp)
      (fun a _ _ => ⟨T, rfl, hT a⟩) Y
      (by
        intro x hx
        obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hTY
        · rw [Finset.mem_singleton] at hx; exact absurd hx hne)
      (by intro T' hT'; cases hT'; exact hTY)
      (by intro T' hT'; cases hT'; exact (hY _ hTY).1)) hY
  exact ⟨Ls₃, ((hE₁.trans hE₂).trans hE₃).mono (by norm_num), hm₃⟩

/-- Resolve every term of `P` in `L₁` against the term `U` of `L₂`, replacing `T` by `τ T`
(or dropping it when `τ T = none`). -/
theorem reach_map {L₂ : RLine p} {U : Term p} (hU : U ∈ L₂) (τ : Term p → Option (Term p))
    {Y : RLine p} (hY : GoodL V ρ Y) (hL₂ : L₂.erase U ⊆ Y) (P : Finset (Term p)) :
    (∀ T ∈ P, SemOK T (some U) (τ T) ∧ ∀ T', τ T = some T' → T' ∈ Y) →
    ∀ {Ls : List (RLine p)}, Der Φ V ρ Ls → L₂ ∈ Ls → ∀ {L₁ : RLine p}, L₁ ∈ Ls →
      L₁ \ P ⊆ Y → ∃ Ls₂, Ext Φ V ρ Ls Ls₂ (P.card + 1) ∧ Y ∈ Ls₂ := by
  induction P using Finset.induction_on with
  | empty =>
    intro _ Ls h _ L₁ h₁ hsub
    obtain ⟨Ls₂, hE, hm⟩ := reach_weak h h₁ (by simpa using hsub) hY
    exact ⟨Ls₂, hE.mono (by simp), hm⟩
  | insert T P hTP ih =>
    intro hP Ls h h₂ L₁ h₁ hsub
    have hP' : ∀ T' ∈ P, SemOK T' (some U) (τ T') ∧ ∀ T'', τ T' = some T'' → T'' ∈ Y :=
      fun T' hT' => hP T' (Finset.mem_insert_of_mem hT')
    rw [Finset.card_insert_of_notMem hTP]
    by_cases hT : T ∈ L₁
    · obtain ⟨hs, hτ⟩ := hP T (Finset.mem_insert_self ..)
      set L' : RLine p := (L₁.erase T ∪ L₂.erase U) ∪ (τ T).toFinset with hL'
      have gL' : GoodL V ρ L' := by
        intro x hx
        rcases Finset.mem_union.1 hx with hx | hx
        · rcases Finset.mem_union.1 hx with hx | hx
          · exact h.good _ h₁ _ (Finset.mem_of_mem_erase hx)
          · exact h.good _ h₂ _ (Finset.mem_of_mem_erase hx)
        · exact hY _ (hτ x (by simpa using hx))
      obtain ⟨Ls₁, hE₁, hm₁⟩ := reach_step h (prems := [L₁, L₂])
        (by intro M hM; simp at hM; rcases hM with rfl | rfl <;> assumption)
        (RInfer.sem2 (T₃ := τ T) hT hU hs L'
          (fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx))
          (fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx))
          (fun T' hT' => Finset.mem_union_right _ (by simpa using hT'))
          (fun T' hT' => (hY _ (hτ T' hT')).1)) gL'
      have hsub' : L' \ P ⊆ Y := by
        intro x hx
        obtain ⟨hx, hxP⟩ := Finset.mem_sdiff.1 hx
        rcases Finset.mem_union.1 hx with hx | hx
        · rcases Finset.mem_union.1 hx with hx | hx
          · obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
            exact hsub (Finset.mem_sdiff.2 ⟨hx, by
              intro hc
              rcases Finset.mem_insert.1 hc with hc | hc
              · exact hne hc
              · exact hxP hc⟩)
          · exact hL₂ hx
        · exact hτ x (by simpa using hx)
      obtain ⟨Ls₂, hE₂, hm₂⟩ := ih hP' hE₁.1 (hE₁.2.1 _ h₂) hm₁ hsub'
      exact ⟨Ls₂, (hE₁.trans hE₂).mono (by omega), hm₂⟩
    · have hsub' : L₁ \ P ⊆ Y := by
        intro x hx
        obtain ⟨hx, hxP⟩ := Finset.mem_sdiff.1 hx
        exact hsub (Finset.mem_sdiff.2 ⟨hx, by
          intro hc
          rcases Finset.mem_insert.1 hc with hc | hc
          · exact hT (hc ▸ hx)
          · exact hxP hc⟩)
      obtain ⟨Ls₂, hE₂, hm₂⟩ := ih hP' h h₂ h₁ hsub'
      exact ⟨Ls₂, hE₂.mono (by omega), hm₂⟩

/-- AND introduction along a list of forms: from lines `⊆ X ∪ {{f}}` for every `f` of the list,
derive `X ∪ {fs}`. -/
theorem reach_and {v₀ : ℕ} (hv : v₀ ∈ V) (hρ : 1 ≤ ρ) (X : RLine p) (fs : List (AffForm p)) :
    ∀ {Ls : List (RLine p)}, Der Φ V ρ Ls → GoodL V ρ (insert fs.toFinset X) →
      (∀ f ∈ fs, ∃ M ∈ Ls, M ⊆ insert {f} X) →
      ∃ Ls₂, Ext Φ V ρ Ls Ls₂ (fs.length + 3) ∧ insert fs.toFinset X ∈ Ls₂ := by
  induction fs with
  | nil =>
    intro Ls h hg _
    obtain ⟨Ls₂, hE, hm⟩ := reach_true hv hρ h (T := (∅ : Term p)) (fun a l hl => by simp at hl)
      hg (by simp)
    exact ⟨Ls₂, hE.mono (by simp), hm⟩
  | cons f fs ih =>
    intro Ls h hg hprem
    have hgX : ∀ T ∈ X, GoodT V ρ T := fun T hT => hg T (Finset.mem_insert_of_mem hT)
    have hgfs : GoodT V ρ (f :: fs).toFinset := hg _ (Finset.mem_insert_self ..)
    have hg' : GoodL V ρ (insert fs.toFinset X) := by
      intro T hT
      rcases Finset.mem_insert.1 hT with rfl | hT
      · exact hgfs.mono (by intro x hx; simp at hx ⊢; exact Or.inr hx)
      · exact hgX T hT
    obtain ⟨Ls₁, hE₁, hm₁⟩ := ih h hg' (fun f' hf' => hprem f' (List.mem_cons_of_mem _ hf'))
    obtain ⟨M, hM, hMsub⟩ := hprem f (List.mem_cons_self ..)
    have hM₁ := hE₁.2.1 _ hM
    by_cases hfM : ({f} : Term p) ∈ M
    · obtain ⟨Ls₂, hE₂, hm₂⟩ := reach_step hE₁.1 (prems := [insert fs.toFinset X, M])
        (by intro M' hM'; simp at hM'; rcases hM' with rfl | rfl <;> assumption)
        (RInfer.sem2 (T₁ := fs.toFinset) (T₂ := {f}) (T₃ := some (f :: fs).toFinset)
          (Finset.mem_insert_self ..) hfM
          (by
            intro a h1 h2
            refine ⟨_, rfl, ?_⟩
            intro l hl
            rw [List.toFinset_cons, Finset.mem_insert] at hl
            rcases hl with rfl | hl
            · exact h2 {l} rfl l (by simp)
            · exact h1 l hl)
          (insert (f :: fs).toFinset X)
          (by
            intro x hx
            obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
            rcases Finset.mem_insert.1 hx with hx | hx
            · exact absurd hx hne
            · exact Finset.mem_insert_of_mem hx)
          (by
            intro x hx
            obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
            rcases Finset.mem_insert.1 (hMsub hx) with hx | hx
            · exact absurd hx hne
            · exact Finset.mem_insert_of_mem hx)
          (by intro T' hT'; cases hT'; exact Finset.mem_insert_self ..)
          (by intro T' hT'; cases hT'; exact hgfs.1)) hg
      exact ⟨Ls₂, (hE₁.trans hE₂).mono (by simp), hm₂⟩
    · obtain ⟨Ls₂, hE₂, hm₂⟩ := reach_weak hE₁.1 hM₁ (L' := insert (f :: fs).toFinset X)
        (by
          intro x hx
          rcases Finset.mem_insert.1 (hMsub hx) with hx' | hx'
          · exact absurd (hx' ▸ hx) hfM
          · exact Finset.mem_insert_of_mem hx') hg
      exact ⟨Ls₂, (hE₁.trans hE₂).mono (by simp), hm₂⟩

/-! ## Translation of flat formulas -/

/-- Value form of a literal: `x_i` for a variable, `1 - v` for a negation (junk otherwise). -/
def vf : Fm → AffForm p
  | .var i => (Finsupp.single i 1, 0)
  | .neg φ => ((0 : ℕ →₀ ZMod p), (1 : ZMod p)) - vf φ
  | _ => 0

/-- `zf s φ` is a form that vanishes exactly when the literal `φ` has truth value `s`. -/
def zf : Bool → Fm → AffForm p
  | true, .var i => formVarSub i
  | false, .var i => formVar i
  | s, .neg φ => zf (!s) φ
  | _, _ => 0

/-- Constant form. -/
def cf (c : ZMod p) : AffForm p := ((0 : ℕ →₀ ZMod p), c)

/-- The number of true members of a list of literals, as an affine form. -/
def msum (l : List Fm) : AffForm p := (l.map vf).sum

/-- The partition line `∨_c (msum l = c)`. -/
def PT (l : List Fm) : RLine p :=
  Finset.univ.image (fun c : ZMod p => ({msum l - cf c} : Term p))

/-- One rank one term per member: `∨_ψ (ψ has value s)`. -/
def sing (s : Bool) (l : List Fm) : RLine p := (l.map fun ψ => ({zf s ψ} : Term p)).toFinset

/-- One term: `∧_ψ (ψ has value s)`. -/
def conj (s : Bool) (l : List Fm) : RLine p := {(l.map (zf s)).toFinset}

/-- Translation of a flat formula with sign `s` (`true`: the formula, `false`: its negation) into
a set of terms. -/
def tr : Bool → Fm → RLine p
  | s, .neg φ => tr (!s) φ
  | true, .var i => {{formVarSub i}}
  | false, .var i => {{formVar i}}
  | true, .or l => sing true l
  | false, .or l => conj false l
  | true, .and l => conj true l
  | false, .and l => sing false l
  | true, .mod r l => {{msum l - cf (r : ZMod p)}}
  | false, .mod r l =>
      (Finset.univ.filter (fun c : ZMod p => c ≠ (r : ZMod p))).image
        (fun c => ({msum l - cf c} : Term p))

/-- A literal over `V`. -/
def LitIn (V : Finset ℕ) : Fm → Prop
  | .var i => i ∈ V
  | .neg φ => LitIn V φ
  | _ => False

/-- A flat formula over `V`: a literal, or (possibly negated) gate of literals. -/
def FlatIn (V : Finset ℕ) : Fm → Prop
  | .var i => i ∈ V
  | .neg φ => FlatIn V φ
  | .and l => ∀ ψ ∈ l, LitIn V ψ
  | .or l => ∀ ψ ∈ l, LitIn V ψ
  | .mod _ l => ∀ ψ ∈ l, LitIn V ψ

/-- Weight of a flat formula (fan in plus one). -/
def wt : Fm → ℕ
  | .var _ => 1
  | .neg φ => wt φ
  | .and l => l.length + 1
  | .or l => l.length + 1
  | .mod _ l => l.length + 1

theorem ev_cf (a : ℕ → ZMod p) (c : ZMod p) : ev a (cf c) = c := by
  simp [ev_apply, cf]

theorem vf_bool (a : Assignment) : ∀ φ : Fm, LitIn V φ →
    ev (boolPt (F := ZMod p) a) (vf φ) = 0 ∨ ev (boolPt (F := ZMod p) a) (vf φ) = 1
  | .var i, _ => by
    have : (vf (.var i) : AffForm p) = formVar i := rfl
    rw [this, ev_formVar]; exact boolPt_bool a i
  | .neg φ, h => by
    have e : (vf (.neg φ) : AffForm p) = cf 1 - vf φ := rfl
    rw [e, map_sub, ev_cf]
    rcases vf_bool a φ h with h0 | h1
    · right; rw [h0]; simp
    · left; rw [h1]; simp
  | .and _, h => h.elim
  | .or _, h => h.elim
  | .mod _ _, h => h.elim

theorem zf_iff (a : Assignment) : ∀ (φ : Fm), LitIn V φ → ∀ s : Bool,
    (ev (boolPt (F := ZMod p) a) (zf s φ) = 0 ↔
      ev (boolPt (F := ZMod p) a) (vf φ) = if s then 1 else 0)
  | .var i, _, s => by
    have e : (vf (.var i) : AffForm p) = formVar i := rfl
    cases s
    · have e2 : (zf false (.var i) : AffForm p) = formVar i := rfl
      rw [e, e2]; simp
    · have e2 : (zf true (.var i) : AffForm p) = formVarSub i := rfl
      rw [e, e2, ev_formVar, ev_formVarSub, sub_eq_zero]; simp
  | .neg φ, h, s => by
    have e : (vf (.neg φ) : AffForm p) = cf 1 - vf φ := rfl
    have e2 : (zf s (.neg φ) : AffForm p) = zf (!s) φ := by cases s <;> rfl
    rw [e, e2, map_sub, ev_cf, zf_iff a φ h (!s)]
    cases s
    · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]; rw [sub_eq_zero]; exact eq_comm
    · simp
  | .and _, h, _ => h.elim
  | .or _, h, _ => h.elim
  | .mod _ _, h, _ => h.elim

theorem vf_supp : ∀ φ : Fm, LitIn V φ → (vf φ : AffForm p).1.support ⊆ V
  | .var i, h => by
    intro x hx
    have : x = i := by
      by_contra hne
      simp [vf, Ne.symm hne] at hx
    rw [this]; exact h
  | .neg φ, h => by
    have e : (vf (.neg φ) : AffForm p).1 = - (vf φ : AffForm p).1 := by
      show (((0 : ℕ →₀ ZMod p), (1 : ZMod p)) - vf φ).1 = _
      simp
    rw [e, Finsupp.support_neg]; exact vf_supp φ h
  | .and _, h => h.elim
  | .or _, h => h.elim
  | .mod _ _, h => h.elim

theorem zf_supp : ∀ φ : Fm, LitIn V φ → ∀ s : Bool, (zf s φ : AffForm p).1.support ⊆ V
  | .var i, h, s => by
    intro x hx
    have : x = i := by
      by_contra hne
      cases s <;> simp [zf, formVar, formVarSub, Ne.symm hne] at hx
    rw [this]; exact h
  | .neg φ, h, s => by
    have e2 : (zf s (.neg φ) : AffForm p) = zf (!s) φ := by cases s <;> rfl
    rw [e2]; exact zf_supp φ h (!s)
  | .and _, h, _ => h.elim
  | .or _, h, _ => h.elim
  | .mod _ _, h, _ => h.elim

theorem lit_taut : ∀ φ : Fm, LitIn V φ → ∃ i ∈ V, ∀ s : Bool,
    ({{zf s φ}, {zf (!s) φ}} : RLine p) = {{formVar i}, {formVarSub i}}
  | .var i, h => ⟨i, h, fun s => by
      cases s
      · rfl
      · exact Finset.pair_comm _ _⟩
  | .neg φ, h => by
    obtain ⟨i, hi, hs⟩ := lit_taut φ h
    refine ⟨i, hi, fun s => ?_⟩
    have e2 : ∀ s, (zf s (.neg φ) : AffForm p) = zf (!s) φ := fun s => by cases s <;> rfl
    rw [e2, e2]; exact hs (!s)
  | .and _, h => h.elim
  | .or _, h => h.elim
  | .mod _ _, h => h.elim

theorem tr_lit : ∀ φ : Fm, LitIn V φ → ∀ s : Bool, (tr s φ : RLine p) = {{zf s φ}}
  | .var i, _, s => by cases s <;> rfl
  | .neg φ, h, s => by
    have e1 : (tr s (.neg φ) : RLine p) = tr (!s) φ := by cases s <;> rfl
    have e2 : (zf s (.neg φ) : AffForm p) = zf (!s) φ := by cases s <;> rfl
    rw [e1, e2]; exact tr_lit φ h (!s)
  | .and _, h, _ => h.elim
  | .or _, h, _ => h.elim
  | .mod _ _, h, _ => h.elim

theorem tr_neg (s : Bool) (φ : Fm) : (tr s (.neg φ) : RLine p) = tr (!s) φ := by cases s <;> rfl

theorem mem_sing {s : Bool} {l : List Fm} {T : Term p} :
    T ∈ sing s l ↔ ∃ ψ ∈ l, T = {zf s ψ} := by
  simp [sing, eq_comm]

theorem mem_conj {s : Bool} {l : List Fm} {T : Term p} :
    T ∈ conj s l ↔ T = (l.map (zf s)).toFinset := by
  simp [conj]

/-- A literal cannot have both truth values. -/
theorem lit_inc {a : Assignment} {φ : Fm} (h : LitIn V φ) {s : Bool}
    (h1 : ev (boolPt (F := ZMod p) a) (zf s φ) = 0)
    (h2 : ev (boolPt (F := ZMod p) a) (zf (!s) φ) = 0) : False := by
  rw [zf_iff a φ h] at h1 h2
  rw [h1] at h2
  cases s <;> simp at h2

theorem sing_conj_inc {a : Assignment} {l : List Fm} (hl : ∀ ψ ∈ l, LitIn V ψ) {s : Bool}
    {T U : Term p} (hT : T ∈ sing s l) (hU : U ∈ conj (!s) l)
    (h1 : TrueAt (boolPt (F := ZMod p) a) T) (h2 : TrueAt (boolPt (F := ZMod p) a) U) : False := by
  obtain ⟨ψ, hψ, rfl⟩ := mem_sing.1 hT
  rw [mem_conj] at hU; subst hU
  exact lit_inc (s := s) (hl ψ hψ) (h1 _ (Finset.mem_singleton_self _))
    (h2 _ (by simp only [List.mem_toFinset, List.mem_map]; exact ⟨ψ, hψ, rfl⟩))

theorem msum_cons (φ : Fm) (l : List Fm) : (msum (φ :: l) : AffForm p) = vf φ + msum l := by
  simp [msum]

theorem msum_supp (l : List Fm) (hl : ∀ ψ ∈ l, LitIn V ψ) :
    (msum l : AffForm p).1.support ⊆ V := by
  induction l with
  | nil => simp [msum]
  | cons ψ l ih =>
    rw [msum_cons, Prod.fst_add]
    exact Finsupp.support_add.trans (Finset.union_subset (vf_supp ψ (hl ψ (by simp)))
      (ih fun ψ' h' => hl ψ' (List.mem_cons_of_mem _ h')))

theorem msum_cf_supp (l : List Fm) (hl : ∀ ψ ∈ l, LitIn V ψ) (c : ZMod p) :
    (msum l - cf c : AffForm p).1.support ⊆ V := by
  have : (msum l - cf c : AffForm p).1 = (msum l : AffForm p).1 := by simp [cf]
  rw [this]; exact msum_supp l hl

/-- Terms of a translated flat formula only use variables of `V`. -/
theorem tr_supp : ∀ φ : Fm, FlatIn V φ → ∀ s : Bool, ∀ T ∈ (tr s φ : RLine p), ∀ f ∈ T,
    f.1.support ⊆ V
  | .var i, h, s => by
    intro T hT f hf
    rw [tr_lit (.var i) h s] at hT
    rw [Finset.mem_singleton] at hT; subst hT
    rw [Finset.mem_singleton] at hf; subst hf
    exact zf_supp (.var i) h s
  | .neg φ, h, s => by rw [tr_neg]; exact tr_supp φ h (!s)
  | .or l, h, s => by
    intro T hT f hf
    cases s
    · rw [show (tr false (.or l) : RLine p) = conj false l from rfl, mem_conj] at hT
      subst hT
      simp only [List.mem_toFinset, List.mem_map] at hf
      obtain ⟨ψ, hψ, rfl⟩ := hf
      exact zf_supp ψ (h ψ hψ) _
    · rw [show (tr true (.or l) : RLine p) = sing true l from rfl, mem_sing] at hT
      obtain ⟨ψ, hψ, rfl⟩ := hT
      rw [Finset.mem_singleton] at hf; subst hf
      exact zf_supp ψ (h ψ hψ) _
  | .and l, h, s => by
    intro T hT f hf
    cases s
    · rw [show (tr false (.and l) : RLine p) = sing false l from rfl, mem_sing] at hT
      obtain ⟨ψ, hψ, rfl⟩ := hT
      rw [Finset.mem_singleton] at hf; subst hf
      exact zf_supp ψ (h ψ hψ) _
    · rw [show (tr true (.and l) : RLine p) = conj true l from rfl, mem_conj] at hT
      subst hT
      simp only [List.mem_toFinset, List.mem_map] at hf
      obtain ⟨ψ, hψ, rfl⟩ := hf
      exact zf_supp ψ (h ψ hψ) _
  | .mod r l, h, s => by
    intro T hT f hf
    cases s
    · simp only [tr, Finset.mem_image] at hT
      obtain ⟨c, _, rfl⟩ := hT
      rw [Finset.mem_singleton] at hf; subst hf
      exact msum_cf_supp l h c
    · simp only [tr, Finset.mem_singleton] at hT
      subst hT
      rw [Finset.mem_singleton] at hf; subst hf
      exact msum_cf_supp l h _

/-- A term of `tr s φ` and a term of `tr (!s) φ` have no common Boolean point. -/
theorem tr_inc (a : Assignment) : ∀ φ : Fm, FlatIn V φ → ∀ s : Bool, ∀ T ∈ (tr s φ : RLine p),
    ∀ U ∈ (tr (!s) φ : RLine p), TrueAt (boolPt (F := ZMod p) a) T →
      TrueAt (boolPt (F := ZMod p) a) U → False
  | .var i, h, s => by
    intro T hT U hU h1 h2
    rw [tr_lit (.var i) h, Finset.mem_singleton] at hT hU
    subst hT; subst hU
    have h' : LitIn V (.var i) := h
    exact lit_inc (s := s) h' (h1 _ (Finset.mem_singleton_self _))
      (h2 _ (Finset.mem_singleton_self _))
  | .neg φ, h, s => by
    intro T hT U hU h1 h2
    rw [tr_neg] at hT hU
    exact tr_inc a φ h (!s) T hT U hU h1 h2
  | .or l, h, s => by
    intro T hT U hU h1 h2
    cases s
    · exact sing_conj_inc (s := true) h hU hT h2 h1
    · exact sing_conj_inc (s := true) h hT hU h1 h2
  | .and l, h, s => by
    intro T hT U hU h1 h2
    cases s
    · exact sing_conj_inc (s := false) h hT hU h1 h2
    · exact sing_conj_inc (s := false) h hU hT h2 h1
  | .mod r l, h, s => by
    intro T hT U hU h1 h2
    have key : ∀ (T U : Term p), T ∈ (tr true (.mod r l) : RLine p) →
        U ∈ (tr false (.mod r l) : RLine p) → TrueAt (boolPt (F := ZMod p) a) T →
        TrueAt (boolPt (F := ZMod p) a) U → False := by
      intro T U hT hU h1 h2
      simp only [tr, Finset.mem_singleton] at hT
      simp only [tr, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hU
      obtain ⟨c, hc, rfl⟩ := hU
      subst hT
      have e1 := h1 _ (Finset.mem_singleton_self _)
      have e2 := h2 _ (Finset.mem_singleton_self _)
      rw [map_sub, ev_cf, sub_eq_zero] at e1 e2
      exact hc (e2.symm.trans e1)
    cases s
    · exact key U T hU hT h2 h1
    · exact key T U hT hU h1 h2

/-- One of the two translations of a formula is a single term. -/
theorem tr_single : ∀ (φ : Fm) (s : Bool),
    (∃ U, (tr s φ : RLine p) = {U}) ∨ (∃ U, (tr (!s) φ : RLine p) = {U})
  | .var i, s => Or.inl (by cases s <;> exact ⟨_, rfl⟩)
  | .neg φ, s => by
    rw [tr_neg, tr_neg]; exact tr_single φ (!s)
  | .or l, s => by
    cases s
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
  | .and l, s => by
    cases s
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
  | .mod r l, s => by
    cases s
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩

theorem card_zmod_image_le {β : Type} [DecidableEq β] (S : Finset (ZMod p)) (g : ZMod p → β) :
    (S.image g).card ≤ p := by
  refine Finset.card_image_le.trans ((Finset.card_le_univ S).trans ?_)
  rw [ZMod.card]

theorem card_sing_le (s : Bool) (l : List Fm) : (sing s l : RLine p).card ≤ l.length := by
  unfold sing
  exact (List.toFinset_card_le _).trans (by simp)

theorem card_tr : ∀ (φ : Fm) (s : Bool), (tr s φ : RLine p).card ≤ wt φ + p
  | .var i, s => by cases s <;> simp [tr, wt]
  | .neg φ, s => by rw [tr_neg]; exact card_tr φ (!s)
  | .or l, s => by
    cases s
    · show (({(l.map (zf false)).toFinset} : RLine p)).card ≤ l.length + 1 + p
      rw [Finset.card_singleton]; omega
    · exact (card_sing_le true l).trans (by show l.length ≤ l.length + 1 + p; omega)
  | .and l, s => by
    cases s
    · exact (card_sing_le false l).trans (by show l.length ≤ l.length + 1 + p; omega)
    · show (({(l.map (zf true)).toFinset} : RLine p)).card ≤ l.length + 1 + p
      rw [Finset.card_singleton]; omega
  | .mod r l, s => by
    cases s
    · show ((Finset.univ.filter (fun c : ZMod p => c ≠ (r : ZMod p))).image
        (fun c => ({msum l - cf c} : Term p))).card ≤ l.length + 1 + p
      exact (card_zmod_image_le (p := p) _ _).trans (Nat.le_add_left _ _)
    · show (({{msum l - cf (r : ZMod p)}} : RLine p)).card ≤ l.length + 1 + p
      rw [Finset.card_singleton]; omega

/-! ## Sequents -/

/-- Translation of a sequent `Γ ⊢ Δ`: negations of `Γ` and the members of `Δ`. -/
def trS (S : Seq) : RLine p :=
  S.1.toFinset.biUnion (tr false) ∪ S.2.toFinset.biUnion (tr true)

theorem mem_trS {S : Seq} {T : Term p} :
    T ∈ trS S ↔ (∃ φ ∈ S.1, T ∈ (tr false φ : RLine p)) ∨ (∃ φ ∈ S.2, T ∈ (tr true φ : RLine p)) := by
  simp [trS]

theorem trS_consL (φ : Fm) (Γ Δ : List Fm) :
    (trS (φ :: Γ, Δ) : RLine p) = tr false φ ∪ trS (Γ, Δ) := by
  ext T; simp only [mem_trS, Finset.mem_union, List.mem_cons]
  constructor
  · rintro (⟨ψ, rfl | h, hT⟩ | h)
    · exact Or.inl hT
    · exact Or.inr (Or.inl ⟨ψ, h, hT⟩)
    · exact Or.inr (Or.inr h)
  · rintro (h | ⟨ψ, h, hT⟩ | h)
    · exact Or.inl ⟨φ, Or.inl rfl, h⟩
    · exact Or.inl ⟨ψ, Or.inr h, hT⟩
    · exact Or.inr h

theorem trS_consR (φ : Fm) (Γ Δ : List Fm) :
    (trS (Γ, φ :: Δ) : RLine p) = tr true φ ∪ trS (Γ, Δ) := by
  ext T; simp only [mem_trS, Finset.mem_union, List.mem_cons]
  constructor
  · rintro (h | ⟨ψ, rfl | h, hT⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inl hT
    · exact Or.inr (Or.inr ⟨ψ, h, hT⟩)
  · rintro (h | h | ⟨ψ, h, hT⟩)
    · exact Or.inr ⟨φ, Or.inl rfl, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨ψ, Or.inr h, hT⟩

/-- All formulas of the sequent are flat over `V`. -/
def FlatS (V : Finset ℕ) (S : Seq) : Prop := ∀ φ ∈ S.1 ++ S.2, FlatIn V φ

/-- Weight of a sequent. -/
def wS (S : Seq) : ℕ := ((S.1 ++ S.2).map wt).sum + 1

theorem good_trS {S : Seq} (hS : FlatS V S) (hb : Bdd ρ (trS S : RLine p)) :
    GoodL V ρ (trS S : RLine p) := by
  intro T hT
  refine ⟨hb T hT, ?_⟩
  rcases mem_trS.1 hT with ⟨φ, hφ, h⟩ | ⟨φ, hφ, h⟩
  · exact tr_supp φ (hS φ (List.mem_append_left _ hφ)) false T h
  · exact tr_supp φ (hS φ (List.mem_append_right _ hφ)) true T h

/-! ## Counting: the partition line and the `MOD_p` axioms -/

theorem good_PT (hρ : 1 ≤ ρ) (l : List Fm) (hl : ∀ ψ ∈ l, LitIn V ψ) :
    GoodL V ρ (PT l : RLine p) := by
  intro T hT
  simp only [PT, Finset.mem_image, Finset.mem_univ, true_and] at hT
  obtain ⟨c, rfl⟩ := hT
  exact goodT_singleton hρ (msum_cf_supp l hl c)

theorem mem_PT (l : List Fm) (c : ZMod p) : ({msum l - cf c} : Term p) ∈ (PT l : RLine p) := by
  simp only [PT, Finset.mem_image, Finset.mem_univ, true_and]; exact ⟨c, rfl⟩

/-- The literal tautology line `{φ true} ∨ {φ false}`. -/
theorem reach_lit {φ : Fm} (hφ : LitIn V φ) (hρ : 1 ≤ ρ) (s : Bool) {Ls : List (RLine p)}
    (h : Der Φ V ρ Ls) :
    ∃ Ls₂, Ext Φ V ρ Ls Ls₂ 1 ∧ ({{zf s φ}, {zf (!s) φ}} : RLine p) ∈ Ls₂ := by
  obtain ⟨i, hi, hs⟩ := lit_taut (p := p) φ hφ
  have g : GoodL V ρ ({{zf s φ}, {zf (!s) φ}} : RLine p) := by
    intro T hT
    rcases Finset.mem_insert.1 hT with rfl | hT
    · exact goodT_singleton hρ (zf_supp φ hφ s)
    · rw [Finset.mem_singleton] at hT; subst hT; exact goodT_singleton hρ (zf_supp φ hφ _)
  refine reach_step h (prems := []) (by simp) ?_ g
  rw [hs s]; exact RInfer.taut i

theorem reach_PT {v₀ : ℕ} (hv : v₀ ∈ V) (hρ : 1 ≤ ρ) (l : List Fm) :
    (∀ ψ ∈ l, LitIn V ψ) → ∀ {Ls : List (RLine p)}, Der Φ V ρ Ls →
      ∃ Ls₂, Ext Φ V ρ Ls Ls₂ ((2 * p + 3) * l.length + 3) ∧ (PT l : RLine p) ∈ Ls₂ := by
  induction l with
  | nil =>
    intro hl Ls h
    obtain ⟨Ls₂, hE, hm⟩ := reach_true hv hρ h (T := ({msum [] - cf 0} : Term p))
      (fun a f hf => by
        rw [Finset.mem_singleton] at hf; subst hf
        rw [map_sub, ev_cf]; simp [msum])
      (good_PT hρ [] hl) (mem_PT [] 0)
    exact ⟨Ls₂, hE.mono (by simp), hm⟩
  | cons φ l ih =>
    intro hl Ls h
    have hφ : LitIn V φ := hl φ (by simp)
    have hl' : ∀ ψ ∈ l, LitIn V ψ := fun ψ hψ => hl ψ (List.mem_cons_of_mem _ hψ)
    obtain ⟨Ls₁, hE₁, hm₁⟩ := ih hl' h
    obtain ⟨Ls₂, hE₂, hm₂⟩ := reach_lit (p := p) hφ hρ false hE₁.1
    have hm₁' := hE₂.2.1 _ hm₁
    have gPT := good_PT (p := p) hρ (φ :: l) hl
    -- phase 1: resolve against `φ false`
    have gY : GoodL V ρ (insert ({zf true φ} : Term p) (PT (φ :: l))) := by
      intro T hT
      rcases Finset.mem_insert.1 hT with rfl | hT
      · exact goodT_singleton hρ (zf_supp φ hφ _)
      · exact gPT T hT
    have hcard : (PT l : RLine p).card ≤ p := by unfold PT; exact card_zmod_image_le (p := p) _ _
    obtain ⟨Ls₃, hE₃, hm₃⟩ := reach_map (Φ := Φ) (L₂ := ({{zf false φ}, {zf (!false) φ}} : RLine p))
      (U := {zf false φ}) (by simp) (fun T => some (T.image (· + vf φ))) gY
      (by
        intro x hx
        obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
        rcases Finset.mem_insert.1 hx with hx | hx
        · exact absurd hx hne
        · rw [Finset.mem_singleton] at hx; subst hx; simp)
      (PT l)
      (by
        intro T hT
        refine ⟨?_, ?_⟩
        · intro a h1 h2
          refine ⟨_, rfl, ?_⟩
          intro f hf
          obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hf
          have hz := h2 _ rfl _ (Finset.mem_singleton_self _)
          rw [zf_iff a φ hφ] at hz
          rw [map_add, h1 g hg, hz]; simp
        · intro T' hT'
          cases hT'
          simp only [PT, Finset.mem_image, Finset.mem_univ, true_and] at hT
          obtain ⟨c, rfl⟩ := hT
          refine Finset.mem_insert_of_mem ?_
          have : (({msum l - cf c} : Term p).image (· + vf φ)) = {msum (φ :: l) - cf c} := by
            rw [Finset.image_singleton, msum_cons]; congr 1; abel
          rw [this]; exact mem_PT _ c)
      hE₂.1 hm₂ hm₁' (by simp)
    have hm₁'' := hE₃.2.1 _ hm₁'
    -- phase 2: resolve against `φ true`
    obtain ⟨Ls₄, hE₄, hm₄⟩ := reach_map (Φ := Φ)
      (L₂ := (insert ({zf true φ} : Term p) (PT (φ :: l))))
      (U := {zf true φ}) (by simp) (fun T => some (T.image (· + vf φ - cf 1))) gPT
      (by
        intro x hx
        obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
        rcases Finset.mem_insert.1 hx with hx | hx
        · exact absurd hx hne
        · exact hx)
      (PT l)
      (by
        intro T hT
        refine ⟨?_, ?_⟩
        · intro a h1 h2
          refine ⟨_, rfl, ?_⟩
          intro f hf
          obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hf
          have hz := h2 _ rfl _ (Finset.mem_singleton_self _)
          rw [zf_iff a φ hφ] at hz
          rw [map_sub, map_add, h1 g hg, hz, ev_cf]; simp
        · intro T' hT'
          cases hT'
          simp only [PT, Finset.mem_image, Finset.mem_univ, true_and] at hT
          obtain ⟨c, rfl⟩ := hT
          have e : (cf (c + 1) : AffForm p) = cf c + cf 1 := by simp [cf]
          have : (({msum l - cf c} : Term p).image (· + vf φ - cf 1)) =
              {msum (φ :: l) - cf (c + 1)} := by
            rw [Finset.image_singleton, msum_cons, e]; congr 1; abel
          rw [this]; exact mem_PT _ (c + 1))
      hE₃.1 hm₃ hm₁'' (by simp)
    refine ⟨Ls₄, (((hE₁.trans hE₂).trans hE₃).trans hE₄).mono ?_, hm₄⟩
    simp only [List.length_cons]
    have : (2 * p + 3) * (l.length + 1) = (2 * p + 3) * l.length + (2 * p + 3) := by ring
    omega

/-- The common shape of the four `MOD_p` counting axioms. -/
theorem reach_modax {v₀ : ℕ} (hv : v₀ ∈ V) (hρ : 1 ≤ ρ) {φ : Fm} (hφ : LitIn V φ)
    (l₁ : List Fm) (hl₁ : ∀ ψ ∈ l₁, LitIn V ψ) (c : ZMod p) (s : Bool) (T₃ : Term p)
    (hsem : ∀ a : Assignment, ev (boolPt (F := ZMod p) a) (msum l₁ - cf c) = 0 →
      ev (boolPt (F := ZMod p) a) (zf s φ) = 0 → TrueAt (boolPt (F := ZMod p) a) T₃)
    {Y : RLine p} (hY : GoodL V ρ Y) (h1 : ∀ c' : ZMod p, c' ≠ c → ({msum l₁ - cf c'} : Term p) ∈ Y)
    (h2 : ({zf (!s) φ} : Term p) ∈ Y) (h3 : T₃ ∈ Y) {Ls : List (RLine p)} (h : Der Φ V ρ Ls) :
    ∃ Ls₂, Ext Φ V ρ Ls Ls₂ ((2 * p + 3) * l₁.length + 5) ∧ Y ∈ Ls₂ := by
  obtain ⟨Ls₁, hE₁, hm₁⟩ := reach_PT (p := p) hv hρ l₁ hl₁ h
  obtain ⟨Ls₂, hE₂, hm₂⟩ := reach_lit (p := p) hφ hρ s hE₁.1
  have hm₁' := hE₂.2.1 _ hm₁
  obtain ⟨Ls₃, hE₃, hm₃⟩ := reach_step hE₂.1 (prems := [PT l₁, {{zf s φ}, {zf (!s) φ}}])
    (by intro M hM; simp at hM; rcases hM with rfl | rfl <;> assumption)
    (RInfer.sem2 (T₁ := {msum l₁ - cf c}) (T₂ := {zf s φ}) (T₃ := some T₃) (mem_PT l₁ c)
      (by simp)
      (fun a h1 h2 => ⟨T₃, rfl, hsem a (h1 _ (Finset.mem_singleton_self _))
        (h2 _ rfl _ (Finset.mem_singleton_self _))⟩)
      Y
      (by
        intro x hx
        obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
        simp only [PT, Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨c', rfl⟩ := hx
        exact h1 c' (by rintro rfl; exact hne rfl))
      (by
        intro x hx
        obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
        rcases Finset.mem_insert.1 hx with hx | hx
        · exact absurd hx hne
        · rw [Finset.mem_singleton] at hx; subst hx; exact h2)
      (by intro T' hT'; cases hT'; exact h3)
      (by intro T' hT'; cases hT'; exact (hY _ h3).1)) hY
  exact ⟨Ls₃, ((hE₁.trans hE₂).trans hE₃).mono (by omega), hm₃⟩

end

end FBridge
