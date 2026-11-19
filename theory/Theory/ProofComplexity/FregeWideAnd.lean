import Theory.ProofComplexity.FregeDegBridge
import Mathlib.Data.List.Sections

/-!
# Wide conjunctions in positive position: expansion of a sequent into several `PIC` lines

`FregeDegBridge.lean` translates a sequent into one line of `PIC` and needs every `AND` in positive
position (and every `OR` in negative position) to have a value polynomial of syntactic degree at
most `d`.  Here such a gate of degree above `d` is expanded instead: a positive `AND` is replaced by
one of its members, one line per member.  A sequent becomes the set of its *selections*, each a
sequent of the low degree fragment, that is its CNF over low degree atoms.

* `sels p d s φ`: the selections of `φ` with sign `s`.  A positive `AND` of degree above `d` gives
  the selections of all members; a negative `AND` gives one selection per member (all
  combinations); dually for `OR`; a gate of degree at most `d` on its single-term side is kept.
* `selsS p d S`: the selections of a sequent, `BS p d S` their number, `XDegS p d S` the syntactic
  condition that every term of every selection has degree at most `d`.
* `sel_fstep`: a selection of the conclusion of a rule follows by a rule of the calculus from
  selections of the premises, except for the axiom `φ ⊢ φ` and for cut.
* `reach_id`, `reach_xcut`: these two cases, by induction on the formula.  Cut on an expanded
  `AND` resolves the members one at a time; its cost is at most `2 |φ|` times the product of the
  numbers of selections of `φ` with the two signs.
* `wide_frege_to_PIC`: a refutation in `FProof` (any depth) with `XDegS p d` and at most `B`
  selections per sequent yields a `PIC` refutation of size at most `|L| · 12 · 2W · B²`.
* `wide_frege_tseitin`, `wide_frege_tseitin_idx`: the size bound of `PIC.pic_main` for such
  refutations of one hot Tseitin mod `q`.

This is the CNF expansion.  The factor is `B²` and not `B`: cut costs the product of the numbers
of lines of its two premises.  It is a bound for a fragment and no lower bound for AC0[p] Frege.

LOG: R4 wideand fable session, expansion of wide conjunctions
-/

open SATurday.ProofComplexity MvPolynomial PIC FDeg

namespace FWide

set_option linter.unusedSectionVars false

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime] {Φ : CNF} {V : Finset ℕ} {d : ℕ}

/-! ## List helpers -/

theorem sections_single {α : Type} (l : List α) : (l.map fun x => [x]).sections = [l] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.sections, ih]

theorem length_sections {α : Type} (L : List (List α)) :
    L.sections.length = (L.map List.length).prod := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [List.sections, List.length_flatMap, ih, mul_comm]

theorem prod_pos' (l : List ℕ) (h : ∀ x ∈ l, 0 < x) : 0 < l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons]
    exact Nat.mul_pos (h a (by simp)) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem forall2_left {α β : Type} {R : α → β → Prop} {l' : List α} {l : List β}
    (h : List.Forall₂ R l' l) {a : α} (ha : a ∈ l') : ∃ b ∈ l, R a b := by
  induction h with
  | nil => simp at ha
  | cons hab _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, by simp, hab⟩
    · obtain ⟨b, hb, hr⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem forall2_right {α β : Type} {R : α → β → Prop} {l' : List α} {l : List β}
    (h : List.Forall₂ R l' l) {b : β} (hb : b ∈ l) : ∃ a ∈ l', R a b := by
  induction h with
  | nil => simp at hb
  | cons hab _ ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, by simp, hab⟩
    · obtain ⟨a, ha, hr⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

theorem forall2_subset {α β : Type} {R : α → β → Prop} {l' : List α} {l : List β}
    (h : List.Forall₂ R l' l) : ∀ l₀ : List β, l₀ ⊆ l →
      ∃ l₀' : List α, List.Forall₂ R l₀' l₀ ∧ l₀' ⊆ l'
  | [], _ => ⟨[], .nil, by simp⟩
  | b :: l₀, hsub => by
    obtain ⟨a, ha, hr⟩ := forall2_right h (hsub List.mem_cons_self)
    obtain ⟨l₀', h1, h2⟩ := forall2_subset h l₀ fun x hx => hsub (List.mem_cons_of_mem _ hx)
    refine ⟨a :: l₀', .cons hr h1, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ha
    · exact h2 hx

theorem forall2_sum_le {R : Fm → Fm → Prop} (f : Fm → ℕ) {l' l : List Fm}
    (h : List.Forall₂ R l' l) (hf : ∀ a b, b ∈ l → R a b → f a ≤ f b) :
    (l'.map f).sum ≤ (l.map f).sum := by
  induction h with
  | nil => simp
  | cons hab _ ih =>
    have h1 := hf _ _ (by simp) hab
    have h2 := ih fun a b hb => hf a b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons]
    omega

/-! ## Gates by sign -/

/-- `gt true` is `AND`, `gt false` is `OR`: the gate whose translation with sign `s` is one term. -/
def gt (s : Bool) (l : List Fm) : Fm :=
  match s with
  | true => .and l
  | false => .or l

theorem pd_gt (s : Bool) (l : List Fm) : pd p (gt s l) = (l.map (pd p)).sum := by
  cases s
  · exact pd_or l
  · exact pd_and l

theorem pd_le_gt {s : Bool} {l : List Fm} {ψ : Fm} (h : ψ ∈ l) : pd p ψ ≤ pd p (gt s l) := by
  rw [pd_gt]; exact le_sum_of_mem (List.mem_map.2 ⟨ψ, h, rfl⟩)

theorem size_gt (s : Bool) (l : List Fm) : (gt s l).size = (l.map Fm.size).sum + 1 := by
  cases s
  · exact size_or l
  · exact size_and l

theorem mem_fv_gt (s : Bool) (l : List Fm) (v : ℕ) : v ∈ fv (gt s l) ↔ ∃ ψ ∈ l, v ∈ fv ψ := by
  cases s
  · exact mem_fv_or l v
  · exact mem_fv_and l v

theorem td_gt_same (s : Bool) (l : List Fm) : td p s (gt s l) = pd p (gt s l) := by
  cases s
  · exact td_or_false l
  · exact td_and_true l

theorem td_gt_opp (s : Bool) (l : List Fm) :
    td p (!s) (gt s l) = (l.map (td p (!s))).foldr max 0 := by
  cases s
  · exact td_or_true l
  · exact td_and_false l

theorem mem_trL_gt (s : Bool) (l : List Fm) (g : Pang.PP p) :
    g ∈ trL p (!s) (gt s l) ↔ ∃ ψ ∈ l, g ∈ trL p (!s) ψ := by
  cases s
  · exact mem_trL_or_true l g
  · exact mem_trL_and_false l g

/-! ## Selections -/

/-- Selections of `φ` with sign `s` at degree threshold `d`. -/
def sels (p d : ℕ) : Bool → Fm → List Fm
  | _, .var i => [.var i]
  | s, .neg φ => (sels p d (!s) φ).map Fm.neg
  | true, .and l =>
      if pd p (.and l) ≤ d then [.and l]
      else (l.attach.map fun ⟨ψ, _⟩ => sels p d true ψ).flatten
  | false, .and l => (l.attach.map fun ⟨ψ, _⟩ => sels p d false ψ).sections.map Fm.and
  | true, .or l => (l.attach.map fun ⟨ψ, _⟩ => sels p d true ψ).sections.map Fm.or
  | false, .or l =>
      if pd p (.or l) ≤ d then [.or l]
      else (l.attach.map fun ⟨ψ, _⟩ => sels p d false ψ).flatten
  | _, .mod r l => [.mod r l]

/-- Largest syntactic degree of a term of a selection of `φ` with sign `s`. -/
def xtd (p d : ℕ) : Bool → Fm → ℕ
  | _, .var _ => 1
  | s, .neg φ => xtd p d (!s) φ
  | true, .and l =>
      if pd p (.and l) ≤ d then pd p (.and l)
      else (l.attach.map fun ⟨ψ, _⟩ => xtd p d true ψ).foldr max 0
  | false, .and l => (l.attach.map fun ⟨ψ, _⟩ => xtd p d false ψ).foldr max 0
  | true, .or l => (l.attach.map fun ⟨ψ, _⟩ => xtd p d true ψ).foldr max 0
  | false, .or l =>
      if pd p (.or l) ≤ d then pd p (.or l)
      else (l.attach.map fun ⟨ψ, _⟩ => xtd p d false ψ).foldr max 0
  | _, .mod r l => pd p (.mod r l)

theorem sels_var (s : Bool) (i : ℕ) : sels p d s (.var i) = [.var i] := by rw [sels]
theorem sels_neg (s : Bool) (φ : Fm) : sels p d s (.neg φ) = (sels p d (!s) φ).map Fm.neg := by
  rw [sels]
theorem sels_mod (s : Bool) (r : ℕ) (l : List Fm) : sels p d s (.mod r l) = [.mod r l] := by
  rw [sels]

theorem sels_and_true (l : List Fm) : sels p d true (.and l) =
    if pd p (.and l) ≤ d then [.and l] else (l.map (sels p d true)).flatten := by
  rw [sels]
  have := Fm.attach_map l (sels p d true)
  simp only at this
  rw [this]

theorem sels_and_false (l : List Fm) :
    sels p d false (.and l) = (l.map (sels p d false)).sections.map Fm.and := by
  rw [sels]
  have := Fm.attach_map l (sels p d false)
  simp only at this
  rw [this]

theorem sels_or_true (l : List Fm) :
    sels p d true (.or l) = (l.map (sels p d true)).sections.map Fm.or := by
  rw [sels]
  have := Fm.attach_map l (sels p d true)
  simp only at this
  rw [this]

theorem sels_or_false (l : List Fm) : sels p d false (.or l) =
    if pd p (.or l) ≤ d then [.or l] else (l.map (sels p d false)).flatten := by
  rw [sels]
  have := Fm.attach_map l (sels p d false)
  simp only at this
  rw [this]

theorem xtd_var (s : Bool) (i : ℕ) : xtd p d s (.var i) = 1 := by rw [xtd]
theorem xtd_neg (s : Bool) (φ : Fm) : xtd p d s (.neg φ) = xtd p d (!s) φ := by rw [xtd]
theorem xtd_mod (s : Bool) (r : ℕ) (l : List Fm) : xtd p d s (.mod r l) = pd p (.mod r l) := by
  rw [xtd]

theorem xtd_and_true (l : List Fm) : xtd p d true (.and l) =
    if pd p (.and l) ≤ d then pd p (.and l) else (l.map (xtd p d true)).foldr max 0 := by
  rw [xtd]
  have := Fm.attach_map l (xtd p d true)
  simp only at this
  rw [this]

theorem xtd_and_false (l : List Fm) :
    xtd p d false (.and l) = (l.map (xtd p d false)).foldr max 0 := by
  rw [xtd]
  have := Fm.attach_map l (xtd p d false)
  simp only at this
  rw [this]

theorem xtd_or_true (l : List Fm) :
    xtd p d true (.or l) = (l.map (xtd p d true)).foldr max 0 := by
  rw [xtd]
  have := Fm.attach_map l (xtd p d true)
  simp only at this
  rw [this]

theorem xtd_or_false (l : List Fm) : xtd p d false (.or l) =
    if pd p (.or l) ≤ d then pd p (.or l) else (l.map (xtd p d false)).foldr max 0 := by
  rw [xtd]
  have := Fm.attach_map l (xtd p d false)
  simp only at this
  rw [this]

theorem sels_gt_same (s : Bool) (l : List Fm) : sels p d s (gt s l) =
    if pd p (gt s l) ≤ d then [gt s l] else (l.map (sels p d s)).flatten := by
  cases s
  · exact sels_or_false l
  · exact sels_and_true l

theorem sels_gt_opp (s : Bool) (l : List Fm) :
    sels p d (!s) (gt s l) = ((l.map (sels p d (!s))).sections).map (gt s) := by
  cases s
  · exact sels_or_true l
  · exact sels_and_false l

theorem xtd_gt_same (s : Bool) (l : List Fm) : xtd p d s (gt s l) =
    if pd p (gt s l) ≤ d then pd p (gt s l) else (l.map (xtd p d s)).foldr max 0 := by
  cases s
  · exact xtd_or_false l
  · exact xtd_and_true l

theorem xtd_gt_opp (s : Bool) (l : List Fm) :
    xtd p d (!s) (gt s l) = (l.map (xtd p d (!s))).foldr max 0 := by
  cases s
  · exact xtd_or_true l
  · exact xtd_and_false l

/-- Memberwise selection of a list of formulas. -/
abbrev SelL (p d : ℕ) (s : Bool) (l' l : List Fm) : Prop :=
  List.Forall₂ (fun φ' φ => φ' ∈ sels p d s φ) l' l

theorem mem_sections_sels {s : Bool} {l' l : List Fm} :
    l' ∈ (l.map (sels p d s)).sections ↔ SelL p d s l' l := by
  unfold SelL
  rw [List.mem_sections, List.forall₂_map_right_iff]

theorem bool_cases (s s₀ : Bool) : s = s₀ ∨ s = !s₀ := by
  cases s <;> cases s₀ <;> simp

/-- A formula of syntactic degree at most `d` is its own and only selection. -/
theorem sels_self : ∀ φ : Fm, pd p φ ≤ d → ∀ s, sels p d s φ = [φ] := by
  have gate : ∀ (s₀ : Bool) (l : List Fm),
      (∀ ψ ∈ l, pd p ψ ≤ d → ∀ s, sels p d s ψ = [ψ]) → pd p (gt s₀ l) ≤ d →
      ∀ s, sels p d s (gt s₀ l) = [gt s₀ l] := by
    intro s₀ l ih hd s
    rcases bool_cases s s₀ with rfl | rfl
    · rw [sels_gt_same, if_pos hd]
    · rw [sels_gt_opp]
      have e : l.map (sels p d (!s₀)) = l.map fun x => [x] :=
        List.map_congr_left fun ψ hψ => ih ψ hψ ((pd_le_gt hψ).trans hd) _
      rw [e, sections_single]; rfl
  refine Fm_ind ?_ ?_ ?_ ?_ ?_
  · intro i _ s; exact sels_var s i
  · intro φ ih hd s
    rw [pd_neg] at hd
    rw [sels_neg, ih hd]; rfl
  · intro l ih; exact gate true l ih
  · intro l ih; exact gate false l ih
  · intro r l _ _ s; exact sels_mod s r l

/-- A selection has terms of degree at most `xtd`, variables of `φ`, and size at most that of `φ`. -/
theorem sels_props : ∀ (φ : Fm) (s : Bool) (φ' : Fm), φ' ∈ sels p d s φ →
    td p s φ' ≤ xtd p d s φ ∧ fv φ' ⊆ fv φ ∧ φ'.size ≤ φ.size := by
  have gate : ∀ (s₀ : Bool) (l : List Fm),
      (∀ ψ ∈ l, ∀ (s : Bool) (φ' : Fm), φ' ∈ sels p d s ψ →
        td p s φ' ≤ xtd p d s ψ ∧ fv φ' ⊆ fv ψ ∧ φ'.size ≤ ψ.size) →
      ∀ (s : Bool) (φ' : Fm), φ' ∈ sels p d s (gt s₀ l) →
        td p s φ' ≤ xtd p d s (gt s₀ l) ∧ fv φ' ⊆ fv (gt s₀ l) ∧ φ'.size ≤ (gt s₀ l).size := by
    intro s₀ l ih s φ' h
    rcases bool_cases s s₀ with rfl | rfl
    · rw [sels_gt_same] at h
      rw [xtd_gt_same]
      by_cases hn : pd p (gt s l) ≤ d
      · rw [if_pos hn, List.mem_singleton] at h
        subst h
        rw [if_pos hn]
        exact ⟨(td_gt_same s l).le, subset_rfl, le_rfl⟩
      · rw [if_neg hn] at h
        rw [if_neg hn]
        obtain ⟨ls, hls, hφ'⟩ := List.mem_flatten.1 h
        obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hls
        obtain ⟨h1, h2, h3⟩ := ih ψ hψ s φ' hφ'
        refine ⟨h1.trans (le_foldr_max (List.mem_map.2 ⟨ψ, hψ, rfl⟩)),
          fun v hv => (mem_fv_gt s l v).2 ⟨ψ, hψ, h2 hv⟩, h3.trans ?_⟩
        rw [size_gt]
        have := le_sum_of_mem (List.mem_map.2 ⟨ψ, hψ, rfl⟩ : ψ.size ∈ l.map Fm.size)
        omega
    · rw [sels_gt_opp] at h
      obtain ⟨l', hl', rfl⟩ := List.mem_map.1 h
      have hF : SelL p d (!s₀) l' l := mem_sections_sels.1 hl'
      refine ⟨?_, ?_, ?_⟩
      · rw [td_gt_opp, xtd_gt_opp]
        refine foldr_max_le fun x hx => ?_
        obtain ⟨ψ', hψ', rfl⟩ := List.mem_map.1 hx
        obtain ⟨ψ, hψ, hr⟩ := forall2_left hF hψ'
        exact (ih ψ hψ _ ψ' hr).1.trans (le_foldr_max (List.mem_map.2 ⟨ψ, hψ, rfl⟩))
      · intro v hv
        obtain ⟨ψ', hψ', hv'⟩ := (mem_fv_gt s₀ l' v).1 hv
        obtain ⟨ψ, hψ, hr⟩ := forall2_left hF hψ'
        exact (mem_fv_gt s₀ l v).2 ⟨ψ, hψ, (ih ψ hψ _ ψ' hr).2.1 hv'⟩
      · rw [size_gt, size_gt]
        have := forall2_sum_le Fm.size hF (fun a b hb hr => (ih b hb _ a hr).2.2)
        omega
  refine Fm_ind ?_ ?_ ?_ ?_ ?_
  · intro i s φ' h
    rw [sels_var, List.mem_singleton] at h
    subst h
    rw [td_var, xtd_var]
    exact ⟨le_rfl, subset_rfl, le_rfl⟩
  · intro φ ih s φ' h
    rw [sels_neg] at h
    obtain ⟨χ, hχ, rfl⟩ := List.mem_map.1 h
    obtain ⟨h1, h2, h3⟩ := ih (!s) χ hχ
    rw [td_neg, xtd_neg, fv_neg, fv_neg, size_neg, size_neg]
    exact ⟨h1, h2, by omega⟩
  · exact fun l ih => gate true l ih
  · exact fun l ih => gate false l ih
  · intro r l _ s φ' h
    rw [sels_mod, List.mem_singleton] at h
    subst h
    rw [td_mod, xtd_mod]
    exact ⟨le_rfl, subset_rfl, le_rfl⟩

/-- Every formula has at least one selection. -/
theorem sels_pos : ∀ (φ : Fm) (s : Bool), 0 < (sels p d s φ).length := by
  have gate : ∀ (s₀ : Bool) (l : List Fm), (∀ ψ ∈ l, ∀ s : Bool, 0 < (sels p d s ψ).length) →
      ∀ s : Bool, 0 < (sels p d s (gt s₀ l)).length := by
    intro s₀ l ih s
    rcases bool_cases s s₀ with rfl | rfl
    · rw [sels_gt_same]
      by_cases hn : pd p (gt s l) ≤ d
      · rw [if_pos hn]; simp
      · rw [if_neg hn]
        cases l with
        | nil => exact absurd (by rw [pd_gt]; simp) hn
        | cons ψ l =>
          have := ih ψ (by simp) s
          simp only [List.map_cons, List.flatten_cons, List.length_append]
          omega
    · rw [sels_gt_opp, List.length_map, length_sections]
      refine prod_pos' _ fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hy
      exact ih ψ hψ _
  refine Fm_ind ?_ ?_ ?_ ?_ ?_
  · intro i s; rw [sels_var]; simp
  · intro φ ih s; rw [sels_neg, List.length_map]; exact ih _
  · exact fun l ih => gate true l ih
  · exact fun l ih => gate false l ih
  · intro r l _ s; rw [sels_mod]; simp

/-- The expansion does nothing more than the one line translation allows: `xtd ≤ td`. -/
theorem xtd_le_td : ∀ (φ : Fm) (s : Bool), xtd p d s φ ≤ td p s φ := by
  have gate : ∀ (s₀ : Bool) (l : List Fm), (∀ ψ ∈ l, ∀ s : Bool, xtd p d s ψ ≤ td p s ψ) →
      ∀ s : Bool, xtd p d s (gt s₀ l) ≤ td p s (gt s₀ l) := by
    intro s₀ l ih s
    rcases bool_cases s s₀ with rfl | rfl
    · rw [xtd_gt_same, td_gt_same]
      by_cases hn : pd p (gt s l) ≤ d
      · rw [if_pos hn]
      · rw [if_neg hn]
        refine foldr_max_le fun x hx => ?_
        obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hx
        exact ((ih ψ hψ s).trans (td_le_pd ψ s)).trans (pd_le_gt hψ)
    · rw [xtd_gt_opp, td_gt_opp]
      refine foldr_max_le fun x hx => ?_
      obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hx
      exact (ih ψ hψ _).trans (le_foldr_max (List.mem_map.2 ⟨ψ, hψ, rfl⟩))
  refine Fm_ind ?_ ?_ ?_ ?_ ?_
  · intro i s; rw [xtd_var, td_var]
  · intro φ ih s; rw [xtd_neg, td_neg]; exact ih _
  · exact fun l ih => gate true l ih
  · exact fun l ih => gate false l ih
  · intro r l _ s; rw [xtd_mod, td_mod]

/-- A positive `AND` of any fan in over members of the fragment is in the fragment. -/
theorem xtd_and_true_le (l : List Fm) (h : ∀ ψ ∈ l, xtd p d true ψ ≤ d) :
    xtd p d true (.and l) ≤ d := by
  rw [xtd_and_true]
  by_cases hn : pd p (.and l) ≤ d
  · rw [if_pos hn]; exact hn
  · rw [if_neg hn]
    refine foldr_max_le fun x hx => ?_
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hx
    exact h ψ hψ

/-- A formula whose one line translation has degree at most `d` is its only selection. -/
theorem sels_of_td : ∀ (φ : Fm) (s : Bool), td p s φ ≤ d → sels p d s φ = [φ] := by
  have gate : ∀ (s₀ : Bool) (l : List Fm),
      (∀ ψ ∈ l, ∀ s : Bool, td p s ψ ≤ d → sels p d s ψ = [ψ]) →
      ∀ s : Bool, td p s (gt s₀ l) ≤ d → sels p d s (gt s₀ l) = [gt s₀ l] := by
    intro s₀ l ih s ht
    rcases bool_cases s s₀ with e | e
    · rw [e] at ht ⊢
      rw [td_gt_same] at ht
      exact sels_self _ ht _
    · rw [e] at ht ⊢
      rw [td_gt_opp] at ht
      rw [sels_gt_opp]
      have e' : l.map (sels p d (!s₀)) = l.map fun x => [x] :=
        List.map_congr_left fun ψ hψ =>
          ih ψ hψ _ ((le_foldr_max (List.mem_map.2 ⟨ψ, hψ, rfl⟩)).trans ht)
      rw [e', sections_single]; rfl
  refine Fm_ind ?_ ?_ ?_ ?_ ?_
  · intro i s _; exact sels_var s i
  · intro φ ih s ht
    rw [td_neg] at ht
    rw [sels_neg, ih _ ht]; rfl
  · exact fun l ih => gate true l ih
  · exact fun l ih => gate false l ih
  · intro r l _ s _; exact sels_mod s r l

/-! ## Sequents -/

/-- The selections of a sequent: antecedent formulas with sign false, succedent with sign true. -/
def selsS (p d : ℕ) (S : Seq) : List Seq :=
  List.product ((S.1.map (sels p d false)).sections) ((S.2.map (sels p d true)).sections)

/-- The number of selections of a sequent, that is of `PIC` lines it is expanded into. -/
def BS (p d : ℕ) (S : Seq) : ℕ := (selsS p d S).length

/-- Degree condition for the expansion: every term of every selection has degree `≤ d`. -/
def XDegS (p d : ℕ) (S : Seq) : Prop :=
  (∀ φ ∈ S.1, xtd p d false φ ≤ d) ∧ (∀ φ ∈ S.2, xtd p d true φ ≤ d)

theorem mem_selsS {S S' : Seq} :
    S' ∈ selsS p d S ↔ SelL p d false S'.1 S.1 ∧ SelL p d true S'.2 S.2 := by
  obtain ⟨a, b⟩ := S'
  unfold selsS
  rw [List.pair_mem_product, mem_sections_sels, mem_sections_sels]

theorem BS_eq (S : Seq) : BS p d S =
    ((S.1.map (sels p d false)).map List.length).prod *
      ((S.2.map (sels p d true)).map List.length).prod := by
  have e := List.length_product (S.1.map (sels p d false)).sections
    (S.2.map (sels p d true)).sections
  rw [length_sections, length_sections] at e
  exact e

theorem BS_pos (S : Seq) : 0 < BS p d S := by
  rw [BS_eq]
  refine Nat.mul_pos (prod_pos' _ fun x hx => ?_) (prod_pos' _ fun x hx => ?_)
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨ψ, -, rfl⟩ := List.mem_map.1 hy
    exact sels_pos ψ _
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨ψ, -, rfl⟩ := List.mem_map.1 hy
    exact sels_pos ψ _

theorem BS_cons_right (Γ Δ : List Fm) (φ : Fm) :
    BS p d (Γ, φ :: Δ) = (sels p d true φ).length * BS p d (Γ, Δ) := by
  rw [BS_eq, BS_eq]
  simp only [List.map_cons, List.prod_cons]
  ring

theorem BS_cons_left (Γ Δ : List Fm) (φ : Fm) :
    BS p d (φ :: Γ, Δ) = (sels p d false φ).length * BS p d (Γ, Δ) := by
  rw [BS_eq, BS_eq]
  simp only [List.map_cons, List.prod_cons]
  ring

theorem selsS_self {S : Seq} (h1 : ∀ φ ∈ S.1, sels p d false φ = [φ])
    (h2 : ∀ φ ∈ S.2, sels p d true φ = [φ]) : selsS p d S = [S] := by
  unfold selsS
  rw [(List.map_congr_left h1 : S.1.map (sels p d false) = S.1.map fun x => [x]),
    (List.map_congr_left h2 : S.2.map (sels p d true) = S.2.map fun x => [x]),
    sections_single, sections_single]
  rfl

theorem self_of {S S' : Seq} (h1 : ∀ φ ∈ S.1, sels p d false φ = [φ])
    (h2 : ∀ φ ∈ S.2, sels p d true φ = [φ]) (h : S' ∈ selsS p d S) : S' = S := by
  rw [selsS_self h1 h2] at h
  exact List.mem_singleton.1 h

/-- A selection of a sequent of the fragment lies in the one line fragment `DegS`. -/
theorem sel_seq_props {S S' : Seq} (h : S' ∈ selsS p d S) (hx : XDegS p d S) (hV : VarS V S) :
    DegS p d S' ∧ VarS V S' ∧ wS S' ≤ wS S := by
  obtain ⟨h1, h2⟩ := mem_selsS.1 h
  refine ⟨⟨fun φ' hφ' => ?_, fun φ' hφ' => ?_⟩, fun φ' hφ' => ?_, ?_⟩
  · obtain ⟨φ, hφ, hr⟩ := forall2_left h1 hφ'
    exact (sels_props φ false φ' hr).1.trans (hx.1 φ hφ)
  · obtain ⟨φ, hφ, hr⟩ := forall2_left h2 hφ'
    exact (sels_props φ true φ' hr).1.trans (hx.2 φ hφ)
  · rcases List.mem_append.1 hφ' with hφ' | hφ'
    · obtain ⟨φ, hφ, hr⟩ := forall2_left h1 hφ'
      exact (sels_props φ false φ' hr).2.1.trans (hV φ (List.mem_append_left _ hφ))
    · obtain ⟨φ, hφ, hr⟩ := forall2_left h2 hφ'
      exact (sels_props φ true φ' hr).2.1.trans (hV φ (List.mem_append_right _ hφ))
  · have e1 := forall2_sum_le Fm.size h1 (fun a b _ hr => (sels_props b false a hr).2.2)
    have e2 := forall2_sum_le Fm.size h2 (fun a b _ hr => (sels_props b true a hr).2.2)
    unfold wS
    rw [List.map_append, List.sum_append, List.map_append, List.sum_append]
    omega

/-- The one line fragment is contained in the expanded one, with one selection per sequent. -/
theorem xdegS_of_degS {S : Seq} (h : DegS p d S) : XDegS p d S :=
  ⟨fun φ hφ => (xtd_le_td φ false).trans (h.1 φ hφ),
    fun φ hφ => (xtd_le_td φ true).trans (h.2 φ hφ)⟩

theorem BS_of_degS {S : Seq} (h : DegS p d S) : BS p d S = 1 := by
  unfold BS
  rw [selsS_self (fun φ hφ => sels_of_td φ false (h.1 φ hφ))
    (fun φ hφ => sels_of_td φ true (h.2 φ hφ))]
  rfl

/-! ## The axiom `φ ⊢ φ` -/

theorem id_narrow {φ : Fm} (hd : pd p φ ≤ d) (hV : fv φ ⊆ V) {Y : PLine p} (hY : GoodL V d Y)
    (h1 : ∀ g ∈ trL p true φ, g ∈ Y) (h2 : ∀ g ∈ trL p false φ, g ∈ Y)
    {Ls : List (PLine p)} (h : Der Φ V d Ls) :
    ∃ Ls₂, Ext Φ V d Ls Ls₂ (10 * φ.size) ∧ Y ∈ Ls₂ := by
  have gI : ∀ s : Bool, GoodL V d (insert (sg s (val p φ)) Y) := by
    intro s x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ind_sg hd hV _
    · exact hY x hx
  obtain ⟨Ls₁, hE₁, hm₁⟩ := reach_split φ hd hV true (gI false)
    (fun g hg => Finset.mem_insert_of_mem (h1 g hg)) (Finset.mem_insert_self _ _) h
  obtain ⟨Ls₂, hE₂, hm₂⟩ := reach_split φ hd hV false (gI true)
    (fun g hg => Finset.mem_insert_of_mem (h2 g hg)) (Finset.mem_insert_self _ _) hE₁.1
  obtain ⟨Ls₃, hE₃, hm₃⟩ := reach_step hE₂.1
    (prems := [insert (sg false (val p φ)) Y, insert (sg true (val p φ)) Y])
    (by intro N hN; simp at hN; rcases hN with rfl | rfl
        · exact hE₂.2.1 _ hm₁
        · exact hm₂)
    (PInfer.sem2 (g₁ := sg false (val p φ)) (g₂ := sg true (val p φ)) (g₃ := 0)
      (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
      (fun a => by
        rw [eval_sg_val, eval_sg_val]
        cases Fm.eval p a φ <;> simp) Y
      (Finset.erase_insert_subset _ _) (Finset.erase_insert_subset _ _) (Or.inr rfl)) hY
  have := FBridge.size_pos φ
  exact ⟨Ls₃, ((hE₁.trans hE₂).trans hE₃).mono (by omega), hm₃⟩

/-- Statement of `reach_id` for one formula. -/
def IdP (p : ℕ) [Fact p.Prime] (d : ℕ) (Φ : CNF) (V : Finset ℕ) (φ : Fm) : Prop :=
  fv φ ⊆ V → ∀ (s : Bool) (φ1 φ2 : Fm), φ1 ∈ sels p d s φ → φ2 ∈ sels p d (!s) φ →
    td p s φ1 ≤ d → td p (!s) φ2 ≤ d → ∀ {Y : PLine p}, GoodL V d Y →
    (∀ g ∈ trL p s φ1, g ∈ Y) → (∀ g ∈ trL p (!s) φ2, g ∈ Y) →
    ∀ {Ls : List (PLine p)}, Der Φ V d Ls → ∃ Ls₂, Ext Φ V d Ls Ls₂ (10 * φ.size) ∧ Y ∈ Ls₂

/-- **Identity.**  For selections `φ1`, `φ2` of `φ` with opposite signs, a line containing both
translations is derivable with at most `10 |φ|` lines. -/
theorem reach_id : ∀ φ : Fm, IdP p d Φ V φ := by
  have narrow : ∀ φ : Fm, pd p φ ≤ d → fv φ ⊆ V → ∀ (s : Bool) (φ1 φ2 : Fm),
      φ1 ∈ sels p d s φ → φ2 ∈ sels p d (!s) φ → ∀ {Y : PLine p}, GoodL V d Y →
      (∀ g ∈ trL p s φ1, g ∈ Y) → (∀ g ∈ trL p (!s) φ2, g ∈ Y) →
      ∀ {Ls : List (PLine p)}, Der Φ V d Ls →
        ∃ Ls₂, Ext Φ V d Ls Ls₂ (10 * φ.size) ∧ Y ∈ Ls₂ := by
    intro φ hd hV s φ1 φ2 h1 h2 Y hY g1 g2 Ls h
    rw [sels_self φ hd, List.mem_singleton] at h1 h2
    rw [h1] at g1
    rw [h2] at g2
    cases s
    · exact id_narrow hd hV hY g2 g1 h
    · exact id_narrow hd hV hY g1 g2 h
  have gate : ∀ (s₀ : Bool) (l : List Fm), (∀ ψ ∈ l, IdP p d Φ V ψ) → fv (gt s₀ l) ⊆ V →
      ∀ (φa φb : Fm), φa ∈ sels p d s₀ (gt s₀ l) → φb ∈ sels p d (!s₀) (gt s₀ l) →
      td p s₀ φa ≤ d → td p (!s₀) φb ≤ d → ∀ {Y : PLine p}, GoodL V d Y →
      (∀ g ∈ trL p s₀ φa, g ∈ Y) → (∀ g ∈ trL p (!s₀) φb, g ∈ Y) →
      ∀ {Ls : List (PLine p)}, Der Φ V d Ls →
        ∃ Ls₂, Ext Φ V d Ls Ls₂ (10 * (gt s₀ l).size) ∧ Y ∈ Ls₂ := by
    intro s₀ l ih hV φa φb ha hb ta tb Y hY ga gb Ls h
    by_cases hn : pd p (gt s₀ l) ≤ d
    · exact narrow _ hn hV s₀ φa φb ha hb hY ga gb h
    · rw [sels_gt_same, if_neg hn] at ha
      obtain ⟨ls, hls, ha'⟩ := List.mem_flatten.1 ha
      obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hls
      rw [sels_gt_opp] at hb
      obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hb
      have hF : SelL p d (!s₀) l' l := mem_sections_sels.1 hl'
      obtain ⟨ψ', hψ', hr⟩ := forall2_right hF hψ
      have tψ' : td p (!s₀) ψ' ≤ d := by
        rw [td_gt_opp] at tb
        exact (le_foldr_max (List.mem_map.2 ⟨ψ', hψ', rfl⟩)).trans tb
      obtain ⟨Ls₂, hE, hm⟩ := ih ψ hψ (fun v hv => hV ((mem_fv_gt s₀ l v).2 ⟨ψ, hψ, hv⟩)) s₀ φa ψ'
        ha' hr ta tψ' hY ga (fun g hg => gb g ((mem_trL_gt s₀ l' g).2 ⟨ψ', hψ', hg⟩)) h
      refine ⟨Ls₂, hE.mono ?_, hm⟩
      rw [size_gt]
      have := le_sum_of_mem (List.mem_map.2 ⟨ψ, hψ, rfl⟩ : ψ.size ∈ l.map Fm.size)
      omega
  refine Fm_ind ?_ ?_ ?_ ?_ ?_
  · intro i hV s φ1 φ2 h1 h2 t1 t2 Y hY g1 g2 Ls h
    have hφ1 := h1
    rw [sels_var, List.mem_singleton] at hφ1
    have hd : pd p (.var i) ≤ d := by
      rw [hφ1, td_var] at t1; rw [pd_var]; exact t1
    exact narrow _ hd hV s φ1 φ2 h1 h2 hY g1 g2 h
  · intro φ ih hV s φ1 φ2 h1 h2 t1 t2 Y hY g1 g2 Ls h
    rw [fv_neg] at hV
    rw [sels_neg] at h1 h2
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 h1
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h2
    rw [td_neg] at t1 t2
    obtain ⟨Ls₂, hE, hm⟩ := ih hV (!s) a b ha hb t1 t2 hY
      (fun g hg => g1 g (by rw [trL_neg]; exact hg))
      (fun g hg => g2 g (by rw [trL_neg]; exact hg)) h
    exact ⟨Ls₂, hE.mono (by rw [size_neg]; omega), hm⟩
  · intro l ih hV s φ1 φ2 h1 h2 t1 t2 Y hY g1 g2 Ls h
    cases s
    · exact gate true l ih hV φ2 φ1 h2 h1 t2 t1 hY g2 g1 h
    · exact gate true l ih hV φ1 φ2 h1 h2 t1 t2 hY g1 g2 h
  · intro l ih hV s φ1 φ2 h1 h2 t1 t2 Y hY g1 g2 Ls h
    cases s
    · exact gate false l ih hV φ1 φ2 h1 h2 t1 t2 hY g1 g2 h
    · exact gate false l ih hV φ2 φ1 h2 h1 t2 t1 hY g2 g1 h
  · intro r l _ hV s φ1 φ2 h1 h2 t1 t2 Y hY g1 g2 Ls h
    have hφ1 := h1
    rw [sels_mod, List.mem_singleton] at hφ1
    have hd : pd p (.mod r l) ≤ d := by
      rw [hφ1, td_mod] at t1; exact t1
    exact narrow _ hd hV s φ1 φ2 h1 h2 hY g1 g2 h

/-! ## Cut -/

/-- Cut on a formula of degree at most `d`: one line per sign. -/
theorem cut_narrow {φ : Fm} {Y : PLine p} (hY : GoodL V d Y)
    {Ls : List (PLine p)} (h : Der Φ V d Ls) {M₁ M₂ : PLine p} (h₁ : M₁ ∈ Ls) (h₂ : M₂ ∈ Ls)
    (hx₁ : ∀ x ∈ M₁, x ∈ Y ∨ x ∈ trL p true φ) (hx₂ : ∀ x ∈ M₂, x ∈ Y ∨ x ∈ trL p false φ) :
    ∃ Ls₂, Ext Φ V d Ls Ls₂ (2 * φ.size) ∧ ∃ M ∈ Ls₂, M ⊆ Y := by
  have core : ∀ (s : Bool), trL p s φ = [sg s (val p φ)] → ∀ {Ms Mo : PLine p}, Ms ∈ Ls →
      Mo ∈ Ls → (∀ x ∈ Ms, x ∈ Y ∨ x ∈ trL p s φ) → (∀ x ∈ Mo, x ∈ Y ∨ x ∈ trL p (!s) φ) →
      ∃ Ls₂, Ext Φ V d Ls Ls₂ (2 * φ.size) ∧ ∃ M ∈ Ls₂, M ⊆ Y := by
    intro s hs Ms Mo hMs hMo hxs hxo
    by_cases hU : sg s (val p φ) ∈ Ms
    · have hA : Ms.erase (sg s (val p φ)) ⊆ Y := by
        intro x hx
        obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
        rcases hxs x hx with hY' | hT
        · exact hY'
        · rw [hs, List.mem_singleton] at hT; exact absurd hT hne
      have hB : Mo \ (trL p (!s) φ).toFinset ⊆ Y := by
        intro x hx
        obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.1 hx
        rcases hxo x hx1 with hY' | hT
        · exact hY'
        · exact absurd (List.mem_toFinset.2 hT) hx2
      obtain ⟨Ls₂, hE, hm⟩ := reach_map2 hU 0 hY hA (Or.inr rfl) (trL p (!s) φ).toFinset
        (fun T hT a => tr_excl (s := s) (List.mem_toFinset.1 hT) a) h hMs hMo hB
      refine ⟨Ls₂, hE.mono ?_, Y, hm, subset_rfl⟩
      have := card_trL_le (p := p) (!s) φ
      have := FBridge.size_pos φ
      omega
    · refine ⟨Ls, (Ext.refl h).mono (Nat.zero_le _), Ms, hMs, fun x hx => ?_⟩
      rcases hxs x hx with hY' | hT
      · exact hY'
      · rw [hs, List.mem_singleton] at hT
        rw [hT] at hx
        exact absurd hx hU
  obtain ⟨s, -, hs⟩ := tr_single (p := p) φ
  cases s
  · exact core false hs h₂ h₁ hx₂ hx₁
  · exact core true hs h₁ h₂ hx₁ hx₂

/-- Reach, for every element of a list, a line contained in its target. -/
theorem reach_list_sub {α : Type} (ts : List α) (cost : ℕ) (tgt : α → PLine p)
    {Ls : List (PLine p)}
    (H : ∀ t ∈ ts, ∀ {Ls' : List (PLine p)}, Der Φ V d Ls' → (∀ M ∈ Ls, M ∈ Ls') →
      ∃ Ls₂, Ext Φ V d Ls' Ls₂ cost ∧ ∃ M ∈ Ls₂, M ⊆ tgt t) (h : Der Φ V d Ls) :
    ∃ Ls₂, Ext Φ V d Ls Ls₂ (ts.length * cost) ∧ ∀ t ∈ ts, ∃ M ∈ Ls₂, M ⊆ tgt t := by
  induction ts with
  | nil => exact ⟨Ls, (Ext.refl h).mono (Nat.zero_le _), by simp⟩
  | cons t ts ih =>
    obtain ⟨Ls₁, hE₁, hm₁⟩ := ih (fun t' ht' => H t' (List.mem_cons_of_mem _ ht'))
    obtain ⟨Ls₂, hE₂, hm₂⟩ := H t (by simp) hE₁.1 hE₁.2.1
    refine ⟨Ls₂, (hE₁.trans hE₂).mono (by rw [List.length_cons, Nat.succ_mul]), ?_⟩
    intro t' ht'
    rcases List.mem_cons.1 ht' with rfl | ht'
    · exact hm₂
    · obtain ⟨M, hM, hsub⟩ := hm₁ t' ht'
      exact ⟨M, hE₂.2.1 _ hM, hsub⟩

/-- Statement of `reach_xcut` for one formula. -/
def CutP (p : ℕ) [Fact p.Prime] (d : ℕ) (Φ : CNF) (V : Finset ℕ) (φ : Fm) : Prop :=
  fv φ ⊆ V → (∀ s' : Bool, xtd p d s' φ ≤ d) → ∀ (s : Bool) {Y : PLine p}, GoodL V d Y →
    ∀ {Ls : List (PLine p)}, Der Φ V d Ls →
    (∀ φ1 ∈ sels p d s φ, ∃ M ∈ Ls, ∀ x ∈ M, x ∈ Y ∨ x ∈ trL p s φ1) →
    (∀ φ2 ∈ sels p d (!s) φ, ∃ M ∈ Ls, ∀ x ∈ M, x ∈ Y ∨ x ∈ trL p (!s) φ2) →
    ∃ Ls₂, Ext Φ V d Ls Ls₂
      (2 * φ.size * (sels p d s φ).length * (sels p d (!s) φ).length) ∧ ∃ M ∈ Ls₂, M ⊆ Y

theorem cut_arith (n t sz S T N : ℕ) (hN : 0 < N) :
    n * (2 * S * T * N) + 2 * sz * t * n ≤ 2 * (sz + S) * (t + T) * (n * N) := by
  have h1 : 2 * sz * t * n ≤ 2 * sz * t * n * N := Nat.le_mul_of_pos_right _ hN
  have e : 2 * (sz + S) * (t + T) * (n * N) =
      n * (2 * S * T * N) + 2 * sz * t * n * N + 2 * sz * T * n * N + 2 * S * t * n * N := by ring
  rw [e]
  exact Nat.le_add_right_of_le (Nat.le_add_right_of_le (Nat.add_le_add_left h1 _))

/-- Cut on the members of an expanded gate, one member at a time.  `s₀` is the sign for which the
gate is expanded into the selections of its members. -/
theorem cut_list (s₀ : Bool) : ∀ (l : List Fm), (∀ ψ ∈ l, CutP p d Φ V ψ) →
    (∀ ψ ∈ l, fv ψ ⊆ V) → (∀ ψ ∈ l, ∀ s' : Bool, xtd p d s' ψ ≤ d) →
    ∀ {Y : PLine p}, GoodL V d Y → ∀ {Ls : List (PLine p)}, Der Φ V d Ls →
    (∀ ψ ∈ l, ∀ φa ∈ sels p d s₀ ψ, ∃ M ∈ Ls, ∀ x ∈ M, x ∈ Y ∨ x ∈ trL p s₀ φa) →
    (∀ l', SelL p d (!s₀) l' l →
      ∃ M ∈ Ls, ∀ x ∈ M, x ∈ Y ∨ ∃ ψ' ∈ l', x ∈ trL p (!s₀) ψ') →
    ∃ Ls₂, Ext Φ V d Ls Ls₂
      (2 * (l.map Fm.size).sum * ((l.map (sels p d s₀)).map List.length).sum *
        ((l.map (sels p d (!s₀))).map List.length).prod) ∧ ∃ M ∈ Ls₂, M ⊆ Y := by
  intro l
  induction l with
  | nil =>
    intro _ _ _ Y hY Ls h _ hb
    obtain ⟨M, hM, hx⟩ := hb [] List.Forall₂.nil
    refine ⟨Ls, (Ext.refl h).mono (Nat.zero_le _), M, hM, fun x hx' => ?_⟩
    rcases hx x hx' with hY' | ⟨ψ', hψ', -⟩
    · exact hY'
    · simp at hψ'
  | cons ψ l ih =>
    intro hC hV hX Y hY Ls h ha hb
    have hCl : ∀ χ ∈ l, CutP p d Φ V χ := fun χ hχ => hC χ (List.mem_cons_of_mem _ hχ)
    have hVl : ∀ χ ∈ l, fv χ ⊆ V := fun χ hχ => hV χ (List.mem_cons_of_mem _ hχ)
    have hXl : ∀ χ ∈ l, ∀ s' : Bool, xtd p d s' χ ≤ d :=
      fun χ hχ => hX χ (List.mem_cons_of_mem _ hχ)
    obtain ⟨Ls₁, hE₁, hm₁⟩ := reach_list_sub (Φ := Φ) (V := V) (d := d) (sels p d (!s₀) ψ)
      (2 * (l.map Fm.size).sum * ((l.map (sels p d s₀)).map List.length).sum *
        ((l.map (sels p d (!s₀))).map List.length).prod)
      (fun ψ' => Y ∪ (trL p (!s₀) ψ').toFinset) (Ls := Ls)
      (fun ψ' hψ' Ls' h' hsub => by
        have hgood : GoodL V d (Y ∪ (trL p (!s₀) ψ').toFinset) := by
          intro x hx
          rcases Finset.mem_union.1 hx with hx | hx
          · exact hY x hx
          · obtain ⟨t1, t2, -⟩ := sels_props ψ (!s₀) ψ' hψ'
            exact tr_ind (t1.trans (hX ψ (by simp) _)) (t2.trans (hV ψ (by simp)))
              (List.mem_toFinset.1 hx)
        refine ih hCl hVl hXl hgood h' ?_ ?_
        · intro χ hχ φa hφa
          obtain ⟨M, hM, hx⟩ := ha χ (List.mem_cons_of_mem _ hχ) φa hφa
          exact ⟨M, hsub M hM, fun x hx' =>
            (hx x hx').imp (fun hy => Finset.mem_union_left _ hy) id⟩
        · intro l' hl'
          obtain ⟨M, hM, hx⟩ := hb (ψ' :: l') (List.Forall₂.cons hψ' hl')
          refine ⟨M, hsub M hM, fun x hx' => ?_⟩
          rcases hx x hx' with hy | ⟨χ, hχ, hg⟩
          · exact Or.inl (Finset.mem_union_left _ hy)
          · rcases List.mem_cons.1 hχ with rfl | hχ
            · exact Or.inl (Finset.mem_union_right _ (List.mem_toFinset.2 hg))
            · exact Or.inr ⟨χ, hχ, hg⟩) h
    have A : ∀ φ1 ∈ sels p d s₀ ψ, ∃ M ∈ Ls₁, ∀ x ∈ M, x ∈ Y ∨ x ∈ trL p s₀ φ1 := by
      intro φ1 h1
      obtain ⟨M, hM, hx⟩ := ha ψ (by simp) φ1 h1
      exact ⟨M, hE₁.2.1 _ hM, hx⟩
    have Bh : ∀ φ2 ∈ sels p d (!s₀) ψ, ∃ M ∈ Ls₁, ∀ x ∈ M, x ∈ Y ∨ x ∈ trL p (!s₀) φ2 := by
      intro φ2 h2
      obtain ⟨M, hM, hsub⟩ := hm₁ φ2 h2
      exact ⟨M, hM, fun x hx => (Finset.mem_union.1 (hsub hx)).imp id List.mem_toFinset.1⟩
    obtain ⟨Ls₂, hE₂, hm₂⟩ := hC ψ (by simp) (hV ψ (by simp)) (hX ψ (by simp)) s₀ hY hE₁.1 A Bh
    refine ⟨Ls₂, (hE₁.trans hE₂).mono ?_, hm₂⟩
    have hN : 0 < ((l.map (sels p d (!s₀))).map List.length).prod := by
      refine prod_pos' _ fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨χ, -, rfl⟩ := List.mem_map.1 hy
      exact sels_pos χ _
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    exact cut_arith _ _ _ _ _ _ hN

/-- **Cut on an expanded formula.**  Given, for every selection of `φ` with either sign, a line
contained in `Y` together with the translation of that selection, a line contained in `Y` is
derivable with at most `2 |φ|` times the product of the two numbers of selections new lines. -/
theorem reach_xcut : ∀ φ : Fm, CutP p d Φ V φ := by
  have narrow : ∀ φ : Fm, pd p φ ≤ d → CutP p d Φ V φ := by
    intro φ hd hV _ s Y hY Ls h h1 h2
    rw [sels_self φ hd] at h1 h2
    rw [sels_self φ hd s, sels_self φ hd (!s)]
    obtain ⟨M1, hM1, hx1⟩ := h1 φ (by simp)
    obtain ⟨M2, hM2, hx2⟩ := h2 φ (by simp)
    cases s
    · obtain ⟨Ls₂, hE, hm⟩ := cut_narrow hY h hM2 hM1 hx2 hx1
      exact ⟨Ls₂, hE.mono (by simp), hm⟩
    · obtain ⟨Ls₂, hE, hm⟩ := cut_narrow hY h hM1 hM2 hx1 hx2
      exact ⟨Ls₂, hE.mono (by simp), hm⟩
  have gate : ∀ (s₀ : Bool) (l : List Fm), (∀ ψ ∈ l, CutP p d Φ V ψ) → fv (gt s₀ l) ⊆ V →
      (∀ s' : Bool, xtd p d s' (gt s₀ l) ≤ d) → ∀ {Y : PLine p}, GoodL V d Y →
      ∀ {Ls : List (PLine p)}, Der Φ V d Ls →
      (∀ φa ∈ sels p d s₀ (gt s₀ l), ∃ M ∈ Ls, ∀ x ∈ M, x ∈ Y ∨ x ∈ trL p s₀ φa) →
      (∀ φb ∈ sels p d (!s₀) (gt s₀ l), ∃ M ∈ Ls, ∀ x ∈ M, x ∈ Y ∨ x ∈ trL p (!s₀) φb) →
      ∃ Ls₂, Ext Φ V d Ls Ls₂ (2 * (gt s₀ l).size * (sels p d s₀ (gt s₀ l)).length *
        (sels p d (!s₀) (gt s₀ l)).length) ∧ ∃ M ∈ Ls₂, M ⊆ Y := by
    intro s₀ l ih hV hX Y hY Ls h ha hb
    by_cases hn : pd p (gt s₀ l) ≤ d
    · exact narrow _ hn hV hX s₀ hY h ha hb
    · have hXm : ∀ ψ ∈ l, ∀ s' : Bool, xtd p d s' ψ ≤ d := by
        intro ψ hψ s'
        rcases bool_cases s' s₀ with e | e
        · rw [e]
          have := hX s₀
          rw [xtd_gt_same, if_neg hn] at this
          exact (le_foldr_max (List.mem_map.2 ⟨ψ, hψ, rfl⟩)).trans this
        · rw [e]
          have := hX (!s₀)
          rw [xtd_gt_opp] at this
          exact (le_foldr_max (List.mem_map.2 ⟨ψ, hψ, rfl⟩)).trans this
      obtain ⟨Ls₂, hE, hm⟩ := cut_list s₀ l ih
        (fun ψ hψ v hv => hV ((mem_fv_gt s₀ l v).2 ⟨ψ, hψ, hv⟩)) hXm hY h
        (fun ψ hψ φa hφa => ha φa (by
          rw [sels_gt_same, if_neg hn]
          exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ψ, hψ, rfl⟩, hφa⟩))
        (fun l' hl' => by
          obtain ⟨M, hM, hx⟩ := hb (gt s₀ l') (by
            rw [sels_gt_opp]
            exact List.mem_map.2 ⟨l', mem_sections_sels.2 hl', rfl⟩)
          exact ⟨M, hM, fun x hx' => (hx x hx').imp id fun hg => (mem_trL_gt s₀ l' x).1 hg⟩)
      refine ⟨Ls₂, hE.mono ?_, hm⟩
      rw [sels_gt_same, if_neg hn, sels_gt_opp, List.length_map, length_sections,
        List.length_flatten, size_gt]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ _)))
  refine Fm_ind ?_ ?_ ?_ ?_ ?_
  · intro i hV hX
    exact narrow _ (by have := hX true; rw [xtd_var] at this; rw [pd_var]; exact this) hV hX
  · intro φ ih hV hX s Y hY Ls h h1 h2
    rw [fv_neg] at hV
    have hX' : ∀ s' : Bool, xtd p d s' φ ≤ d := fun s' => by
      have := hX (!s'); rwa [xtd_neg, Bool.not_not] at this
    obtain ⟨Ls₂, hE, hm⟩ := ih hV hX' (!s) hY h
      (fun φ1 hφ1 => by
        obtain ⟨M, hM, hx⟩ := h1 (.neg φ1) (by
          rw [sels_neg]; exact List.mem_map.2 ⟨φ1, hφ1, rfl⟩)
        exact ⟨M, hM, fun x hx' => (hx x hx').imp id fun hg => by rw [trL_neg] at hg; exact hg⟩)
      (fun φ2 hφ2 => by
        obtain ⟨M, hM, hx⟩ := h2 (.neg φ2) (by
          rw [sels_neg]; exact List.mem_map.2 ⟨φ2, hφ2, rfl⟩)
        exact ⟨M, hM, fun x hx' => (hx x hx').imp id fun hg => by rw [trL_neg] at hg; exact hg⟩)
    refine ⟨Ls₂, hE.mono ?_, hm⟩
    rw [sels_neg, sels_neg, List.length_map, List.length_map, size_neg]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ _)))
  · intro l ih hV hX s Y hY Ls h h1 h2
    cases s
    · obtain ⟨Ls₂, hE, hm⟩ := gate true l ih hV hX hY h h2 h1
      have e : 2 * (Fm.and l).size * (sels p d true (.and l)).length *
          (sels p d false (.and l)).length ≤ 2 * (Fm.and l).size *
          (sels p d false (.and l)).length * (sels p d true (.and l)).length :=
        le_of_eq (by ring)
      exact ⟨Ls₂, hE.mono e, hm⟩
    · exact gate true l ih hV hX hY h h1 h2
  · intro l ih hV hX s Y hY Ls h h1 h2
    cases s
    · exact gate false l ih hV hX hY h h1 h2
    · obtain ⟨Ls₂, hE, hm⟩ := gate false l ih hV hX hY h h2 h1
      have e : 2 * (Fm.or l).size * (sels p d false (.or l)).length *
          (sels p d true (.or l)).length ≤ 2 * (Fm.or l).size *
          (sels p d true (.or l)).length * (sels p d false (.or l)).length :=
        le_of_eq (by ring)
      exact ⟨Ls₂, hE.mono e, hm⟩
  · intro r l _ hV hX
    exact narrow _ (by have := hX true; rw [xtd_mod] at this; exact this) hV hX

/-! ## Selections commute with the rules -/

theorem sels_lit (l : Literal) : sels p d true (litFm l) = [litFm l] := by
  unfold litFm
  split_ifs
  · exact sels_var _ _
  · rw [sels_neg, sels_var]; rfl

theorem sels_clause (C : Clause) : sels p d true (clauseFm C) = [clauseFm C] := by
  unfold clauseFm
  rw [sels_or_true]
  have e : (C.toList.map litFm).map (sels p d true) = (C.toList.map litFm).map fun x => [x] :=
    List.map_congr_left fun ψ hψ => by
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hψ
      exact sels_lit l
  rw [e, sections_single]; rfl

/-- **Selections commute with the rules.**  A selection of the conclusion of a rule follows by a
rule of the calculus from the selections of the premises, except for the axiom `φ ⊢ φ` and cut. -/
theorem sel_fstep {F : CNF} {prev : List Seq} {S S' : Seq} (hstep : FStep p F prev S)
    (hx : XDegS p d S) (hS' : S' ∈ selsS p d S) :
    (∃ φ, S = ([φ], [φ])) ∨ (∃ φ, (S.1, φ :: S.2) ∈ prev ∧ (φ :: S.1, S.2) ∈ prev) ∨
      FStep p F (prev.flatMap (selsS p d)) S' := by
  rcases hstep with ⟨C, hC, rfl⟩ | ⟨φ, rfl⟩ | rfl | rfl | rfl | ⟨r, hr, rfl⟩ | ⟨r, φ, l, rfl⟩ |
      ⟨r, φ, l, rfl⟩ | ⟨r, φ, l, rfl⟩ | ⟨r, φ, l, rfl⟩ | ⟨T, hT, h1, h2⟩ | ⟨φ, h1, h2⟩ |
      ⟨φ, Γ, Δ, rfl, h1⟩ | ⟨φ, Γ, Δ, rfl, h1⟩ | ⟨l, Γ, Δ, φ, hφ, rfl, h1⟩ | ⟨l, Γ, Δ, rfl, h1⟩ |
      ⟨l, Γ, Δ, rfl, h1⟩ | ⟨l, Γ, Δ, φ, hφ, rfl, h1⟩
  · -- clause axiom
    have e := self_of (S := ([], [clauseFm C])) (by simp)
      (by intro φ hφ; simp at hφ; subst hφ; exact sels_clause C) hS'
    subst e
    right; right; unfold FStep
    exact Or.inl ⟨C, hC, rfl⟩
  · exact Or.inl ⟨φ, rfl⟩
  · -- ⊢ AND()
    have e := self_of (S := ([], [Fm.and []])) (by simp)
      (by intro φ hφ; simp at hφ; subst hφ; exact sels_self _ (by rw [pd_and]; simp) true) hS'
    subst e
    right; right; unfold FStep
    exact Or.inr (Or.inr (Or.inl rfl))
  · -- OR() ⊢
    have e := self_of (S := ([Fm.or []], []))
      (by intro φ hφ; simp at hφ; subst hφ; exact sels_self _ (by rw [pd_or]; simp) false)
      (by simp) hS'
    subst e
    right; right; unfold FStep
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · -- ⊢ MOD_0()
    have e := self_of (S := ([], [Fm.mod 0 []])) (by simp)
      (by intro φ hφ; simp at hφ; subst hφ; exact sels_mod _ _ _) hS'
    subst e
    right; right; unfold FStep
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · -- MOD_r() ⊢
    have e := self_of (S := ([Fm.mod r []], []))
      (by intro φ hφ; simp at hφ; subst hφ; exact sels_mod _ _ _) (by simp) hS'
    subst e
    right; right; unfold FStep
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, rfl⟩)))))
  · -- MOD_r(φ, l), φ ⊢ MOD_{r-1}(l)
    have hpd : pd p φ ≤ d := by
      have := hx.1 (.mod r (φ :: l)) (by simp)
      rw [xtd_mod] at this
      exact (pd_le_mod (by simp)).trans this
    have e := self_of (S := ([Fm.mod r (φ :: l), φ], [Fm.mod (r + p - 1) l]))
      (by intro χ hχ; simp at hχ; rcases hχ with rfl | rfl
          · exact sels_mod _ _ _
          · exact sels_self _ hpd _)
      (by intro χ hχ; simp at hχ; subst hχ; exact sels_mod _ _ _) hS'
    subst e
    right; right; unfold FStep
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, φ, l, rfl⟩))))))
  · -- MOD_r(φ, l) ⊢ φ, MOD_r(l)
    have hpd : pd p φ ≤ d := by
      have := hx.1 (.mod r (φ :: l)) (by simp)
      rw [xtd_mod] at this
      exact (pd_le_mod (by simp)).trans this
    have e := self_of (S := ([Fm.mod r (φ :: l)], [φ, Fm.mod r l]))
      (by intro χ hχ; simp at hχ; subst hχ; exact sels_mod _ _ _)
      (by intro χ hχ; simp at hχ; rcases hχ with rfl | rfl
          · exact sels_self _ hpd _
          · exact sels_mod _ _ _) hS'
    subst e
    right; right; unfold FStep
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, φ, l, rfl⟩)))))))
  · -- φ, MOD_{r-1}(l) ⊢ MOD_r(φ, l)
    have hpd : pd p φ ≤ d := by
      have := hx.2 (.mod r (φ :: l)) (by simp)
      rw [xtd_mod] at this
      exact (pd_le_mod (by simp)).trans this
    have e := self_of (S := ([φ, Fm.mod (r + p - 1) l], [Fm.mod r (φ :: l)]))
      (by intro χ hχ; simp at hχ; rcases hχ with rfl | rfl
          · exact sels_self _ hpd _
          · exact sels_mod _ _ _)
      (by intro χ hχ; simp at hχ; subst hχ; exact sels_mod _ _ _) hS'
    subst e
    right; right; unfold FStep
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨r, φ, l, rfl⟩))))))))
  · -- MOD_r(l) ⊢ φ, MOD_r(φ, l)
    have hpd : pd p φ ≤ d := by
      have := hx.2 (.mod r (φ :: l)) (by simp)
      rw [xtd_mod] at this
      exact (pd_le_mod (by simp)).trans this
    have e := self_of (S := ([Fm.mod r l], [φ, Fm.mod r (φ :: l)]))
      (by intro χ hχ; simp at hχ; subst hχ; exact sels_mod _ _ _)
      (by intro χ hχ; simp at hχ; rcases hχ with rfl | rfl
          · exact sels_self _ hpd _
          · exact sels_mod _ _ _) hS'
    subst e
    right; right; unfold FStep
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨r, φ, l, rfl⟩)))))))))
  · -- weakening
    obtain ⟨hs1, hs2⟩ := mem_selsS.1 hS'
    obtain ⟨a, ha1, ha2⟩ := forall2_subset hs1 T.1 h1
    obtain ⟨b, hb1, hb2⟩ := forall2_subset hs2 T.2 h2
    right; right; unfold FStep
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨(a, b), List.mem_flatMap.2 ⟨T, hT, mem_selsS.2 ⟨ha1, hb1⟩⟩, ha2, hb2⟩))))))))))
  · exact Or.inr (Or.inl ⟨φ, h1, h2⟩)
  · -- NOT left
    obtain ⟨A, B⟩ := S'
    obtain ⟨hs1, hs2⟩ := mem_selsS.1 hS'
    obtain ⟨χ, Γ', hχ, hΓ', e⟩ := List.forall₂_cons_right_iff.1 hs1
    simp only at e hs2
    subst e
    rw [sels_neg] at hχ
    obtain ⟨φ', hφ', rfl⟩ := List.mem_map.1 hχ
    right; right; unfold FStep
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨φ', Γ', B, rfl, List.mem_flatMap.2 ⟨_, h1,
        mem_selsS.2 ⟨hΓ', List.Forall₂.cons hφ' hs2⟩⟩⟩))))))))))))
  · -- NOT right
    obtain ⟨A, B⟩ := S'
    obtain ⟨hs1, hs2⟩ := mem_selsS.1 hS'
    obtain ⟨χ, Δ', hχ, hΔ', e⟩ := List.forall₂_cons_right_iff.1 hs2
    simp only at e hs1
    subst e
    rw [sels_neg] at hχ
    obtain ⟨φ', hφ', rfl⟩ := List.mem_map.1 hχ
    right; right; unfold FStep
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨φ', A, Δ', rfl, List.mem_flatMap.2 ⟨_, h1,
        mem_selsS.2 ⟨List.Forall₂.cons hφ' hs1, hΔ'⟩⟩⟩)))))))))))))
  · -- AND left
    obtain ⟨A, B⟩ := S'
    obtain ⟨hs1, hs2⟩ := mem_selsS.1 hS'
    obtain ⟨χ, Γ', hχ, hΓ', e⟩ := List.forall₂_cons_right_iff.1 hs1
    simp only at e hs2
    subst e
    rw [sels_and_false] at hχ
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hχ
    obtain ⟨φ', hφ', hr⟩ := forall2_right (mem_sections_sels.1 hl') hφ
    right; right; unfold FStep
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l', Γ', B, φ', hφ', rfl, List.mem_flatMap.2
        ⟨_, h1, mem_selsS.2 ⟨List.Forall₂.cons hr hΓ', hs2⟩⟩⟩))))))))))))))
  · -- AND right
    obtain ⟨A, B⟩ := S'
    obtain ⟨hs1, hs2⟩ := mem_selsS.1 hS'
    obtain ⟨χ, Δ', hχ, hΔ', e⟩ := List.forall₂_cons_right_iff.1 hs2
    simp only at e hs1
    subst e
    rw [sels_and_true] at hχ
    right; right; unfold FStep
    by_cases hn : pd p (.and l) ≤ d
    · rw [if_pos hn, List.mem_singleton] at hχ
      subst hχ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, A, Δ', rfl, fun φ hφ =>
          List.mem_flatMap.2 ⟨_, h1 φ hφ, mem_selsS.2 ⟨hs1, List.Forall₂.cons
            (by rw [sels_self φ ((pd_le_and hφ).trans hn)]; simp) hΔ'⟩⟩⟩)))))))))))))))
    · rw [if_neg hn] at hχ
      obtain ⟨ls, hls, hχ'⟩ := List.mem_flatten.1 hχ
      obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hls
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨(A, χ :: Δ'), List.mem_flatMap.2 ⟨_, h1 ψ hψ,
          mem_selsS.2 ⟨hs1, List.Forall₂.cons hχ' hΔ'⟩⟩, List.Subset.refl _,
          List.Subset.refl _⟩))))))))))
  · -- OR left
    obtain ⟨A, B⟩ := S'
    obtain ⟨hs1, hs2⟩ := mem_selsS.1 hS'
    obtain ⟨χ, Γ', hχ, hΓ', e⟩ := List.forall₂_cons_right_iff.1 hs1
    simp only at e hs2
    subst e
    rw [sels_or_false] at hχ
    right; right; unfold FStep
    by_cases hn : pd p (.or l) ≤ d
    · rw [if_pos hn, List.mem_singleton] at hχ
      subst hχ
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, Γ', B, rfl, fun φ hφ =>
          List.mem_flatMap.2 ⟨_, h1 φ hφ, mem_selsS.2 ⟨List.Forall₂.cons
            (by rw [sels_self φ ((pd_le_or hφ).trans hn)]; simp) hΓ', hs2⟩⟩⟩))))))))))))))))
    · rw [if_neg hn] at hχ
      obtain ⟨ls, hls, hχ'⟩ := List.mem_flatten.1 hχ
      obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hls
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨(χ :: Γ', B), List.mem_flatMap.2 ⟨_, h1 ψ hψ,
          mem_selsS.2 ⟨List.Forall₂.cons hχ' hΓ', hs2⟩⟩, List.Subset.refl _,
          List.Subset.refl _⟩))))))))))
  · -- OR right
    obtain ⟨A, B⟩ := S'
    obtain ⟨hs1, hs2⟩ := mem_selsS.1 hS'
    obtain ⟨χ, Δ', hχ, hΔ', e⟩ := List.forall₂_cons_right_iff.1 hs2
    simp only at e hs1
    subst e
    rw [sels_or_true] at hχ
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hχ
    obtain ⟨φ', hφ', hr⟩ := forall2_right (mem_sections_sels.1 hl') hφ
    right; right; unfold FStep
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨l', A, Δ', φ', hφ', rfl,
        List.mem_flatMap.2 ⟨_, h1, mem_selsS.2 ⟨hs1, List.Forall₂.cons hr hΔ'⟩⟩⟩))))))))))))))))

/-! ## Simulation of one step -/

theorem arith1 (b c w B : ℕ) (hb : b ≤ B) (hc : c ≤ 11 * w) : b * c ≤ 12 * w * (B * B) :=
  calc b * c ≤ B * (11 * w) := Nat.mul_le_mul hb hc
    _ ≤ (B * B) * (12 * w) := Nat.mul_le_mul (Nat.le_mul_self B) (by omega)
    _ = 12 * w * (B * B) := by ring

theorem arith2 (b bt bf sz w M B : ℕ) (h1 : bt * b ≤ B) (h2 : bf * b ≤ B) (hb : 1 ≤ b)
    (hsz : sz ≤ M) (hb' : b ≤ B) (hw : 1 ≤ w) :
    b * (2 * sz * bt * bf + 1) ≤ 12 * (w + M) * (B * B) := by
  have h3 : bf ≤ B := le_trans (Nat.le_mul_of_pos_right bf hb) h2
  have h4 : 1 * (B * B) ≤ w * (B * B) := Nat.mul_le_mul_right _ hw
  calc b * (2 * sz * bt * bf + 1) = 2 * sz * (bt * b) * bf + b := by ring
    _ ≤ 2 * M * B * B + B * B :=
        Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hsz) h1) h3)
          (hb'.trans (Nat.le_mul_self B))
    _ ≤ 12 * (w + M) * (B * B) := by nlinarith [h4, Nat.zero_le (M * (B * B))]

/-- **One step of the sequent calculus, expanded.**  All selections of the conclusion are derived
from the selections of the premises with at most `12 (wS S + M) B²` new lines, `M` a bound on the
weights and `B` on the numbers of selections of the sequents involved. -/
theorem xstep_sim {F : CNF} {prev : List Seq} {S : Seq} (hstep : FStep p F prev S)
    (hd : XDegS p d S) (hV : VarS V S) (hdp : ∀ T ∈ prev, XDegS p d T)
    (hVp : ∀ T ∈ prev, VarS V T) (M B : ℕ) (hM : ∀ T ∈ prev, wS T ≤ M)
    (hB : ∀ T ∈ prev, BS p d T ≤ B) (hBS : BS p d S ≤ B)
    {Ls : List (PLine p)} (h : Der F V d Ls)
    (hprev : ∀ T ∈ prev, ∀ T' ∈ selsS p d T, trS p T' ∈ Ls) :
    ∃ Ls₂, Ext F V d Ls Ls₂ (12 * (wS S + M) * (B * B)) ∧
      ∀ S' ∈ selsS p d S, trS p S' ∈ Ls₂ := by
  have hW : 1 ≤ wS S := by unfold wS; omega
  have hB1 : 1 ≤ BS p d S := BS_pos S
  have collect : ∀ c : ℕ, BS p d S * c ≤ 12 * (wS S + M) * (B * B) →
      (∀ S' ∈ selsS p d S, ∀ {Ls' : List (PLine p)}, Der F V d Ls' → (∀ N ∈ Ls, N ∈ Ls') →
        ∃ Ls₂, Ext F V d Ls' Ls₂ c ∧ trS p S' ∈ Ls₂) →
      ∃ Ls₂, Ext F V d Ls Ls₂ (12 * (wS S + M) * (B * B)) ∧
        ∀ S' ∈ selsS p d S, trS p S' ∈ Ls₂ := by
    intro c hc H
    obtain ⟨Ls₂, hE, hm⟩ := reach_list (Φ := F) (V := V) (d := d) (selsS p d S) (fun _ => c)
      (fun S' => trS p S') H h
    refine ⟨Ls₂, hE.mono ?_, hm⟩
    have e : ((selsS p d S).map fun _ => c).sum = BS p d S * c := by simp [BS]
    rw [e]; exact hc
  have selp : ∀ S' ∈ selsS p d S, DegS p d S' ∧ VarS V S' ∧ wS S' ≤ wS S :=
    fun S' hS' => sel_seq_props hS' hd hV
  by_cases hid : ∃ φ, S = ([φ], [φ])
  · obtain ⟨φ, rfl⟩ := hid
    refine collect (10 * φ.size) (arith1 _ _ _ _ hBS ?_) ?_
    · have := size_le_wS (S := ([φ], [φ])) (φ := φ) (by simp)
      omega
    · intro S' hS' Ls' h' hsub
      obtain ⟨hD, hVS, -⟩ := selp _ hS'
      obtain ⟨A, B'⟩ := S'
      obtain ⟨hs1, hs2⟩ := mem_selsS.1 hS'
      obtain ⟨φ1, r1, hφ1, hr1, e1⟩ := List.forall₂_cons_right_iff.1 hs1
      obtain ⟨φ2, r2, hφ2, hr2, e2⟩ := List.forall₂_cons_right_iff.1 hs2
      rw [List.forall₂_nil_right_iff] at hr1 hr2
      simp only at e1 e2
      subst hr1; subst hr2; subst e1; subst e2
      exact reach_id φ (hV φ (by simp)) false φ1 φ2 hφ1 hφ2 (hD.1 φ1 (by simp))
        (hD.2 φ2 (by simp)) (good_trS hD hVS)
        (fun g hg => mem_trS.2 (Or.inl ⟨φ1, by simp, hg⟩))
        (fun g hg => mem_trS.2 (Or.inr ⟨φ2, by simp, hg⟩)) h'
  by_cases hcut : ∃ φ, (S.1, φ :: S.2) ∈ prev ∧ (φ :: S.1, S.2) ∈ prev
  · obtain ⟨φ, h1, h2⟩ := hcut
    refine collect (2 * φ.size * (sels p d true φ).length * (sels p d false φ).length + 1)
      (arith2 _ _ _ _ _ _ _ ?_ ?_ hB1 ?_ hBS hW) ?_
    · have := hB _ h1
      rwa [BS_cons_right] at this
    · have := hB _ h2
      rwa [BS_cons_left] at this
    · have e1 := size_le_wS (S := (S.1, φ :: S.2)) (φ := φ) (by simp)
      have e2 := hM _ h1
      omega
    · intro S' hS' Ls' h' hsub
      obtain ⟨hs1, hs2⟩ := mem_selsS.1 hS'
      obtain ⟨hD, hVS, -⟩ := selp _ hS'
      have G := good_trS hD hVS
      have hXφ : ∀ s' : Bool, xtd p d s' φ ≤ d := fun s' => by
        cases s'
        · exact (hdp _ h2).1 φ (by simp)
        · exact (hdp _ h1).2 φ (by simp)
      have hVφ : fv φ ⊆ V := hVp _ h1 φ (by simp)
      obtain ⟨Ls₂, hE, M', hM', hsubM⟩ := reach_xcut φ hVφ hXφ true G h'
        (fun φ2 hφ2 => ⟨trS p (S'.1, φ2 :: S'.2),
          hsub _ (hprev _ h1 _ (mem_selsS.2 ⟨hs1, List.Forall₂.cons hφ2 hs2⟩)), fun x hx => by
            rcases mem_trS.1 hx with ⟨ψ, hψ, hg⟩ | ⟨ψ, hψ, hg⟩
            · exact Or.inl (mem_trS.2 (Or.inl ⟨ψ, hψ, hg⟩))
            · rcases List.mem_cons.1 hψ with rfl | hψ
              · exact Or.inr hg
              · exact Or.inl (mem_trS.2 (Or.inr ⟨ψ, hψ, hg⟩))⟩)
        (fun φ1 hφ1 => ⟨trS p (φ1 :: S'.1, S'.2),
          hsub _ (hprev _ h2 _ (mem_selsS.2 ⟨List.Forall₂.cons hφ1 hs1, hs2⟩)), fun x hx => by
            rcases mem_trS.1 hx with ⟨ψ, hψ, hg⟩ | ⟨ψ, hψ, hg⟩
            · rcases List.mem_cons.1 hψ with rfl | hψ
              · exact Or.inr hg
              · exact Or.inl (mem_trS.2 (Or.inl ⟨ψ, hψ, hg⟩))
            · exact Or.inl (mem_trS.2 (Or.inr ⟨ψ, hψ, hg⟩))⟩)
      obtain ⟨Ls₃, hE₃, hm₃⟩ := reach_weak hE.1 hM' hsubM G
      exact ⟨Ls₃, hE.trans hE₃, hm₃⟩
  · refine collect (10 * (wS S + M)) (arith1 _ _ _ _ hBS (by omega)) ?_
    intro S' hS' Ls' h' hsub
    obtain ⟨hD, hVS, hw⟩ := selp _ hS'
    have hst : FStep p F (prev.flatMap (selsS p d)) S' := by
      rcases sel_fstep hstep hd hS' with h1 | h1 | h1
      · exact absurd h1 hid
      · exact absurd h1 hcut
      · exact h1
    obtain ⟨Ls₂, hE, hm⟩ := step_sim hst hD hVS M
      (fun T' hT' => by
        obtain ⟨T, hT, hTT⟩ := List.mem_flatMap.1 hT'
        exact (sel_seq_props hTT (hdp T hT) (hVp T hT)).2.2.trans (hM T hT)) h'
      (fun T' hT' => by
        obtain ⟨T, hT, hTT⟩ := List.mem_flatMap.1 hT'
        exact hsub _ (hprev T hT T' hTT))
    exact ⟨Ls₂, hE.mono (by omega), hm⟩

theorem xsim_all {F : CNF} {L : List Seq} (hL : FProof p F L) (hdeg : ∀ S ∈ L, XDegS p d S)
    (hvar : ∀ S ∈ L, VarS V S) (M B : ℕ) (hM : ∀ S ∈ L, wS S ≤ M)
    (hB : ∀ S ∈ L, BS p d S ≤ B) :
    ∀ k ≤ L.length, ∃ Ls : List (PLine p), Der F V d Ls ∧
      (∀ S ∈ L.take k, ∀ S' ∈ selsS p d S, trS p S' ∈ Ls) ∧
      Ls.length ≤ k * (12 * (M + M) * (B * B)) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨[], Der.nil, by simp, by simp⟩
  | succ k ih =>
    intro hk
    have hk' : k < L.length := by omega
    obtain ⟨Ls, hD, hmem, hlen⟩ := ih (by omega)
    have hSm : L.get ⟨k, hk'⟩ ∈ L := List.get_mem _ _
    have hT : ∀ T ∈ L.take k, T ∈ L := fun T hT => List.mem_of_mem_take hT
    obtain ⟨Ls₂, hE, hm⟩ := xstep_sim (hL k hk') (hdeg _ hSm) (hvar _ hSm)
      (fun T h => hdeg T (hT T h)) (fun T h => hvar T (hT T h)) M B
      (fun T h => hM T (hT T h)) (fun T h => hB T (hT T h)) (hB _ hSm) hD hmem
    refine ⟨Ls₂, hE.1, ?_, ?_⟩
    · intro S hS
      rw [List.take_add_one] at hS
      rcases List.mem_append.1 hS with h | h
      · exact fun S' hS' => hE.2.1 _ (hmem S h S' hS')
      · rw [List.getElem?_eq_getElem hk'] at h
        simp only [Option.toList_some, List.mem_singleton] at h
        subst h; exact hm
    · have h2 : 12 * (wS (L.get ⟨k, hk'⟩) + M) * (B * B) ≤ 12 * (M + M) * (B * B) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by have := hM _ hSm; omega))
      calc Ls₂.length ≤ Ls.length + 12 * (wS (L.get ⟨k, hk'⟩) + M) * (B * B) := hE.2.2
        _ ≤ k * (12 * (M + M) * (B * B)) + 12 * (M + M) * (B * B) := Nat.add_le_add hlen h2
        _ = (k + 1) * (12 * (M + M) * (B * B)) := by ring

/-- **Bridge with expansion.**  A refutation in the sequent calculus `FProof` (any depth) all of
whose sequents satisfy `XDegS p d`, have variables in `V` and at most `B` selections yields a `PIC`
refutation over `V` with indicators of degree at most `d` and at most `|L| · 12 · 2W · B²` nodes. -/
theorem wide_frege_to_PIC {F : CNF} {L : List Seq} (hL : FProof p F L)
    (hE : (([], []) : Seq) ∈ L) (hdeg : ∀ S ∈ L, XDegS p d S) (hvar : ∀ S ∈ L, VarS V S)
    (B : ℕ) (hB : ∀ S ∈ L, BS p d S ≤ B) :
    ∃ R : PRefutation F V d p, R.S ≤ L.length * (12 * (fW L + fW L) * (B * B)) := by
  have hM : ∀ S ∈ L, wS S ≤ fW L := fun S hS =>
    List.single_le_sum (by simp) _ (List.mem_map.2 ⟨S, hS, rfl⟩)
  obtain ⟨Ls, hD, hmem, hlen⟩ := xsim_all hL hdeg hvar (fW L) B hM hB L.length le_rfl
  rw [List.take_length] at hmem
  have he : (∅ : PLine p) ∈ Ls := by
    have := hmem _ hE ([], []) (mem_selsS.2 ⟨List.Forall₂.nil, List.Forall₂.nil⟩)
    rwa [trS_empty] at this
  obtain ⟨R, hR⟩ := der_refutation hD he
  exact ⟨R, hR.trans hlen⟩

/-! ## The fragment is larger than the one line fragment -/

/-- A sequent `⊢ AND(x_1, ..., x_w)` with `w > d ≥ 1` lies in the expanded fragment, has `w`
selections, and does not lie in the one line fragment `DegS`. -/
theorem wide_and_example (is : List ℕ) (hd : 1 ≤ d) (hw : d < is.length) :
    XDegS p d ([], [Fm.and (is.map Fm.var)]) ∧
      BS p d ([], [Fm.and (is.map Fm.var)]) = is.length ∧
      ¬ DegS p d ([], [Fm.and (is.map Fm.var)]) := by
  have hpd : pd p (.and (is.map Fm.var)) = is.length := by
    rw [pd_and, List.map_map]
    have : (pd p ∘ Fm.var) = fun _ => 1 := by funext i; simp [pd_var]
    rw [this]; simp
  refine ⟨⟨by simp, fun φ hφ => ?_⟩, ?_, fun h => ?_⟩
  · simp at hφ; subst hφ
    refine xtd_and_true_le _ fun ψ hψ => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hψ
    rw [xtd_var]; exact hd
  · rw [BS_eq]
    simp only [List.map_nil, List.prod_nil, List.map_cons, List.prod_cons, one_mul, mul_one]
    rw [sels_and_true, if_neg (by rw [hpd]; omega), List.length_flatten, List.map_map,
      List.map_map]
    rw [List.map_congr_left (g := fun _ => 1) (fun i _ => by simp [sels_var])]
    simp
  · have := h.2 (.and (is.map Fm.var)) (by simp)
    rw [td_and_true, hpd] at this
    omega

/-! ## The size bound on Tseitin formulas -/

open SATurday.ProofComplexity.TseitinPC in
/-- **AC0[p] Frege with expanded wide conjunctions, any depth, on one hot Tseitin mod `q`.**
Primes `p ∤ q`, `ε > 0` with `(κ+1) ε < 1`.  For every `M` there is a cubic graph on `n ≥ M`
vertices such that for every charge `b` and every `1 ≤ ρ ≤ ε ln n`: every refutation `L` in
`FProof`, of any formula depth, whose sequents use only variables of the formula, satisfy
`XDegS p ((p-1) ρ)` and have at most `B` selections each, has
`exp (n^(1 - (κ+1) ε)) ≤ |L| · 24 (fSize L + |L|) · B²`. -/
theorem wide_frege_tseitin (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (ε : ℝ) (hε : 0 < ε) (hεκ : (C1.kappa p q + 1) * ε < 1) (M : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), M ≤ n ∧ IsRegular G 3 ∧ ∀ b : Fin n → ZMod q,
      ∀ ρ : ℕ, 1 ≤ ρ → (ρ : ℝ) ≤ ε * Real.log n →
      ∀ (L : List Seq) (B : ℕ), FProof p (tcnf G q b) L → (([], []) : Seq) ∈ L →
        (∀ S ∈ L, VarS (tVars G q) S) → (∀ S ∈ L, XDegS p ((p - 1) * ρ) S) →
        (∀ S ∈ L, BS p ((p - 1) * ρ) S ≤ B) →
        Real.exp ((n : ℝ) ^ (1 - (C1.kappa p q + 1) * ε)) ≤
          ((L.length * (24 * (fSize L + L.length) * (B * B)) : ℕ) : ℝ) := by
  obtain ⟨n, G, hn, hreg, H⟩ := pic_main p hq hpq ε hε hεκ M
  refine ⟨n, G, hn, hreg, fun b ρ hρ1 hρ L B hL hE hvar hdeg hB => ?_⟩
  obtain ⟨R, hR⟩ := wide_frege_to_PIC (p := p) hL hE hdeg hvar B hB
  refine (H b ρ hρ1 hρ R).trans ?_
  have h3 : R.S ≤ L.length * (24 * (fSize L + L.length) * (B * B)) := by
    refine hR.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ?_))
    have := fW_le L
    omega
  exact_mod_cast h3

open SATurday.ProofComplexity.TseitinPC in
/-- **Indexed form with an explicit unsatisfiable family, for every formula depth `D`.**  There is
a threshold `m0` such that for every `m ≥ m0`, on the explicit cubic graph `cubFam m` with
`n = 8 m^2` vertices and the explicit charge `tseitinCharge1`: the formula is unsatisfiable, and for
every `ρ` with `q + 3 ≤ ρ ≤ ε ln n` the expanded fragment contains a refutation (non vacuity, at
depth one, with one selection per sequent) and every refutation `FRefutes p D` in the expanded
fragment with at most `B` selections per sequent, for every `D` and `B`, satisfies
`exp (n^(1 - (κ+1) ε)) ≤ |L| · 24 (fSize L + |L|) · B²`. -/
theorem wide_frege_tseitin_idx (p : ℕ) [Fact p.Prime] {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (ε : ℝ) (hε : 0 < ε) (hεκ : (C1.kappa p q + 1) * ε < 1) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
      ¬ Satisfiable (tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q)) ∧
      ∀ ρ : ℕ, q + 3 ≤ ρ → (ρ : ℝ) ≤ ε * Real.log (m * m * 8 : ℕ) →
        (∃ L, FRefutes p 1 (tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q)) L ∧
          (∀ S ∈ L, VarS (tVars (cubFam m) q) S) ∧ (∀ S ∈ L, XDegS p ((p - 1) * ρ) S) ∧
          (∀ S ∈ L, BS p ((p - 1) * ρ) S = 1)) ∧
        ∀ (D : ℕ) (L : List Seq) (B : ℕ),
          FRefutes p D (tcnf (cubFam m) q (tseitinCharge1 (m * m * 8) q)) L →
          (∀ S ∈ L, VarS (tVars (cubFam m) q) S) → (∀ S ∈ L, XDegS p ((p - 1) * ρ) S) →
          (∀ S ∈ L, BS p ((p - 1) * ρ) S ≤ B) →
          Real.exp (((m * m * 8 : ℕ) : ℝ) ^ (1 - (C1.kappa p q + 1) * ε)) ≤
            ((L.length * (24 * (fSize L + L.length) * (B * B)) : ℕ) : ℝ) := by
  obtain ⟨m1, H1⟩ := lowdeg_frege_tseitin_idx p hq hpq ε hε hεκ
  obtain ⟨m2, H2⟩ := pic_main_idx p hq hpq ε hε hεκ
  refine ⟨max m1 m2, fun m hm => ?_⟩
  obtain ⟨hunsat, Hρ⟩ := H1 m ((le_max_left _ _).trans hm)
  refine ⟨hunsat, fun ρ hρq hρ => ⟨?_, ?_⟩⟩
  · obtain ⟨⟨L, hL, hvar, hdeg⟩, -⟩ := Hρ ρ hρq hρ
    exact ⟨L, hL, hvar, fun S hS => xdegS_of_degS (hdeg S hS),
      fun S hS => BS_of_degS (hdeg S hS)⟩
  · intro D L B hL hvar hdeg hB
    obtain ⟨R, hR⟩ := wide_frege_to_PIC (p := p) hL.1 hL.2.2 hdeg hvar B hB
    refine (H2 m ((le_max_right _ _).trans hm) _ ρ (by omega) hρ R).trans ?_
    have h3 : R.S ≤ L.length * (24 * (fSize L + L.length) * (B * B)) := by
      refine hR.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ?_))
      have := fW_le L
      omega
    exact_mod_cast h3

end

end FWide
