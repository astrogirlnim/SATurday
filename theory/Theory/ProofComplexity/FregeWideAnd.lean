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
def SelL (p d : ℕ) (s : Bool) (l' l : List Fm) : Prop :=
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

end

end FWide
