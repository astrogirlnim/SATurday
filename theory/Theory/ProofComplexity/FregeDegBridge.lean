import Theory.ProofComplexity.PolyIndCalc
import Theory.ProofComplexity.FregeRankBridge

/-!
# Bridge: a low degree fragment of AC0[p] Frege, of any depth, into the calculus `PIC`

Every formula `φ` of `Fm` has a value polynomial `val p φ` over `F_p` (`AND` is a product, `OR` its
dual, `MOD_{p,r}` is `1 - (Σ - r)^(p-1)`) of syntactic degree `pd p φ`: fan ins of `AND`/`OR` add up,
a `MOD_p` gate multiplies the largest member degree by `p - 1` whatever its fan in.

A sequent is translated into a line of `PIC`: a formula in positive position that is an `OR` is split
into its members (recursively), dually for `AND` in negative position, and every other formula gives
one term, its value polynomial or the complement.  `td p s φ` is the largest syntactic degree of a
term of the translation of `φ` with sign `s`.

Main results:
* `FDeg.frege_to_PIC`: a refutation in the pinned sequent calculus `FProof` (no depth bound) in which
  every sequent has `td ≤ d` and variables in `V` yields a `PIC` refutation with indicators of degree
  `≤ d`, of size at most `|L| · 10 · 2W`, `W = fSize L + |L|`.
* `FDeg.lowdeg_frege_tseitin`, `FDeg.lowdeg_frege_tseitin_idx`: hence the size bound of
  `PIC.pic_main` for such refutations of one hot Tseitin mod `q`, `d = (p-1) ρ`, `ρ ≤ ε ln n`.
* `FDeg.degS_of_rankS`: the flat rank fragment of `FregeRankBridge.lean` is contained in this one.

This is a bound for a fragment.  It says nothing about formulas whose value polynomial has degree
above `(p-1) ε ln n` in a position where the translation does not split them, in particular about a
wide `AND` in positive position.

LOG: R4 ac0p fable session, low degree bridge for all depths
-/

open SATurday.ProofComplexity MvPolynomial PIC

namespace FDeg

set_option linter.unusedSectionVars false

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime] {Φ : CNF} {V : Finset ℕ} {d : ℕ}

/-! ## Induction on formulas and list lemmas -/

theorem Fm_ind {P : Fm → Prop} (hvar : ∀ i, P (.var i)) (hneg : ∀ φ, P φ → P (.neg φ))
    (hand : ∀ l, (∀ ψ ∈ l, P ψ) → P (.and l)) (hor : ∀ l, (∀ ψ ∈ l, P ψ) → P (.or l))
    (hmod : ∀ r l, (∀ ψ ∈ l, P ψ) → P (.mod r l)) : ∀ φ, P φ
  | .var i => hvar i
  | .neg φ => hneg φ (Fm_ind hvar hneg hand hor hmod φ)
  | .and l => hand l fun ψ _ => Fm_ind hvar hneg hand hor hmod ψ
  | .or l => hor l fun ψ _ => Fm_ind hvar hneg hand hor hmod ψ
  | .mod r l => hmod r l fun ψ _ => Fm_ind hvar hneg hand hor hmod ψ

theorem mem_foldr_union {α : Type} [DecidableEq α] (ls : List (Finset α)) (x : α) :
    x ∈ ls.foldr (· ∪ ·) ∅ ↔ ∃ s ∈ ls, x ∈ s := by
  induction ls with
  | nil => simp
  | cons s ls ih => simp [ih]

theorem le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := ih h
      simp only [List.foldr_cons]; omega

theorem foldr_max_le {l : List ℕ} {m : ℕ} (h : ∀ x ∈ l, x ≤ m) : l.foldr max 0 ≤ m := by
  induction l with
  | nil => simp
  | cons y l ih =>
    have h1 := h y (by simp)
    have h2 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.foldr_cons]; omega

theorem le_sum_of_mem {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := ih h
      simp only [List.sum_cons]; omega

/-! ## Value polynomial, syntactic degree, variables, translation -/

/-- The value polynomial of a formula. -/
def val (p : ℕ) [Fact p.Prime] : Fm → Pang.PP p
  | .var i => X i
  | .neg φ => 1 - val p φ
  | .and l => (l.attach.map fun ⟨ψ, _⟩ => val p ψ).prod
  | .or l => 1 - (l.attach.map fun ⟨ψ, _⟩ => 1 - val p ψ).prod
  | .mod r l => 1 - ((l.attach.map fun ⟨ψ, _⟩ => val p ψ).sum - C (r : ZMod p)) ^ (p - 1)

/-- Syntactic degree: `AND`/`OR` add the member degrees, `MOD_p` multiplies the largest by `p - 1`. -/
def pd (p : ℕ) : Fm → ℕ
  | .var _ => 1
  | .neg φ => pd p φ
  | .and l => (l.attach.map fun ⟨ψ, _⟩ => pd p ψ).sum
  | .or l => (l.attach.map fun ⟨ψ, _⟩ => pd p ψ).sum
  | .mod _ l => (p - 1) * (l.attach.map fun ⟨ψ, _⟩ => pd p ψ).foldr max 0

/-- Variables of a formula. -/
def fv : Fm → Finset ℕ
  | .var i => {i}
  | .neg φ => fv φ
  | .and l => (l.attach.map fun ⟨ψ, _⟩ => fv ψ).foldr (· ∪ ·) ∅
  | .or l => (l.attach.map fun ⟨ψ, _⟩ => fv ψ).foldr (· ∪ ·) ∅
  | .mod _ l => (l.attach.map fun ⟨ψ, _⟩ => fv ψ).foldr (· ∪ ·) ∅

/-- A polynomial or its complement. -/
def sg (s : Bool) (g : Pang.PP p) : Pang.PP p := if s then g else 1 - g

/-- Translation of a formula with a sign into a list of terms (their disjunction says "`φ` has
truth value `s`"). -/
def trL (p : ℕ) [Fact p.Prime] : Bool → Fm → List (Pang.PP p)
  | s, .var i => [sg s (X i)]
  | s, .neg φ => trL p (!s) φ
  | true, .and l => [val p (.and l)]
  | false, .and l => (l.attach.map fun ⟨ψ, _⟩ => trL p false ψ).flatten
  | true, .or l => (l.attach.map fun ⟨ψ, _⟩ => trL p true ψ).flatten
  | false, .or l => [1 - val p (.or l)]
  | s, .mod r l => [sg s (val p (.mod r l))]

/-- Largest syntactic degree of a term of `trL p s φ`. -/
def td (p : ℕ) : Bool → Fm → ℕ
  | _, .var _ => 1
  | s, .neg φ => td p (!s) φ
  | true, .and l => pd p (.and l)
  | false, .and l => (l.attach.map fun ⟨ψ, _⟩ => td p false ψ).foldr max 0
  | true, .or l => (l.attach.map fun ⟨ψ, _⟩ => td p true ψ).foldr max 0
  | false, .or l => pd p (.or l)
  | _, .mod r l => pd p (.mod r l)

/-! ### Unfolding lemmas -/

theorem val_var (i : ℕ) : val p (.var i) = X i := by rw [val]
theorem val_neg (φ : Fm) : val p (.neg φ) = 1 - val p φ := by rw [val]

theorem val_and (l : List Fm) : val p (.and l) = (l.map (val p)).prod := by
  rw [val]
  have := Fm.attach_map l (val p)
  simp only at this
  rw [this]

theorem val_or (l : List Fm) : val p (.or l) = 1 - (l.map fun ψ => 1 - val p ψ).prod := by
  rw [val]
  have := Fm.attach_map l (fun ψ => 1 - val p ψ)
  simp only at this
  rw [this]

theorem val_mod (r : ℕ) (l : List Fm) :
    val p (.mod r l) = 1 - ((l.map (val p)).sum - C (r : ZMod p)) ^ (p - 1) := by
  rw [val]
  have := Fm.attach_map l (val p)
  simp only at this
  rw [this]

theorem pd_var (i : ℕ) : pd p (.var i) = 1 := by rw [pd]
theorem pd_neg (φ : Fm) : pd p (.neg φ) = pd p φ := by rw [pd]

theorem pd_and (l : List Fm) : pd p (.and l) = (l.map (pd p)).sum := by
  rw [pd]
  have := Fm.attach_map l (pd p)
  simp only at this
  rw [this]

theorem pd_or (l : List Fm) : pd p (.or l) = (l.map (pd p)).sum := by
  rw [pd]
  have := Fm.attach_map l (pd p)
  simp only at this
  rw [this]

theorem pd_mod (r : ℕ) (l : List Fm) : pd p (.mod r l) = (p - 1) * (l.map (pd p)).foldr max 0 := by
  rw [pd]
  have := Fm.attach_map l (pd p)
  simp only at this
  rw [this]

theorem mem_fv_gate (l : List Fm) (v : ℕ) :
    v ∈ (l.attach.map fun x : {φ // φ ∈ l} => fv x.1).foldr (· ∪ ·) ∅ ↔ ∃ ψ ∈ l, v ∈ fv ψ := by
  rw [Fm.attach_map l fv, mem_foldr_union]
  simp

theorem fv_var (i : ℕ) : fv (.var i) = {i} := by rw [fv]
theorem fv_neg (φ : Fm) : fv (.neg φ) = fv φ := by rw [fv]

theorem mem_fv_and (l : List Fm) (v : ℕ) : v ∈ fv (.and l) ↔ ∃ ψ ∈ l, v ∈ fv ψ := by
  rw [fv]; exact mem_fv_gate l v

theorem mem_fv_or (l : List Fm) (v : ℕ) : v ∈ fv (.or l) ↔ ∃ ψ ∈ l, v ∈ fv ψ := by
  rw [fv]; exact mem_fv_gate l v

theorem mem_fv_mod (r : ℕ) (l : List Fm) (v : ℕ) : v ∈ fv (.mod r l) ↔ ∃ ψ ∈ l, v ∈ fv ψ := by
  rw [fv]; exact mem_fv_gate l v

theorem trL_var (s : Bool) (i : ℕ) : trL p s (.var i) = [sg s (X i)] := by rw [trL]
theorem trL_neg (s : Bool) (φ : Fm) : trL p s (.neg φ) = trL p (!s) φ := by rw [trL]
theorem trL_and_true (l : List Fm) : trL p true (.and l) = [val p (.and l)] := by rw [trL]
theorem trL_or_false (l : List Fm) : trL p false (.or l) = [1 - val p (.or l)] := by rw [trL]
theorem trL_mod (s : Bool) (r : ℕ) (l : List Fm) :
    trL p s (.mod r l) = [sg s (val p (.mod r l))] := by rw [trL]

theorem mem_trL_and_false (l : List Fm) (g : Pang.PP p) :
    g ∈ trL p false (.and l) ↔ ∃ ψ ∈ l, g ∈ trL p false ψ := by
  rw [trL]
  have := Fm.attach_map l (trL p false)
  simp only at this
  rw [this]
  simp [List.mem_flatten]

theorem mem_trL_or_true (l : List Fm) (g : Pang.PP p) :
    g ∈ trL p true (.or l) ↔ ∃ ψ ∈ l, g ∈ trL p true ψ := by
  rw [trL]
  have := Fm.attach_map l (trL p true)
  simp only at this
  rw [this]
  simp [List.mem_flatten]

theorem td_var (s : Bool) (i : ℕ) : td p s (.var i) = 1 := by rw [td]
theorem td_neg (s : Bool) (φ : Fm) : td p s (.neg φ) = td p (!s) φ := by rw [td]
theorem td_and_true (l : List Fm) : td p true (.and l) = pd p (.and l) := by rw [td]
theorem td_or_false (l : List Fm) : td p false (.or l) = pd p (.or l) := by rw [td]
theorem td_mod (s : Bool) (r : ℕ) (l : List Fm) : td p s (.mod r l) = pd p (.mod r l) := by rw [td]

theorem td_and_false (l : List Fm) : td p false (.and l) = (l.map (td p false)).foldr max 0 := by
  rw [td]
  have := Fm.attach_map l (td p false)
  simp only at this
  rw [this]

theorem td_or_true (l : List Fm) : td p true (.or l) = (l.map (td p true)).foldr max 0 := by
  rw [td]
  have := Fm.attach_map l (td p true)
  simp only at this
  rw [this]

/-! ## Semantics of the value polynomial -/

/-- Truth value as an element of `F_p`. -/
def tv (p : ℕ) (a : Assignment) (φ : Fm) : ZMod p := if φ.eval p a = true then 1 else 0

theorem prod_ite {R : Type} [CommRing R] (l : List Fm) (f : Fm → R) (b : Fm → Prop)
    (h : ∀ ψ ∈ l, f ψ = if b ψ then 1 else 0) :
    (l.map f).prod = if (∀ ψ ∈ l, b ψ) then 1 else 0 := by
  induction l with
  | nil => simp
  | cons φ l ih =>
    rw [List.map_cons, List.prod_cons, ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ),
      h φ (by simp)]
    by_cases h1 : b φ <;> by_cases h2 : ∀ ψ ∈ l, b ψ <;> simp [h1, h2]

theorem sum_cnt (a : Assignment) (l : List Fm) (f : Fm → ZMod p)
    (h : ∀ ψ ∈ l, f ψ = tv p a ψ) : (l.map f).sum = (Fm.cnt p a l : ZMod p) := by
  induction l with
  | nil => simp [Fm.cnt_nil]
  | cons φ l ih =>
    rw [List.map_cons, List.sum_cons, ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ),
      h φ (by simp), Fm.cnt_cons]
    unfold tv
    split_ifs <;> push_cast <;> ring

theorem pow_ind (x : ZMod p) : 1 - x ^ (p - 1) = if x = 0 then 1 else 0 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  by_cases hx : x = 0
  · rw [if_pos hx, hx, zero_pow (by omega)]; simp
  · rw [if_neg hx, ZMod.pow_card_sub_one_eq_one hx]; simp

theorem eval_val (a : Assignment) : ∀ φ : Fm,
    eval (boolPt (F := ZMod p) a) (val p φ) = tv p a φ := by
  refine Fm_ind ?_ ?_ ?_ ?_ ?_
  · intro i
    rw [val_var, eval_X]; unfold tv boolPt; rw [Fm.eval]
  · intro φ ih
    rw [val_neg, map_sub, map_one, ih]; unfold tv
    rw [Fm.eval]
    cases Fm.eval p a φ <;> simp
  · intro l ih
    rw [val_and, map_list_prod, List.map_map,
      prod_ite l _ (fun ψ => ψ.eval p a = true) (fun ψ hψ => by
        simp only [Function.comp]; rw [ih ψ hψ]; unfold tv; split_ifs <;> rfl)]
    unfold tv
    by_cases h : ∀ ψ ∈ l, Fm.eval p a ψ = true
    · rw [if_pos h, if_pos (Fm.eval_and.2 h)]
    · rw [if_neg h, if_neg (fun h' => h (Fm.eval_and.1 h'))]
  · intro l ih
    rw [val_or, map_sub, map_one, map_list_prod, List.map_map,
      prod_ite l _ (fun ψ => ¬ ψ.eval p a = true) (fun ψ hψ => by
        simp only [Function.comp]; rw [map_sub, map_one, ih ψ hψ]; unfold tv
        split_ifs <;> simp)]
    unfold tv
    simp only [Fm.eval_or]
    by_cases h : ∃ φ ∈ l, Fm.eval p a φ = true
    · rw [if_pos h, if_neg (by push Not; exact h)]; simp
    · rw [if_neg h, if_pos (by push Not at h; exact fun ψ hψ => by simp [h ψ hψ])]; simp
  · intro r l ih
    rw [val_mod, map_sub, map_one, map_pow, map_sub, map_list_sum, List.map_map,
      sum_cnt a l _ (fun ψ hψ => by simp only [Function.comp]; exact ih ψ hψ), eval_C, pow_ind]
    unfold tv
    simp only [Fm.eval_mod]
    have e : ((Fm.cnt p a l : ZMod p) - (r : ZMod p) = 0) ↔ Fm.cnt p a l % p = r % p := by
      rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff]; rfl
    simp only [e]

theorem sg_not_one_sub (s : Bool) (v : Pang.PP p) : sg (!s) (1 - v) = sg s v := by
  cases s <;> simp [sg]

theorem eval_sg_val (a : Assignment) (s : Bool) (φ : Fm) :
    eval (boolPt (F := ZMod p) a) (sg s (val p φ)) = if φ.eval p a = s then 1 else 0 := by
  cases s
  · simp only [sg, Bool.false_eq_true, if_false, map_sub, map_one, eval_val]; unfold tv
    cases Fm.eval p a φ <;> simp
  · simp only [sg, if_true, eval_val]; unfold tv; rfl

/-! ## Degree and variables of the value polynomial -/

theorem deg_list_prod (l : List Fm) (f : Fm → Pang.PP p) (g : Fm → ℕ)
    (h : ∀ ψ ∈ l, (f ψ).totalDegree ≤ g ψ) : ((l.map f).prod).totalDegree ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons φ l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons]
    exact (totalDegree_mul _ _).trans (Nat.add_le_add (h φ (by simp))
      (ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)))

theorem deg_list_sum (l : List Fm) (f : Fm → Pang.PP p) (g : Fm → ℕ)
    (h : ∀ ψ ∈ l, (f ψ).totalDegree ≤ g ψ) :
    ((l.map f).sum).totalDegree ≤ (l.map g).foldr max 0 := by
  induction l with
  | nil => simp
  | cons φ l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.foldr_cons]
    exact (totalDegree_add _ _).trans (max_le_max (h φ (by simp))
      (ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)))

theorem deg_one_sub (g : Pang.PP p) : (1 - g).totalDegree ≤ g.totalDegree :=
  (totalDegree_sub _ _).trans (max_le (by simp) le_rfl)

theorem deg_val : ∀ φ : Fm, (val p φ).totalDegree ≤ pd p φ := by
  refine Fm_ind ?_ ?_ ?_ ?_ ?_
  · intro i; rw [val_var, pd_var]; exact (totalDegree_X _).le
  · intro φ ih; rw [val_neg, pd_neg]; exact (deg_one_sub _).trans ih
  · intro l ih; rw [val_and, pd_and]; exact deg_list_prod l _ _ ih
  · intro l ih
    rw [val_or, pd_or]
    exact (deg_one_sub _).trans (deg_list_prod l _ _ fun ψ hψ => (deg_one_sub _).trans (ih ψ hψ))
  · intro r l ih
    rw [val_mod, pd_mod]
    refine (deg_one_sub _).trans ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ ?_))
    refine (totalDegree_sub _ _).trans (max_le (deg_list_sum l _ _ ih) ?_)
    rw [totalDegree_C]; exact Nat.zero_le _

theorem vars_one_sub (g : Pang.PP p) : (1 - g).vars ⊆ g.vars := by
  intro v hv
  have h := (vars_sub_subset ..) hv
  rcases Finset.mem_union.1 h with h | h
  · simp at h
  · exact h

theorem vars_list_prod (l : List Fm) (f : Fm → Pang.PP p) (v : ℕ)
    (hv : v ∈ ((l.map f).prod).vars) : ∃ ψ ∈ l, v ∈ (f ψ).vars := by
  induction l with
  | nil => simp at hv
  | cons φ l ih =>
    rw [List.map_cons, List.prod_cons] at hv
    rcases Finset.mem_union.1 (vars_mul _ _ hv) with h | h
    · exact ⟨φ, by simp, h⟩
    · obtain ⟨ψ, hψ, h'⟩ := ih h
      exact ⟨ψ, List.mem_cons_of_mem _ hψ, h'⟩

theorem vars_list_sum (l : List Fm) (f : Fm → Pang.PP p) (v : ℕ)
    (hv : v ∈ ((l.map f).sum).vars) : ∃ ψ ∈ l, v ∈ (f ψ).vars := by
  induction l with
  | nil => simp at hv
  | cons φ l ih =>
    rw [List.map_cons, List.sum_cons] at hv
    rcases Finset.mem_union.1 (vars_add_subset _ _ hv) with h | h
    · exact ⟨φ, by simp, h⟩
    · obtain ⟨ψ, hψ, h'⟩ := ih h
      exact ⟨ψ, List.mem_cons_of_mem _ hψ, h'⟩

theorem vars_val : ∀ φ : Fm, ∀ v ∈ (val p φ).vars, v ∈ fv φ := by
  refine Fm_ind ?_ ?_ ?_ ?_ ?_
  · intro i v hv; rw [val_var, vars_X] at hv; rw [fv_var]; exact hv
  · intro φ ih v hv; rw [val_neg] at hv; rw [fv_neg]; exact ih v (vars_one_sub _ hv)
  · intro l ih v hv
    rw [val_and] at hv
    obtain ⟨ψ, hψ, h⟩ := vars_list_prod l _ v hv
    exact (mem_fv_and l v).2 ⟨ψ, hψ, ih ψ hψ v h⟩
  · intro l ih v hv
    rw [val_or] at hv
    obtain ⟨ψ, hψ, h⟩ := vars_list_prod l _ v (vars_one_sub _ hv)
    exact (mem_fv_or l v).2 ⟨ψ, hψ, ih ψ hψ v (vars_one_sub _ h)⟩
  · intro r l ih v hv
    rw [val_mod] at hv
    have h1 := vars_pow _ _ (vars_one_sub _ hv)
    rcases Finset.mem_union.1 ((vars_sub_subset ..) h1) with h | h
    · obtain ⟨ψ, hψ, h'⟩ := vars_list_sum l _ v h
      exact (mem_fv_mod r l v).2 ⟨ψ, hψ, ih ψ hψ v h'⟩
    · rw [vars_C] at h; exact absurd h (Finset.notMem_empty _)

/-- `sg s (val p φ)` is an indicator of degree `pd p φ` over `fv φ`. -/
theorem ind_sg {φ : Fm} (hd : pd p φ ≤ d) (hV : fv φ ⊆ V) (s : Bool) :
    Ind V d (sg s (val p φ)) := by
  refine ⟨fun a => ?_, ?_, ?_⟩
  · rw [eval_sg_val]; split_ifs <;> simp
  · cases s
    · exact ((deg_one_sub _).trans (deg_val φ)).trans hd
    · exact (deg_val φ).trans hd
  · intro v hv
    cases s
    · exact hV (vars_val φ v (vars_one_sub _ hv))
    · exact hV (vars_val φ v hv)

end

end FDeg
