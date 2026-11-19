import Theory.ProofComplexity.AC0pFrege

/-!
# MOD-gate arithmetic in the pinned AC0[p] Frege calculus `FStep`

Referee leftover (dossier Section 17): simulating Pang's `Res(lin F_p)` in `FRefutes p 2` needs
MOD-gate arithmetic (additivity, residue change, deletion of `p` copies, scaling) derived from
the cons-wise `MOD_p` defining axioms of `FStep`.  This file shows that, with the axioms as they
are pinned, none of these is derivable, and why.

The residue `r` of `Fm.mod r l` is a natural number and the axioms never reduce it modulo `p`
(axiom `([.mod r (φ :: l), φ], [.mod (r + p - 1) l])` and its converse shift it by `p - 1`;
`⊢ mod 0 []` and `mod r [] ⊢` for `r % p ≠ 0` are the only base axioms).  Following the axioms
along `l`, `mod r l` is tied to `mod (r + (p - 1) * #true(l)) []`, and nothing fixes the truth of
`mod n []` for a nonzero multiple `n` of `p`.  So for every set `G ⊆ pℕ` with `0 ∈ G` the
evaluation `evalG` that reads `mod r l` as `r + (p - 1) * #true(l) ∈ G` is a model of every rule
of `FStep` (`fstep_sound_G`, `fproof_sound_G`).  The standard semantics is `G = pℕ`.

Consequences (all for `2 ≤ p`, any CNF `F` satisfied by an assignment with `x_i` true; each
listed sequent is a tautology of the standard semantics, `valid_*`, yet is a line of no `FProof`):
* `nd_mod_p_nil`: `⊢ mod p []` (residue change);
* `nd_true_arg`: `⊢ mod r (x_i :: l)` for every `r`, `l`: no `MOD` gate with a true argument is ever
  derivable in the succedent from such an `F`;
* `nd_add`: additivity, `mod 0 X ⊢ mod 0 (X ++ X)` with `X` = `p` copies of `x_i`;
* `nd_delete`: deletion of `p` copies, `mod 1 (X ++ [x_i]) ⊢ mod 1 [x_i]`;
* `nd_insert`: insertion of `p` copies, `⊢ mod 0 X`;
* `nd_scale`: scaling by 2, `mod 1 [x_i] ⊢ mod 2 [x_i, x_i]`.
Permutation invariance is consistent with every `G` model (the quantity `r + (p - 1) * #true(l)`
is symmetric in `l`) and is derived in the second part of the file.
-/

namespace SATurday.ProofComplexity

namespace FModArith

open Fm

/-! ## The `G` models -/

/-- Evaluation in which `mod r l` means `r + (p - 1) * #true(l) ∈ G` (`g` is the indicator of `G`). -/
def evalG (p : ℕ) (g : ℕ → Bool) (a : Assignment) : Fm → Bool
  | .var i => a i
  | .neg φ => !(evalG p g a φ)
  | .and l => (l.attach.map fun ⟨φ, _⟩ => evalG p g a φ).all id
  | .or l => (l.attach.map fun ⟨φ, _⟩ => evalG p g a φ).any id
  | .mod r l => g (r + (p - 1) * (l.attach.map fun ⟨φ, _⟩ => evalG p g a φ).count true)

/-- Number of members true in the `G` model. -/
def cntG (p : ℕ) (g : ℕ → Bool) (a : Assignment) (l : List Fm) : ℕ :=
  (l.map (evalG p g a)).count true

variable {p : ℕ} {g : ℕ → Bool} {a : Assignment}

theorem evalG_and {l : List Fm} :
    evalG p g a (.and l) = true ↔ ∀ φ ∈ l, evalG p g a φ = true := by
  rw [evalG]
  have := attach_map l (evalG p g a)
  simp only at this
  rw [this]; simp

theorem evalG_or {l : List Fm} :
    evalG p g a (.or l) = true ↔ ∃ φ ∈ l, evalG p g a φ = true := by
  rw [evalG]
  have := attach_map l (evalG p g a)
  simp only at this
  rw [this]; simp

theorem evalG_neg {φ : Fm} : evalG p g a (.neg φ) = true ↔ evalG p g a φ = false := by
  rw [evalG]; simp

theorem evalG_mod {r : ℕ} {l : List Fm} :
    evalG p g a (.mod r l) = g (r + (p - 1) * cntG p g a l) := by
  rw [evalG]
  have := attach_map l (evalG p g a)
  simp only at this
  rw [this]; rfl

theorem cntG_nil : cntG p g a [] = 0 := rfl

theorem cntG_cons {φ : Fm} {l : List Fm} :
    cntG p g a (φ :: l) = cntG p g a l + (if evalG p g a φ = true then 1 else 0) := by
  unfold cntG
  rw [List.map_cons, List.count_cons]
  split_ifs <;> simp_all

theorem cntG_append {l l' : List Fm} : cntG p g a (l ++ l') = cntG p g a l + cntG p g a l' := by
  unfold cntG; rw [List.map_append, List.count_append]

theorem cntG_replicate {φ : Fm} (n : ℕ) (h : evalG p g a φ = true) :
    cntG p g a (List.replicate n φ) = n := by
  unfold cntG; rw [List.map_replicate, h, List.count_replicate_self]

/-- Sequent satisfaction in the `G` model. -/
def SeqSatG (p : ℕ) (g : ℕ → Bool) (a : Assignment) (S : Seq) : Prop :=
  (∀ φ ∈ S.1, evalG p g a φ = true) → ∃ ψ ∈ S.2, evalG p g a ψ = true

theorem evalG_litFm {l : Literal} : evalG p g a (litFm l) = true ↔ litSat a l := by
  unfold litFm litSat
  cases hl : l.pos
  · simp [evalG]
  · simp [evalG]

theorem evalG_clauseFm {C : Clause} (h : clauseSat a C) : evalG p g a (clauseFm C) = true := by
  obtain ⟨l, hl, hs⟩ := h
  unfold clauseFm
  rw [evalG_or]
  exact ⟨litFm l, List.mem_map.2 ⟨l, Finset.mem_toList.2 hl, rfl⟩, evalG_litFm.2 hs⟩

/-- A `G` model: `0 ∈ G ⊆ pℕ`. -/
structure GoodG (p : ℕ) (g : ℕ → Bool) : Prop where
  zero : g 0 = true
  dvd : ∀ n, g n = true → n % p = 0

theorem shift_eq (hp : 0 < p) (r c : ℕ) :
    r + (p - 1) * (c + 1) = r + p - 1 + (p - 1) * c := by
  rw [Nat.mul_succ]; omega

/-- Every rule of `FStep` is sound in every `G` model. -/
theorem fstep_sound_G (hp : 0 < p) (hg : GoodG p g) {F : CNF} (ha : cnfSat a F)
    {prev : List Seq} (hprev : ∀ T ∈ prev, SeqSatG p g a T) {S : Seq} (h : FStep p F prev S) :
    SeqSatG p g a S := by
  rcases h with ⟨C, hC, rfl⟩ | ⟨φ, rfl⟩ | rfl | rfl | rfl | ⟨r, hr, rfl⟩ | ⟨r, φ, l, rfl⟩ |
      ⟨r, φ, l, rfl⟩ | ⟨r, φ, l, rfl⟩ | ⟨r, φ, l, rfl⟩ | ⟨T, hT, h1, h2⟩ | ⟨φ, h1, h2⟩ |
      ⟨φ, Γ, Δ, rfl, h1⟩ | ⟨φ, Γ, Δ, rfl, h1⟩ | ⟨l, Γ, Δ, φ, hφ, rfl, h1⟩ | ⟨l, Γ, Δ, rfl, h1⟩ |
      ⟨l, Γ, Δ, rfl, h1⟩ | ⟨l, Γ, Δ, φ, hφ, rfl, h1⟩
  · intro _; exact ⟨_, List.mem_singleton_self _, evalG_clauseFm (ha C hC)⟩
  · intro h; exact ⟨φ, List.mem_singleton_self _, h φ (List.mem_singleton_self _)⟩
  · intro _; exact ⟨_, List.mem_singleton_self _, evalG_and.2 (by simp)⟩
  · intro h
    have := h _ (List.mem_singleton_self _)
    rw [evalG_or] at this; simp at this
  · intro _
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rw [evalG_mod, cntG_nil]; simpa using hg.zero
  · intro h
    have := h _ (List.mem_singleton_self _)
    rw [evalG_mod, cntG_nil] at this
    exact absurd (hg.dvd _ (by simpa using this)) (by simpa using hr)
  · intro h
    have h1 := h (.mod r (φ :: l)) (by simp)
    have h2 := h φ (by simp)
    rw [evalG_mod, cntG_cons, if_pos h2, shift_eq hp] at h1
    exact ⟨_, List.mem_singleton_self _, by rw [evalG_mod]; exact h1⟩
  · intro h
    have h1 := h (.mod r (φ :: l)) (by simp)
    by_cases hφ : evalG p g a φ = true
    · exact ⟨φ, by simp, hφ⟩
    · rw [evalG_mod, cntG_cons, if_neg hφ, add_zero] at h1
      exact ⟨.mod r l, by simp, by rw [evalG_mod]; exact h1⟩
  · intro h
    have h1 := h (.mod (r + p - 1) l) (by simp)
    have h2 := h φ (by simp)
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rw [evalG_mod, cntG_cons, if_pos h2, shift_eq hp]
    rw [evalG_mod] at h1; exact h1
  · intro h
    have h1 := h (.mod r l) (by simp)
    by_cases hφ : evalG p g a φ = true
    · exact ⟨φ, by simp, hφ⟩
    · refine ⟨.mod r (φ :: l), by simp, ?_⟩
      rw [evalG_mod, cntG_cons, if_neg hφ, add_zero]; rw [evalG_mod] at h1; exact h1
  · intro h
    obtain ⟨ψ, hψ, hv⟩ := hprev T hT (fun φ hφ => h φ (h1 hφ))
    exact ⟨ψ, h2 hψ, hv⟩
  · intro h
    by_cases hφ : evalG p g a φ = true
    · exact hprev _ h2 (fun ψ hψ => by
        rcases List.mem_cons.1 hψ with rfl | hψ
        · exact hφ
        · exact h ψ hψ)
    · obtain ⟨ψ, hψ, hv⟩ := hprev _ h1 h
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact absurd hv hφ
      · exact ⟨ψ, hψ, hv⟩
  · intro h
    have hn := evalG_neg.1 (h (.neg φ) (by simp))
    obtain ⟨ψ, hψ, hv⟩ := hprev _ h1 (fun ψ hψ => h ψ (by simp [hψ]))
    rcases List.mem_cons.1 hψ with rfl | hψ
    · rw [hn] at hv; cases hv
    · exact ⟨ψ, hψ, hv⟩
  · intro h
    by_cases hφ : evalG p g a φ = true
    · obtain ⟨ψ, hψ, hv⟩ := hprev _ h1 (fun ψ hψ => by
        rcases List.mem_cons.1 hψ with rfl | hψ
        · exact hφ
        · exact h ψ hψ)
      exact ⟨ψ, by simp [hψ], hv⟩
    · exact ⟨.neg φ, by simp, evalG_neg.2 (by simpa using hφ)⟩
  · intro h
    have hand := evalG_and.1 (h (.and l) (by simp))
    obtain ⟨ψ, hψ, hv⟩ := hprev _ h1 (fun ψ hψ => by
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact hand ψ hφ
      · exact h ψ (by simp [hψ]))
    exact ⟨ψ, hψ, hv⟩
  · intro h
    by_contra hno
    push Not at hno
    apply hno (.and l) (List.mem_cons_self ..)
    rw [evalG_and]
    intro φ hφ
    obtain ⟨ψ, hψ, hv⟩ := hprev _ (h1 φ hφ) h
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact hv
    · exact absurd hv (by have := hno ψ (by simp [hψ]); simpa using this)
  · intro h
    obtain ⟨φ, hφ, hv⟩ := evalG_or.1 (h (.or l) (by simp))
    exact hprev _ (h1 φ hφ) (fun ψ hψ => by
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact hv
      · exact h ψ (by simp [hψ]))
  · intro h
    obtain ⟨ψ, hψ, hv⟩ := hprev _ h1 h
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact ⟨.or l, by simp, evalG_or.2 ⟨ψ, hφ, hv⟩⟩
    · exact ⟨ψ, by simp [hψ], hv⟩

/-- Every line of an `FProof` holds in every `G` model of an assignment satisfying `F`. -/
theorem fproof_sound_G (hp : 0 < p) (hg : GoodG p g) {F : CNF} (ha : cnfSat a F)
    {L : List Seq} (hL : FProof p F L) : ∀ S ∈ L, SeqSatG p g a S := by
  have key : ∀ k ≤ L.length, ∀ S ∈ L.take k, SeqSatG p g a S := by
    intro k
    induction k with
    | zero => intro _ S hS; simp at hS
    | succ k ih =>
        intro hk S hS
        rw [List.take_add_one] at hS
        rcases List.mem_append.1 hS with h | h
        · exact ih (by omega) S h
        · have hk' : k < L.length := by omega
          rw [List.getElem?_eq_getElem hk'] at h
          simp only [Option.toList_some, List.mem_singleton] at h
          subst h
          exact fstep_sound_G hp hg ha (ih (by omega)) (hL k hk')
  intro S hS
  exact key L.length le_rfl S (by rwa [List.take_length])

/-- A sequent false in some `G` model of a satisfying assignment of `F` is a line of no proof. -/
theorem not_mem_of_G (hp : 0 < p) (hg : GoodG p g) {F : CNF} (ha : cnfSat a F) {S : Seq}
    (hS : ¬ SeqSatG p g a S) {L : List Seq} (hL : FProof p F L) : S ∉ L :=
  fun hm => hS (fproof_sound_G hp hg ha hL S hm)

/-! ## The counterexamples -/

/-- `G = {0}`. -/
def g0 : ℕ → Bool := fun n => n == 0

/-- `G = {0, m}`. -/
def g2 (m : ℕ) : ℕ → Bool := fun n => n == 0 || n == m

theorem good_g0 : GoodG p g0 :=
  ⟨rfl, fun n h => by simp only [g0, beq_iff_eq] at h; simp [h]⟩

theorem good_g2 {m : ℕ} (hm : m % p = 0) : GoodG p (g2 m) :=
  ⟨by simp [g2], fun n h => by
    simp only [g2, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | rfl
    · simp
    · exact hm⟩

/-- Validity in the standard semantics. -/
def Valid (p : ℕ) (S : Seq) : Prop := ∀ a, SeqSat p a S

theorem not_satG_nil {ψ : Fm} (h : evalG p g a ψ = false) : ¬ SeqSatG p g a ([], [ψ]) := by
  intro hS
  obtain ⟨ψ', hψ', hv⟩ := hS (by simp)
  rw [List.mem_singleton] at hψ'; subst hψ'
  rw [h] at hv; cases hv

theorem not_satG_one {φ ψ : Fm} (h1 : evalG p g a φ = true) (h2 : evalG p g a ψ = false) :
    ¬ SeqSatG p g a ([φ], [ψ]) := by
  intro hS
  obtain ⟨ψ', hψ', hv⟩ := hS (by simpa using h1)
  rw [List.mem_singleton] at hψ'; subst hψ'
  rw [h2] at hv; cases hv

theorem cnt_append' {l l' : List Fm} : Fm.cnt p a (l ++ l') = Fm.cnt p a l + Fm.cnt p a l' := by
  unfold Fm.cnt; rw [List.map_append, List.count_append]

theorem cnt_replicate (n : ℕ) (φ : Fm) :
    Fm.cnt p a (List.replicate n φ) = n * (if φ.eval p a = true then 1 else 0) := by
  induction n with
  | zero => simp [Fm.cnt_nil]
  | succ n ih => rw [List.replicate_succ, Fm.cnt_cons, ih, Nat.succ_mul]

/-- `p` copies of the variable `x_i`. -/
def reps (p i : ℕ) : List Fm := List.replicate p (.var i)

theorem evalG_var {i : ℕ} : evalG p g a (.var i) = a i := by rw [evalG]

/-- `⊢ MOD_{p,p}()` is a tautology. -/
theorem valid_mod_p_nil : Valid p (([], [.mod p []]) : Seq) := by
  intro a _
  exact ⟨_, List.mem_singleton_self _, Fm.eval_mod.2 (by simp [Fm.cnt_nil])⟩

/-- Residue change is not derivable: `⊢ MOD_{p,p}()` is a line of no proof. -/
theorem nd_mod_p_nil (hp : 2 ≤ p) {F : CNF} {a : Assignment} (ha : cnfSat a F) {L : List Seq}
    (hL : FProof p F L) : (([], [.mod p []]) : Seq) ∉ L := by
  refine not_mem_of_G (g := g0) (by omega) good_g0 ha (not_satG_nil ?_) hL
  rw [evalG_mod, cntG_nil]; simp [g0]; omega

/-- No `MOD` gate with a true argument is derivable: if `F` has a satisfying assignment with
`x_i` true, then `⊢ MOD_{p,r}(x_i, l)` is a line of no proof from `F`, for every `r` and `l`
(although, for instance, `F ⊨ MOD_{p,1}(x_i)` whenever `F ⊨ x_i`). -/
theorem nd_true_arg (hp : 2 ≤ p) {F : CNF} {a : Assignment} {i : ℕ} (ha : cnfSat a F)
    (hi : a i = true) (r : ℕ) (l : List Fm) {L : List Seq} (hL : FProof p F L) :
    (([], [.mod r (.var i :: l)]) : Seq) ∉ L := by
  refine not_mem_of_G (g := g0) (by omega) good_g0 ha (not_satG_nil ?_) hL
  rw [evalG_mod, cntG_cons, evalG_var, if_pos hi, Nat.mul_succ]
  simp only [g0, beq_eq_false_iff_ne]; omega

/-- Additivity `MOD_{p,0}(X) ⊢ MOD_{p,0}(X ++ X)` is a tautology. -/
theorem valid_add (i : ℕ) : Valid p (([.mod 0 (reps p i)], [.mod 0 (reps p i ++ reps p i)]) : Seq) := by
  intro a h
  have h1 := Fm.eval_mod.1 (h _ (List.mem_singleton_self _))
  refine ⟨_, List.mem_singleton_self _, Fm.eval_mod.2 ?_⟩
  rw [cnt_append', Nat.add_mod, h1]; simp

/-- Additivity is not derivable: with `X` the list of `p` copies of `x_i` (true in a satisfying
assignment of `F`), `MOD_{p,0}(X) ⊢ MOD_{p,0}(X ++ X)` is a line of no proof from `F`. -/
theorem nd_add (hp : 2 ≤ p) {F : CNF} {a : Assignment} {i : ℕ} (ha : cnfSat a F)
    (hi : a i = true) {L : List Seq} (hL : FProof p F L) :
    (([.mod 0 (reps p i)], [.mod 0 (reps p i ++ reps p i)]) : Seq) ∉ L := by
  have hm : ((p - 1) * p) % p = 0 := Nat.mul_mod_left _ _
  have hx : evalG p (g2 ((p - 1) * p)) a (.var i) = true := by
    rw [evalG_var]; exact hi
  refine not_mem_of_G (by omega) (good_g2 hm) ha (not_satG_one ?_ ?_) hL
  · rw [evalG_mod, reps, cntG_replicate _ hx]; simp [g2]
  · rw [evalG_mod, reps, cntG_append, cntG_replicate _ hx]
    have h1 : 0 < (p - 1) * p := Nat.mul_pos (by omega) (by omega)
    have h2 : (p - 1) * (p + p) = 2 * ((p - 1) * p) := by ring
    simp only [g2, zero_add, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    omega

/-- Deletion of `p` copies `MOD_{p,1}(X ++ [x_i]) ⊢ MOD_{p,1}(x_i)` is a tautology. -/
theorem valid_delete (i : ℕ) :
    Valid p (([.mod 1 (reps p i ++ [.var i])], [.mod 1 [.var i]]) : Seq) := by
  intro a h
  have h1 := Fm.eval_mod.1 (h _ (List.mem_singleton_self _))
  refine ⟨_, List.mem_singleton_self _, Fm.eval_mod.2 ?_⟩
  rw [cnt_append', reps, cnt_replicate] at h1
  rw [← h1, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]

/-- Deletion of `p` copies is not derivable. -/
theorem nd_delete (hp : 2 ≤ p) {F : CNF} {a : Assignment} {i : ℕ} (ha : cnfSat a F)
    (hi : a i = true) {L : List Seq} (hL : FProof p F L) :
    (([.mod 1 (reps p i ++ [.var i])], [.mod 1 [.var i]]) : Seq) ∉ L := by
  have hm : (p * p) % p = 0 := Nat.mul_mod_left _ _
  have hx : evalG p (g2 (p * p)) a (.var i) = true := by
    rw [evalG_var]; exact hi
  refine not_mem_of_G (by omega) (good_g2 hm) ha (not_satG_one ?_ ?_) hL
  · rw [evalG_mod, reps, cntG_append, cntG_replicate _ hx, cntG_cons, cntG_nil, if_pos hx]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [g2, Bool.or_eq_true, beq_iff_eq, Nat.add_sub_cancel]
    right; ring
  · rw [evalG_mod, cntG_cons, cntG_nil, if_pos hx]
    have h1 : p < p * p := by nlinarith
    simp only [g2, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    omega

/-- Insertion of `p` copies, `⊢ MOD_{p,0}(X)`, is a tautology. -/
theorem valid_insert (i : ℕ) : Valid p (([], [.mod 0 (reps p i)]) : Seq) := by
  intro a _
  refine ⟨_, List.mem_singleton_self _, Fm.eval_mod.2 ?_⟩
  rw [reps, cnt_replicate, Nat.mul_mod_right]; simp

/-- Insertion of `p` copies is not derivable. -/
theorem nd_insert (hp : 2 ≤ p) {F : CNF} {a : Assignment} {i : ℕ} (ha : cnfSat a F)
    (hi : a i = true) {L : List Seq} (hL : FProof p F L) :
    (([], [.mod 0 (reps p i)]) : Seq) ∉ L := by
  have hx : evalG p g0 a (.var i) = true := by
    rw [evalG_var]; exact hi
  refine not_mem_of_G (by omega) good_g0 ha (not_satG_nil ?_) hL
  rw [evalG_mod, reps, cntG_replicate _ hx]
  have h1 : 0 < (p - 1) * p := Nat.mul_pos (by omega) (by omega)
  simp only [g0, zero_add, beq_eq_false_iff_ne]; omega

/-- Scaling by `2`, `MOD_{p,1}(x_i) ⊢ MOD_{p,2}(x_i, x_i)`, is a tautology for `p ≥ 2`. -/
theorem valid_scale (hp : 2 ≤ p) (i : ℕ) :
    Valid p (([.mod 1 [.var i]], [.mod 2 [.var i, .var i]]) : Seq) := by
  intro a h
  have h1 := Fm.eval_mod.1 (h _ (List.mem_singleton_self _))
  refine ⟨_, List.mem_singleton_self _, Fm.eval_mod.2 ?_⟩
  simp only [Fm.cnt_cons, Fm.cnt_nil] at h1 ⊢
  split_ifs at h1 ⊢
  · rfl
  · rw [Nat.mod_eq_of_lt (by omega : 1 < p)] at h1; simp at h1

/-- Scaling is not derivable. -/
theorem nd_scale (hp : 2 ≤ p) {F : CNF} {a : Assignment} {i : ℕ} (ha : cnfSat a F)
    (hi : a i = true) {L : List Seq} (hL : FProof p F L) :
    (([.mod 1 [.var i]], [.mod 2 [.var i, .var i]]) : Seq) ∉ L := by
  have hm : p % p = 0 := Nat.mod_self _
  have hx : evalG p (g2 p) a (.var i) = true := by
    rw [evalG_var]; exact hi
  refine not_mem_of_G (by omega) (good_g2 hm) ha (not_satG_one ?_ ?_) hL
  · rw [evalG_mod, cntG_cons, cntG_nil, if_pos hx]
    simp only [g2, Bool.or_eq_true, beq_iff_eq]; right; omega
  · rw [evalG_mod, cntG_cons, cntG_cons, cntG_nil, if_pos hx]
    simp only [g2, Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega

end FModArith

end SATurday.ProofComplexity
