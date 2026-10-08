import Theory.ProofComplexity.Resolution

/-!
# AC0[p] Frege (Ladder Rung R4)

Formulas with unbounded fan in `AND`, `OR`, `NOT` and `MOD_p` connectives, their depth and
size, and Boolean semantics; a dag like sequent calculus with `MOD_p` defining axioms
(`FRefutes p d F L`), its soundness (`frefutes_unsat`), completeness at depth one by
simulating resolution (`frefutes_of_unsat`, the non vacuity witness), and the R4 target
`AC0pFregeLB` as the Frontier pin `AC0pFregeFrontier.r4_target`.

LOG: R4 AC0pFrege module (formulas)
-/

namespace SATurday.ProofComplexity

/-- Formulas with unbounded fan in connectives; `mod r l` is `MOD_{p,r}` of `l`. -/
inductive Fm where
  | var (i : ℕ)
  | neg (φ : Fm)
  | and (l : List Fm)
  | or (l : List Fm)
  | mod (r : ℕ) (l : List Fm)

namespace Fm

/-- Evaluation; `mod r l` is true iff the number of true members is `r` mod `p`. -/
def eval (p : ℕ) (a : Assignment) : Fm → Bool
  | .var i => a i
  | .neg φ => !(eval p a φ)
  | .and l => (l.attach.map fun ⟨φ, _⟩ => eval p a φ).all id
  | .or l => (l.attach.map fun ⟨φ, _⟩ => eval p a φ).any id
  | .mod r l => decide (((l.attach.map fun ⟨φ, _⟩ => eval p a φ).count true) % p = r % p)

/-- Depth: connectives `AND`, `OR`, `MOD` count one level; negation is free. -/
def depth : Fm → ℕ
  | .var _ => 0
  | .neg φ => depth φ
  | .and l => (l.attach.map fun ⟨φ, _⟩ => depth φ).foldr max 0 + 1
  | .or l => (l.attach.map fun ⟨φ, _⟩ => depth φ).foldr max 0 + 1
  | .mod _ l => (l.attach.map fun ⟨φ, _⟩ => depth φ).foldr max 0 + 1

/-- Size: number of connective and variable occurrences. -/
def size : Fm → ℕ
  | .var _ => 1
  | .neg φ => size φ + 1
  | .and l => (l.attach.map fun ⟨φ, _⟩ => size φ).sum + 1
  | .or l => (l.attach.map fun ⟨φ, _⟩ => size φ).sum + 1
  | .mod _ l => (l.attach.map fun ⟨φ, _⟩ => size φ).sum + 1

theorem attach_map {β : Type} (l : List Fm) (g : Fm → β) :
    (l.attach.map fun x : {φ // φ ∈ l} => g x.1) = l.map g := by
  simp

theorem eval_and {p : ℕ} {a : Assignment} {l : List Fm} :
    eval p a (.and l) = true ↔ ∀ φ ∈ l, eval p a φ = true := by
  rw [eval]
  have := attach_map l (eval p a)
  simp only at this
  rw [this]; simp

theorem eval_or {p : ℕ} {a : Assignment} {l : List Fm} :
    eval p a (.or l) = true ↔ ∃ φ ∈ l, eval p a φ = true := by
  rw [eval]
  have := attach_map l (eval p a)
  simp only at this
  rw [this]; simp

theorem eval_neg {p : ℕ} {a : Assignment} {φ : Fm} :
    eval p a (.neg φ) = true ↔ eval p a φ = false := by
  rw [eval]; simp

/-- Number of true members. -/
def cnt (p : ℕ) (a : Assignment) (l : List Fm) : ℕ := (l.map (eval p a)).count true

theorem eval_mod {p : ℕ} {a : Assignment} {r : ℕ} {l : List Fm} :
    eval p a (.mod r l) = true ↔ cnt p a l % p = r % p := by
  rw [eval]
  have := attach_map l (eval p a)
  simp only at this
  rw [this, decide_eq_true_iff]; rfl

theorem cnt_nil {p : ℕ} {a : Assignment} : cnt p a [] = 0 := rfl

theorem cnt_cons {p : ℕ} {a : Assignment} {φ : Fm} {l : List Fm} :
    cnt p a (φ :: l) = cnt p a l + (if eval p a φ = true then 1 else 0) := by
  unfold cnt
  rw [List.map_cons, List.count_cons]
  split_ifs <;> simp_all

end Fm

/-! ## Sequents and AC0[p] Frege proofs -/

/-- A sequent `Γ ⊢ Δ`. -/
abbrev Seq := List Fm × List Fm

/-- An assignment satisfies `Γ ⊢ Δ`: if all of `Γ` hold then some member of `Δ` holds. -/
def SeqSat (p : ℕ) (a : Assignment) (S : Seq) : Prop :=
  (∀ φ ∈ S.1, φ.eval p a = true) → ∃ ψ ∈ S.2, ψ.eval p a = true

/-- Literal of a clause as a formula. -/
def litFm (l : Literal) : Fm := if l.pos then .var l.var else .neg (.var l.var)

/-- A clause as the disjunction of its literals. -/
noncomputable def clauseFm (C : Clause) : Fm := .or (C.toList.map litFm)

/-- One inference of the sequent calculus (dag like: premises are earlier lines). -/
def FStep (p : ℕ) (F : CNF) (prev : List Seq) (S : Seq) : Prop :=
  -- hypotheses and axioms
  (∃ C ∈ F, S = ([], [clauseFm C])) ∨
  (∃ φ, S = ([φ], [φ])) ∨
  S = ([], [.and []]) ∨
  S = ([.or []], []) ∨
  -- MOD_p defining axioms
  S = ([], [.mod 0 []]) ∨
  (∃ r, r % p ≠ 0 ∧ S = ([.mod r []], [])) ∨
  (∃ r φ l, S = ([.mod r (φ :: l), φ], [.mod (r + p - 1) l])) ∨
  (∃ r φ l, S = ([.mod r (φ :: l)], [φ, .mod r l])) ∨
  (∃ r φ l, S = ([φ, .mod (r + p - 1) l], [.mod r (φ :: l)])) ∨
  (∃ r φ l, S = ([.mod r l], [φ, .mod r (φ :: l)])) ∨
  -- structural rules
  (∃ T ∈ prev, T.1 ⊆ S.1 ∧ T.2 ⊆ S.2) ∨
  (∃ φ, (S.1, φ :: S.2) ∈ prev ∧ (φ :: S.1, S.2) ∈ prev) ∨
  -- logical rules
  (∃ φ Γ Δ, S = (.neg φ :: Γ, Δ) ∧ (Γ, φ :: Δ) ∈ prev) ∨
  (∃ φ Γ Δ, S = (Γ, .neg φ :: Δ) ∧ (φ :: Γ, Δ) ∈ prev) ∨
  (∃ l Γ Δ φ, φ ∈ l ∧ S = (.and l :: Γ, Δ) ∧ (φ :: Γ, Δ) ∈ prev) ∨
  (∃ l Γ Δ, S = (Γ, .and l :: Δ) ∧ ∀ φ ∈ l, (Γ, φ :: Δ) ∈ prev) ∨
  (∃ l Γ Δ, S = (.or l :: Γ, Δ) ∧ ∀ φ ∈ l, (φ :: Γ, Δ) ∈ prev) ∨
  (∃ l Γ Δ φ, φ ∈ l ∧ S = (Γ, .or l :: Δ) ∧ (Γ, φ :: Δ) ∈ prev)

/-- A dag like proof: every line follows from earlier lines. -/
def FProof (p : ℕ) (F : CNF) (L : List Seq) : Prop :=
  ∀ k (hk : k < L.length), FStep p F (L.take k) (L.get ⟨k, hk⟩)

/-- Depth of a proof: all formulas have depth at most `d`. -/
def FDepthLe (d : ℕ) (L : List Seq) : Prop := ∀ S ∈ L, ∀ φ ∈ S.1 ++ S.2, φ.depth ≤ d

/-- Size of a proof: total size of all formulas in all lines. -/
def fSize (L : List Seq) : ℕ := (L.map fun S => ((S.1 ++ S.2).map Fm.size).sum).sum

/-- A depth `d` AC0[p] Frege refutation of `F`: a proof containing the empty sequent. -/
def FRefutes (p d : ℕ) (F : CNF) (L : List Seq) : Prop :=
  FProof p F L ∧ FDepthLe d L ∧ ([], []) ∈ L

/-! ## Soundness -/

theorem litFm_eval {p : ℕ} {a : Assignment} {l : Literal} :
    (litFm l).eval p a = true ↔ litSat a l := by
  unfold litFm litSat
  cases hl : l.pos
  · simp [Fm.eval_neg, Fm.eval]
  · simp [Fm.eval]

theorem clauseFm_eval {p : ℕ} {a : Assignment} {C : Clause} (h : clauseSat a C) :
    (clauseFm C).eval p a = true := by
  obtain ⟨l, hl, hs⟩ := h
  unfold clauseFm
  rw [Fm.eval_or]
  exact ⟨litFm l, List.mem_map.2 ⟨l, Finset.mem_toList.2 hl, rfl⟩, litFm_eval.2 hs⟩

theorem mod_succ_iff {p x r : ℕ} (hp : 0 < p) :
    (x + 1) % p = r % p ↔ x % p = (r + p - 1) % p := by
  constructor
  · intro h
    have h1 : x + 1 ≡ r [MOD p] := h
    have h2 : r + p - 1 + 1 ≡ r [MOD p] := by
      rw [show r + p - 1 + 1 = r + p by omega]
      exact Nat.ModEq.symm (Nat.modEq_iff_dvd' (by omega) |>.2 (by simp))
    exact Nat.ModEq.add_right_cancel' 1 (h1.trans h2.symm)
  · intro h
    have h1 : x ≡ r + p - 1 [MOD p] := h
    have h2 := Nat.ModEq.add_right 1 h1
    rw [show r + p - 1 + 1 = r + p by omega] at h2
    exact h2.trans (Nat.modEq_iff_dvd' (by omega) |>.2 (by simp)).symm

theorem fstep_sound {p : ℕ} (hp : 0 < p) {F : CNF} {a : Assignment} (ha : cnfSat a F)
    {prev : List Seq} (hprev : ∀ T ∈ prev, SeqSat p a T) {S : Seq} (h : FStep p F prev S) :
    SeqSat p a S := by
  rcases h with ⟨C, hC, rfl⟩ | ⟨φ, rfl⟩ | rfl | rfl | rfl | ⟨r, hr, rfl⟩ | ⟨r, φ, l, rfl⟩ |
      ⟨r, φ, l, rfl⟩ | ⟨r, φ, l, rfl⟩ | ⟨r, φ, l, rfl⟩ | ⟨T, hT, h1, h2⟩ | ⟨φ, h1, h2⟩ |
      ⟨φ, Γ, Δ, rfl, h1⟩ | ⟨φ, Γ, Δ, rfl, h1⟩ | ⟨l, Γ, Δ, φ, hφ, rfl, h1⟩ | ⟨l, Γ, Δ, rfl, h1⟩ |
      ⟨l, Γ, Δ, rfl, h1⟩ | ⟨l, Γ, Δ, φ, hφ, rfl, h1⟩
  · intro _; exact ⟨_, List.mem_singleton_self _, clauseFm_eval (ha C hC)⟩
  · intro h; exact ⟨φ, List.mem_singleton_self _, h φ (List.mem_singleton_self _)⟩
  · intro _; exact ⟨_, List.mem_singleton_self _, Fm.eval_and.2 (by simp)⟩
  · intro h
    have := h _ (List.mem_singleton_self _)
    rw [Fm.eval_or] at this; simp at this
  · intro _; exact ⟨_, List.mem_singleton_self _, Fm.eval_mod.2 (by simp [Fm.cnt_nil])⟩
  · intro h
    have := h _ (List.mem_singleton_self _)
    rw [Fm.eval_mod, Fm.cnt_nil] at this
    simp at this; exact absurd this.symm hr
  · intro h
    have h1 := Fm.eval_mod.1 (h (.mod r (φ :: l)) (by simp))
    have h2 := h φ (by simp)
    rw [Fm.cnt_cons, if_pos h2] at h1
    exact ⟨_, List.mem_singleton_self _, Fm.eval_mod.2 ((mod_succ_iff hp).1 h1)⟩
  · intro h
    have h1 := Fm.eval_mod.1 (h (.mod r (φ :: l)) (by simp))
    by_cases hφ : φ.eval p a = true
    · exact ⟨φ, by simp, hφ⟩
    · rw [Fm.cnt_cons, if_neg hφ, add_zero] at h1
      exact ⟨.mod r l, by simp, Fm.eval_mod.2 h1⟩
  · intro h
    have h1 := Fm.eval_mod.1 (h (.mod (r + p - 1) l) (by simp))
    have h2 := h φ (by simp)
    refine ⟨_, List.mem_singleton_self _, Fm.eval_mod.2 ?_⟩
    rw [Fm.cnt_cons, if_pos h2]
    exact (mod_succ_iff hp).2 h1
  · intro h
    have h1 := Fm.eval_mod.1 (h (.mod r l) (by simp))
    by_cases hφ : φ.eval p a = true
    · exact ⟨φ, by simp, hφ⟩
    · refine ⟨.mod r (φ :: l), by simp, Fm.eval_mod.2 ?_⟩
      rw [Fm.cnt_cons, if_neg hφ, add_zero]; exact h1
  · intro h
    obtain ⟨ψ, hψ, hv⟩ := hprev T hT (fun φ hφ => h φ (h1 hφ))
    exact ⟨ψ, h2 hψ, hv⟩
  · intro h
    by_cases hφ : φ.eval p a = true
    · exact hprev _ h2 (fun ψ hψ => by
        rcases List.mem_cons.1 hψ with rfl | hψ
        · exact hφ
        · exact h ψ hψ)
    · obtain ⟨ψ, hψ, hv⟩ := hprev _ h1 h
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact absurd hv hφ
      · exact ⟨ψ, hψ, hv⟩
  · intro h
    have hn := Fm.eval_neg.1 (h (.neg φ) (by simp))
    obtain ⟨ψ, hψ, hv⟩ := hprev _ h1 (fun ψ hψ => h ψ (by simp [hψ]))
    rcases List.mem_cons.1 hψ with rfl | hψ
    · rw [hn] at hv; cases hv
    · exact ⟨ψ, hψ, hv⟩
  · intro h
    by_cases hφ : φ.eval p a = true
    · obtain ⟨ψ, hψ, hv⟩ := hprev _ h1 (fun ψ hψ => by
        rcases List.mem_cons.1 hψ with rfl | hψ
        · exact hφ
        · exact h ψ hψ)
      exact ⟨ψ, by simp [hψ], hv⟩
    · exact ⟨.neg φ, by simp, Fm.eval_neg.2 (by simpa using hφ)⟩
  · intro h
    have hand := Fm.eval_and.1 (h (.and l) (by simp))
    obtain ⟨ψ, hψ, hv⟩ := hprev _ h1 (fun ψ hψ => by
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact hand ψ hφ
      · exact h ψ (by simp [hψ]))
    exact ⟨ψ, hψ, hv⟩
  · intro h
    by_contra hno
    push_neg at hno
    apply hno (.and l) (List.mem_cons_self ..)
    rw [Fm.eval_and]
    intro φ hφ
    obtain ⟨ψ, hψ, hv⟩ := hprev _ (h1 φ hφ) h
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact hv
    · exact absurd hv (by have := hno ψ (by simp [hψ]); simpa using this)
  · intro h
    obtain ⟨φ, hφ, hv⟩ := Fm.eval_or.1 (h (.or l) (by simp))
    exact hprev _ (h1 φ hφ) (fun ψ hψ => by
      rcases List.mem_cons.1 hψ with rfl | hψ
      · exact hv
      · exact h ψ (by simp [hψ]))
  · intro h
    obtain ⟨ψ, hψ, hv⟩ := hprev _ h1 h
    rcases List.mem_cons.1 hψ with rfl | hψ
    · exact ⟨.or l, by simp, Fm.eval_or.2 ⟨ψ, hφ, hv⟩⟩
    · exact ⟨ψ, by simp [hψ], hv⟩

theorem fproof_sound {p : ℕ} (hp : 0 < p) {F : CNF} {a : Assignment} (ha : cnfSat a F)
    {L : List Seq} (hL : FProof p F L) : ∀ S ∈ L, SeqSat p a S := by
  have key : ∀ k ≤ L.length, ∀ S ∈ L.take k, SeqSat p a S := by
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
          exact fstep_sound hp ha (ih (by omega)) (hL k hk')
  intro S hS
  exact key L.length le_rfl S (by rwa [List.take_length])

/-- AC0[p] Frege is sound: a refutable CNF is unsatisfiable. -/
theorem frefutes_unsat {p d : ℕ} (hp : 0 < p) {F : CNF} {L : List Seq} (h : FRefutes p d F L) :
    ¬ Satisfiable F := by
  rintro ⟨a, ha⟩
  obtain ⟨hL, _, hE⟩ := h
  obtain ⟨ψ, hψ, _⟩ := fproof_sound hp ha hL _ hE (by simp)
  simp at hψ

/-! ## Non vacuity: AC0[p] Frege simulates resolution -/

theorem fstep_mono {p : ℕ} {F : CNF} {prev prev' : List Seq} (hsub : ∀ T ∈ prev, T ∈ prev')
    {S : Seq} (h : FStep p F prev S) : FStep p F prev' S := by
  rcases h with h | h | h | h | h | h | h | h | h | h | ⟨T, hT, h1, h2⟩ | ⟨φ, h1, h2⟩ |
      ⟨φ, Γ, Δ, e, h1⟩ | ⟨φ, Γ, Δ, e, h1⟩ | ⟨l, Γ, Δ, φ, hφ, e, h1⟩ | ⟨l, Γ, Δ, e, h1⟩ |
      ⟨l, Γ, Δ, e, h1⟩ | ⟨l, Γ, Δ, φ, hφ, e, h1⟩
  all_goals first
    | exact Or.inl h
    | exact Or.inr (Or.inl h)
    | exact Or.inr (Or.inr (Or.inl h))
    | exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h)))))))))
    | skip
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨T, hsub T hT, h1, h2⟩))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨φ, hsub _ h1, hsub _ h2⟩)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨φ, Γ, Δ, e, hsub _ h1⟩))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, Γ, Δ, e, hsub _ h1⟩)))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, Γ, Δ, φ, hφ, e, hsub _ h1⟩))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, Γ, Δ, e,
        fun φ hφ => hsub _ (h1 φ hφ)⟩)))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, Γ, Δ, e,
        fun φ hφ => hsub _ (h1 φ hφ)⟩))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, Γ, Δ, φ, hφ, e,
        hsub _ h1⟩))))))))))))))))

/-- Proofs compose by concatenation. -/
theorem fproof_append {p : ℕ} {F : CNF} {L1 L2 : List Seq} (h1 : FProof p F L1)
    (h2 : FProof p F L2) : FProof p F (L1 ++ L2) := by
  intro k hk
  by_cases hk1 : k < L1.length
  · have e : (L1 ++ L2).get ⟨k, hk⟩ = L1.get ⟨k, hk1⟩ := by simp [List.getElem_append_left hk1]
    rw [e]
    refine fstep_mono (fun T hT => ?_) (h1 k hk1)
    rw [List.take_append_of_le_length hk1.le]; exact hT
  · have hk2 : k - L1.length < L2.length := by simp at hk; omega
    have e : (L1 ++ L2).get ⟨k, hk⟩ = L2.get ⟨k - L1.length, hk2⟩ := by
      simp [List.getElem_append_right (Nat.le_of_not_lt hk1)]
    rw [e]
    refine fstep_mono (fun T hT => ?_) (h2 _ hk2)
    rw [List.take_append, List.take_of_length_le (by omega)]
    exact List.mem_append_right _ (by rwa [show k - L1.length = k - L1.length from rfl])

/-- A single new line justified by the lines before it. -/
theorem fproof_snoc {p : ℕ} {F : CNF} {L : List Seq} {S : Seq} (h : FProof p F L)
    (hS : FStep p F L S) : FProof p F (L ++ [S]) := by
  intro k hk
  by_cases hk1 : k < L.length
  · have e : (L ++ [S]).get ⟨k, hk⟩ = L.get ⟨k, hk1⟩ := by simp [List.getElem_append_left hk1]
    rw [e]
    refine fstep_mono (fun T hT => ?_) (h k hk1)
    rw [List.take_append_of_le_length hk1.le]; exact hT
  · have hkL : k = L.length := by simp at hk; omega
    subst hkL
    have e : (L ++ [S]).get ⟨L.length, hk⟩ = S := by simp
    rw [e, List.take_append_of_le_length le_rfl, List.take_length]
    exact hS

/-- Literal list of a clause. -/
noncomputable def litsOf (C : Clause) : List Fm := C.toList.map litFm

theorem mem_litsOf {C : Clause} {l : Literal} (h : l ∈ C) : litFm l ∈ litsOf C :=
  List.mem_map.2 ⟨l, Finset.mem_toList.2 h, rfl⟩

theorem depth_litFm (l : Literal) : (litFm l).depth = 0 := by
  unfold litFm; split_ifs <;> simp [Fm.depth]

theorem foldr_max_zero (l : List ℕ) (h : ∀ x ∈ l, x = 0) : l.foldr max 0 = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      simp only [List.foldr_cons]
      rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]; rfl

theorem depth_clauseFm (C : Clause) : (clauseFm C).depth ≤ 1 := by
  unfold clauseFm
  rw [Fm.depth]
  have := Fm.attach_map (C.toList.map litFm) Fm.depth
  simp only at this
  rw [this, foldr_max_zero]
  intro x hx
  obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hx
  obtain ⟨l, _, rfl⟩ := List.mem_map.1 hφ
  exact depth_litFm l

theorem depth_lits {C : Clause} : ∀ φ ∈ litsOf C, φ.depth ≤ 1 := by
  intro φ hφ
  obtain ⟨l, _, rfl⟩ := List.mem_map.1 hφ
  rw [depth_litFm]; omega

theorem fdepth_append {d : ℕ} {L1 L2 : List Seq} (h1 : FDepthLe d L1) (h2 : FDepthLe d L2) :
    FDepthLe d (L1 ++ L2) := by
  intro S hS
  rcases List.mem_append.1 hS with h | h
  · exact h1 S h
  · exact h2 S h

theorem fdepth_single {d : ℕ} {S : Seq} (h : ∀ φ ∈ S.1 ++ S.2, φ.depth ≤ d) :
    FDepthLe d [S] := by
  intro T hT; rw [List.mem_singleton] at hT; subst hT; exact h

/-- Axiom and weakening lines `[φ] ⊢ φ`, `[φ] ⊢ litsOf C` for each `φ` of `M`. -/
def axLines (Δ : List Fm) : List Fm → List Seq
  | [] => []
  | φ :: M => [([φ], [φ]), ([φ], Δ)] ++ axLines Δ M

theorem axLines_proof {p : ℕ} {F : CNF} (Δ : List Fm) :
    ∀ M : List Fm, (∀ φ ∈ M, φ ∈ Δ) → FProof p F (axLines Δ M) := by
  intro M
  induction M with
  | nil => intro _ k hk; simp [axLines] at hk
  | cons φ M ih =>
      intro hM
      refine fproof_append ?_ (ih fun ψ hψ => hM ψ (by simp [hψ]))
      have h0 : FProof p F [([φ], [φ])] := by
        intro k hk
        simp at hk; subst hk
        exact Or.inr (Or.inl ⟨φ, rfl⟩)
      have := fproof_snoc (S := ([φ], Δ)) h0 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨([φ], [φ]), by simp, by simp,
          by intro ψ hψ; rw [List.mem_singleton] at hψ; subst hψ; exact hM ψ (by simp)⟩)))))))))))
      simpa using this

theorem axLines_mem (Δ : List Fm) : ∀ M : List Fm, ∀ φ ∈ M, ([φ], Δ) ∈ axLines Δ M := by
  intro M
  induction M with
  | nil => intro φ h; simp at h
  | cons ψ M ih =>
      intro φ h
      rcases List.mem_cons.1 h with rfl | h
      · simp [axLines]
      · simp only [axLines, List.cons_append, List.singleton_append, List.mem_cons]
        exact Or.inr (Or.inr (ih φ h))

theorem axLines_depth (Δ : List Fm) (hΔ : ∀ φ ∈ Δ, φ.depth ≤ 1) :
    ∀ M : List Fm, (∀ φ ∈ M, φ ∈ Δ) → FDepthLe 1 (axLines Δ M) := by
  intro M
  induction M with
  | nil => intro _ S hS; simp [axLines] at hS
  | cons φ M ih =>
      intro hM
      refine fdepth_append ?_ (ih fun ψ hψ => hM ψ (by simp [hψ]))
      intro S hS
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hS
      rcases hS with rfl | rfl
      · intro ψ hψ; simp at hψ; rcases hψ with rfl | rfl <;> exact hΔ _ (hM _ (by simp))
      · intro ψ hψ
        simp only [List.mem_append, List.mem_singleton] at hψ
        rcases hψ with rfl | hψ
        · exact hΔ _ (hM _ (by simp))
        · exact hΔ _ hψ

-- rule shorthands (positions in `FStep`)
theorem step_hyp {p : ℕ} {F : CNF} {prev : List Seq} {C : Clause} (hC : C ∈ F) :
    FStep p F prev ([], [clauseFm C]) := Or.inl ⟨C, hC, rfl⟩

theorem step_ax {p : ℕ} {F : CNF} {prev : List Seq} (φ : Fm) :
    FStep p F prev ([φ], [φ]) := Or.inr (Or.inl ⟨φ, rfl⟩)

theorem step_weak {p : ℕ} {F : CNF} {prev : List Seq} {T S : Seq} (hT : T ∈ prev)
    (h1 : T.1 ⊆ S.1) (h2 : T.2 ⊆ S.2) : FStep p F prev S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨T, hT, h1, h2⟩))))))))))

theorem step_cut {p : ℕ} {F : CNF} {prev : List Seq} {S : Seq} (φ : Fm)
    (h1 : (S.1, φ :: S.2) ∈ prev) (h2 : (φ :: S.1, S.2) ∈ prev) : FStep p F prev S :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl ⟨φ, h1, h2⟩)))))))))))

theorem step_negL {p : ℕ} {F : CNF} {prev : List Seq} (φ : Fm) (Γ Δ : List Fm)
    (h1 : (Γ, φ :: Δ) ∈ prev) : FStep p F prev (.neg φ :: Γ, Δ) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl ⟨φ, Γ, Δ, rfl, h1⟩))))))))))))

theorem step_orL {p : ℕ} {F : CNF} {prev : List Seq} (l Γ Δ : List Fm)
    (h1 : ∀ φ ∈ l, (φ :: Γ, Δ) ∈ prev) : FStep p F prev (.or l :: Γ, Δ) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, Γ, Δ, rfl, h1⟩))))))))))))))))

/-- Every resolution derivation of `C` becomes a depth one proof containing `⊢ litsOf C`. -/
theorem sim_resolution {p : ℕ} {F : CNF} : ∀ {C : Clause} (_ : Derivation F C),
    ∃ L : List Seq, FProof p F L ∧ FDepthLe 1 L ∧ ([], litsOf C) ∈ L := by
  intro C d
  induction d with
  | hyp C hC =>
      set Δ := litsOf C
      let L0 : List Seq := [([], [clauseFm C])]
      have h0 : FProof p F L0 := by
        intro k hk; simp [L0] at hk; subst hk; exact step_hyp hC
      have hax := axLines_proof (p := p) (F := F) Δ Δ (fun _ h => h)
      have h1 : FProof p F (L0 ++ axLines Δ Δ) := fproof_append h0 hax
      -- `or Δ ⊢ Δ`
      have h2 := fproof_snoc (S := ([.or Δ], Δ)) h1 (step_orL Δ [] Δ (fun φ hφ =>
        List.mem_append_right _ (axLines_mem Δ Δ φ hφ)))
      -- `⊢ or Δ, Δ`
      have h3 := fproof_snoc (S := ([], .or Δ :: Δ)) h2
        (step_weak (T := ([], [clauseFm C])) (by simp [L0]) (by simp)
          (by intro ψ hψ; simp at hψ; subst hψ; simp [clauseFm, Δ, litsOf]))
      -- cut
      have h4 := fproof_snoc (S := ([], Δ)) h3 (step_cut (.or Δ) (by simp) (by simp))
      refine ⟨_, h4, ?_, by simp⟩
      refine fdepth_append (fdepth_append (fdepth_append (fdepth_append
        (fdepth_single ?_) (axLines_depth Δ depth_lits Δ (fun _ h => h)))
        (fdepth_single ?_)) (fdepth_single ?_)) (fdepth_single ?_)
      · intro ψ hψ; simp at hψ; subst hψ; exact depth_clauseFm C
      · intro ψ hψ
        simp only [List.mem_append, List.mem_singleton] at hψ
        rcases hψ with rfl | hψ
        · exact depth_clauseFm C
        · exact depth_lits ψ hψ
      · intro ψ hψ
        simp only [List.nil_append, List.mem_cons] at hψ
        rcases hψ with rfl | hψ
        · exact depth_clauseFm C
        · exact depth_lits ψ hψ
      · intro ψ hψ; simp only [List.nil_append] at hψ; exact depth_lits ψ hψ
  | res x dC dD hx hnx ihC ihD =>
      rename_i C D
      obtain ⟨LC, pC, dC', mC⟩ := ihC
      obtain ⟨LD, pD, dD', mD⟩ := ihD
      set X : Fm := .var x
      set NX : Fm := .neg (.var x)
      set R := resolvent C D x
      have hlx : litFm ⟨x, true⟩ = X := by simp [litFm, X]
      have hlnx : litFm ⟨x, false⟩ = NX := by simp [litFm, NX]
      have hDsub : litsOf D ⊆ NX :: litsOf R := by
        intro ψ hψ
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hψ
        rw [Finset.mem_toList] at hl
        by_cases he : l = ⟨x, false⟩
        · subst he; rw [hlnx]; simp
        · exact List.mem_cons_of_mem _ (mem_litsOf (Finset.mem_union_right _
            (Finset.mem_erase.2 ⟨he, hl⟩)))
      have hCsub : litsOf C ⊆ X :: litsOf R := by
        intro ψ hψ
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hψ
        rw [Finset.mem_toList] at hl
        by_cases he : l = ⟨x, true⟩
        · subst he; rw [hlx]; simp
        · exact List.mem_cons_of_mem _ (mem_litsOf (Finset.mem_union_left _
            (Finset.mem_erase.2 ⟨he, hl⟩)))
      have p0 := fproof_append pC pD
      have p1 := fproof_snoc (S := ([X], [X])) p0 (step_ax X)
      have p2 := fproof_snoc (S := ([NX, X], [])) p1 (step_negL X [X] [] (by simp))
      have p3 := fproof_snoc (S := ([X], NX :: litsOf R)) p2
        (step_weak (T := ([], litsOf D)) (by simp [mD]) (by simp) hDsub)
      have p4 := fproof_snoc (S := ([NX, X], litsOf R)) p3
        (step_weak (T := ([NX, X], [])) (by simp) (by simp) (by simp))
      have p5 := fproof_snoc (S := ([X], litsOf R)) p4 (step_cut NX (by simp) (by simp))
      have p6 := fproof_snoc (S := ([], X :: litsOf R)) p5
        (step_weak (T := ([], litsOf C)) (by simp [mC]) (by simp) hCsub)
      have p7 := fproof_snoc (S := ([], litsOf R)) p6 (step_cut X (by simp) (by simp))
      refine ⟨_, p7, ?_, by simp⟩
      have dep : ∀ ψ : Fm, (ψ = X ∨ ψ = NX ∨ ψ ∈ litsOf R) → ψ.depth ≤ 1 := by
        rintro ψ (rfl | rfl | h)
        · simp [X, Fm.depth]
        · simp [NX, Fm.depth]
        · exact depth_lits ψ h
      refine fdepth_append (fdepth_append (fdepth_append (fdepth_append (fdepth_append
        (fdepth_append (fdepth_append (fdepth_append dC' dD') ?_) ?_) ?_) ?_) ?_) ?_) ?_ <;>
        apply fdepth_single <;> intro ψ hψ <;> apply dep <;>
        simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false, List.nil_append, List.append_nil] at hψ <;> tauto

/-- Non vacuity: every unsatisfiable CNF has a depth one AC0[p] Frege refutation. -/
theorem frefutes_of_unsat {p : ℕ} {F : CNF} (h : ¬ Satisfiable F) :
    ∃ L, FRefutes p 1 F L := by
  obtain ⟨d⟩ := resolution_complete h
  obtain ⟨L, hL, hd, hm⟩ := sim_resolution (p := p) d
  refine ⟨L, hL, hd, ?_⟩
  have : litsOf (∅ : Clause) = [] := by simp [litsOf]
  rwa [this] at hm

/-! ## The R4 target -/

/-- Size of a CNF: total number of literal occurrences. -/
def cnfSize (F : CNF) : ℕ := ∑ C ∈ F, C.card

/-- AC0[p] Frege has super polynomial lower bounds: some polynomial size family of
unsatisfiable CNFs needs super polynomial size refutations at every fixed depth. -/
def AC0pFregeLB (p : ℕ) : Prop :=
  ∃ Fam : ℕ → CNF, (∃ c0 : ℕ, ∀ n, cnfSize (Fam n) ≤ (n + 1) ^ c0) ∧
    (∀ n, ¬ Satisfiable (Fam n)) ∧
    ∀ d c : ℕ, ∃ N, ∀ n ≥ N, ∀ L, FRefutes p d (Fam n) L → n ^ c < fSize L

namespace AC0pFregeFrontier

/-- R4 (open problem since the late 1980s): super polynomial lower bounds for AC0[p] Frege
for every prime `p`. Primary candidate families: Tseitin mod q on expanders (q ≠ p),
Count_q, onto PHP, random k CNF. See docs/ladder/r4-completion-checklist.md. -/
theorem r4_target : ∀ p : ℕ, p.Prime → AC0pFregeLB p := by
  sorry

end AC0pFregeFrontier

end SATurday.ProofComplexity
