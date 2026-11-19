import Theory.ProofComplexity.AC0pFrege

/-!
# MOD elimination for the pinned AC0[p] Frege calculus

The `G = {0}` model of `FregeModArith.lean` is syntactic: reading `MOD_{p,0}(l)` as
`AND(¬l)` and `MOD_{p,r}(l)`, `r ≠ 0`, as `OR()` (`sig`) turns every instance of the six `MOD_p`
defining axioms of `FStep` into a sequent with a short MOD-free proof (for `p ≥ 2`), and commutes
with every other rule.  Hence (`elim_mod`, `frefutes_elim_mod`): every `FRefutes p d F L` gives an
`FRefutes p d F L'` of the same depth `d` in which no `MOD` gate occurs, with
`|L'| ≤ 3 fSize L + 6 |L|` lines and `fSize L' ≤ 18 (fSize L + 2 |L|)^2`.

So the pinned calculus `FRefutes p d` is polynomially simulated, at the same depth, by its MOD-free
fragment (depth `d` Frege with unbounded fan in `AND`, `OR`), and the pinned target
`AC0pFregeLB p` is implied by a super polynomial lower bound for bounded depth Frege at every fixed
depth on one polynomial size family (such bounds are known in the literature for the pigeonhole
principle and for Tseitin formulas on expanders; they are not formalized here).  The defect is in
the axioms: they never reduce the residue `r` modulo `p` (see `FregeModArith.lean`).
-/

namespace SATurday.ProofComplexity

namespace FModElim

open Fm

/-! ## The translation -/

/-- `MOD_{p,0}(l) ↦ AND(¬l)`, `MOD_{p,r}(l) ↦ OR()` for `r ≠ 0`, homomorphic elsewhere. -/
def sig : Fm → Fm
  | .var i => .var i
  | .neg φ => .neg (sig φ)
  | .and l => .and (l.attach.map fun ⟨φ, _⟩ => sig φ)
  | .or l => .or (l.attach.map fun ⟨φ, _⟩ => sig φ)
  | .mod r l => if r = 0 then .and (l.attach.map fun ⟨φ, _⟩ => .neg (sig φ)) else .or []

/-- No `MOD` gate occurs. -/
def noMod : Fm → Bool
  | .var _ => true
  | .neg φ => noMod φ
  | .and l => (l.attach.map fun ⟨φ, _⟩ => noMod φ).all id
  | .or l => (l.attach.map fun ⟨φ, _⟩ => noMod φ).all id
  | .mod _ _ => false

theorem sig_var {i : ℕ} : sig (.var i) = .var i := by rw [sig]

theorem sig_neg {φ : Fm} : sig (.neg φ) = .neg (sig φ) := by rw [sig]

theorem sig_and {l : List Fm} : sig (.and l) = .and (l.map sig) := by
  rw [sig]
  have := attach_map l sig
  simp only at this
  rw [this]

theorem sig_or {l : List Fm} : sig (.or l) = .or (l.map sig) := by
  rw [sig]
  have := attach_map l sig
  simp only at this
  rw [this]

theorem sig_mod0 {l : List Fm} : sig (.mod 0 l) = .and (l.map fun φ => .neg (sig φ)) := by
  rw [sig, if_pos rfl]
  have := attach_map l (fun φ => Fm.neg (sig φ))
  simp only at this
  rw [this]

theorem sig_modr {r : ℕ} {l : List Fm} (hr : r ≠ 0) : sig (.mod r l) = .or [] := by
  rw [sig, if_neg hr]

theorem noMod_and {l : List Fm} : noMod (.and l) = true ↔ ∀ φ ∈ l, noMod φ = true := by
  rw [noMod]
  have := attach_map l noMod
  simp only at this
  rw [this]; simp

theorem noMod_or {l : List Fm} : noMod (.or l) = true ↔ ∀ φ ∈ l, noMod φ = true := by
  rw [noMod]
  have := attach_map l noMod
  simp only at this
  rw [this]; simp

theorem noMod_sig : ∀ φ : Fm, noMod (sig φ) = true
  | .var _ => by rw [sig_var, noMod]
  | .neg φ => by rw [sig_neg, noMod]; exact noMod_sig φ
  | .and l => by
      rw [sig_and, noMod_and]
      intro ψ hψ
      obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hψ
      exact noMod_sig φ
  | .or l => by
      rw [sig_or, noMod_or]
      intro ψ hψ
      obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hψ
      exact noMod_sig φ
  | .mod r l => by
      by_cases hr : r = 0
      · subst hr
        rw [sig_mod0, noMod_and]
        intro ψ hψ
        obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hψ
        rw [noMod]; exact noMod_sig φ
      · rw [sig_modr hr, noMod_or]; simp

theorem noMod_lit (l : Literal) : noMod (litFm l) = true := by
  unfold litFm; split_ifs <;> simp [noMod]

theorem sig_lit (l : Literal) : sig (litFm l) = litFm l := by
  unfold litFm; split_ifs <;> simp [sig_neg, sig_var]

theorem sig_clauseFm (C : Clause) : sig (clauseFm C) = clauseFm C := by
  unfold clauseFm
  rw [sig_or, List.map_map]
  congr 1
  exact List.map_congr_left (fun l _ => sig_lit l)

/-! ## Depth and size -/

theorem foldr_max_le_iff {l : List ℕ} {m : ℕ} : l.foldr max 0 ≤ m ↔ ∀ x ∈ l, x ≤ m := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

theorem le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 :=
  foldr_max_le_iff.1 le_rfl x h

theorem depth_list (l : List Fm) :
    (l.attach.map fun x : {φ // φ ∈ l} => Fm.depth x.1).foldr max 0 = (l.map Fm.depth).foldr max 0 := by
  rw [attach_map]

theorem depth_and {l : List Fm} : (Fm.and l).depth = (l.map Fm.depth).foldr max 0 + 1 := by
  rw [Fm.depth]; have := attach_map l Fm.depth; simp only at this; rw [this]

theorem depth_or {l : List Fm} : (Fm.or l).depth = (l.map Fm.depth).foldr max 0 + 1 := by
  rw [Fm.depth]; have := attach_map l Fm.depth; simp only at this; rw [this]

theorem depth_mod {r : ℕ} {l : List Fm} :
    (Fm.mod r l).depth = (l.map Fm.depth).foldr max 0 + 1 := by
  rw [Fm.depth]; have := attach_map l Fm.depth; simp only at this; rw [this]

theorem depth_neg {φ : Fm} : (Fm.neg φ).depth = φ.depth := by rw [Fm.depth]

theorem depth_lt_mod {r : ℕ} {l : List Fm} {φ : Fm} (h : φ ∈ l) :
    φ.depth < (Fm.mod r l).depth := by
  rw [depth_mod]
  have := le_foldr_max (List.mem_map_of_mem (f := Fm.depth) h)
  omega

theorem one_le_depth_mod {r : ℕ} {l : List Fm} : 1 ≤ (Fm.mod r l).depth := by
  rw [depth_mod]; omega

theorem depth_sig : ∀ φ : Fm, (sig φ).depth ≤ φ.depth
  | .var _ => by rw [sig_var]
  | .neg φ => by rw [sig_neg, depth_neg, depth_neg]; exact depth_sig φ
  | .and l => by
      rw [sig_and, depth_and, depth_and, List.map_map]
      have : (l.map (Fm.depth ∘ sig)).foldr max 0 ≤ (l.map Fm.depth).foldr max 0 := by
        rw [foldr_max_le_iff]
        intro x hx
        obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hx
        exact (depth_sig φ).trans (le_foldr_max (List.mem_map_of_mem hφ))
      omega
  | .or l => by
      rw [sig_or, depth_or, depth_or, List.map_map]
      have : (l.map (Fm.depth ∘ sig)).foldr max 0 ≤ (l.map Fm.depth).foldr max 0 := by
        rw [foldr_max_le_iff]
        intro x hx
        obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hx
        exact (depth_sig φ).trans (le_foldr_max (List.mem_map_of_mem hφ))
      omega
  | .mod r l => by
      by_cases hr : r = 0
      · subst hr
        rw [sig_mod0, depth_and, depth_mod, List.map_map]
        have : (l.map (Fm.depth ∘ fun φ => Fm.neg (sig φ))).foldr max 0 ≤
            (l.map Fm.depth).foldr max 0 := by
          rw [foldr_max_le_iff]
          intro x hx
          obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hx
          simp only [Function.comp, depth_neg]
          exact (depth_sig φ).trans (le_foldr_max (List.mem_map_of_mem hφ))
        omega
      · rw [sig_modr hr, depth_or, depth_mod]; simp

theorem size_and {l : List Fm} : (Fm.and l).size = (l.map Fm.size).sum + 1 := by
  rw [Fm.size]; have := attach_map l Fm.size; simp only at this; rw [this]

theorem size_or {l : List Fm} : (Fm.or l).size = (l.map Fm.size).sum + 1 := by
  rw [Fm.size]; have := attach_map l Fm.size; simp only at this; rw [this]

theorem size_mod {r : ℕ} {l : List Fm} : (Fm.mod r l).size = (l.map Fm.size).sum + 1 := by
  rw [Fm.size]; have := attach_map l Fm.size; simp only at this; rw [this]

theorem size_neg {φ : Fm} : (Fm.neg φ).size = φ.size + 1 := by rw [Fm.size]

theorem one_le_size : ∀ φ : Fm, 1 ≤ φ.size
  | .var _ => by rw [Fm.size]
  | .neg φ => by rw [size_neg]; omega
  | .and l => by rw [size_and]; omega
  | .or l => by rw [size_or]; omega
  | .mod r l => by rw [size_mod]; omega

theorem sum_map_le {l : List Fm} {f g : Fm → ℕ} (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

theorem le_sum_map {l : List Fm} {f : Fm → ℕ} {x : Fm} (h : x ∈ l) : f x ≤ (l.map f).sum :=
  List.le_sum_of_mem (List.mem_map_of_mem h)

theorem size_lt_mod {r : ℕ} {l : List Fm} {φ : Fm} (h : φ ∈ l) : φ.size < (Fm.mod r l).size := by
  rw [size_mod]; have := le_sum_map (f := Fm.size) h; omega

theorem length_lt_mod {r : ℕ} {l : List Fm} : l.length < (Fm.mod r l).size := by
  rw [size_mod]
  have : (l.map fun _ => 1).sum ≤ (l.map Fm.size).sum := sum_map_le (fun x _ => one_le_size x)
  simp at this; omega

theorem size_sig : ∀ φ : Fm, (sig φ).size + 1 ≤ 2 * φ.size
  | .var _ => by rw [sig_var, Fm.size]
  | .neg φ => by rw [sig_neg, size_neg, size_neg]; have := size_sig φ; omega
  | .and l => by
      rw [sig_and, size_and, size_and, List.map_map]
      have : (l.map (Fm.size ∘ sig)).sum ≤ (l.map fun φ => 2 * φ.size).sum :=
        sum_map_le fun φ hφ => by have := size_sig φ; simp only [Function.comp]; omega
      have h2 : (l.map fun φ => 2 * φ.size).sum = 2 * (l.map Fm.size).sum := by
        rw [List.sum_map_mul_left]
      omega
  | .or l => by
      rw [sig_or, size_or, size_or, List.map_map]
      have : (l.map (Fm.size ∘ sig)).sum ≤ (l.map fun φ => 2 * φ.size).sum :=
        sum_map_le fun φ hφ => by have := size_sig φ; simp only [Function.comp]; omega
      have h2 : (l.map fun φ => 2 * φ.size).sum = 2 * (l.map Fm.size).sum := by
        rw [List.sum_map_mul_left]
      omega
  | .mod r l => by
      by_cases hr : r = 0
      · subst hr
        rw [sig_mod0, size_and, size_mod, List.map_map]
        have : (l.map (Fm.size ∘ fun φ => Fm.neg (sig φ))).sum ≤ (l.map fun φ => 2 * φ.size).sum :=
          sum_map_le fun φ hφ => by
            have := size_sig φ; simp only [Function.comp, size_neg]; omega
        have h2 : (l.map fun φ => 2 * φ.size).sum = 2 * (l.map Fm.size).sum := by
          rw [List.sum_map_mul_left]
        omega
      · rw [sig_modr hr, size_or, size_mod]; simp

/-! ## Rule shorthands and sizes -/

variable {p : ℕ} {F : CNF}

theorem step_andNil {prev : List Seq} : FStep p F prev ([], [.and []]) :=
  Or.inr (Or.inr (Or.inl rfl))

theorem step_orNil {prev : List Seq} : FStep p F prev ([.or []], []) :=
  Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem step_negR {prev : List Seq} (φ : Fm) (Γ Δ : List Fm) (h1 : (φ :: Γ, Δ) ∈ prev) :
    FStep p F prev (Γ, .neg φ :: Δ) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, Γ, Δ, rfl, h1⟩)))))))))))))

theorem step_andL {prev : List Seq} (l Γ Δ : List Fm) (φ : Fm) (hφ : φ ∈ l)
    (h1 : (φ :: Γ, Δ) ∈ prev) : FStep p F prev (.and l :: Γ, Δ) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, Γ, Δ, φ, hφ, rfl, h1⟩))))))))))))))

theorem step_andR {prev : List Seq} (l Γ Δ : List Fm) (h1 : ∀ φ ∈ l, (Γ, φ :: Δ) ∈ prev) :
    FStep p F prev (Γ, .and l :: Δ) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨l, Γ, Δ, rfl, h1⟩)))))))))))))))

theorem step_orR {prev : List Seq} (l Γ Δ : List Fm) (φ : Fm) (hφ : φ ∈ l)
    (h1 : (Γ, φ :: Δ) ∈ prev) : FStep p F prev (Γ, .or l :: Δ) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨l, Γ, Δ, φ, hφ, rfl, h1⟩))))))))))))))))

/-- Translation of a sequent. -/
def sigS (S : Seq) : Seq := (S.1.map sig, S.2.map sig)

/-- Size of a sequent (`fSize L` is the sum over the lines). -/
def seqSize (S : Seq) : ℕ := ((S.1 ++ S.2).map Fm.size).sum

theorem fSize_eq (L : List Seq) : fSize L = (L.map seqSize).sum := rfl

theorem fSize_append (A B : List Seq) : fSize (A ++ B) = fSize A + fSize B := by
  simp [fSize_eq, List.map_append, List.sum_append]

theorem fSize_single (S : Seq) : fSize [S] = seqSize S := by simp [fSize_eq]

theorem fSize_le (B : List Seq) (m : ℕ) (h : ∀ T ∈ B, seqSize T ≤ m) :
    fSize B ≤ B.length * m := by
  induction B with
  | nil => simp [fSize_eq]
  | cons T B ih =>
      rw [show T :: B = [T] ++ B from rfl, fSize_append, fSize_single, List.length_append]
      have := ih (fun U hU => h U (by simp [hU]))
      have := h T (by simp)
      simp only [List.length_singleton]
      nlinarith

theorem size_le_seq {S : Seq} {φ : Fm} (h : φ ∈ S.1 ++ S.2) : φ.size ≤ seqSize S :=
  le_sum_map h

/-- A formula admissible in the block of `S`. -/
def Sub (S : Seq) (ψ : Fm) : Prop :=
  noMod ψ = true ∧ ψ.size ≤ 2 * seqSize S + 1 ∧
    ∀ d, (∀ φ ∈ S.1 ++ S.2, φ.depth ≤ d) → ψ.depth ≤ d

/-- A line admissible in the block of `S`. -/
def Good (S T : Seq) : Prop :=
  (∀ ψ ∈ T.1 ++ T.2, noMod ψ = true ∧ ∀ d, (∀ φ ∈ S.1 ++ S.2, φ.depth ≤ d) → ψ.depth ≤ d) ∧
    seqSize T ≤ 6 * seqSize S + 3

theorem good_short {S T : Seq} (hl : (T.1 ++ T.2).length ≤ 3) (h : ∀ ψ ∈ T.1 ++ T.2, Sub S ψ) :
    Good S T := by
  refine ⟨fun ψ hψ => ⟨(h ψ hψ).1, (h ψ hψ).2.2⟩, ?_⟩
  have := sum_map_le (l := T.1 ++ T.2) (g := fun _ => 2 * seqSize S + 1)
    (fun ψ hψ => (h ψ hψ).2.1)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at this
  have h3 := Nat.mul_le_mul_right (2 * seqSize S + 1) hl
  show ((T.1 ++ T.2).map Fm.size).sum ≤ 6 * seqSize S + 3
  omega

theorem allSub1 {S : Seq} {a : Fm} (ha : Sub S a) : ∀ ψ ∈ [a], Sub S ψ := by
  intro ψ hψ; rw [List.mem_singleton] at hψ; subst hψ; exact ha

theorem allSub2 {S : Seq} {a b : Fm} (ha : Sub S a) (hb : Sub S b) : ∀ ψ ∈ [a, b], Sub S ψ := by
  intro ψ hψ
  rcases List.mem_cons.1 hψ with rfl | hψ
  · exact ha
  · exact allSub1 hb ψ hψ

theorem allSub3 {S : Seq} {a b c : Fm} (ha : Sub S a) (hb : Sub S b) (hc : Sub S c) :
    ∀ ψ ∈ [a, b, c], Sub S ψ := by
  intro ψ hψ
  rcases List.mem_cons.1 hψ with rfl | hψ
  · exact ha
  · exact allSub2 hb hc ψ hψ

theorem sub_sig {S : Seq} {φ : Fm} (h : φ ∈ S.1 ++ S.2) : Sub S (sig φ) := by
  refine ⟨noMod_sig φ, ?_, fun d hd => (depth_sig φ).trans (hd φ h)⟩
  have := size_sig φ; have := size_le_seq h; omega

theorem sub_neg_sig {S : Seq} {φ : Fm} (h : φ ∈ S.1 ++ S.2) : Sub S (.neg (sig φ)) := by
  refine ⟨by rw [noMod]; exact noMod_sig φ, ?_, fun d hd => ?_⟩
  · rw [size_neg]; have := size_sig φ; have := size_le_seq h; omega
  · rw [depth_neg]; exact (depth_sig φ).trans (hd φ h)

theorem sub_arg {S : Seq} {r : ℕ} {l : List Fm} {χ : Fm} (h : Fm.mod r l ∈ S.1 ++ S.2)
    (hχ : χ ∈ l) : Sub S (.neg (sig χ)) := by
  refine ⟨by rw [noMod]; exact noMod_sig χ, ?_, fun d hd => ?_⟩
  · rw [size_neg]; have := size_sig χ; have := size_le_seq h
    have := size_lt_mod (r := r) hχ; omega
  · rw [depth_neg]
    have := depth_lt_mod (r := r) hχ; have := hd _ h; have := depth_sig χ; omega

theorem sub_orNil {S : Seq} {r : ℕ} {l : List Fm} (h : Fm.mod r l ∈ S.1 ++ S.2) :
    Sub S (.or []) := by
  refine ⟨by rw [noMod_or]; simp, ?_, fun d hd => ?_⟩
  · rw [size_or]; simp
  · rw [depth_or]; have := hd _ h; have := one_le_depth_mod (r := r) (l := l); simp; omega

theorem good_sigS (S : Seq) : Good S (sigS S) := by
  have e : (sigS S).1 ++ (sigS S).2 = (S.1 ++ S.2).map sig := by simp [sigS]
  refine ⟨fun ψ hψ => ?_, ?_⟩
  · rw [e] at hψ
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hψ
    exact ⟨noMod_sig φ, fun d hd => (depth_sig φ).trans (hd φ hφ)⟩
  · unfold seqSize; rw [e, List.map_map]
    have := sum_map_le (l := S.1 ++ S.2) (f := Fm.size ∘ sig) (g := fun φ => 2 * φ.size)
      (fun φ _ => by have := size_sig φ; simp only [Function.comp]; omega)
    have h2 : ((S.1 ++ S.2).map fun φ => 2 * φ.size).sum = 2 * ((S.1 ++ S.2).map Fm.size).sum := by
      rw [List.sum_map_mul_left]
    unfold seqSize at *
    omega

/-! ## Projection lines `[A] ⊢ ψ, Δ` for the members `ψ` of a conjunction `A` -/

/-- For each `ψ ∈ N`: `ψ ⊢ ψ`, `ψ ⊢ ψ, Δ`, `A ⊢ ψ, Δ`. -/
def projLines (A : Fm) (Δ : List Fm) : List Fm → List Seq
  | [] => []
  | ψ :: N => [([ψ], [ψ]), ([ψ], ψ :: Δ), ([A], ψ :: Δ)] ++ projLines A Δ N

theorem projLines_proof (M Δ : List Fm) :
    ∀ N : List Fm, (∀ ψ ∈ N, ψ ∈ M) → FProof p F (projLines (.and M) Δ N) := by
  intro N
  induction N with
  | nil => intro _ k hk; simp [projLines] at hk
  | cons ψ N ih =>
      intro hN
      refine fproof_append ?_ (ih fun χ hχ => hN χ (by simp [hχ]))
      have q0 : FProof p F [([ψ], [ψ])] := by
        intro k hk; simp at hk; subst hk; exact step_ax ψ
      have q1 := fproof_snoc (S := ([ψ], ψ :: Δ)) q0
        (step_weak (T := ([ψ], [ψ])) (by simp) (by simp) (by simp))
      have q2 := fproof_snoc (S := ([.and M], ψ :: Δ)) q1
        (step_andL M [] (ψ :: Δ) ψ (hN ψ (by simp)) (by simp))
      simpa using q2

theorem projLines_mem (A : Fm) (Δ : List Fm) :
    ∀ N : List Fm, ∀ ψ ∈ N, ([A], ψ :: Δ) ∈ projLines A Δ N := by
  intro N
  induction N with
  | nil => intro ψ h; simp at h
  | cons χ N ih =>
      intro ψ h
      rcases List.mem_cons.1 h with rfl | h
      · simp [projLines]
      · simp only [projLines, List.cons_append, List.mem_cons]
        exact Or.inr (Or.inr (Or.inr (ih ψ h)))

theorem projLines_length (A : Fm) (Δ : List Fm) :
    ∀ N : List Fm, (projLines A Δ N).length = 3 * N.length := by
  intro N
  induction N with
  | nil => rfl
  | cons ψ N ih => simp [projLines, ih]; ring

theorem projLines_good {S : Seq} (A : Fm) (δ : Fm) (hA : Sub S A) (hδ : Sub S δ) :
    ∀ N : List Fm, (∀ ψ ∈ N, Sub S ψ) → ∀ T ∈ projLines A [δ] N, Good S T := by
  intro N
  induction N with
  | nil => intro _ T hT; simp [projLines] at hT
  | cons ψ N ih =>
      intro hN T hT
      have hψ := hN ψ (by simp)
      simp only [projLines, List.cons_append, List.mem_cons] at hT
      rcases hT with rfl | rfl | rfl | hT
      · exact good_short (by simp) (allSub2 hψ hψ)
      · exact good_short (by simp) (allSub3 hψ hψ hδ)
      · exact good_short (by simp) (allSub3 hA hψ hδ)
      · exact ih (fun χ hχ => hN χ (by simp [hχ])) T hT

/-! ## One block per line -/

/-- The block of `S`: a proof segment ending in `sigS S`. -/
def BlockOK (p : ℕ) (F : CNF) (L : List Seq) (S : Seq) (B : List Seq) : Prop :=
  FProof p F (L ++ B) ∧ sigS S ∈ L ++ B ∧ (∀ T ∈ B, Good S T) ∧
    (B = [sigS S] ∨ (1 ≤ seqSize S ∧ B.length ≤ 3 * seqSize S + 6))

theorem block_one {L : List Seq} {S : Seq} (hL : FProof p F L) (h : FStep p F L (sigS S)) :
    ∃ B, BlockOK p F L S B :=
  ⟨[sigS S], fproof_snoc hL h, by simp, by simp [good_sigS], Or.inl rfl⟩

theorem one_le_seqSize {S : Seq} {φ : Fm} (h : φ ∈ S.1 ++ S.2) : 1 ≤ seqSize S :=
  (one_le_size φ).trans (size_le_seq h)

theorem block_orNil {L : List Seq} {S : Seq} {r : ℕ} {l : List Fm} (hL : FProof p F L)
    (hmod : Fm.mod r l ∈ S.1 ++ S.2) (hm : Fm.or [] ∈ (sigS S).1) : ∃ B, BlockOK p F L S B := by
  refine ⟨[([.or []], []), sigS S], ?_, by simp, ?_, Or.inr ⟨one_le_seqSize hmod, by
    simp only [List.length_cons, List.length_nil]; omega⟩⟩
  · have q1 := fproof_snoc (S := ([.or []], [])) hL step_orNil
    have q2 := fproof_snoc (S := sigS S) q1
      (step_weak (T := ([.or []], [])) (by simp) (by simpa using hm) (by simp))
    simpa using q2
  · intro T hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact good_short (by simp) (allSub1 (sub_orNil hmod))
    · exact good_sigS S

theorem length_le_seq {S : Seq} {r : ℕ} {l : List Fm} (h : Fm.mod r l ∈ S.1 ++ S.2) :
    l.length + 1 ≤ seqSize S := by
  have := length_lt_mod (r := r) (l := l); have := size_le_seq h; omega

/-- Axiom `MOD_r(φ :: l), φ ⊢ MOD_{r+p-1}(l)`, `r = 0`. -/
theorem block_a3 {L : List Seq} (hL : FProof p F L) (φ : Fm) (l : List Fm) :
    ∃ B, BlockOK p F L ([.mod 0 (φ :: l), φ], [.mod (0 + p - 1) l]) B := by
  set S : Seq := ([.mod 0 (φ :: l), φ], [.mod (0 + p - 1) l])
  set A := sig (.mod 0 (φ :: l))
  have hA : A = .and (.neg (sig φ) :: l.map fun χ => .neg (sig χ)) := by
    simp only [A, sig_mod0, List.map_cons]
  have eS : sigS S = ([A, sig φ], [sig (.mod (0 + p - 1) l)]) := rfl
  have hmA : Fm.mod 0 (φ :: l) ∈ S.1 ++ S.2 := by simp [S]
  have hmφ : φ ∈ S.1 ++ S.2 := by simp [S]
  refine ⟨[([sig φ], [sig φ]), ([.neg (sig φ), sig φ], []), ([A, sig φ], []), sigS S],
    ?_, by simp, ?_, Or.inr ⟨one_le_seqSize hmA, by
      simp only [List.length_cons, List.length_nil]; omega⟩⟩
  · have q1 := fproof_snoc hL (step_ax (sig φ))
    have q2 := fproof_snoc q1 (step_negL (sig φ) [sig φ] [] (by simp))
    have q3 := fproof_snoc (S := ([A, sig φ], [])) q2 (by
      rw [hA]; exact step_andL _ [sig φ] [] (.neg (sig φ)) (by simp) (by simp))
    have q4 := fproof_snoc (S := sigS S) q3
      (step_weak (T := ([A, sig φ], [])) (by simp) (by simp [eS]) (by simp))
    simpa using q4
  · intro T hT
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl | rfl
    · exact good_short (by simp) (allSub2 (sub_sig hmφ) (sub_sig hmφ))
    · exact good_short (by simp) (allSub2 (sub_neg_sig hmφ) (sub_sig hmφ))
    · exact good_short (by simp) (allSub2 (sub_sig hmA) (sub_sig hmφ))
    · exact good_sigS S

/-- Axiom `MOD_r(φ :: l) ⊢ φ, MOD_r(l)`, `r = 0`. -/
theorem block_a4 {L : List Seq} (hL : FProof p F L) (φ : Fm) (l : List Fm) :
    ∃ B, BlockOK p F L ([.mod 0 (φ :: l)], [φ, .mod 0 l]) B := by
  set S : Seq := ([.mod 0 (φ :: l)], [φ, .mod 0 l])
  set N := l.map fun χ => Fm.neg (sig χ)
  set A := sig (.mod 0 (φ :: l))
  set AN := sig (.mod 0 l)
  have hA : A = .and (.neg (sig φ) :: N) := by simp only [A, N, sig_mod0, List.map_cons]
  have hAN : AN = .and N := by simp only [AN, N, sig_mod0]
  have eS : sigS S = ([A], [sig φ, AN]) := rfl
  have hmA : Fm.mod 0 (φ :: l) ∈ S.1 ++ S.2 := by simp [S]
  have hmAN : Fm.mod 0 l ∈ S.1 ++ S.2 := by simp [S]
  have hmφ : φ ∈ S.1 ++ S.2 := by simp [S]
  have hN : ∀ ψ ∈ N, Sub S ψ := by
    intro ψ hψ; obtain ⟨χ, hχ, rfl⟩ := List.mem_map.1 hψ
    exact sub_arg hmA (by simp [hχ])
  refine ⟨projLines A [sig φ] N ++ [([A], [AN, sig φ]), sigS S], ?_, by simp, ?_,
    Or.inr ⟨one_le_seqSize hmA, ?_⟩⟩
  · have q0 := fproof_append (L2 := projLines A [sig φ] N) hL (by
      rw [hA]; exact projLines_proof (p := p) (F := F) (.neg (sig φ) :: N) [sig φ] N
        (fun ψ hψ => by simp [hψ]))
    have q1 := fproof_snoc (S := ([A], [AN, sig φ])) q0 (by
      rw [hAN]
      exact step_andR N [A] [sig φ] (fun ψ hψ =>
        List.mem_append_right _ (projLines_mem A [sig φ] N ψ hψ)))
    have q2 := fproof_snoc (S := sigS S) q1
      (step_weak (T := ([A], [AN, sig φ])) (by simp) (by simp [eS]) (by
        rw [eS]; intro χ hχ; simp at hχ ⊢; tauto))
    simpa using q2
  · intro T hT
    rcases List.mem_append.1 hT with hT | hT
    · exact projLines_good A (sig φ) (sub_sig hmA) (sub_sig hmφ) N hN T hT
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl
      · exact good_short (by simp) (allSub3 (sub_sig hmA) (sub_sig hmAN) (sub_sig hmφ))
      · exact good_sigS S
  · have := length_le_seq hmAN
    simp [projLines_length, N]; omega

/-- Axiom `MOD_r(l) ⊢ φ, MOD_r(φ :: l)`, `r = 0`. -/
theorem block_a6 {L : List Seq} (hL : FProof p F L) (φ : Fm) (l : List Fm) :
    ∃ B, BlockOK p F L ([.mod 0 l], [φ, .mod 0 (φ :: l)]) B := by
  set S : Seq := ([.mod 0 l], [φ, .mod 0 (φ :: l)])
  set N := l.map fun χ => Fm.neg (sig χ)
  set A := sig (.mod 0 (φ :: l))
  set AN := sig (.mod 0 l)
  have hA : A = .and (.neg (sig φ) :: N) := by simp only [A, N, sig_mod0, List.map_cons]
  have hAN : AN = .and N := by simp only [AN, N, sig_mod0]
  have eS : sigS S = ([AN], [sig φ, A]) := rfl
  have hmA : Fm.mod 0 (φ :: l) ∈ S.1 ++ S.2 := by simp [S]
  have hmAN : Fm.mod 0 l ∈ S.1 ++ S.2 := by simp [S]
  have hmφ : φ ∈ S.1 ++ S.2 := by simp [S]
  have hN : ∀ ψ ∈ N, Sub S ψ := by
    intro ψ hψ; obtain ⟨χ, hχ, rfl⟩ := List.mem_map.1 hψ
    exact sub_arg hmAN hχ
  refine ⟨projLines AN [sig φ] N ++ [([sig φ], [sig φ]), ([], [.neg (sig φ), sig φ]),
    ([AN], [.neg (sig φ), sig φ]), ([AN], [A, sig φ]), sigS S], ?_, by simp, ?_,
    Or.inr ⟨one_le_seqSize hmA, ?_⟩⟩
  · have q0 := fproof_append (L2 := projLines AN [sig φ] N) hL (by
      rw [hAN]; exact projLines_proof (p := p) (F := F) N [sig φ] N (fun ψ hψ => hψ))
    have q1 := fproof_snoc q0 (step_ax (sig φ))
    have q2 := fproof_snoc q1 (step_negR (sig φ) [] [sig φ] (by simp))
    have q3 := fproof_snoc (S := ([AN], [.neg (sig φ), sig φ])) q2
      (step_weak (T := ([], [.neg (sig φ), sig φ])) (by simp) (by simp) (by simp))
    have q4 := fproof_snoc (S := ([AN], [A, sig φ])) q3 (by
      rw [hA]
      refine step_andR _ [AN] [sig φ] (fun ψ hψ => ?_)
      rcases List.mem_cons.1 hψ with rfl | hψ
      · simp
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (projLines_mem AN [sig φ] N ψ hψ)))))
    have q5 := fproof_snoc (S := sigS S) q4
      (step_weak (T := ([AN], [A, sig φ])) (by simp) (by simp [eS]) (by
        rw [eS]; intro χ hχ; simp at hχ ⊢; tauto))
    simpa using q5
  · intro T hT
    rcases List.mem_append.1 hT with hT | hT
    · exact projLines_good AN (sig φ) (sub_sig hmAN) (sub_sig hmφ) N hN T hT
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl | rfl
      · exact good_short (by simp) (allSub2 (sub_sig hmφ) (sub_sig hmφ))
      · exact good_short (by simp) (allSub2 (sub_neg_sig hmφ) (sub_sig hmφ))
      · exact good_short (by simp) (allSub3 (sub_sig hmAN) (sub_neg_sig hmφ) (sub_sig hmφ))
      · exact good_short (by simp) (allSub3 (sub_sig hmAN) (sub_sig hmA) (sub_sig hmφ))
      · exact good_sigS S
  · have := length_le_seq hmAN
    simp [projLines_length, N]; omega

/-- Every line of a proof, translated, gets a short MOD-free block. -/
theorem block (hp : 2 ≤ p) {prev L : List Seq} {S : Seq} (h : FStep p F prev S)
    (hL : FProof p F L) (hprev : ∀ T ∈ prev, sigS T ∈ L) : ∃ B, BlockOK p F L S B := by
  rcases h with ⟨C, hC, rfl⟩ | ⟨φ, rfl⟩ | rfl | rfl | rfl | ⟨r, hr, rfl⟩ | ⟨r, φ, l, rfl⟩ |
      ⟨r, φ, l, rfl⟩ | ⟨r, φ, l, rfl⟩ | ⟨r, φ, l, rfl⟩ | ⟨T, hT, h1, h2⟩ | ⟨φ, h1, h2⟩ |
      ⟨φ, Γ, Δ, rfl, h1⟩ | ⟨φ, Γ, Δ, rfl, h1⟩ | ⟨l, Γ, Δ, φ, hφ, rfl, h1⟩ | ⟨l, Γ, Δ, rfl, h1⟩ |
      ⟨l, Γ, Δ, rfl, h1⟩ | ⟨l, Γ, Δ, φ, hφ, rfl, h1⟩
  · refine block_one hL ?_
    have : sigS ([], [clauseFm C]) = ([], [clauseFm C]) := by simp [sigS, sig_clauseFm]
    rw [this]; exact step_hyp hC
  · exact block_one hL (step_ax (sig φ))
  · refine block_one hL ?_
    have : sigS ([], [.and []]) = ([], [.and []]) := by simp [sigS, sig_and]
    rw [this]; exact step_andNil
  · refine block_one hL ?_
    have : sigS ([.or []], []) = ([.or []], []) := by simp [sigS, sig_or]
    rw [this]; exact step_orNil
  · refine block_one hL ?_
    have : sigS ([], [.mod 0 []]) = ([], [.and []]) := by simp [sigS, sig_mod0]
    rw [this]; exact step_andNil
  · have hr0 : r ≠ 0 := by rintro rfl; simp at hr
    refine block_one hL ?_
    have : sigS ([.mod r []], []) = ([.or []], []) := by simp [sigS, sig_modr hr0]
    rw [this]; exact step_orNil
  · by_cases hr0 : r = 0
    · subst hr0; exact block_a3 hL φ l
    · exact block_orNil (r := r) (l := φ :: l) hL (by simp) (by simp [sigS, sig_modr hr0])
  · by_cases hr0 : r = 0
    · subst hr0; exact block_a4 hL φ l
    · exact block_orNil (r := r) (l := φ :: l) hL (by simp) (by simp [sigS, sig_modr hr0])
  · have hr0 : r + p - 1 ≠ 0 := by omega
    exact block_orNil (r := r + p - 1) (l := l) hL (by simp) (by simp [sigS, sig_modr hr0])
  · by_cases hr0 : r = 0
    · subst hr0; exact block_a6 hL φ l
    · exact block_orNil (r := r) (l := l) hL (by simp) (by simp [sigS, sig_modr hr0])
  · exact block_one hL (step_weak (hprev T hT) (List.map_subset sig h1) (List.map_subset sig h2))
  · exact block_one hL (step_cut (sig φ) (hprev _ h1) (hprev _ h2))
  · refine block_one hL ?_
    have : sigS (.neg φ :: Γ, Δ) = (.neg (sig φ) :: Γ.map sig, Δ.map sig) := by
      simp [sigS, sig_neg]
    rw [this]; exact step_negL (sig φ) _ _ (hprev _ h1)
  · refine block_one hL ?_
    have : sigS (Γ, .neg φ :: Δ) = (Γ.map sig, .neg (sig φ) :: Δ.map sig) := by
      simp [sigS, sig_neg]
    rw [this]; exact step_negR (sig φ) _ _ (hprev _ h1)
  · refine block_one hL ?_
    have : sigS (.and l :: Γ, Δ) = (.and (l.map sig) :: Γ.map sig, Δ.map sig) := by
      simp [sigS, sig_and]
    rw [this]; exact step_andL _ _ _ (sig φ) (List.mem_map_of_mem hφ) (hprev _ h1)
  · refine block_one hL ?_
    have : sigS (Γ, .and l :: Δ) = (Γ.map sig, .and (l.map sig) :: Δ.map sig) := by
      simp [sigS, sig_and]
    rw [this]
    refine step_andR _ _ _ (fun ψ hψ => ?_)
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hψ
    exact hprev _ (h1 φ hφ)
  · refine block_one hL ?_
    have : sigS (.or l :: Γ, Δ) = (.or (l.map sig) :: Γ.map sig, Δ.map sig) := by
      simp [sigS, sig_or]
    rw [this]
    refine step_orL _ _ _ (fun ψ hψ => ?_)
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hψ
    exact hprev _ (h1 φ hφ)
  · refine block_one hL ?_
    have : sigS (Γ, .or l :: Δ) = (Γ.map sig, .or (l.map sig) :: Δ.map sig) := by
      simp [sigS, sig_or]
    rw [this]; exact step_orR _ _ _ (sig φ) (List.mem_map_of_mem hφ) (hprev _ h1)

theorem seqSize_sigS (S : Seq) : seqSize (sigS S) ≤ 2 * seqSize S := by
  have := (good_sigS S).2
  have e : (sigS S).1 ++ (sigS S).2 = (S.1 ++ S.2).map sig := by simp [sigS]
  unfold seqSize; rw [e, List.map_map]
  have := sum_map_le (l := S.1 ++ S.2) (f := Fm.size ∘ sig) (g := fun φ => 2 * φ.size)
    (fun φ _ => by have := size_sig φ; simp only [Function.comp]; omega)
  have h2 : ((S.1 ++ S.2).map fun φ => 2 * φ.size).sum = 2 * ((S.1 ++ S.2).map Fm.size).sum := by
    rw [List.sum_map_mul_left]
  omega

theorem blockOK_size {L : List Seq} {S : Seq} {B : List Seq} (h : BlockOK p F L S B) :
    fSize B ≤ 81 * seqSize S ^ 2 ∧ B.length ≤ 9 * seqSize S + 1 := by
  rcases h.2.2.2 with rfl | ⟨h1, h2⟩
  · rw [fSize_single]
    have := seqSize_sigS S
    constructor
    · have := Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) (seqSize S); omega
    · simp
  · have := fSize_le B (6 * seqSize S + 3) (fun T hT => (h.2.2.1 T hT).2)
    constructor
    · have h3 : B.length * (6 * seqSize S + 3) ≤ (3 * seqSize S + 6) * (6 * seqSize S + 3) :=
        Nat.mul_le_mul_right _ h2
      nlinarith
    · omega

theorem fproof_init {L : List Seq} {S : Seq} (h : FProof p F (L ++ [S])) :
    FProof p F L ∧ FStep p F L S := by
  constructor
  · intro k hk
    have := h k (by simp; omega)
    rw [List.take_append_of_le_length hk.le] at this
    simpa [List.getElem_append_left hk] using this
  · have := h L.length (by simp)
    simpa using this

/-! ## MOD elimination -/

/-- MOD elimination: every `FProof` from `F` becomes a MOD-free `FProof` from `F` containing the
translation of each line, of no larger depth, with at most `9 fSize L + |L|` lines and
`fSize L' ≤ 81 (fSize L)^2`. -/
theorem elim_mod (hp : 2 ≤ p) (L : List Seq) (hL : FProof p F L) :
    ∃ L' : List Seq, FProof p F L' ∧ (∀ S ∈ L, sigS S ∈ L') ∧
      (∀ T ∈ L', ∀ ψ ∈ T.1 ++ T.2, noMod ψ = true) ∧
      (∀ d, FDepthLe d L → FDepthLe d L') ∧
      L'.length ≤ 9 * fSize L + L.length ∧ fSize L' ≤ 81 * fSize L ^ 2 := by
  induction L using List.reverseRecOn with
  | nil =>
      refine ⟨[], fun k hk => by simp at hk, by simp, by simp, fun d _ S hS => by simp at hS,
        by simp, by simp [fSize_eq]⟩
  | append_singleton L S ih =>
      obtain ⟨hL0, hS⟩ := fproof_init hL
      obtain ⟨L', h1, h2, h3, h4, h5, h6⟩ := ih hL0
      obtain ⟨B, hB⟩ := block hp hS h1 h2
      obtain ⟨s1, s2⟩ := blockOK_size hB
      obtain ⟨b1, b2, b3, -⟩ := hB
      refine ⟨L' ++ B, b1, ?_, ?_, ?_, ?_, ?_⟩
      · intro T hT
        rcases List.mem_append.1 hT with hT | hT
        · exact List.mem_append_left _ (h2 T hT)
        · simp at hT; subst hT; exact b2
      · intro T hT ψ hψ
        rcases List.mem_append.1 hT with hT | hT
        · exact h3 T hT ψ hψ
        · exact ((b3 T hT).1 ψ hψ).1
      · intro d hd
        have hd0 : FDepthLe d L := fun T hT => hd T (List.mem_append_left _ hT)
        have hdS : ∀ φ ∈ S.1 ++ S.2, φ.depth ≤ d := hd S (by simp)
        intro T hT
        rcases List.mem_append.1 hT with hT | hT
        · exact h4 d hd0 T hT
        · exact fun ψ hψ => ((b3 T hT).1 ψ hψ).2 d hdS
      · rw [List.length_append, fSize_append, fSize_single, List.length_append]
        simp only [List.length_singleton]; omega
      · rw [fSize_append, fSize_append, fSize_single]
        have key : 81 * fSize L ^ 2 + 81 * seqSize S ^ 2 ≤ 81 * (fSize L + seqSize S) ^ 2 := by
          nlinarith [Nat.zero_le (fSize L * seqSize S)]
        omega

/-- MOD elimination for refutations: `FRefutes p d F L` gives a MOD-free `FRefutes p d F L'`
with `fSize L' ≤ 81 (fSize L)^2` (`p ≥ 2`). -/
theorem frefutes_elim_mod (hp : 2 ≤ p) {d : ℕ} {L : List Seq} (h : FRefutes p d F L) :
    ∃ L' : List Seq, FRefutes p d F L' ∧ (∀ T ∈ L', ∀ ψ ∈ T.1 ++ T.2, noMod ψ = true) ∧
      L'.length ≤ 9 * fSize L + L.length ∧ fSize L' ≤ 81 * fSize L ^ 2 := by
  obtain ⟨hL, hd, he⟩ := h
  obtain ⟨L', h1, h2, h3, h4, h5, h6⟩ := elim_mod hp L hL
  exact ⟨L', ⟨h1, h4 d hd, h2 _ he⟩, h3, h5, h6⟩

/-- The MOD-free analogue of `AC0pFregeLB`: a super polynomial lower bound for bounded depth
Frege (unbounded fan in `AND`, `OR`) at every fixed depth, on one polynomial size family. -/
def BDFregeLB (p : ℕ) : Prop :=
  ∃ Fam : ℕ → CNF, (∃ c0 : ℕ, ∀ n, cnfSize (Fam n) ≤ (n + 1) ^ c0) ∧
    (∀ n, ¬ Satisfiable (Fam n)) ∧
    ∀ d c : ℕ, ∃ N, ∀ n ≥ N, ∀ L, FRefutes p d (Fam n) L →
      (∀ T ∈ L, ∀ ψ ∈ T.1 ++ T.2, noMod ψ = true) → n ^ c < fSize L

/-- The pinned R4 target is equivalent to its MOD-free special case: for `p ≥ 2`,
`AC0pFregeLB p ↔ BDFregeLB p`. -/
theorem ac0pFregeLB_iff (hp : 2 ≤ p) : AC0pFregeLB p ↔ BDFregeLB p := by
  constructor
  · rintro ⟨Fam, h1, h2, h3⟩
    refine ⟨Fam, h1, h2, fun d c => ?_⟩
    obtain ⟨N, hN⟩ := h3 d c
    exact ⟨N, fun n hn L hL _ => hN n hn L hL⟩
  · rintro ⟨Fam, h1, h2, h3⟩
    refine ⟨Fam, h1, h2, fun d c => ?_⟩
    obtain ⟨N, hN⟩ := h3 d (2 * c + 7)
    refine ⟨max N 2, fun n hn L hL => ?_⟩
    obtain ⟨L', hL', hm, -, hs⟩ := frefutes_elim_mod hp hL
    have hlt := hN n (le_of_max_le_left hn) L' hL' hm
    by_contra hle
    have hle : fSize L ≤ n ^ c := Nat.not_lt.1 hle
    have hn2 : 2 ≤ n := le_of_max_le_right hn
    have h7 : 81 < n ^ 7 := by
      calc 81 < 2 ^ 7 := by norm_num
        _ ≤ n ^ 7 := Nat.pow_le_pow_left hn2 7
    have hsq : fSize L ^ 2 ≤ (n ^ c) ^ 2 := Nat.pow_le_pow_left hle 2
    have hpos : 0 < (n ^ c) ^ 2 := by positivity
    have hbig : 81 * fSize L ^ 2 < n ^ (2 * c + 7) :=
      calc 81 * fSize L ^ 2 ≤ 81 * (n ^ c) ^ 2 := Nat.mul_le_mul_left 81 hsq
        _ < n ^ 7 * (n ^ c) ^ 2 := Nat.mul_lt_mul_of_pos_right h7 hpos
        _ = n ^ (2 * c + 7) := by ring
    omega

end FModElim

end SATurday.ProofComplexity
