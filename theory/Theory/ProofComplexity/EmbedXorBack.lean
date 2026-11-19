import Theory.ProofComplexity.EmbedXorLin

/-!
# Removing semantic weakening over `F_2`: `RL.DagRefutes` into `RLDag` over `F_2`

Referee leftover (dossier Section 17, item 1): the converse of `RLF.rldag2_to_dagRefutes`.
`RL.DagRefutes` (ResLinDag.lean) is dag-like `Res(⊕)` with *semantic* weakening (`Imp L0 L`: every
point of `F_2^ℕ` satisfying `L0` satisfies `L`) and a resolution rule applied to semantic
weakenings of the premises.  `RLF.RLDag` over `ZMod 2` is the syntactic Part-Tzameret system.

Over `F_2` every point of `F_2^ℕ` is Boolean, so semantic implication between linear clauses is
linear algebra: if `g` is an equation of `L0` and `L0 ⊨ L`, the system `g = 0`, `e ≠ 0`
(`e ∈ L`) has no solution, and (`decomp`, via a separating functional) some sum
`β g + Σ_{e ∈ T} ¬e` (`T ⊆ L`, `¬e` the negated equation) is the false constant `0 = 1`.
The equation `g` is then eliminated syntactically by `|T|` linear combinations with the lines
`e ∨ ¬e` and one deletion of `0 = 1` (`r_elim`); the lines `f = 0 ∨ f = 1` are derived from the
Boolean axioms with at most `12 |supp f| + 5` lines (`r_taut`).

Main results:
* `RLF.r_wsim`: one semantic weakening `M0 ⊨ L` costs at most
  `|L| (12 N + 5) + |M0| (|L| + 1) + 1` lines of `RLDag`, `N` a bound on the support sizes in `L`;
* `RLF.dagRefutes_to_rldag2`: a `Res(⊕)` refutation (a derivation `P` with `∅ ∈ P`) all of whose
  lines have at most `W` equations, each with at most `N` variables, gives an `RLDag` refutation
  from `Ax2 Φ ∪ boolAx` with at most `xorBackCost W N * |P|` lines, where
  `xorBackCost W N = 2 ((W+1)(12 (N + 4 W N) + 5) + W (W + 2) + 1) + 3`, i.e. `O(W² N)` per line.

The overhead is polynomial in the symbol size of the `Res(⊕)` refutation, not in its number of
lines alone (a line of `Res(⊕)` may have many equations).  Only `F_2` is treated; over `F_p`,
`p > 2`, semantic weakening on the Boolean cube is not linear algebra and is not addressed.
-/

open SATurday.ProofComplexity

namespace SATurday.ProofComplexity

namespace RLF

noncomputable section

open Classical

local instance instDecEqLEq2b : DecidableEq (LEq (ZMod 2)) := leqDec (ZMod 2)

/-- Lines of `RLDag` over `F_2`. -/
abbrev Ln2 := Finset (LEq (ZMod 2))

/-! ## Extensions of a derivation -/

/-- `𝓛'` is a derivation containing `𝓛` with at most `c` more lines. -/
def Ext2 (Ax : Set Ln2) (𝓛 𝓛' : Finset Ln2) (c : ℕ) : Prop :=
  RLDag Ax 𝓛' ∧ 𝓛 ⊆ 𝓛' ∧ 𝓛'.card ≤ 𝓛.card + c

variable {Ax : Set Ln2}

theorem Ext2.refl {𝓛 : Finset Ln2} (h : RLDag Ax 𝓛) : Ext2 Ax 𝓛 𝓛 0 :=
  ⟨h, Finset.Subset.refl _, le_rfl⟩

theorem Ext2.trans {𝓛 𝓛₂ 𝓛₃ : Finset Ln2} {c c' : ℕ} (h : Ext2 Ax 𝓛 𝓛₂ c)
    (h' : Ext2 Ax 𝓛₂ 𝓛₃ c') : Ext2 Ax 𝓛 𝓛₃ (c + c') :=
  ⟨h'.1, h.2.1.trans h'.2.1, by have := h.2.2; have := h'.2.2; omega⟩

theorem Ext2.mono {𝓛 𝓛₂ : Finset Ln2} {c c' : ℕ} (h : Ext2 Ax 𝓛 𝓛₂ c) (hc : c ≤ c') :
    Ext2 Ax 𝓛 𝓛₂ c' :=
  ⟨h.1, h.2.1, h.2.2.trans (by omega)⟩

theorem ext_insert {𝓛 : Finset Ln2} {X : Ln2} (h : RLDag Ax (insert X 𝓛)) :
    Ext2 Ax 𝓛 (insert X 𝓛) 1 :=
  ⟨h, Finset.subset_insert _ _, Finset.card_insert_le _ _⟩

theorem r_ax {𝓛 : Finset Ln2} (h : RLDag Ax 𝓛) {C : Ln2} (hC : C ∈ Ax) :
    ∃ 𝓛', Ext2 Ax 𝓛 𝓛' 1 ∧ C ∈ 𝓛' :=
  ⟨_, ext_insert (RLDag.ax C h hC), Finset.mem_insert_self _ _⟩

theorem r_weak {𝓛 : Finset Ln2} (h : RLDag Ax 𝓛) {L L' : Ln2} (hL : L ∈ 𝓛) (hs : L ⊆ L') :
    ∃ 𝓛', Ext2 Ax 𝓛 𝓛' 1 ∧ L' ∈ 𝓛' :=
  ⟨_, ext_insert (RLDag.weak L L' h hL hs), Finset.mem_insert_self _ _⟩

theorem r_comb {𝓛 : Finset Ln2} (h : RLDag Ax 𝓛) {A B : Ln2} {e1 e2 : LEq (ZMod 2)}
    (α β : ZMod 2) (hA : A ∈ 𝓛) (hB : B ∈ 𝓛) (h1 : e1 ∈ A) (h2 : e2 ∈ B) :
    ∃ 𝓛', Ext2 Ax 𝓛 𝓛' 1 ∧ (A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2}) ∈ 𝓛' :=
  ⟨_, ext_insert (RLDag.comb A B e1 e2 α β h hA hB h1 h2), Finset.mem_insert_self _ _⟩

/-- The false equation `0 = 1`. -/
def fz : LEq (ZMod 2) := (0, 1)

theorem r_simp {𝓛 : Finset Ln2} (h : RLDag Ax 𝓛) {M : Ln2} (hM : M ∈ 𝓛) (h0 : fz ∈ M) :
    ∃ 𝓛', Ext2 Ax 𝓛 𝓛' 1 ∧ M.erase fz ∈ 𝓛' := by
  have : insert ((0 : ℕ →₀ ZMod 2), (1 : ZMod 2)) (M.erase fz) ∈ 𝓛 := by
    have e : ((0 : ℕ →₀ ZMod 2), (1 : ZMod 2)) = fz := rfl
    rw [e, Finset.insert_erase h0]; exact hM
  exact ⟨_, ext_insert (RLDag.simp (M.erase fz) 1 h one_ne_zero this), Finset.mem_insert_self _ _⟩

theorem mem_comb {A B : Ln2} {e1 e2 c y : LEq (ZMod 2)} :
    y ∈ A.erase e1 ∪ B.erase e2 ∪ {c} ↔ (y ≠ e1 ∧ y ∈ A) ∨ (y ≠ e2 ∧ y ∈ B) ∨ y = c := by
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, or_assoc, ne_eq]

theorem comb_sub {A B X : Ln2} {e1 e2 c : LEq (ZMod 2)} (hA : ∀ y ∈ A, y ≠ e1 → y ∈ X)
    (hB : ∀ y ∈ B, y ≠ e2 → y ∈ X) (hc : c ∈ X) : A.erase e1 ∪ B.erase e2 ∪ {c} ⊆ X := by
  intro y hy
  rcases mem_comb.1 hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ | rfl
  · exact hA y h2 h1
  · exact hB y h2 h1
  · exact hc

/-! ## Arithmetic over `F_2` -/

theorem z2_two : (1 : ZMod 2) + 1 = 0 := by decide

theorem add_self2 (c : ℕ →₀ ZMod 2) : c + c = 0 := by
  ext i
  simp only [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply]
  generalize c i = t; revert t; decide

theorem cmb11 (e1 e2 : LEq (ZMod 2)) : cmb 1 1 e1 e2 = e1 + e2 := by
  unfold cmb; ext <;> simp

theorem cmb00 (e1 e2 : LEq (ZMod 2)) : cmb 0 0 e1 e2 = ((0 : ℕ →₀ ZMod 2), (0 : ZMod 2)) := by
  unfold cmb; ext <;> simp

/-- The negated equation. -/
def ng (e : LEq (ZMod 2)) : LEq (ZMod 2) := (e.1, e.2 + 1)

/-- The tautological line `f = 0 ∨ f = 1`. -/
def tl (f : ℕ →₀ ZMod 2) : Ln2 := {(f, 0), (f, 1)}

theorem z2_cases' : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem mem_tl (e : LEq (ZMod 2)) : e ∈ tl e.1 := by
  rcases z2_cases' e.2 with h | h
  · simp [tl, ← h]
  · simp [tl, ← h]

theorem ng_mem_tl (e : LEq (ZMod 2)) : ng e ∈ tl e.1 := by
  rcases z2_cases' e.2 with h | h
  · simp [tl, ng, h]
  · simp [tl, ng, h, z2_two]

theorem tl_sub (e : LEq (ZMod 2)) : ∀ y ∈ tl e.1, y = e ∨ y = ng e := by
  intro y hy
  simp only [tl, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases z2_cases' e.2 with h | h
  · rcases hy with rfl | rfl
    · left; ext <;> simp [h]
    · right; ext <;> simp [ng, h]
  · rcases hy with rfl | rfl
    · right; ext <;> simp [ng, h, z2_two]
    · left; ext <;> simp [h]

theorem ng_ne (e : LEq (ZMod 2)) : ng e ≠ e := by
  intro h
  have := congrArg Prod.snd h
  simp [ng] at this

/-! ## Steps with a membership predicate -/

theorem r_combP {𝓛 : Finset Ln2} (h : RLDag Ax 𝓛) {A B : Ln2} {e1 e2 : LEq (ZMod 2)}
    (α β : ZMod 2) (hA : A ∈ 𝓛) (hB : B ∈ 𝓛) (h1 : e1 ∈ A) (h2 : e2 ∈ B)
    {P : LEq (ZMod 2) → Prop} (hPA : ∀ y ∈ A, y ≠ e1 → P y) (hPB : ∀ y ∈ B, y ≠ e2 → P y)
    (hc : P (cmb α β e1 e2)) :
    ∃ 𝓛', Ext2 Ax 𝓛 𝓛' 1 ∧ ∃ M ∈ 𝓛', (∀ y ∈ M, P y) ∧ cmb α β e1 e2 ∈ M ∧
      (∀ y ∈ A, y ≠ e1 → y ∈ M) ∧ (∀ y ∈ B, y ≠ e2 → y ∈ M) := by
  obtain ⟨𝓛', E, m⟩ := r_comb h α β hA hB h1 h2
  refine ⟨𝓛', E, _, m, ?_, mem_comb.2 (Or.inr (Or.inr rfl)),
    fun y hy hne => mem_comb.2 (Or.inl ⟨hne, hy⟩), fun y hy hne => mem_comb.2 (Or.inr (Or.inl ⟨hne, hy⟩))⟩
  intro y hy
  rcases mem_comb.1 hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ | rfl
  · exact hPA y h2 h1
  · exact hPB y h2 h1
  · exact hc

theorem r_simpP {𝓛 : Finset Ln2} (h : RLDag Ax 𝓛) {M : Ln2} (hM : M ∈ 𝓛) (h0 : fz ∈ M) :
    ∃ 𝓛', Ext2 Ax 𝓛 𝓛' 1 ∧ ∃ M' ∈ 𝓛', (∀ y ∈ M', y ∈ M ∧ y ≠ fz) ∧
      (∀ y ∈ M, y ≠ fz → y ∈ M') := by
  obtain ⟨𝓛', E, m⟩ := r_simp h hM h0
  exact ⟨𝓛', E, _, m, fun y hy => (Finset.mem_erase.1 hy).symm,
    fun y hy hne => Finset.mem_erase.2 ⟨hne, hy⟩⟩

theorem r_sub {𝓛 : Finset Ln2} (h : RLDag Ax 𝓛) {M L : Ln2} (hM : M ∈ 𝓛) (hs : ∀ y ∈ M, y ∈ L) :
    ∃ 𝓛', Ext2 Ax 𝓛 𝓛' 1 ∧ L ∈ 𝓛' :=
  r_weak h hM hs

theorem mem_pair {u v y : LEq (ZMod 2)} (hy : y ∈ ({u, v} : Ln2)) : y = u ∨ y = v := by
  simpa using hy

/-! ## The lines `f = 0 ∨ f = 1` -/

theorem r_taut0 (hB : boolAx ⊆ Ax) {𝓛 : Finset Ln2} (h : RLDag Ax 𝓛) :
    ∃ 𝓛', Ext2 Ax 𝓛 𝓛' 5 ∧ tl 0 ∈ 𝓛' := by
  set x0 : LEq (ZMod 2) := (Finsupp.single 0 1, 0)
  set x1 : LEq (ZMod 2) := (Finsupp.single 0 1, 1)
  have hB0 : (boolCl 0 : Ln2) = {x0, x1} := rfl
  have h01 : x0 ≠ x1 := by intro e; have := congrArg Prod.snd e; simp [x0, x1] at this
  have z0 : ((0 : ℕ →₀ ZMod 2), (0 : ZMod 2)) ∈ tl 0 := by simp [tl]
  obtain ⟨𝓛1, E1, m1⟩ := r_ax h (hB (boolCl_mem_boolAx (F := ZMod 2) 0))
  rw [hB0] at m1
  obtain ⟨𝓛2, E2, M2, m2, p2, -, q2, -⟩ := r_combP E1.1 0 0 m1 m1 (e1 := x0) (e2 := x0)
    (by simp) (by simp) (P := fun y => y = x1 ∨ y ∈ tl 0)
    (fun y hy hne => by rcases mem_pair hy with rfl | rfl; exact absurd rfl hne; left; rfl)
    (fun y hy hne => by rcases mem_pair hy with rfl | rfl; exact absurd rfl hne; left; rfl)
    (by rw [cmb00]; right; exact z0)
  obtain ⟨𝓛3, E3, M3, m3, p3, -, q3, -⟩ := r_combP E2.1 0 0 (E2.2.1 m1) (E2.2.1 m1) (e1 := x1) (e2 := x1)
    (by simp) (by simp) (P := fun y => y = x0 ∨ y ∈ tl 0)
    (fun y hy hne => by rcases mem_pair hy with rfl | rfl; left; rfl; exact absurd rfl hne)
    (fun y hy hne => by rcases mem_pair hy with rfl | rfl; left; rfl; exact absurd rfl hne)
    (by rw [cmb00]; right; exact z0)
  have hx1 : x1 ∈ M2 := q2 x1 (by simp) (Ne.symm h01)
  have hx0 : x0 ∈ M3 := q3 x0 (by simp) h01
  obtain ⟨𝓛4, E4, M4, m4, p4, -, -, -⟩ := r_combP E3.1 1 1 (E3.2.1 m2) m3 hx1 hx0
    (P := fun y => y ∈ tl 0)
    (fun y hy hne => by rcases p2 y hy with rfl | h; exact absurd rfl hne; exact h)
    (fun y hy hne => by rcases p3 y hy with rfl | h; exact absurd rfl hne; exact h)
    (by rw [cmb11]; simp [tl, x0, x1, add_self2])
  obtain ⟨𝓛5, E5, m5⟩ := r_sub E4.1 m4 p4
  exact ⟨𝓛5, ((((E1.trans E2).trans E3).trans E4).trans E5).mono (by norm_num), m5⟩

theorem r_taut_step (hB : boolAx ⊆ Ax) {𝓛 : Finset Ln2} (h : RLDag Ax 𝓛) {f : ℕ →₀ ZMod 2}
    {i : ℕ} (hi : f i = 0) (hf : tl f ∈ 𝓛) :
    ∃ 𝓛', Ext2 Ax 𝓛 𝓛' 12 ∧ tl (f + Finsupp.single i 1) ∈ 𝓛' := by
  set s : ℕ →₀ ZMod 2 := Finsupp.single i 1
  set F := f + s
  set a : LEq (ZMod 2) := (f, 0)
  set a' : LEq (ZMod 2) := (f, 1)
  set b : LEq (ZMod 2) := (s, 0)
  set b' : LEq (ZMod 2) := (s, 1)
  set u : LEq (ZMod 2) := (F, 0)
  set u' : LEq (ZMod 2) := (F, 1)
  have hBi : (boolCl i : Ln2) = {b, b'} := rfl
  have htl : tl f = {a, a'} := rfl
  have hfs : f ≠ s := by intro e; have := congrArg (fun g => g i) e; simp [s, hi] at this
  have hs0 : s ≠ 0 := by intro e; have := congrArg (fun g => g i) e; simp [s] at this
  have haa : a ≠ a' := by intro e; have := congrArg Prod.snd e; simp [a, a'] at this
  have hbb : b ≠ b' := by intro e; have := congrArg Prod.snd e; simp [b, b'] at this
  have hab' : a' ≠ b' := by intro e; exact hfs (congrArg Prod.fst e)
  have hab : a' ≠ b := by intro e; have := congrArg Prod.snd e; simp [a', b] at this
  have hbz' : b' ≠ fz := by intro e; exact hs0 (congrArg Prod.fst e)
  have hbz : b ≠ fz := by intro e; have := congrArg Prod.snd e; simp [b, fz] at this
  have c1 : cmb 1 1 a b = u := by rw [cmb11]; rfl
  have c2 : cmb 1 1 a' b = u' := by rw [cmb11]; ext <;> simp [a', b, u', F]
  have c3 : cmb 1 1 a' a = fz := by rw [cmb11]; ext <;> simp [a', a, fz, add_self2]
  have c4 : cmb 1 1 a b' = u' := by rw [cmb11]; ext <;> simp [a, b', u', F]
  have c5 : cmb 1 1 a' b' = u := by rw [cmb11]; ext <;> simp [a', b', u, F, z2_two]
  have c6 : cmb 1 1 b' b = fz := by rw [cmb11]; ext <;> simp [b', b, fz, add_self2]
  have hu : u ∈ tl F := by simp [tl, u]
  have hu' : u' ∈ tl F := by simp [tl, u']
  obtain ⟨𝓛0, E0, m0⟩ := r_ax h (hB (boolCl_mem_boolAx (F := ZMod 2) i))
  rw [hBi] at m0
  have hf0 := E0.2.1 hf
  rw [htl] at hf0
  have ma : a ∈ ({a, a'} : Ln2) := by simp
  have ma' : a' ∈ ({a, a'} : Ln2) := by simp
  have mb : b ∈ ({b, b'} : Ln2) := by simp
  have mb' : b' ∈ ({b, b'} : Ln2) := by simp
  -- first half
  obtain ⟨𝓛1, E1, A1, m1, p1, -, q1, r1⟩ := r_combP E0.1 1 1 hf0 m0 ma mb
    (P := fun y => y = a' ∨ y = b' ∨ y = u)
    (fun y hy hne => by rcases mem_pair hy with rfl | rfl; exact absurd rfl hne; left; rfl)
    (fun y hy hne => by rcases mem_pair hy with rfl | rfl; exact absurd rfl hne; right; left; rfl)
    (by rw [c1]; right; right; rfl)
  obtain ⟨𝓛2, E2, A2, m2, p2, -, q2, -⟩ := r_combP E1.1 1 1 (E1.2.1 hf0) (E1.2.1 m0) ma' mb
    (P := fun y => y = a ∨ y = b' ∨ y = u')
    (fun y hy hne => by rcases mem_pair hy with rfl | rfl; left; rfl; exact absurd rfl hne)
    (fun y hy hne => by rcases mem_pair hy with rfl | rfl; exact absurd rfl hne; right; left; rfl)
    (by rw [c2]; right; right; rfl)
  obtain ⟨𝓛3, E3, A3, m3, p3, z3, q3, -⟩ := r_combP E2.1 1 1 (E2.2.1 m1) m2
    (q1 a' ma' (Ne.symm haa)) (q2 a ma haa)
    (P := fun y => y = b' ∨ y ∈ tl F ∨ y = fz)
    (fun y hy hne => by
      rcases p1 y hy with rfl | rfl | rfl
      · exact absurd rfl hne
      · left; rfl
      · right; left; exact hu)
    (fun y hy hne => by
      rcases p2 y hy with rfl | rfl | rfl
      · exact absurd rfl hne
      · left; rfl
      · right; left; exact hu')
    (by rw [c3]; right; right; rfl)
  rw [c3] at z3
  obtain ⟨𝓛4, E4, A4, m4, p4, q4⟩ := r_simpP E3.1 m3 z3
  have hb'4 : b' ∈ A4 := q4 b' (q3 b' (r1 b' mb' (Ne.symm hbb)) (Ne.symm hab')) hbz'
  -- second half
  obtain ⟨𝓛5, E5, A5, m5, p5, -, q5, r5⟩ := r_combP E4.1 1 1 (E4.2.1 (E3.2.1 (E2.2.1 (E1.2.1 hf0))))
    (E4.2.1 (E3.2.1 (E2.2.1 (E1.2.1 m0)))) ma mb'
    (P := fun y => y = a' ∨ y = b ∨ y = u')
    (fun y hy hne => by rcases mem_pair hy with rfl | rfl; exact absurd rfl hne; left; rfl)
    (fun y hy hne => by rcases mem_pair hy with rfl | rfl; right; left; rfl; exact absurd rfl hne)
    (by rw [c4]; right; right; rfl)
  obtain ⟨𝓛6, E6, A6, m6, p6, -, q6, -⟩ := r_combP E5.1 1 1
    (E5.2.1 (E4.2.1 (E3.2.1 (E2.2.1 (E1.2.1 hf0))))) (E5.2.1 (E4.2.1 (E3.2.1 (E2.2.1 (E1.2.1 m0)))))
    ma' mb'
    (P := fun y => y = a ∨ y = b ∨ y = u)
    (fun y hy hne => by rcases mem_pair hy with rfl | rfl; left; rfl; exact absurd rfl hne)
    (fun y hy hne => by rcases mem_pair hy with rfl | rfl; right; left; rfl; exact absurd rfl hne)
    (by rw [c5]; right; right; rfl)
  obtain ⟨𝓛7, E7, A7, m7, p7, z7, q7, -⟩ := r_combP E6.1 1 1 (E6.2.1 m5) m6
    (q5 a' ma' (Ne.symm haa)) (q6 a ma haa)
    (P := fun y => y = b ∨ y ∈ tl F ∨ y = fz)
    (fun y hy hne => by
      rcases p5 y hy with rfl | rfl | rfl
      · exact absurd rfl hne
      · left; rfl
      · right; left; exact hu')
    (fun y hy hne => by
      rcases p6 y hy with rfl | rfl | rfl
      · exact absurd rfl hne
      · left; rfl
      · right; left; exact hu)
    (by rw [c3]; right; right; rfl)
  rw [c3] at z7
  obtain ⟨𝓛8, E8, A8, m8, p8, q8⟩ := r_simpP E7.1 m7 z7
  have hb8 : b ∈ A8 := q8 b (q7 b (r5 b mb hbb) hab.symm) hbz
  -- the final resolution on `s`
  obtain ⟨𝓛9, E9, A9, m9, p9, z9, -, -⟩ := r_combP E8.1 1 1
    (E8.2.1 (E7.2.1 (E6.2.1 (E5.2.1 m4)))) m8 hb'4 hb8
    (P := fun y => y ∈ tl F ∨ y = fz)
    (fun y hy hne => by
      obtain ⟨hy3, hz⟩ := p4 y hy
      rcases p3 y hy3 with rfl | h | rfl
      · exact absurd rfl hne
      · left; exact h
      · exact absurd rfl hz)
    (fun y hy hne => by
      obtain ⟨hy7, hz⟩ := p8 y hy
      rcases p7 y hy7 with rfl | h | rfl
      · exact absurd rfl hne
      · left; exact h
      · exact absurd rfl hz)
    (by rw [c6]; right; rfl)
  rw [c6] at z9
  obtain ⟨𝓛10, E10, A10, m10, p10, -⟩ := r_simpP E9.1 m9 z9
  obtain ⟨𝓛11, E11, m11⟩ := r_sub E10.1 m10 (L := tl F) (fun y hy => by
    obtain ⟨hy9, hz⟩ := p10 y hy
    rcases p9 y hy9 with h | rfl
    · exact h
    · exact absurd rfl hz)
  exact ⟨𝓛11, ((((((((((((E0.trans E1).trans E2).trans E3).trans E4).trans E5).trans E6).trans
    E7).trans E8).trans E9).trans E10).trans E11).mono (by norm_num)), m11⟩

/-! ## Tautological lines for every form -/

/-- The form `∑_{i ∈ S} x_i`. -/
def indic (S : Finset ℕ) : ℕ →₀ ZMod 2 := ∑ i ∈ S, Finsupp.single i 1

theorem indic_apply (S : Finset ℕ) (j : ℕ) : indic S j = if j ∈ S then 1 else 0 := by
  unfold indic
  rw [Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

theorem indic_support (c : ℕ →₀ ZMod 2) : indic c.support = c := by
  ext j
  rw [indic_apply]
  by_cases h : j ∈ c.support
  · rw [if_pos h]
    have := Finsupp.mem_support_iff.1 h
    revert this; generalize c j = t; revert t; decide
  · rw [if_neg h]; exact (Finsupp.notMem_support_iff.1 h).symm

theorem r_taut_indic (hB : boolAx ⊆ Ax) (S : Finset ℕ) : ∀ {𝓛 : Finset Ln2}, RLDag Ax 𝓛 →
    ∃ 𝓛', Ext2 Ax 𝓛 𝓛' (12 * S.card + 5) ∧ tl (indic S) ∈ 𝓛' := by
  induction S using Finset.induction_on with
  | empty =>
    intro 𝓛 h
    have : indic (∅ : Finset ℕ) = 0 := by simp [indic]
    rw [this]
    obtain ⟨𝓛', E, m⟩ := r_taut0 hB h
    exact ⟨𝓛', E.mono (by simp), m⟩
  | insert i S hi ih =>
    intro 𝓛 h
    obtain ⟨𝓛1, E1, m1⟩ := ih h
    have hi0 : indic S i = 0 := by rw [indic_apply, if_neg hi]
    obtain ⟨𝓛2, E2, m2⟩ := r_taut_step hB E1.1 hi0 m1
    have e : indic (insert i S) = indic S + Finsupp.single i 1 := by
      unfold indic; rw [Finset.sum_insert hi, add_comm]
    rw [e]
    refine ⟨𝓛2, (E1.trans E2).mono ?_, m2⟩
    rw [Finset.card_insert_of_notMem hi]; omega

theorem r_taut (hB : boolAx ⊆ Ax) {𝓛 : Finset Ln2} (h : RLDag Ax 𝓛) (c : ℕ →₀ ZMod 2) :
    ∃ 𝓛', Ext2 Ax 𝓛 𝓛' (12 * c.support.card + 5) ∧ tl c ∈ 𝓛' := by
  have := r_taut_indic hB c.support h
  rwa [indic_support] at this

theorem r_tauts (hB : boolAx ⊆ Ax) (N : ℕ) (Ls : Finset (LEq (ZMod 2))) :
    (∀ e ∈ Ls, e.1.support.card ≤ N) → ∀ {𝓛 : Finset Ln2}, RLDag Ax 𝓛 →
    ∃ 𝓛', Ext2 Ax 𝓛 𝓛' (Ls.card * (12 * N + 5)) ∧ ∀ e ∈ Ls, tl e.1 ∈ 𝓛' := by
  induction Ls using Finset.induction_on with
  | empty => intro _ 𝓛 h; exact ⟨𝓛, (Ext2.refl h).mono (by simp), by simp⟩
  | insert e Ls he ih =>
    intro hN 𝓛 h
    obtain ⟨𝓛1, E1, m1⟩ := ih (fun e' he' => hN e' (Finset.mem_insert_of_mem he')) h
    obtain ⟨𝓛2, E2, m2⟩ := r_taut hB E1.1 e.1
    refine ⟨𝓛2, (E1.trans E2).mono ?_, fun e' he' => ?_⟩
    · rw [Finset.card_insert_of_notMem he]
      have := hN e (Finset.mem_insert_self _ _)
      calc Ls.card * (12 * N + 5) + (12 * e.1.support.card + 5)
          ≤ Ls.card * (12 * N + 5) + (12 * N + 5) := Nat.add_le_add_left (by omega) _
        _ = (Ls.card + 1) * (12 * N + 5) := by ring
    · rcases Finset.mem_insert.1 he' with rfl | he'
      · exact m2
      · exact E2.2.1 (m1 e' he')

/-! ## Eliminating one equation -/

theorem r_elim (T : Finset (LEq (ZMod 2))) : ∀ {𝓛 : Finset Ln2}, RLDag Ax 𝓛 →
    (∀ e ∈ T, tl e.1 ∈ 𝓛) → ∀ (M : Ln2) (g : LEq (ZMod 2)), M ∈ 𝓛 → g ∈ M →
    g + ∑ e ∈ T, ng e = fz →
    ∃ 𝓛', Ext2 Ax 𝓛 𝓛' (T.card + 1) ∧ ∃ M' ∈ 𝓛', ∀ y ∈ M', (y ∈ M ∧ y ≠ g) ∨ y ∈ T := by
  induction T using Finset.induction_on with
  | empty =>
    intro 𝓛 h _ M g hM hg hs
    simp only [Finset.sum_empty, add_zero] at hs
    subst hs
    obtain ⟨𝓛', E, M', m', p, -⟩ := r_simpP h hM hg
    exact ⟨𝓛', E.mono (by simp), M', m', fun y hy => Or.inl (p y hy)⟩
  | insert e T he ih =>
    intro 𝓛 h ht M g hM hg hs
    obtain ⟨𝓛1, E1, M1, m1, p1, z1, -, -⟩ := r_combP h 1 1 hM (ht e (Finset.mem_insert_self _ _))
      hg (ng_mem_tl e) (P := fun y => (y ∈ M ∧ y ≠ g) ∨ y = e ∨ y = g + ng e)
      (fun y hy hne => Or.inl ⟨hy, hne⟩)
      (fun y hy hne => by
        rcases tl_sub e y hy with rfl | rfl
        · right; left; rfl
        · exact absurd rfl hne)
      (by rw [cmb11]; right; right; rfl)
    rw [cmb11] at z1
    obtain ⟨𝓛2, E2, M2, m2, p2⟩ := ih E1.1
      (fun e' he' => E1.2.1 (ht e' (Finset.mem_insert_of_mem he'))) M1 (g + ng e) m1 z1
      (by rw [add_assoc]; rwa [Finset.sum_insert he] at hs)
    refine ⟨𝓛2, (E1.trans E2).mono (by rw [Finset.card_insert_of_notMem he]; omega), M2, m2,
      fun y hy => ?_⟩
    rcases p2 y hy with ⟨hy1, hne⟩ | hT
    · rcases p1 y hy1 with h1 | rfl | rfl
      · left; exact h1
      · right; exact Finset.mem_insert_self _ _
      · exact absurd rfl hne
    · right; exact Finset.mem_insert_of_mem hT

/-! ## Linear algebra over `F_2` -/

/-- The value `lval c x + a` of an equation `(c, a)`; it is `0` exactly when the equation holds. -/
def Ψ (x : ℕ → ZMod 2) : LEq (ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (Finsupp.linearCombination (ZMod 2) x).coprod LinearMap.id

theorem Ψ_apply (x : ℕ → ZMod 2) (e : LEq (ZMod 2)) : Ψ x e = lval e.1 x + e.2 := by
  simp [Ψ, lval, Finsupp.linearCombination_apply, smul_eq_mul]

theorem eSat_iff (x : ℕ → ZMod 2) (e : LEq (ZMod 2)) : eSat x e ↔ Ψ x e = 0 := by
  rw [Ψ_apply]; unfold eSat
  generalize lval e.1 x = u; generalize e.2 = v; revert u v; decide

theorem not_eSat_iff (x : ℕ → ZMod 2) (e : LEq (ZMod 2)) : ¬ eSat x e ↔ Ψ x (ng e) = 0 := by
  rw [Ψ_apply]; unfold eSat ng; dsimp only
  generalize lval e.1 x = u; generalize e.2 = v; revert u v; decide

theorem fz_mem_span (U : Set (LEq (ZMod 2))) (h : ∀ x : ℕ → ZMod 2, ∃ u ∈ U, Ψ x u ≠ 0) :
    fz ∈ Submodule.span (ZMod 2) U := by
  by_contra hn
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_notMem hn
  set x : ℕ → ZMod 2 := fun i => φ (Finsupp.single i 1, 0)
  have h1 : φ fz = 1 := by
    have key : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
    exact key _ hφ
  have hc : ∀ c : ℕ →₀ ZMod 2, φ (c, 0) = lval c x := by
    intro c
    induction c using Finsupp.induction_linear with
    | zero =>
      rw [show ((0 : ℕ →₀ ZMod 2), (0 : ZMod 2)) = 0 from rfl, map_zero, lval_zero]
    | add c d hc hd =>
      rw [show ((c + d, (0 : ZMod 2)) : LEq (ZMod 2)) = (c, 0) + (d, 0) by ext <;> simp,
        map_add, hc, hd, lval_add]
    | single i b =>
      rw [show ((Finsupp.single i b, (0 : ZMod 2)) : LEq (ZMod 2)) =
          b • ((Finsupp.single i 1, 0) : LEq (ZMod 2)) by ext <;> simp, map_smul, smul_eq_mul]
      simp [lval, Finsupp.sum_single_index, x]
  have hall : ∀ v, φ v = Ψ x v := by
    intro v
    conv_lhs => rw [show v = (v.1, 0) + v.2 • fz by ext <;> simp [fz]]
    rw [map_add, map_smul, hc, h1, Ψ_apply]
    simp
  obtain ⟨u, hu, hne⟩ := h x
  apply hne
  rw [← hall]
  exact LinearMap.mem_ker.1 (hle (Submodule.subset_span hu))

theorem span_ng_sum (L : Finset (LEq (ZMod 2))) :
    ∀ z ∈ Submodule.span (ZMod 2) (ng '' (L : Set (LEq (ZMod 2)))),
      ∃ T ⊆ L, z = ∑ e ∈ T, ng e := by
  induction L using Finset.induction_on with
  | empty =>
    intro z hz
    simp at hz
    exact ⟨∅, by simp, by simp [hz]⟩
  | insert e L he ih =>
    intro z hz
    rw [Finset.coe_insert, Set.image_insert_eq, Submodule.mem_span_insert] at hz
    obtain ⟨a, z', hz', rfl⟩ := hz
    obtain ⟨T, hT, rfl⟩ := ih z' hz'
    rcases z2_cases' a with rfl | rfl
    · exact ⟨T, hT.trans (Finset.subset_insert _ _), by simp⟩
    · have heT : e ∉ T := fun h => he (hT h)
      exact ⟨insert e T, Finset.insert_subset_insert _ hT,
        by rw [Finset.sum_insert heT, one_smul]⟩

/-- If `g ⊨ L` on `F_2^ℕ`, some `β g + Σ_{e ∈ T} ¬e`, `T ⊆ L`, is the false constant. -/
theorem decomp (g : LEq (ZMod 2)) (L : Finset (LEq (ZMod 2)))
    (h : ∀ x, eSat x g → ∃ e ∈ L, eSat x e) :
    ∃ β : ZMod 2, ∃ T ⊆ L, β • g + ∑ e ∈ T, ng e = fz := by
  have hm := fz_mem_span (insert g (ng '' (L : Set (LEq (ZMod 2))))) (by
    intro x
    by_cases hg : eSat x g
    · obtain ⟨e, he, hs⟩ := h x hg
      refine ⟨ng e, Set.mem_insert_of_mem _ ⟨e, Finset.mem_coe.2 he, rfl⟩, ?_⟩
      intro h0; exact (not_eSat_iff x e).2 h0 hs
    · exact ⟨g, Set.mem_insert _ _, fun h0 => hg ((eSat_iff x g).2 h0)⟩)
  rw [Submodule.mem_span_insert] at hm
  obtain ⟨β, z, hz, hfz⟩ := hm
  obtain ⟨T, hT, rfl⟩ := span_ng_sum L z hz
  exact ⟨β, T, hT, hfz.symm⟩

/-! ## One semantic weakening -/

theorem r_reduce {L : Ln2} (k : ℕ) : ∀ {𝓛 : Finset Ln2}, RLDag Ax 𝓛 →
    (∀ e ∈ L, tl e.1 ∈ 𝓛) → ∀ M ∈ 𝓛, (M \ L).card ≤ k → (∀ x, clSat x M → clSat x L) →
    ∃ 𝓛', Ext2 Ax 𝓛 𝓛' (k * (L.card + 1)) ∧ ∃ M' ∈ 𝓛', M' ⊆ L := by
  induction k with
  | zero =>
    intro 𝓛 h _ M hM hk _
    have : M \ L = ∅ := Finset.card_eq_zero.1 (by omega)
    exact ⟨𝓛, (Ext2.refl h).mono (by simp), M, hM, Finset.sdiff_eq_empty_iff_subset.1 this⟩
  | succ k ih =>
    intro 𝓛 h ht M hM hk hI
    by_cases hsub : M ⊆ L
    · exact ⟨𝓛, (Ext2.refl h).mono (Nat.zero_le _), M, hM, hsub⟩
    obtain ⟨g, hgM, hgL⟩ := Finset.not_subset.1 hsub
    obtain ⟨β, T, hT, hs⟩ := decomp g L (fun x hx => by
      obtain ⟨e, he, hs⟩ := hI x ⟨g, hgM, hx⟩
      exact ⟨e, he, hs⟩)
    have htT : ∀ e ∈ T, tl e.1 ∈ 𝓛 := fun e he => ht e (hT he)
    have hTL := Finset.card_le_card hT
    rcases z2_cases' β with rfl | rfl
    · rw [zero_smul, zero_add] at hs
      have hTne : T.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        have := congrArg Prod.snd hs
        simp [fz] at this
      obtain ⟨e0, he0⟩ := hTne
      obtain ⟨𝓛1, E1, M1, m1, p1⟩ := r_elim (T.erase e0) h
        (fun e he => htT e (Finset.mem_of_mem_erase he)) (tl e0.1) (ng e0) (htT e0 he0)
        (ng_mem_tl e0) (by rw [Finset.add_sum_erase _ _ he0]; exact hs)
      refine ⟨𝓛1, E1.mono ?_, M1, m1, fun y hy => ?_⟩
      · have := Finset.card_erase_of_mem he0 (s := T)
        calc (T.erase e0).card + 1 ≤ L.card + 1 := by omega
          _ ≤ (k + 1) * (L.card + 1) := Nat.le_mul_of_pos_left _ (by omega)
      · rcases p1 y hy with ⟨hy1, hne⟩ | hy1
        · rcases tl_sub e0 y hy1 with rfl | rfl
          · exact hT he0
          · exact absurd rfl hne
        · exact hT (Finset.mem_of_mem_erase hy1)
    · rw [one_smul] at hs
      obtain ⟨𝓛1, E1, M1, m1, p1⟩ := r_elim T h htT M g hM hgM hs
      have hk' : (M1 \ L).card ≤ k := by
        have hsub2 : M1 \ L ⊆ (M \ L).erase g := by
          intro y hy
          obtain ⟨hy1, hyL⟩ := Finset.mem_sdiff.1 hy
          rcases p1 y hy1 with ⟨hyM, hne⟩ | hyT
          · exact Finset.mem_erase.2 ⟨hne, Finset.mem_sdiff.2 ⟨hyM, hyL⟩⟩
          · exact absurd (hT hyT) hyL
        have := Finset.card_le_card hsub2
        rw [Finset.card_erase_of_mem (Finset.mem_sdiff.2 ⟨hgM, hgL⟩)] at this
        omega
      have hI1 : ∀ x, clSat x M1 → clSat x L := by
        rintro x ⟨y, hy, hs⟩
        rcases p1 y hy with ⟨hyM, -⟩ | hyT
        · exact hI x ⟨y, hyM, hs⟩
        · exact ⟨y, hT hyT, hs⟩
      obtain ⟨𝓛2, E2, M2, m2, hM2⟩ := ih E1.1 (fun e he => E1.2.1 (ht e he)) M1 m1 hk' hI1
      refine ⟨𝓛2, (E1.trans E2).mono ?_, M2, m2, hM2⟩
      calc T.card + 1 + k * (L.card + 1) ≤ L.card + 1 + k * (L.card + 1) :=
            Nat.add_le_add_right (by omega) _
        _ = (k + 1) * (L.card + 1) := by ring

/-- **One semantic weakening in `RLDag` over `F_2`.**  If `M0 ⊨ L` on `F_2^ℕ`, `M0` is a line
and every equation of `L` has at most `N` variables, then `L` is derivable with at most
`|L| (12 N + 5) + |M0| (|L| + 1) + 1` further lines. -/
theorem r_wsim (hB : boolAx ⊆ Ax) {𝓛 : Finset Ln2} (h : RLDag Ax 𝓛) {M0 L : Ln2}
    (hM0 : M0 ∈ 𝓛) (hI : ∀ x, clSat x M0 → clSat x L) {N : ℕ}
    (hN : ∀ e ∈ L, e.1.support.card ≤ N) :
    ∃ 𝓛', Ext2 Ax 𝓛 𝓛' (L.card * (12 * N + 5) + M0.card * (L.card + 1) + 1) ∧ L ∈ 𝓛' := by
  obtain ⟨𝓛1, E1, ht⟩ := r_tauts hB N L hN h
  obtain ⟨𝓛2, E2, M2, m2, hM2⟩ := r_reduce M0.card E1.1 ht M0 (E1.2.1 hM0)
    (Finset.card_le_card Finset.sdiff_subset) hI
  obtain ⟨𝓛3, E3, m3⟩ := r_sub E2.1 m2 (L := L) (fun y hy => hM2 hy)
  exact ⟨𝓛3, (E1.trans E2).trans E3, m3⟩

/-! ## From `Res(⊕)` lines to `RLDag` lines -/

/-- An `RL` equation `∑_{w ∈ S} x_w = a` as an equation over `F_2`. -/
def fromE (e : Finset ℕ × ZMod 2) : LEq (ZMod 2) := (indic e.1, e.2)

/-- An `RL` linear clause as a line of `RLDag`. -/
def fromL (L : RL.LClause) : Ln2 := L.image fromE

theorem support_indic (S : Finset ℕ) : (indic S).support = S := by
  ext j
  rw [Finsupp.mem_support_iff, indic_apply]
  by_cases h : j ∈ S <;> simp [h]

theorem lval_indic (S : Finset ℕ) (x : ℕ → ZMod 2) : lval (indic S) x = RL.lf S x := by
  rw [← lf_support, support_indic]

theorem clSat_fromL (x : ℕ → ZMod 2) (L : RL.LClause) : clSat x (fromL L) ↔ RL.lsatL x L := by
  unfold clSat fromL RL.lsatL
  constructor
  · rintro ⟨e, he, hv⟩
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
    exact ⟨e', he', by simpa [eSat, fromE, lval_indic] using hv⟩
  · rintro ⟨e, he, hv⟩
    exact ⟨fromE e, Finset.mem_image_of_mem _ he, by simpa [eSat, fromE, lval_indic] using hv⟩

theorem fromL_toL (X : Ln2) : fromL (toL X) = X := by
  unfold fromL toL
  rw [Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := X)]
  refine Finset.image_congr fun e _ => ?_
  simp [fromE, toE, indic_support]

theorem fromL_ofClause (C : Clause) : fromL (RL.ofClause C) = encCl C := by
  rw [← toL_encCl, fromL_toL]

theorem supp_fromL {L : RL.LClause} {N : ℕ} (hN : ∀ e ∈ L, e.1.card ≤ N) :
    ∀ e ∈ fromL L, e.1.support.card ≤ N := by
  intro e he
  obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
  simpa [fromE, support_indic] using hN e' he'

/-- Restriction of the resolved form to the variables `V` of the clauses involved. -/
theorem imp_restrict {L1 C : RL.LClause} {f : Finset ℕ} {a : ZMod 2} (V : Finset ℕ)
    (hV1 : ∀ e ∈ L1, e.1 ⊆ V) (hVC : ∀ e ∈ C, e.1 ⊆ V) (h : RL.Imp L1 (insert (f, a) C)) :
    RL.Imp L1 (insert (f ∩ V, a) C) := by
  intro x hx
  set x' : ℕ → ZMod 2 := fun i => if i ∈ V then x i else 0
  have hsub : ∀ S : Finset ℕ, S ⊆ V → RL.lf S x' = RL.lf S x := by
    intro S hS
    unfold RL.lf
    exact Finset.sum_congr rfl fun w hw => by simp [x', hS hw]
  have hf : RL.lf f x' = RL.lf (f ∩ V) x := by
    unfold RL.lf
    rw [← Finset.filter_mem_eq_inter, Finset.sum_filter]
  obtain ⟨e, he, hv⟩ := hx
  obtain ⟨e', he', hv'⟩ := h x' ⟨e, he, by rw [hsub e.1 (hV1 e he)]; exact hv⟩
  rcases Finset.mem_insert.1 he' with rfl | he'
  · exact ⟨(f ∩ V, a), Finset.mem_insert_self _ _, by rw [← hf]; exact hv'⟩
  · exact ⟨e', Finset.mem_insert_of_mem he', by rw [← hsub e'.1 (hVC e' he')]; exact hv'⟩

/-! ## The simulation -/

/-- Lines of `RLDag` per line of `Res(⊕)`: `O(W² N)`. -/
def xorBackCost (W N : ℕ) : ℕ := 2 * ((W + 1) * (12 * (N + 4 * W * N) + 5) + W * (W + 2) + 1) + 3

theorem cost_weak {a b W N : ℕ} (ha : a ≤ W) (hb : b ≤ W) :
    a * (12 * N + 5) + b * (a + 1) + 1 ≤ xorBackCost W N := by
  unfold xorBackCost
  have h1 : a * (12 * N + 5) ≤ (W + 1) * (12 * (N + 4 * W * N) + 5) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : b * (a + 1) ≤ W * (W + 2) := Nat.mul_le_mul hb (by omega)
  omega

theorem cost_res {a1 a2 b1 b2 W N N' : ℕ} (hN' : N' ≤ N + 4 * W * N) (ha1 : a1 ≤ W + 1)
    (ha2 : a2 ≤ W + 1) (hb1 : b1 ≤ W) (hb2 : b2 ≤ W) :
    a1 * (12 * N' + 5) + b1 * (a1 + 1) + 1 + (a2 * (12 * N' + 5) + b2 * (a2 + 1) + 1) + 3 ≤
      xorBackCost W N := by
  unfold xorBackCost
  have h1 : a1 * (12 * N' + 5) ≤ (W + 1) * (12 * (N + 4 * W * N) + 5) :=
    Nat.mul_le_mul ha1 (by omega)
  have h2 : a2 * (12 * N' + 5) ≤ (W + 1) * (12 * (N + 4 * W * N) + 5) :=
    Nat.mul_le_mul ha2 (by omega)
  have h3 : b1 * (a1 + 1) ≤ W * (W + 2) := Nat.mul_le_mul hb1 (by omega)
  have h4 : b2 * (a2 + 1) ≤ W * (W + 2) := Nat.mul_le_mul hb2 (by omega)
  omega

theorem card_fromL_le (L : RL.LClause) : (fromL L).card ≤ L.card := Finset.card_image_le

theorem fz_add (c : ℕ →₀ ZMod 2) (a : ZMod 2) :
    cmb 1 1 ((c, a) : LEq (ZMod 2)) (c, a + 1) = fz := by
  rw [cmb11]
  ext
  · simp [fz, add_self2]
  · show a + (a + 1) = 1
    generalize a = t; revert t; decide

/-- One step of `Res(⊕)` in `RLDag` over `F_2`, with at most `xorBackCost W N` lines. -/
theorem step_back {Φ : CNF} {P : Finset RL.LClause} {L : RL.LClause}
    (hs : RL.Step (↑Φ : Set Clause) P L) {W N : ℕ} (hW : ∀ M ∈ insert L P, M.card ≤ W)
    (hN : ∀ M ∈ insert L P, ∀ e ∈ M, e.1.card ≤ N) {𝓛 : Finset Ln2}
    (h : RLDag (Ax2 Φ ∪ boolAx) 𝓛) (hmem : ∀ M ∈ P, fromL M ∈ 𝓛) :
    ∃ 𝓛', Ext2 (Ax2 Φ ∪ boolAx) 𝓛 𝓛' (xorBackCost W N) ∧ fromL L ∈ 𝓛' := by
  have hB : (boolAx : Set Ln2) ⊆ Ax2 Φ ∪ boolAx := Set.subset_union_right
  have hWL := hW L (Finset.mem_insert_self _ _)
  have hNL := hN L (Finset.mem_insert_self _ _)
  cases hs with
  | @ax C hC =>
    obtain ⟨𝓛', E, m⟩ := r_ax (Ax := Ax2 Φ ∪ boolAx) h (C := encCl C)
      (Or.inl ⟨C, Finset.mem_coe.1 hC, rfl⟩)
    rw [fromL_ofClause]
    exact ⟨𝓛', E.mono (by unfold xorBackCost; omega), m⟩
  | @weak L0 _ hL0 himp =>
    obtain ⟨𝓛', E, m⟩ := r_wsim hB h (hmem L0 hL0) (L := fromL L)
      (fun x hx => (clSat_fromL x L).2 (himp x ((clSat_fromL x L0).1 hx))) (supp_fromL hNL)
    exact ⟨𝓛', E.mono (cost_weak ((card_fromL_le L).trans hWL)
      ((card_fromL_le L0).trans (hW L0 (Finset.mem_insert_of_mem hL0)))), m⟩
  | @res L1 L2 C D f a hL1 hL2 i1 i2 =>
    set V : Finset ℕ := (L1 ∪ L2 ∪ C ∪ D).biUnion Prod.fst
    have hV : ∀ e ∈ L1 ∪ L2 ∪ C ∪ D, e.1 ⊆ V := fun e he => Finset.subset_biUnion_of_mem _ he
    have hW1 := hW L1 (Finset.mem_insert_of_mem hL1)
    have hW2 := hW L2 (Finset.mem_insert_of_mem hL2)
    have hCW : C.card ≤ W := (Finset.card_le_card Finset.subset_union_left).trans hWL
    have hDW : D.card ≤ W := (Finset.card_le_card Finset.subset_union_right).trans hWL
    have hNall : ∀ e ∈ L1 ∪ L2 ∪ C ∪ D, e.1.card ≤ N := by
      intro e he
      simp only [Finset.mem_union] at he
      rcases he with ((he | he) | he) | he
      · exact hN L1 (Finset.mem_insert_of_mem hL1) e he
      · exact hN L2 (Finset.mem_insert_of_mem hL2) e he
      · exact hNL e (Finset.mem_union_left _ he)
      · exact hNL e (Finset.mem_union_right _ he)
    have hVcard : V.card ≤ 4 * W * N := by
      refine (Finset.card_biUnion_le).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ N hNall).trans ?_
      rw [smul_eq_mul]
      have : (L1 ∪ L2 ∪ C ∪ D).card ≤ 4 * W := by
        have := Finset.card_union_le (L1 ∪ L2 ∪ C) D
        have := Finset.card_union_le (L1 ∪ L2) C
        have := Finset.card_union_le L1 L2
        omega
      exact Nat.mul_le_mul_right _ this
    have i1' := imp_restrict V (fun e he => hV e (by simp [he])) (fun e he => hV e (by simp [he])) i1
    have i2' := imp_restrict V (fun e he => hV e (by simp [he])) (fun e he => hV e (by simp [he])) i2
    set g := f ∩ V
    have hgV : g.card ≤ 4 * W * N := (Finset.card_le_card Finset.inter_subset_right).trans hVcard
    have hNX : ∀ (b : ZMod 2) (X : RL.LClause), X ⊆ C ∪ D →
        ∀ e ∈ fromL (insert (g, b) X), e.1.support.card ≤ N + 4 * W * N := by
      intro b X hX
      refine supp_fromL fun e he => ?_
      rcases Finset.mem_insert.1 he with rfl | he
      · exact hgV.trans (Nat.le_add_left _ _)
      · exact (hNL e (hX he)).trans (Nat.le_add_right _ _)
    obtain ⟨𝓛1, E1, m1⟩ := r_wsim hB h (hmem L1 hL1) (L := fromL (insert (g, a) C))
      (fun x hx => (clSat_fromL x _).2 (i1' x ((clSat_fromL x L1).1 hx)))
      (hNX a C Finset.subset_union_left)
    obtain ⟨𝓛2, E2, m2⟩ := r_wsim hB E1.1 (E1.2.1 (hmem L2 hL2)) (L := fromL (insert (g, a + 1) D))
      (fun x hx => (clSat_fromL x _).2 (i2' x ((clSat_fromL x L2).1 hx)))
      (hNX (a + 1) D Finset.subset_union_right)
    have e1 : fromL (insert (g, a) C) = insert (indic g, a) (fromL C) := by
      simp [fromL, Finset.image_insert, fromE]
    have e2 : fromL (insert (g, a + 1) D) = insert (indic g, a + 1) (fromL D) := by
      simp [fromL, Finset.image_insert, fromE]
    rw [e1] at m1
    rw [e2] at m2
    obtain ⟨𝓛3, E3, M3, m3, p3, z3, -, -⟩ := r_combP E2.1 1 1 (E2.2.1 m1) m2
      (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
      (P := fun y => y ∈ fromL (C ∪ D) ∨ y = fz)
      (fun y hy hne => by
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact absurd rfl hne
        · left; unfold fromL at hy ⊢; rw [Finset.image_union]; exact Finset.mem_union_left _ hy)
      (fun y hy hne => by
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact absurd rfl hne
        · left; unfold fromL at hy ⊢; rw [Finset.image_union]; exact Finset.mem_union_right _ hy)
      (by rw [fz_add]; right; rfl)
    rw [fz_add] at z3
    obtain ⟨𝓛4, E4, M4, m4, p4, -⟩ := r_simpP E3.1 m3 z3
    obtain ⟨𝓛5, E5, m5⟩ := r_sub E4.1 m4 (L := fromL (C ∪ D)) (fun y hy => by
      obtain ⟨hy3, hz⟩ := p4 y hy
      rcases p3 y hy3 with h | rfl
      · exact h
      · exact absurd rfl hz)
    refine ⟨𝓛5, ((((E1.trans E2).trans E3).trans E4).trans E5).mono ?_, m5⟩
    have hc1 : (insert (indic g, a) (fromL C)).card ≤ W + 1 :=
      (Finset.card_insert_le _ _).trans (by have := card_fromL_le C; omega)
    have hc2 : (insert (indic g, a + 1) (fromL D)).card ≤ W + 1 :=
      (Finset.card_insert_le _ _).trans (by have := card_fromL_le D; omega)
    have := cost_res (N' := N + 4 * W * N) le_rfl hc1 hc2
      ((card_fromL_le L1).trans hW1) ((card_fromL_le L2).trans hW2)
    rw [e1, e2]
    omega

/-- **Semantic weakening removed over `F_2`.**  A dag-like `Res(⊕)` derivation `P` of the CNF `Φ`
(semantic weakening, `RL.Der`) containing the empty clause, all of whose lines have at most `W`
equations each with at most `N` variables, gives a refutation in the syntactic dag-like
`Res(lin F_2)` of Part-Tzameret (`RLDag` from `Ax2 Φ ∪ boolAx`) with at most
`xorBackCost W N * |P|` lines.  Converse of `rldag2_to_dagRefutes` up to this factor. -/
theorem dagRefutes_to_rldag2 {Φ : CNF} {P : Finset RL.LClause} (hP : RL.Der (↑Φ : Set Clause) P)
    (h0 : (∅ : RL.LClause) ∈ P) {W N : ℕ} (hW : ∀ M ∈ P, M.card ≤ W)
    (hN : ∀ M ∈ P, ∀ e ∈ M, e.1.card ≤ N) :
    ∃ 𝓛, RLDag (Ax2 Φ ∪ boolAx) 𝓛 ∧ (∅ : Ln2) ∈ 𝓛 ∧ 𝓛.card ≤ xorBackCost W N * P.card := by
  have key : ∀ {P : Finset RL.LClause}, RL.Der (↑Φ : Set Clause) P → (∀ M ∈ P, M.card ≤ W) →
      (∀ M ∈ P, ∀ e ∈ M, e.1.card ≤ N) →
      ∃ 𝓛, RLDag (Ax2 Φ ∪ boolAx) 𝓛 ∧ (∀ M ∈ P, fromL M ∈ 𝓛) ∧
        𝓛.card ≤ xorBackCost W N * P.card := by
    intro P hP
    induction hP with
    | empty => intro _ _; exact ⟨∅, RLDag.empty, by simp, by simp⟩
    | @add P L hP' hs ih =>
      intro hW hN
      obtain ⟨𝓛, h𝓛, hmem, hc⟩ := ih (fun M hM => hW M (Finset.mem_insert_of_mem hM))
        (fun M hM => hN M (Finset.mem_insert_of_mem hM))
      by_cases hL : L ∈ P
      · rw [Finset.insert_eq_of_mem hL]
        exact ⟨𝓛, h𝓛, hmem, hc⟩
      · obtain ⟨𝓛', E, m⟩ := step_back hs hW hN h𝓛 hmem
        refine ⟨𝓛', E.1, fun M hM => ?_, ?_⟩
        · rcases Finset.mem_insert.1 hM with rfl | hM
          · exact m
          · exact E.2.1 (hmem M hM)
        · rw [Finset.card_insert_of_notMem hL, Nat.mul_succ]
          have := E.2.2
          omega
  obtain ⟨𝓛, h𝓛, hmem, hc⟩ := key hP hW hN
  exact ⟨𝓛, h𝓛, by simpa [fromL] using hmem ∅ h0, hc⟩

end

end RLF

end SATurday.ProofComplexity
