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
  `|L| (12 N + 5) + |M0| (|L| + 1) + |L| + 2` lines of `RLDag`, `N` a bound on the support sizes in `L`;
* `RLF.dagRefutes_to_rldag2`: a `Res(⊕)` refutation (a derivation `P` with `∅ ∈ P`) all of whose
  lines have at most `W` equations, each with at most `N` variables, gives an `RLDag` refutation
  from `Ax2 Φ ∪ boolAx` with at most `xorBackCost W N * |P|` lines, where
  `xorBackCost W N = 2 ((W+1)(12 (N + 4 W N) + 5) + W (W + 2) + W + 3) + 3`, i.e. `O(W² N)` per line.

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

end

end RLF

end SATurday.ProofComplexity
