import Theory.ProofComplexity.PHPKEval

/-!
# Tree-like resolution over parities: PHP lifted with MAJ₃ (Ladder Rung R4, 1D.3)

Parity decision trees (`PDT`) query `F₂` linear forms `∑_{w ∈ S} x_w`; a tree solves the
search problem of a set of clauses when every input reaches a leaf labelled by a clause of the
set falsified by the input. Tree-like `Res(⊕)` refutations convert into such trees with no more
leaves than axiom occurrences (`tree_to_pdt`).

The formula: the pigeonhole CNF `phpCNF n` with every variable `z_v` replaced by
`MAJ₃(x_{3v}, x_{3v+1}, x_{3v+2})` (`liftedPHP`). Lower bound by stifling (Chattopadhyay–Mande–
Sanyal–Sherif): along the tree, maintain an affine parametrisation of a subspace of solutions in
which every "stifled" block has its two non pivot coordinates fixed to the value given by a
matching adversary for PHP, so `MAJ₃` of the block is fixed whatever the pivot. Every query that
is not constant on the parametrised subspace splits it in two, each half one base query further
(`pdt_leaves`). A leaf needs a PHP clause falsified by the adversary, hence `n` base queries:
every solving tree has at least `2^n` leaves (`pdt_lifted_php`), and so does every tree-like
`Res(⊕)` refutation (`treelike_reslin_php`).

LOG: R4 ResLin module (tree-like Res(⊕) lower bound)
-/

namespace SATurday.ProofComplexity

namespace RL

open Finset

theorem z2_g1 : ∀ a B B' C : ZMod 2, a + (B + B' + C) + (a + C) = a + B + (a + B') := by decide
theorem z2_g2 : ∀ a X : ZMod 2, a + X = 0 → X = a := by decide
theorem z2_g3 : ∀ a X Y Z : ZMod 2, Y + Z = 1 → a + X = 1 → X + Y + Z = a := by decide
theorem z2_g4 : ∀ x y z : ZMod 2, x + y + z + z = x + y := by decide
theorem z2_0ne1 : (0 : ZMod 2) ≠ 1 := by decide
theorem z2_1ne0 : (1 : ZMod 2) ≠ 0 := by decide
theorem z2_01 : ((0 : ZMod 2) = 1) ↔ False := by decide
theorem z2_10 : ((1 : ZMod 2) = 0) ↔ False := by decide
theorem z2_g5 : ∀ A B C : ZMod 2, A + B = A + C + (B + C) := by decide

noncomputable section

open Classical

/-! ## Linear forms and parity decision trees -/

/-- Value of the linear form `∑_{w ∈ S} x_w`. -/
def lf (S : Finset ℕ) (x : ℕ → ZMod 2) : ZMod 2 := ∑ w ∈ S, x w

/-- `0/1` value of a polarity. -/
def bv (b : Bool) : ZMod 2 := if b then 1 else 0

/-- A literal is satisfied by a `ZMod 2` assignment. -/
def lsat (x : ℕ → ZMod 2) (l : Literal) : Prop := x l.var = bv l.pos

/-- A clause is falsified: no literal is satisfied. -/
def cfalse (x : ℕ → ZMod 2) (C : Clause) : Prop := ∀ l ∈ C, ¬ lsat x l

/-- Parity decision trees with clause labelled leaves. -/
inductive PDT where
  | leaf (C : Clause)
  | node (S : Finset ℕ) (t0 t1 : PDT)

namespace PDT

/-- The leaf reached by an input. -/
def leafOf : PDT → (ℕ → ZMod 2) → Clause
  | leaf C, _ => C
  | node S t0 t1, x => if lf S x = 0 then leafOf t0 x else leafOf t1 x

/-- Number of leaves. -/
def nl : PDT → ℕ
  | leaf _ => 1
  | node _ t0 t1 => nl t0 + nl t1

/-- All variables mentioned (queries and leaf clauses). -/
def vars : PDT → Finset ℕ
  | leaf C => C.image Literal.var
  | node S t0 t1 => S ∪ vars t0 ∪ vars t1

end PDT

/-- Equations `S = a` collected along a path. -/
abbrev Eqs := List (Finset ℕ × ZMod 2)

def satE (Φ : Eqs) (x : ℕ → ZMod 2) : Prop := ∀ e ∈ Φ, lf e.1 x = e.2

/-- `T` solves the search problem of `Ax` on the inputs satisfying `Φ`. -/
def Solves (Ax : Set Clause) (T : PDT) (Φ : Eqs) : Prop :=
  ∀ x, satE Φ x → T.leafOf x ∈ Ax ∧ cfalse x (T.leafOf x)

/-! ## The lifted pigeonhole principle -/

/-- Coordinate `k` of the block of base variable `v`. -/
def lv (v k : ℕ) : ℕ := 3 * v + k

/-- The two coordinates of the `c`-th pair of a block. -/
def pr1 (c : Fin 3) : ℕ := if c.val = 2 then 1 else 0
def pr2 (c : Fin 3) : ℕ := if c.val = 0 then 1 else 2

/-- The lifted clause: for each literal `z_v = b` and chosen pair, the two literals
`x_{v,k} = b` of the pair. It is falsified iff every chosen pair has both coordinates `¬ b`,
which forces `MAJ₃ = ¬ b` on every block. -/
def liftC (C : Clause) (ch : Literal → Fin 3) : Clause :=
  C.biUnion fun l => {⟨lv l.var (pr1 (ch l)), l.pos⟩, ⟨lv l.var (pr2 (ch l)), l.pos⟩}

/-- Clauses of `F ∘ MAJ₃`. -/
def lifted (F : CNF) : Set Clause := {C' | ∃ C ∈ F, ∃ ch, C' = liftC C ch}

/-- `PHP_n ∘ MAJ₃`. -/
def liftedPHP (n : ℕ) : Set Clause := lifted (phpCNF n)

theorem pr_ne (c : Fin 3) : pr1 c ≠ pr2 c := by
  unfold pr1 pr2; fin_cases c <;> simp

theorem pr_lt (c : Fin 3) : pr1 c < 3 ∧ pr2 c < 3 := by
  unfold pr1 pr2; fin_cases c <;> simp

/-! ## A matching adversary for PHP -/

section Adv

variable (n : ℕ)

/-- A base variable of `PHP_n`. -/
def isP (v : ℕ) : Prop := v < (n + 1) * n

/-- Base answers so far: `ρ v = some b` for queried `v`. -/
abbrev BAsg := ℕ → Option Bool

/-- Variables answered `1`: matched edges. -/
def ones (ρ : BAsg) (J : Finset ℕ) : Finset ℕ := J.filter fun v => isP n v ∧ ρ v = some true

/-- The adversary invariant: `1` answers form a matching; every `0` answer has its pigeon or
its hole matched. -/
def AdvInv (ρ : BAsg) (J : Finset ℕ) : Prop :=
  (∀ v ∈ ones n ρ J, ∀ v' ∈ ones n ρ J, (v / n = v' / n ∨ v % n = v' % n) → v = v') ∧
  (∀ v ∈ J, isP n v → ρ v = some false →
    ∃ v' ∈ ones n ρ J, v' / n = v / n ∨ v' % n = v % n) ∧
  (∀ v, ρ v ≠ none ↔ v ∈ J)

/-- The adversary's answer to a base query. -/
def adv (ρ : BAsg) (J : Finset ℕ) (v : ℕ) : Bool :=
  decide (isP n v ∧ (∀ v' ∈ ones n ρ J, v' / n ≠ v / n ∧ v' % n ≠ v % n))

/-- Recording an answer. -/
def upd (ρ : BAsg) (v : ℕ) (b : Bool) : BAsg := fun w => if w = v then some b else ρ w

theorem advInv_empty : AdvInv n (fun _ => none) ∅ := by
  refine ⟨fun v hv => by simp [ones] at hv, fun v hv => by simp at hv, fun v => by simp⟩

theorem ones_upd_sub {ρ : BAsg} {J : Finset ℕ} {v : ℕ} (hv : v ∉ J) (b : Bool) :
    ones n ρ J ⊆ ones n (upd ρ v b) (insert v J) := by
  intro w hw
  simp only [ones, mem_filter, mem_insert] at hw ⊢
  refine ⟨Or.inr hw.1, hw.2.1, ?_⟩
  have : w ≠ v := fun h => hv (h ▸ hw.1)
  simp [upd, this, hw.2.2]

theorem mem_ones_upd {ρ : BAsg} {J : Finset ℕ} {v w : ℕ} (hv : v ∉ J) (b : Bool) :
    w ∈ ones n (upd ρ v b) (insert v J) ↔ (w = v ∧ isP n v ∧ b = true) ∨ w ∈ ones n ρ J := by
  by_cases hw : w = v
  · subst hw; simp [ones, upd, hv]
  · simp [ones, upd, hw]

theorem advInv_upd {ρ : BAsg} {J : Finset ℕ} (h : AdvInv n ρ J) {v : ℕ} (hv : v ∉ J) :
    AdvInv n (upd ρ v (adv n ρ J v)) (insert v J) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hfree : adv n ρ J v = true → ∀ v' ∈ ones n ρ J, v' / n ≠ v / n ∧ v' % n ≠ v % n := by
    intro ha; unfold adv at ha; exact (decide_eq_true_iff.1 ha).2
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    rw [mem_ones_upd n hv] at ha hb
    rcases ha with ⟨rfl, -, hA⟩ | ha <;> rcases hb with ⟨rfl, -, hB⟩ | hb
    · rfl
    · exfalso; have := hfree hA b hb; rcases hab with h | h
      · exact this.1 h.symm
      · exact this.2 h.symm
    · exfalso; have := hfree hB a ha; rcases hab with h | h
      · exact this.1 h
      · exact this.2 h
    · exact h1 a ha b hb hab
  · intro w hw hwP hw0
    rcases mem_insert.1 hw with rfl | hw'
    · simp only [upd, if_true] at hw0
      have ha : adv n ρ J w = false := by simpa using hw0
      unfold adv at ha
      rw [decide_eq_false_iff_not] at ha
      have : ¬ ∀ v' ∈ ones n ρ J, v' / n ≠ w / n ∧ v' % n ≠ w % n := fun hc => ha ⟨hwP, hc⟩
      push Not at this
      obtain ⟨v', hv', hc⟩ := this
      refine ⟨v', (mem_ones_upd n hv _).2 (Or.inr hv'), ?_⟩
      by_cases h' : v' / n = w / n
      · exact Or.inl h'
      · exact Or.inr (hc h')
    · have hne : w ≠ v := fun h => hv (h ▸ hw')
      simp only [upd, if_neg hne] at hw0
      obtain ⟨v', hv', hc⟩ := h2 w hw' hwP hw0
      exact ⟨v', (mem_ones_upd n hv _).2 (Or.inr hv'), hc⟩
  · intro w
    by_cases hw : w = v
    · subst hw; simp [upd]
    · simp [upd, hw, h3 w]

theorem pvar_div {i : Fin (n + 1)} {j : Fin n} : pvar n i j / n = i.val := by
  have hn : 0 < n := Fin.pos j
  unfold pvar
  rw [show i.val * n + j.val = j.val + n * i.val by ring, Nat.add_mul_div_left _ _ hn,
    Nat.div_eq_of_lt j.2, zero_add]

theorem pvar_mod {i : Fin (n + 1)} {j : Fin n} : pvar n i j % n = j.val := by
  unfold pvar
  rw [show i.val * n + j.val = j.val + n * i.val by ring, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt j.2]

theorem pvar_isP (i : Fin (n + 1)) (j : Fin n) : isP n (pvar n i j) := by
  unfold isP pvar
  have := i.2; have := j.2
  nlinarith

/-- A PHP clause falsified by the adversary's answers needs `n` answered queries. -/
theorem adv_clause {ρ : BAsg} {J : Finset ℕ} (h : AdvInv n ρ J) {C : Clause} (hC : C ∈ phpCNF n)
    (hf : ∀ l ∈ C, ρ l.var = some (!l.pos)) : n ≤ J.card := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases mem_phpCNF hC with ⟨i, rfl⟩ | ⟨i, i', j, hii, rfl⟩
  · -- pigeon clause
    have hz : ∀ j : Fin n, ρ (pvar n i j) = some false := fun j =>
      hf ⟨pvar n i j, true⟩ (mem_image.2 ⟨j, mem_univ _, rfl⟩)
    have hunm : ∀ v ∈ ones n ρ J, v / n ≠ i.val := by
      intro v hv hvi
      obtain ⟨-, hvP, hvt⟩ := mem_filter.1 hv
      have hn : 0 < n := by
        by_contra h0; unfold isP at hvP; simp at h0; subst h0; simp at hvP
      have hj : v % n < n := Nat.mod_lt _ hn
      have hv' : v = pvar n i ⟨v % n, hj⟩ := by
        unfold pvar; simp only; rw [← hvi]; exact (Nat.div_add_mod' v n).symm
      rw [hv', hz] at hvt; cases hvt
    have hcov : ∀ j : Fin n, ∃ v' ∈ ones n ρ J, v' % n = j.val := by
      intro j
      have hJ : pvar n i j ∈ J := (h3 _).1 (by rw [hz]; simp)
      obtain ⟨v', hv', hc⟩ := h2 _ hJ (pvar_isP n i j) (hz j)
      rw [pvar_div, pvar_mod] at hc
      rcases hc with hc | hc
      · exact absurd hc (hunm v' hv')
      · exact ⟨v', hv', hc⟩
    have hsub : range n ⊆ (ones n ρ J).image (· % n) := by
      intro j hj
      obtain ⟨v', hv', hc⟩ := hcov ⟨j, mem_range.1 hj⟩
      exact mem_image.2 ⟨v', hv', hc⟩
    have := (card_le_card hsub).trans card_image_le
    rw [card_range] at this
    exact this.trans (card_le_card (filter_subset _ _))
  · -- hole clause: two matched edges at hole `j`
    exfalso
    have ht : ∀ k : Fin (n + 1), (k = i ∨ k = i') → ρ (pvar n k j) = some true := by
      rintro k (rfl | rfl)
      · exact hf ⟨pvar n k j, false⟩ (by simp)
      · exact hf ⟨pvar n k j, false⟩ (by simp)
    have hmem : ∀ k : Fin (n + 1), (k = i ∨ k = i') → pvar n k j ∈ ones n ρ J := by
      intro k hk
      refine mem_filter.2 ⟨(h3 _).1 (by rw [ht k hk]; simp), pvar_isP n k j, ht k hk⟩
    have := h1 _ (hmem i (Or.inl rfl)) _ (hmem i' (Or.inr rfl))
      (Or.inr (by rw [pvar_mod, pvar_mod]))
    have h' := congrArg (· / n) this
    simp only [pvar_div] at h'
    exact absurd (Fin.ext h') (ne_of_lt hii)

end Adv

/-! ## The stifling simulation -/

theorem z2_add_self (a : ZMod 2) : a + a = 0 := by fin_cases a <;> decide

theorem z2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem lf_add (S : Finset ℕ) (x y : ℕ → ZMod 2) : lf S (x + y) = lf S x + lf S y := by
  unfold lf; simp [sum_add_distrib]

theorem lf_zero (S : Finset ℕ) : lf S 0 = 0 := by simp [lf]

/-- Affine maps over `F₂`. -/
def Aff (f : (ℕ → ZMod 2) → (ℕ → ZMod 2)) : Prop := ∀ u u', f (u + u') + f 0 = f u + f u'

theorem aff_add {f : (ℕ → ZMod 2) → (ℕ → ZMod 2)} (hf : Aff f) (u u' : ℕ → ZMod 2) :
    f (u + u') = f u + f u' + f 0 := by
  have := hf u u'
  funext w
  have hw := congrFun this w
  simp only [Pi.add_apply] at hw ⊢
  calc f (u + u') w = f (u + u') w + f 0 w + f 0 w := by rw [add_assoc, z2_add_self, add_zero]
    _ = f u w + f u' w + f 0 w := by rw [hw]

theorem aff_comp {f g : (ℕ → ZMod 2) → (ℕ → ZMod 2)} (hf : Aff f) (hg : Aff g) : Aff (f ∘ g) := by
  intro u u'
  simp only [Function.comp]
  rw [aff_add hg, aff_add hf, aff_add hf (g u)]
  funext w
  simp only [Pi.add_apply]
  have h1 := z2_add_self (f 0 w)
  have h2 := z2_add_self (f (g 0) w)
  linear_combination h1 + h2

section Sim

variable (n : ℕ) (U : Finset ℕ)

/-- Base value of an answered block. -/
def rb (ρ : BAsg) (j : ℕ) : Bool := (ρ j).getD false

/-- The invariant of the simulation. -/
structure Inv (Φ : Eqs) (ρ : BAsg) (J : Finset ℕ) (π : ℕ → ℕ) (P : (ℕ → ZMod 2) → (ℕ → ZMod 2)) :
    Prop where
  adv : AdvInv n ρ J
  aff : Aff P
  free : ∀ u w, w ∈ U → w / 3 ∉ J → P u w = u w
  out : ∀ u w, w ∉ U → P u w = 0
  stif : ∀ u j, j ∈ J → ∀ k < 3, k ≠ π j → lv j k ∈ U → P u (lv j k) = bv (rb ρ j)
  sol : ∀ u, satE Φ (P u)
  dep : ∀ u u', (∀ w ∈ U, w / 3 ∉ J → u w = u' w) → P u = P u'

end Sim

section Steps

variable {n : ℕ} {U : Finset ℕ}

theorem lv_div {v k : ℕ} (hk : k < 3) : lv v k / 3 = v := by unfold lv; omega

/-- Indicator of a coordinate. -/
def ee (w : ℕ) : ℕ → ZMod 2 := fun w' => if w' = w then 1 else 0

/-- **Leaves**: a leaf clause falsified on the parametrised subspace needs `n` base queries. -/
theorem leaf_bound {Φ : Eqs} {ρ : BAsg} {J : Finset ℕ} {π : ℕ → ℕ}
    {P : (ℕ → ZMod 2) → (ℕ → ZMod 2)} (hI : Inv n U Φ ρ J π P) {C' : Clause}
    (hU : C'.image Literal.var ⊆ U)
    (hsolve : ∀ x, satE Φ x → C' ∈ liftedPHP n ∧ cfalse x C') : n ≤ J.card := by
  obtain ⟨⟨C, hC, ch, rfl⟩, -⟩ := hsolve (P 0) (hI.sol 0)
  refine adv_clause n hI.adv hC fun l hl => ?_
  set v := l.var
  set c := ch l
  have hL1 : (⟨lv v (pr1 c), l.pos⟩ : Literal) ∈ liftC C ch :=
    mem_biUnion.2 ⟨l, hl, by simp [c, v]⟩
  have hL2 : (⟨lv v (pr2 c), l.pos⟩ : Literal) ∈ liftC C ch :=
    mem_biUnion.2 ⟨l, hl, by simp [c, v]⟩
  have hU1 : lv v (pr1 c) ∈ U := hU (mem_image.2 ⟨_, hL1, rfl⟩)
  have hU2 : lv v (pr2 c) ∈ U := hU (mem_image.2 ⟨_, hL2, rfl⟩)
  have hvJ : v ∈ J := by
    by_contra hv
    set u : ℕ → ZMod 2 := fun w => if w = lv v (pr1 c) then bv l.pos else 0
    have hf := (hsolve (P u) (hI.sol u)).2 _ hL1
    apply hf
    show P u (lv v (pr1 c)) = bv l.pos
    rw [hI.free u _ hU1 (by rw [lv_div (pr_lt c).1]; exact hv)]
    simp [u]
  have hf0 := (hsolve (P 0) (hI.sol 0)).2
  have hk : ∃ k ∈ ({pr1 c, pr2 c} : Finset ℕ), k ≠ π v := by
    by_cases h : pr1 c = π v
    · exact ⟨pr2 c, by simp, fun h' => pr_ne c (h.trans h'.symm)⟩
    · exact ⟨pr1 c, by simp, h⟩
  obtain ⟨k, hkm, hkπ⟩ := hk
  have hk3 : k < 3 := by
    simp only [mem_insert, mem_singleton] at hkm; rcases hkm with rfl | rfl
    · exact (pr_lt c).1
    · exact (pr_lt c).2
  have hkU : lv v k ∈ U := by
    simp only [mem_insert, mem_singleton] at hkm; rcases hkm with rfl | rfl
    · exact hU1
    · exact hU2
  have hfk : ¬ lsat (P 0) ⟨lv v k, l.pos⟩ := by
    simp only [mem_insert, mem_singleton] at hkm; rcases hkm with rfl | rfl
    · exact hf0 _ hL1
    · exact hf0 _ hL2
  have hst := hI.stif 0 v hvJ k hk3 hkπ hkU
  unfold lsat at hfk; simp only at hfk
  rw [hst] at hfk
  have hsome : ρ v = some (rb ρ v) := by
    have := (hI.adv.2.2 v).2 hvJ
    unfold rb; cases h : ρ v with
    | none => exact absurd h this
    | some b => rfl
  rw [hsome]
  congr 1
  cases hr : rb ρ v <;> cases hp : l.pos <;> simp_all [bv]

/-- The linear part of a query along the parametrisation. -/
def lam (S : Finset ℕ) (P : (ℕ → ZMod 2) → (ℕ → ZMod 2)) (u : ℕ → ZMod 2) : ZMod 2 :=
  lf S (P u) + lf S (P 0)

theorem lam_add {S : Finset ℕ} {P : (ℕ → ZMod 2) → (ℕ → ZMod 2)} (hP : Aff P) (u u' : ℕ → ZMod 2) :
    lam S P (u + u') = lam S P u + lam S P u' := by
  unfold lam
  rw [aff_add hP, lf_add, lf_add]
  ring

theorem lam_zero (S : Finset ℕ) (P : (ℕ → ZMod 2) → (ℕ → ZMod 2)) : lam S P 0 = 0 := by
  unfold lam; exact z2_add_self _

/-- **Constant queries**: if no free coordinate moves the query, it is constant. -/
theorem caseA {Φ : Eqs} {ρ : BAsg} {J : Finset ℕ} {π : ℕ → ℕ}
    {P : (ℕ → ZMod 2) → (ℕ → ZMod 2)} (hI : Inv n U Φ ρ J π P) {S : Finset ℕ}
    (hA : ∀ w ∈ U, w / 3 ∉ J → lam S P (ee w) = 0) (u : ℕ → ZMod 2) :
    lf S (P u) = lf S (P 0) := by
  set W := U.filter fun w => w / 3 ∉ J
  set uF : ℕ → ZMod 2 := ∑ w ∈ W, fun w' => if w' = w then u w else 0
  have huF : ∀ w ∈ U, w / 3 ∉ J → u w = uF w := by
    intro w hw hwJ
    simp only [uF, Finset.sum_apply]
    rw [Finset.sum_ite_eq, if_pos (mem_filter.2 ⟨hw, hwJ⟩)]
  have hP := hI.dep u uF huF
  have hsum : ∀ W' ⊆ W, lam S P (∑ w ∈ W', fun w' => if w' = w then u w else 0) = 0 := by
    intro W'
    induction W' using Finset.induction_on with
    | empty => intro _; simp only [sum_empty]; exact lam_zero S P
    | insert a W' ha ih =>
      intro hsub
      rw [sum_insert ha, lam_add hI.aff, ih ((subset_insert _ _).trans hsub), add_zero]
      have haW := mem_filter.1 (hsub (mem_insert_self a W'))
      rcases z2_cases (u a) with h0 | h1
      · have : (fun w' => if w' = a then u a else 0) = (0 : ℕ → ZMod 2) := by
          funext w'; split_ifs <;> simp [h0]
        rw [this]; exact lam_zero S P
      · have : (fun w' => if w' = a then u a else 0) = ee a := by
          funext w'; simp [ee, h1]
        rw [this]; exact hA a haW.1 haW.2
  have := hsum W subset_rfl
  unfold lam at this
  rw [hP]
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination this - (lf S (P 0)) * h2

/-- **Splitting queries**: stifle the block of a coordinate that moves the query, answer the base
query by the adversary, and keep the pivot free; both answers to the query remain possible. -/
theorem caseB {Φ : Eqs} {ρ : BAsg} {J : Finset ℕ} {π : ℕ → ℕ}
    {P : (ℕ → ZMod 2) → (ℕ → ZMod 2)} (hI : Inv n U Φ ρ J π P) {S : Finset ℕ} {w0 : ℕ}
    (hw0U : w0 ∈ U) (hw0J : w0 / 3 ∉ J) (hlam : lam S P (ee w0) = 1) (a : ZMod 2) :
    ∃ P', Inv n U (Φ ++ [(S, a)]) (upd ρ (w0 / 3) (adv n ρ J (w0 / 3))) (insert (w0 / 3) J)
      (Function.update π (w0 / 3) (w0 % 3)) P' := by
  set j := w0 / 3 with hj
  set b := adv n ρ J j
  set β := bv b
  set u0 : (ℕ → ZMod 2) → (ℕ → ZMod 2) := fun u w =>
    if w / 3 = j then (if w = w0 then 0 else β) else u w with hu0
  set τ : (ℕ → ZMod 2) → ZMod 2 := fun u => a + lf S (P (u0 u)) with hτ
  set σ : (ℕ → ZMod 2) → (ℕ → ZMod 2) := fun u w => if w = w0 then τ u else u0 u w with hσ
  have hβ2 := z2_add_self β
  have haffu0 : Aff u0 := by
    intro u u'; funext w
    simp only [hu0, Pi.add_apply, Pi.zero_apply]
    split_ifs <;> simp [hβ2]
  have hQ : Aff (P ∘ u0) := aff_comp hI.aff haffu0
  have haffσ : Aff σ := by
    intro u u'; funext w
    simp only [hσ, Pi.add_apply]
    split_ifs with h
    · simp only [hτ]
      have h1 := congrArg (lf S) (aff_add hQ u u')
      simp only [Function.comp, lf_add] at h1
      rw [h1]
      exact z2_g1 _ _ _ _
    · have := congrFun (haffu0 u u') w
      simpa using this
  have hw0j : w0 / 3 = j := rfl
  have hu0w0 : ∀ u, u0 u w0 = 0 := fun u => by simp only [hu0]; rw [if_pos hw0j]; simp
  -- the new query value
  have hval : ∀ u, lf S (P (σ u)) = a := by
    intro u
    rcases z2_cases (τ u) with h0 | h1
    · have : σ u = u0 u := by
        funext w; simp only [hσ]; split_ifs with h
        · rw [h0, h, hu0w0]
        · rfl
      rw [this]
      simp only [hτ] at h0
      exact z2_g2 _ _ h0
    · have : σ u = u0 u + ee w0 := by
        funext w; simp only [hσ, Pi.add_apply, ee]; split_ifs with h
        · rw [h1, h, hu0w0, zero_add]
        · rw [add_zero]
      rw [this, aff_add hI.aff, lf_add, lf_add]
      unfold lam at hlam
      simp only [hτ] at h1
      exact z2_g3 _ _ _ _ hlam h1
  refine ⟨P ∘ σ, ⟨advInv_upd n hI.adv hw0J, aff_comp hI.aff haffσ, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro u w hwU hwJ
    have hwj : w / 3 ≠ j := fun h => hwJ (h ▸ mem_insert_self _ _)
    have hwJ' : w / 3 ∉ J := fun h => hwJ (mem_insert_of_mem h)
    simp only [Function.comp]
    rw [hI.free _ w hwU hwJ']
    have hne : w ≠ w0 := fun h => hwj (h ▸ rfl)
    simp [hσ, hne, hu0, hwj]
  · intro u w hw; exact hI.out _ w hw
  · intro u j' hj' k hk hkπ hkU
    simp only [Function.comp]
    by_cases hjj : j' = j
    · rw [hjj] at hkπ hkU ⊢
      have hkπ' : k ≠ w0 % 3 := by simpa [Function.update] using hkπ
      have hblk : lv j k / 3 = j := lv_div hk
      rw [hI.free _ _ hkU (by rw [hblk]; exact hw0J)]
      have hne : lv j k ≠ w0 := by
        intro h; apply hkπ'; rw [← h]; unfold lv; omega
      simp only [hσ, hne, if_false, hu0, hblk, if_true]
      simp [rb, upd, β, b]
    · have hj'J : j' ∈ J := (mem_insert.1 hj').resolve_left hjj
      have hπ : Function.update π j (w0 % 3) j' = π j' := Function.update_of_ne hjj _ _
      rw [hπ] at hkπ
      rw [hI.stif _ j' hj'J k hk hkπ hkU]
      simp [rb, upd, hjj]
  · intro u e he
    rcases List.mem_append.1 he with he | he
    · exact hI.sol _ e he
    · simp only [List.mem_singleton] at he; subst he; exact hval u
  · intro u u' hag
    simp only [Function.comp]
    -- `σ u` and `σ u'` agree on the old free coordinates
    apply hI.dep
    intro w hwU hwJ
    by_cases hwj : w / 3 = j
    · simp only [hσ]
      split_ifs with hw
      · simp only [hτ]
        congr 2
        apply hI.dep
        intro w' hw'U hw'J
        simp only [hu0]
        by_cases h' : w' / 3 = j
        · simp [h']
        · simp only [h', if_false]
          exact hag w' hw'U (by
            intro hm; rcases mem_insert.1 hm with h'' | h''
            · exact h' h''
            · exact hw'J h'')
      · simp [hu0, hwj]
    · have hwJ' : w / 3 ∉ insert j J := by
        intro hm; rcases mem_insert.1 hm with h'' | h''
        · exact hwj h''
        · exact hwJ h''
      have hne : w ≠ w0 := fun h => hwj (h ▸ rfl)
      simp only [hσ, hne, if_false, hu0, hwj]
      exact hag w hwU hwJ'

end Steps

/-! ## The lower bound -/

/-- **Main induction**: a tree solving the lifted search problem on a parametrised subspace
with `|J|` stifled blocks has at least `2^{n - |J|}` leaves. -/
theorem pdt_leaves (n : ℕ) (U : Finset ℕ) : ∀ (T : PDT) (Φ : Eqs) (ρ : BAsg) (J : Finset ℕ)
    (π : ℕ → ℕ) (P : (ℕ → ZMod 2) → (ℕ → ZMod 2)), T.vars ⊆ U →
    Solves (liftedPHP n) T Φ → Inv n U Φ ρ J π P → 2 ^ n ≤ T.nl * 2 ^ J.card := by
  intro T
  induction T with
  | leaf C =>
    intro Φ ρ J π P hU hsolve hI
    have := leaf_bound hI (C' := C) hU (fun x hx => hsolve x hx)
    simp only [PDT.nl, one_mul]
    exact Nat.pow_le_pow_right (by norm_num) this
  | node S t0 t1 ih0 ih1 =>
    intro Φ ρ J π P hU hsolve hI
    simp only [PDT.vars, union_subset_iff] at hU
    obtain ⟨⟨hSU, hU0⟩, hU1⟩ := hU
    have hs0 : Solves (liftedPHP n) t0 (Φ ++ [(S, 0)]) := by
      intro x hx
      have hΦ : satE Φ x := fun e he => hx e (List.mem_append_left _ he)
      have hS : lf S x = 0 := hx (S, 0) (by simp)
      have := hsolve x hΦ
      simpa [PDT.leafOf, hS] using this
    have hs1 : Solves (liftedPHP n) t1 (Φ ++ [(S, 1)]) := by
      intro x hx
      have hΦ : satE Φ x := fun e he => hx e (List.mem_append_left _ he)
      have hS : lf S x = 1 := hx (S, 1) (by simp)
      have := hsolve x hΦ
      simpa [PDT.leafOf, hS] using this
    simp only [PDT.nl]
    by_cases hA : ∀ w ∈ U, w / 3 ∉ J → lam S P (ee w) = 0
    · have hc := caseA hI hA
      have hext : ∀ a, lf S (P 0) = a → Inv n U (Φ ++ [(S, a)]) ρ J π P := by
        intro a ha
        refine ⟨hI.adv, hI.aff, hI.free, hI.out, hI.stif, fun u e he => ?_, hI.dep⟩
        rcases List.mem_append.1 he with he | he
        · exact hI.sol u e he
        · simp only [List.mem_singleton] at he; subst he; rw [hc u]; exact ha
      rcases z2_cases (lf S (P 0)) with h0 | h1
      · have := ih0 _ ρ J π P hU0 hs0 (hext 0 h0)
        rw [add_mul]; exact this.trans (Nat.le_add_right _ _)
      · have := ih1 _ ρ J π P hU1 hs1 (hext 1 h1)
        rw [add_mul]; exact this.trans (Nat.le_add_left _ _)
    · push Not at hA
      obtain ⟨w0, hw0U, hw0J, hlam⟩ := hA
      have hlam1 : lam S P (ee w0) = 1 := (z2_cases _).resolve_left hlam
      obtain ⟨P0, hP0⟩ := caseB hI hw0U hw0J hlam1 0
      obtain ⟨P1, hP1⟩ := caseB hI hw0U hw0J hlam1 1
      have h0 := ih0 _ _ _ _ _ hU0 hs0 hP0
      have h1 := ih1 _ _ _ _ _ hU1 hs1 hP1
      rw [card_insert_of_notMem hw0J, pow_succ] at h0 h1
      nlinarith

/-- The initial parametrisation. -/
def P0 (U : Finset ℕ) : (ℕ → ZMod 2) → (ℕ → ZMod 2) := fun u w => if w ∈ U then u w else 0

theorem inv_init (n : ℕ) (U : Finset ℕ) : Inv n U [] (fun _ => none) ∅ (fun _ => 0) (P0 U) := by
  refine ⟨advInv_empty n, fun u u' => ?_, fun u w hw _ => by simp [P0, hw],
    fun u w hw => by simp [P0, hw], fun u j hj => by simp at hj, fun u e he => by simp at he,
    fun u u' h => ?_⟩
  · funext w; simp only [P0, Pi.add_apply, Pi.zero_apply]; split_ifs <;> simp
  · funext w; simp only [P0]; split_ifs with hw
    · exact h w hw (by simp)
    · rfl

/-- **Parity decision trees for `PHP_n ∘ MAJ₃` have at least `2^n` leaves.** -/
theorem pdt_lifted_php (n : ℕ) (T : PDT) (h : Solves (liftedPHP n) T []) : 2 ^ n ≤ T.nl := by
  have := pdt_leaves n T.vars T [] _ _ _ _ subset_rfl h (inv_init n T.vars)
  simpa using this

/-! ## Tree-like `Res(⊕)` -/

/-- Linear clauses: disjunctions of equations `∑_{w ∈ S} x_w = a`. -/
abbrev LClause := Finset (Finset ℕ × ZMod 2)

def lsatL (x : ℕ → ZMod 2) (L : LClause) : Prop := ∃ e ∈ L, lf e.1 x = e.2

/-- A clause as a linear clause. -/
def ofClause (C : Clause) : LClause := C.image fun l => ({l.var}, bv l.pos)

/-- Tree-like `Res(⊕)` derivations, indexed by the number of axiom leaves. -/
inductive RLD (Ax : Set Clause) : LClause → ℕ → Prop
  | ax {C} : C ∈ Ax → RLD Ax (ofClause C) 1
  | weak {L L' s} : RLD Ax L s → L ⊆ L' → RLD Ax L' s
  | comb {C D : LClause} {S1 S2 : Finset ℕ} {a1 a2 : ZMod 2} {s1 s2 : ℕ} :
      RLD Ax (insert (S1, a1) C) s1 → RLD Ax (insert (S2, a2) D) s2 →
      RLD Ax (C ∪ D ∪ {(symmDiff S1 S2, a1 + a2)}) (s1 + s2)
  | simp {L s} : RLD Ax (insert (∅, 1) L) s → RLD Ax L s

theorem lf_symmDiff (S1 S2 : Finset ℕ) (x : ℕ → ZMod 2) :
    lf (symmDiff S1 S2) x = lf S1 x + lf S2 x := by
  unfold lf
  have e1 : ∑ w ∈ S1, x w = ∑ w ∈ S1 \ S2, x w + ∑ w ∈ S1 ∩ S2, x w := by
    rw [← sum_union (disjoint_sdiff_inter S1 S2), sdiff_union_inter]
  have e2 : ∑ w ∈ S2, x w = ∑ w ∈ S2 \ S1, x w + ∑ w ∈ S1 ∩ S2, x w := by
    rw [inter_comm, ← sum_union (disjoint_sdiff_inter S2 S1), sdiff_union_inter]
  have e3 : ∑ w ∈ symmDiff S1 S2, x w = ∑ w ∈ S1 \ S2, x w + ∑ w ∈ S2 \ S1, x w := by
    rw [symmDiff_def, sup_eq_union, sum_union disjoint_sdiff_sdiff]
  rw [e1, e2, e3]
  exact z2_g5 _ _ _

/-- **Soundness by trees**: a tree-like `Res(⊕)` derivation with `s` axiom leaves yields a parity
decision tree with at most `s` leaves that, on every input falsifying the conclusion, reaches an
axiom falsified by the input. -/
theorem tree_to_pdt {Ax : Set Clause} {L : LClause} {s : ℕ} (h : RLD Ax L s) :
    ∃ T : PDT, T.nl ≤ s ∧ ∀ x, ¬ lsatL x L → T.leafOf x ∈ Ax ∧ cfalse x (T.leafOf x) := by
  induction h with
  | ax hC =>
    rename_i C
    refine ⟨PDT.leaf C, le_rfl, fun x hx => ⟨hC, fun l hl hs => hx ⟨_, mem_image.2 ⟨l, hl, rfl⟩, ?_⟩⟩⟩
    simp [lf]; exact hs
  | weak _ hsub ih =>
    obtain ⟨T, hT, hTx⟩ := ih
    exact ⟨T, hT, fun x hx => hTx x fun ⟨e, he, hv⟩ => hx ⟨e, hsub he, hv⟩⟩
  | comb _ _ ih1 ih2 =>
    rename_i C D S1 S2 a1 a2 s1 s2 _ _
    obtain ⟨T1, hT1, hT1x⟩ := ih1
    obtain ⟨T2, hT2, hT2x⟩ := ih2
    refine ⟨PDT.node S1 (if a1 = 0 then T2 else T1) (if a1 = 0 then T1 else T2), ?_, fun x hx => ?_⟩
    · simp only [PDT.nl]; split_ifs <;> omega
    · have hC : ¬ lsatL x C := fun ⟨e, he, hv⟩ => hx ⟨e, mem_union_left _ (mem_union_left _ he), hv⟩
      have hD : ¬ lsatL x D := fun ⟨e, he, hv⟩ => hx ⟨e, mem_union_left _ (mem_union_right _ he), hv⟩
      have hS : lf S1 x + lf S2 x ≠ a1 + a2 := fun hv =>
        hx ⟨_, mem_union_right _ (mem_singleton_self _), by rw [lf_symmDiff]; exact hv⟩
      have h1 : lf S1 x = a1 → ¬ lsatL x (insert (S2, a2) D) := by
        intro he ⟨e, hm, hv⟩
        rcases mem_insert.1 hm with rfl | hm
        · exact hS (by rw [he]; exact congrArg (a1 + ·) hv)
        · exact hD ⟨e, hm, hv⟩
      have h2 : lf S1 x ≠ a1 → ¬ lsatL x (insert (S1, a1) C) := by
        intro he ⟨e, hm, hv⟩
        rcases mem_insert.1 hm with rfl | hm
        · exact he hv
        · exact hC ⟨e, hm, hv⟩
      simp only [PDT.leafOf]
      rcases z2_cases a1 with ha | ha <;> rcases z2_cases (lf S1 x) with hl | hl <;>
        simp only [ha, hl, if_true, if_false, zero_ne_one, one_ne_zero] <;>
        first
        | exact hT2x x (h1 (by rw [ha, hl]))
        | exact hT1x x (h2 (by rw [ha, hl]; decide))
  | simp _ ih =>
    obtain ⟨T, hT, hTx⟩ := ih
    refine ⟨T, hT, fun x hx => hTx x fun ⟨e, he, hv⟩ => ?_⟩
    rcases mem_insert.1 he with rfl | he
    · simp [lf] at hv
    · exact hx ⟨e, he, hv⟩

/-- **Tree-like `Res(⊕)` refutations of `PHP_n ∘ MAJ₃` have at least `2^n` axiom leaves.** -/
theorem treelike_reslin_php (n s : ℕ) (h : RLD (liftedPHP n) ∅ s) : 2 ^ n ≤ s := by
  obtain ⟨T, hT, hTx⟩ := tree_to_pdt h
  have hsol : Solves (liftedPHP n) T [] := fun x _ => hTx x fun ⟨e, he, _⟩ => by simp at he
  exact (pdt_lifted_php n T hsol).trans hT

/-! ## Non vacuity: `PHP_n ∘ MAJ₃` is unsatisfiable -/

/-- `MAJ₃` of a block. -/
def maj (x : ℕ → ZMod 2) (v : ℕ) : Bool :=
  decide ((x (lv v 0) = 1 ∧ x (lv v 1) = 1) ∨ (x (lv v 0) = 1 ∧ x (lv v 2) = 1) ∨
    (x (lv v 1) = 1 ∧ x (lv v 2) = 1))

theorem pair_of_maj (x : ℕ → ZMod 2) (v : ℕ) (b : Bool) (h : maj x v ≠ b) :
    ∃ c : Fin 3, x (lv v (pr1 c)) ≠ bv b ∧ x (lv v (pr2 c)) ≠ bv b := by
  have p10 : pr1 0 = 0 := rfl
  have p20 : pr2 0 = 1 := rfl
  have p11 : pr1 1 = 0 := rfl
  have p21 : pr2 1 = 2 := rfl
  have p12 : pr1 2 = 1 := rfl
  have p22 : pr2 2 = 2 := rfl
  unfold maj at h
  rcases z2_cases (x (lv v 0)) with h0 | h0 <;> rcases z2_cases (x (lv v 1)) with h1 | h1 <;>
    rcases z2_cases (x (lv v 2)) with h2 | h2 <;> cases b <;>
    simp only [h0, h1, h2, z2_01, z2_10, and_true, true_and, and_false, false_and, or_false,
      false_or, or_true, true_or, bv, Bool.false_eq_true, if_false, if_true] at h ⊢ <;>
    first
    | (simp at h; done)
    | (refine ⟨0, ?_⟩; rw [p10, p20, h0, h1]; exact ⟨z2_0ne1, z2_0ne1⟩)
    | (refine ⟨1, ?_⟩; rw [p11, p21, h0, h2]; exact ⟨z2_0ne1, z2_0ne1⟩)
    | (refine ⟨2, ?_⟩; rw [p12, p22, h1, h2]; exact ⟨z2_0ne1, z2_0ne1⟩)
    | (refine ⟨0, ?_⟩; rw [p10, p20, h0, h1]; exact ⟨z2_1ne0, z2_1ne0⟩)
    | (refine ⟨1, ?_⟩; rw [p11, p21, h0, h2]; exact ⟨z2_1ne0, z2_1ne0⟩)
    | (refine ⟨2, ?_⟩; rw [p12, p22, h1, h2]; exact ⟨z2_1ne0, z2_1ne0⟩)

/-- Every input falsifies some clause of `PHP_n ∘ MAJ₃`. -/
theorem lifted_unsat (n : ℕ) (x : ℕ → ZMod 2) : ∃ C' ∈ liftedPHP n, cfalse x C' := by
  have hu := phpCNF_unsat n
  have : ∃ C ∈ phpCNF n, ¬ clauseSat (maj x) C := by
    by_contra hc; push Not at hc; exact hu ⟨maj x, hc⟩
  obtain ⟨C, hC, hns⟩ := this
  have hl : ∀ l ∈ C, maj x l.var ≠ l.pos := fun l hl h => hns ⟨l, hl, h⟩
  let ch : Literal → Fin 3 := fun l =>
    if h : maj x l.var ≠ l.pos then Classical.choose (pair_of_maj x l.var l.pos h) else 0
  refine ⟨liftC C ch, ⟨C, hC, ch, rfl⟩, fun L hL hs => ?_⟩
  obtain ⟨l, hlC, hLl⟩ := mem_biUnion.1 hL
  have hspec := Classical.choose_spec (pair_of_maj x l.var l.pos (hl l hlC))
  have hch : ch l = Classical.choose (pair_of_maj x l.var l.pos (hl l hlC)) := by
    simp only [ch, dif_pos (hl l hlC)]
  simp only [mem_insert, mem_singleton] at hLl
  unfold lsat at hs
  rcases hLl with rfl | rfl
  · simp only at hs; rw [hch] at hs; exact hspec.1 hs
  · simp only at hs; rw [hch] at hs; exact hspec.2 hs

end

end RL

end SATurday.ProofComplexity
