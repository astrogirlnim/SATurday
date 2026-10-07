import Theory.ProofComplexity.Resolution
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Cutting planes and clique coloring (Ladder Rung R3)

R3 candidate adopted 2026-10-07: a super polynomial lower bound for cutting planes
(CP) refutations of the clique coloring formulas, by monotone feasible interpolation
(Pudlák 1997) plus a lower bound for monotone real circuits that separate
`k` cliques from `k - 1` colorings.

This module holds the accepted surface:

1. CP lines (integer linear inequalities over 0/1 variables), dag like CP proofs
   as line lists with addition, positive scaling and division with rounding,
   and soundness (`cpRefutes_unsat`).
2. Clique coloring CNFs `ccCNF n k m` split into the clique part `cliqueCNF`
   (edge and clique variables) and the coloring part `colorCNF` (edge and color
   variables), with unsatisfiability for `m < k` (non vacuity witness).
3. Monotone real circuits as straight line programs (dag size), evaluation on
   0/1 inputs.
4. The three statements of the R3 plan as named propositions, and the packaging
   theorem `cp_superpoly_of_interp_lb` that derives the CP lower bound from the
   interpolation theorem and the circuit lower bound.

The two research obligations live in `CuttingPlanesFrontier` at the end of the file.

Interpolation is known not to extend above this level (Bonet Pitassi Raz;
Krajíček Pudlák); this result is R3 only, not the R4 plan.

LOG: R3 CuttingPlanes module (CP, clique coloring, monotone real circuits)
-/

namespace SATurday.ProofComplexity

open scoped BigOperators

noncomputable section

/-! ## Cutting planes lines -/

/-- A CP line `∑ coef i * x i ≥ rhs` with integer coefficients of finite support. -/
structure Ineq where
  coef : ℕ →₀ ℤ
  rhs : ℤ

/-- Value of a 0/1 variable. -/
def bitZ (a : Assignment) (i : ℕ) : ℤ := if a i then 1 else 0

/-- Left hand side of a line under an assignment. -/
def Ineq.lhs (a : Assignment) (I : Ineq) : ℤ := I.coef.sum fun i c => c * bitZ a i

/-- An assignment satisfies a line. -/
def Ineq.Sat (a : Assignment) (I : Ineq) : Prop := I.rhs ≤ I.lhs a

instance : Add Ineq := ⟨fun I J => ⟨I.coef + J.coef, I.rhs + J.rhs⟩⟩

/-- Positive scaling of a line. -/
def Ineq.scale (c : ℕ) (I : Ineq) : Ineq := ⟨(c : ℤ) • I.coef, (c : ℤ) * I.rhs⟩

/-- The literal as a signed unit: `x` or `- x`. -/
def litCoef (l : Literal) : ℕ →₀ ℤ := Finsupp.single l.var (if l.pos then 1 else -1)

/-- The CP translation of a clause: `∑ pos x + ∑ neg (1 - x) ≥ 1`. -/
def clauseIneq (C : Clause) : Ineq :=
  ⟨∑ l ∈ C, litCoef l, 1 - ((C.filter fun l => l.pos = false).card : ℤ)⟩

/-- `x i ≥ 0`. -/
def lowerAx (i : ℕ) : Ineq := ⟨Finsupp.single i 1, 0⟩

/-- `- x i ≥ - 1`. -/
def upperAx (i : ℕ) : Ineq := ⟨Finsupp.single i (-1), -1⟩

/-- One CP inference from the earlier lines `prev`.
Division: from `c * coef ≥ rhs'` infer `coef ≥ rhs` whenever `c * (rhs - 1) < rhs'`,
that is `rhs ≤ ⌈rhs' / c⌉`. -/
def CPStep (F : CNF) (prev : List Ineq) (I : Ineq) : Prop :=
  (∃ C ∈ F, I = clauseIneq C) ∨
  (∃ i, I = lowerAx i) ∨ (∃ i, I = upperAx i) ∨
  (∃ J ∈ prev, ∃ K ∈ prev, I = J + K) ∨
  (∃ J ∈ prev, ∃ c : ℕ, I = J.scale c) ∨
  (∃ J ∈ prev, ∃ c : ℕ, 0 < c ∧ J.coef = (c : ℤ) • I.coef ∧ (c : ℤ) * (I.rhs - 1) < J.rhs)

/-- A dag like CP proof: every line follows from earlier lines. Its size is the
number of lines. -/
def CPProof (F : CNF) (L : List Ineq) : Prop :=
  ∀ k (hk : k < L.length), CPStep F (L.take k) (L.get ⟨k, hk⟩)

/-- A CP refutation: a proof containing a line `0 ≥ b` with `b > 0`. -/
def CPRefutes (F : CNF) (L : List Ineq) : Prop :=
  CPProof F L ∧ ∃ I ∈ L, I.coef = 0 ∧ 0 < I.rhs

/-! ## Soundness -/

theorem bitZ_nonneg (a : Assignment) (i : ℕ) : 0 ≤ bitZ a i := by
  unfold bitZ; split <;> norm_num

theorem bitZ_le_one (a : Assignment) (i : ℕ) : bitZ a i ≤ 1 := by
  unfold bitZ; split <;> norm_num

theorem Ineq.lhs_add (a : Assignment) (I J : Ineq) : (I + J).lhs a = I.lhs a + J.lhs a := by
  show (I.coef + J.coef).sum _ = _
  unfold Ineq.lhs
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

theorem Ineq.lhs_smul (a : Assignment) (c : ℤ) (f : ℕ →₀ ℤ) :
    (c • f).sum (fun i d => d * bitZ a i) = c * f.sum (fun i d => d * bitZ a i) := by
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_eq_mul]; ring

theorem Ineq.lhs_scale (a : Assignment) (c : ℕ) (I : Ineq) :
    (I.scale c).lhs a = c * I.lhs a := Ineq.lhs_smul a c I.coef

theorem lhs_single (a : Assignment) (i : ℕ) (c : ℤ) :
    (Finsupp.single i c).sum (fun j d => d * bitZ a j) = c * bitZ a i :=
  Finsupp.sum_single_index (by simp)

theorem lhs_finset_sum (a : Assignment) (s : Finset Literal) (g : Literal → ℕ →₀ ℤ) :
    (∑ l ∈ s, g l).sum (fun i d => d * bitZ a i) =
      ∑ l ∈ s, (g l).sum (fun i d => d * bitZ a i) :=
  (Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by ring)).symm

/-- Value of a literal as `0` or `1`. -/
def litVal (a : Assignment) (l : Literal) : ℤ := if l.pos then bitZ a l.var else 1 - bitZ a l.var

theorem litVal_nonneg (a : Assignment) (l : Literal) : 0 ≤ litVal a l := by
  unfold litVal; have := bitZ_nonneg a l.var; have := bitZ_le_one a l.var
  split <;> omega

theorem litVal_of_sat {a : Assignment} {l : Literal} (h : litSat a l) : litVal a l = 1 := by
  unfold litSat at h; unfold litVal bitZ
  cases hp : l.pos <;> simp_all

theorem clauseIneq_sat {a : Assignment} {C : Clause} (h : clauseSat a C) :
    (clauseIneq C).Sat a := by
  obtain ⟨l0, hl0, hs⟩ := h
  unfold Ineq.Sat Ineq.lhs clauseIneq
  simp only
  rw [lhs_finset_sum]
  have key : ∀ l ∈ C, (litCoef l).sum (fun i d => d * bitZ a i) =
      litVal a l - (if l.pos = false then 1 else 0) := by
    intro l _
    unfold litCoef
    rw [lhs_single]
    unfold litVal
    cases l.pos <;> simp
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib]
  have hcount : (∑ l ∈ C, (if l.pos = false then (1 : ℤ) else 0)) =
      ((C.filter fun l => l.pos = false).card : ℤ) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcount]
  have hge : 1 ≤ ∑ l ∈ C, litVal a l := by
    rw [← Finset.add_sum_erase C _ hl0, litVal_of_sat hs]
    have := Finset.sum_nonneg (fun l (_ : l ∈ C.erase l0) => litVal_nonneg a l)
    omega
  omega

theorem cpStep_sound {F : CNF} {a : Assignment} (ha : cnfSat a F) {prev : List Ineq}
    (hprev : ∀ J ∈ prev, J.Sat a) {I : Ineq} (h : CPStep F prev I) : I.Sat a := by
  rcases h with ⟨C, hC, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨J, hJ, K, hK, rfl⟩ | ⟨J, hJ, c, rfl⟩ |
      ⟨J, hJ, c, hc, hcoef, hrhs⟩
  · exact clauseIneq_sat (ha C hC)
  · unfold Ineq.Sat Ineq.lhs lowerAx; simp only; rw [lhs_single]
    have := bitZ_nonneg a i; linarith
  · unfold Ineq.Sat Ineq.lhs upperAx; simp only; rw [lhs_single]
    have := bitZ_le_one a i; linarith
  · unfold Ineq.Sat; rw [Ineq.lhs_add]
    have h1 := hprev J hJ; have h2 := hprev K hK
    unfold Ineq.Sat at h1 h2
    show J.rhs + K.rhs ≤ _
    linarith
  · unfold Ineq.Sat; rw [Ineq.lhs_scale]
    have h1 := hprev J hJ; unfold Ineq.Sat at h1
    show (c : ℤ) * J.rhs ≤ _
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · have h1 := hprev J hJ
    unfold Ineq.Sat Ineq.lhs at h1 ⊢
    rw [hcoef, Ineq.lhs_smul] at h1
    have hc' : (0 : ℤ) < c := by exact_mod_cast hc
    by_contra hlt
    rw [not_le] at hlt
    have : I.coef.sum (fun i d => d * bitZ a i) ≤ I.rhs - 1 := by omega
    have := mul_le_mul_of_nonneg_left this hc'.le
    linarith

theorem cpProof_sound {F : CNF} {a : Assignment} (ha : cnfSat a F) {L : List Ineq}
    (hL : CPProof F L) : ∀ I ∈ L, I.Sat a := by
  have key : ∀ k ≤ L.length, ∀ I ∈ L.take k, I.Sat a := by
    intro k
    induction k with
    | zero => intro _ I hI; simp at hI
    | succ k ih =>
        intro hk I hI
        rw [List.take_add_one] at hI
        rcases List.mem_append.1 hI with h | h
        · exact ih (by omega) I h
        · have hk' : k < L.length := by omega
          rw [List.getElem?_eq_getElem hk'] at h
          simp only [Option.toList_some, List.mem_singleton] at h
          subst h
          exact cpStep_sound ha (ih (by omega)) (hL k hk')
  intro I hI
  exact key L.length le_rfl I (by rwa [List.take_length])

/-- CP is sound: a refutable CNF is unsatisfiable. -/
theorem cpRefutes_unsat {F : CNF} {L : List Ineq} (h : CPRefutes F L) : ¬ Satisfiable F := by
  rintro ⟨a, ha⟩
  obtain ⟨hL, I, hI, h0, hpos⟩ := h
  have hs := cpProof_sound ha hL I hI
  unfold Ineq.Sat Ineq.lhs at hs
  rw [h0] at hs
  simp at hs
  omega

/-! ## Clique coloring formulas -/

/-- Edge variable of the unordered pair `{i, j}`. -/
def eVar (n : ℕ) (i j : Fin n) : ℕ := min i.val j.val * n + max i.val j.val

/-- Clique variable: the `u`th clique member is vertex `i`. -/
def qVar (n : ℕ) {k : ℕ} (u : Fin k) (i : Fin n) : ℕ := n * n + u.val * n + i.val

/-- Color variable: vertex `i` has color `c`. -/
def rVar (n k : ℕ) {m : ℕ} (i : Fin n) (c : Fin m) : ℕ := n * n + k * n + i.val * m + c.val

/-- The clique part: a `k` clique in the graph given by the edge variables. -/
def cliqueCNF (n k : ℕ) : CNF :=
  (Finset.univ.image fun u : Fin k =>
      (Finset.univ.image fun i : Fin n => (⟨qVar n u i, true⟩ : Literal))) ∪
  ((Finset.univ.filter fun t : Fin k × Fin k × Fin n => t.1 ≠ t.2.1).image fun t =>
      ({⟨qVar n t.1 t.2.2, false⟩, ⟨qVar n t.2.1 t.2.2, false⟩} : Clause)) ∪
  ((Finset.univ.filter fun t : Fin k × Fin k × Fin n × Fin n =>
      t.1 ≠ t.2.1 ∧ t.2.2.1 ≠ t.2.2.2).image fun t =>
      ({⟨qVar n t.1 t.2.2.1, false⟩, ⟨qVar n t.2.1 t.2.2.2, false⟩,
        ⟨eVar n t.2.2.1 t.2.2.2, true⟩} : Clause))

/-- The coloring part: a proper `m` coloring of the graph given by the edge variables. -/
def colorCNF (n k m : ℕ) : CNF :=
  (Finset.univ.image fun i : Fin n =>
      (Finset.univ.image fun c : Fin m => (⟨rVar n k i c, true⟩ : Literal))) ∪
  ((Finset.univ.filter fun t : Fin n × Fin n × Fin m => t.1 ≠ t.2.1).image fun t =>
      ({⟨rVar n k t.1 t.2.2, false⟩, ⟨rVar n k t.2.1 t.2.2, false⟩,
        ⟨eVar n t.1 t.2.1, false⟩} : Clause))

/-- Clique coloring: a graph with a `k` clique that is `m` colorable. -/
def ccCNF (n k m : ℕ) : CNF := cliqueCNF n k ∪ colorCNF n k m

theorem litSat_true {a : Assignment} {v : ℕ} : litSat a ⟨v, true⟩ ↔ a v = true := Iff.rfl
theorem litSat_false {a : Assignment} {v : ℕ} : litSat a ⟨v, false⟩ ↔ a v = false := Iff.rfl

/-- Non vacuity witness: clique coloring is unsatisfiable when `m < k`. -/
theorem ccCNF_unsat {n k m : ℕ} (hmk : m < k) : ¬ Satisfiable (ccCNF n k m) := by
  rintro ⟨a, ha⟩
  have hq : ∀ u : Fin k, ∃ i : Fin n, a (qVar n u i) = true := by
    intro u
    have h := ha _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image.2 ⟨u, Finset.mem_univ _, rfl⟩))))
    obtain ⟨l, hl, hs⟩ := h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hl
    exact ⟨i, hs⟩
  choose f hf using hq
  have hdist : ∀ u u' : Fin k, u ≠ u' → f u ≠ f u' := by
    intro u u' huu heq
    have h := ha _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨(u, u', f u), by simp [huu], rfl⟩))))
    obtain ⟨l, hl, hs⟩ := h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · rw [litSat_false, hf u] at hs; exact Bool.noConfusion hs
    · rw [litSat_false, heq, hf u'] at hs; exact Bool.noConfusion hs
  have hedge : ∀ u u' : Fin k, u ≠ u' → a (eVar n (f u) (f u')) = true := by
    intro u u' huu
    have h := ha _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨(u, u', f u, f u'), by simp [huu, hdist u u' huu], rfl⟩)))
    obtain ⟨l, hl, hs⟩ := h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · rw [litSat_false, hf u] at hs; exact Bool.noConfusion hs
    · rw [litSat_false, hf u'] at hs; exact Bool.noConfusion hs
    · exact hs
  have hc : ∀ i : Fin n, ∃ c : Fin m, a (rVar n k i c) = true := by
    intro i
    have h := ha _ (Finset.mem_union_right _ (Finset.mem_union_left _
      (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)))
    obtain ⟨l, hl, hs⟩ := h
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hl
    exact ⟨c, hs⟩
  choose g hg using hc
  obtain ⟨u, u', huu, hcol⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun u => g (f u))
    (by simpa using hmk)
  have h := ha _ (Finset.mem_union_right _ (Finset.mem_union_right _
    (Finset.mem_image.2 ⟨(f u, f u', g (f u)), by simp [hdist u u' huu], rfl⟩)))
  obtain ⟨l, hl, hs⟩ := h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl | rfl
  · rw [litSat_false, hg] at hs; exact Bool.noConfusion hs
  · rw [litSat_false] at hs; rw [show g (f u) = g (f u') from hcol, hg] at hs
    exact Bool.noConfusion hs
  · rw [litSat_false, hedge u u' huu] at hs; exact Bool.noConfusion hs

/-! ## Monotone real circuits -/

/-- A gate of a monotone real circuit, as a straight line program: an input
variable, a real constant, or a binary function of two earlier gate values. -/
inductive MGate where
  | inp (v : ℕ)
  | cst (c : ℝ)
  | op (f : ℝ → ℝ → ℝ) (i j : ℕ)

/-- Monotone gates: binary functions nondecreasing in both arguments. -/
def MGate.Mono : MGate → Prop
  | .op f _ _ => ∀ x x' y y' : ℝ, x ≤ x' → y ≤ y' → f x y ≤ f x' y'
  | _ => True

/-- Value of a gate given the earlier values (missing indices read as `0`). -/
def MGate.val (a : Assignment) (vals : List ℝ) : MGate → ℝ
  | .inp v => if a v then 1 else 0
  | .cst c => c
  | .op f i j => f (vals.getD i 0) (vals.getD j 0)

/-- All gate values, left to right. -/
def mcVals (a : Assignment) (C : List MGate) : List ℝ :=
  C.foldl (fun vals g => vals ++ [g.val a vals]) []

/-- Output of a circuit: the value of its last gate. Size is `C.length`. -/
def mcEval (a : Assignment) (C : List MGate) : ℝ := (mcVals a C).getLastD 0

/-- Every gate is monotone. -/
def MCMono (C : List MGate) : Prop := ∀ g ∈ C, g.Mono

/-- The circuit reads only variables in `P`. -/
def MCInputsIn (P : Finset ℕ) (C : List MGate) : Prop := ∀ v, MGate.inp v ∈ C → v ∈ P

/-! ## The R3 plan as propositions -/

/-- Edge variables of `n` vertex graphs. -/
def edgeVars (n : ℕ) : Finset ℕ :=
  (Finset.univ.filter fun t : Fin n × Fin n => t.1 ≠ t.2).image fun t => eVar n t.1 t.2

/-- Clique size used for the lower bound: `⌊n^{1/4}⌋`. -/
def ccK (n : ℕ) : ℕ := Nat.sqrt (Nat.sqrt n)

/-- Monotone feasible interpolation for CP (Pudlák 1997): a CP refutation of
`A(p, q) ∪ B(p, r)` with `p` only positive in `A` yields a monotone real circuit on
`p`, of size polynomial in the refutation size and the number of variables, that is
`1` on assignments satisfying `A` and `0` on assignments satisfying `B`. -/
def CPMonotoneInterpolation : Prop :=
  ∃ q : Polynomial ℕ, ∀ (A B : CNF) (P Q R : Finset ℕ) (L : List Ineq),
    (∀ C ∈ A, ∀ l ∈ C, l.var ∈ P ∪ Q ∧ (l.var ∈ P → l.pos = true)) →
    (∀ C ∈ B, ∀ l ∈ C, l.var ∈ P ∪ R) →
    Disjoint P Q → Disjoint P R → Disjoint Q R →
    CPRefutes (A ∪ B) L →
    ∃ C : List MGate, MCMono C ∧ MCInputsIn P C ∧
      C.length ≤ q.eval (L.length + (P ∪ Q ∪ R).card) ∧
      ∀ a, (cnfSat a A → mcEval a C = 1) ∧ (cnfSat a B → mcEval a C = 0)

/-- Monotone real circuits separating `k` cliques from `k - 1` colorings
(`k = ⌊n^{1/4}⌋`) need super polynomial size (Pudlák 1997; Haken Cook 1999). -/
def MonoRealCliqueLB : Prop :=
  ∀ c : ℕ, ∃ N, ∀ n ≥ N, ∀ C : List MGate, MCMono C → MCInputsIn (edgeVars n) C →
    (∀ a, (cnfSat a (cliqueCNF n (ccK n)) → mcEval a C = 1) ∧
      (cnfSat a (colorCNF n (ccK n) (ccK n - 1)) → mcEval a C = 0)) →
    n ^ c < C.length

/-- R3 target: CP refutations of clique coloring need super polynomial size. -/
def CPCliqueColoringSuperpoly : Prop :=
  ∀ c : ℕ, ∃ N, ∀ n ≥ N, ∀ L : List Ineq,
    CPRefutes (ccCNF n (ccK n) (ccK n - 1)) L → n ^ c < L.length

/-! ## Packaging: interpolation plus the circuit bound give the CP bound -/

theorem eVar_lt {n : ℕ} (i j : Fin n) : eVar n i j < n * n := by
  unfold eVar
  have hi := i.isLt; have hj := j.isLt
  have h1 : min i.val j.val ≤ n - 1 := by omega
  have h2 : max i.val j.val ≤ n - 1 := by omega
  have h3 : min i.val j.val * n ≤ (n - 1) * n := Nat.mul_le_mul_right _ h1
  have h4 : (n - 1) * n + n = n * n := by
    cases n with
    | zero => omega
    | succ n => simp [Nat.succ_mul, Nat.mul_succ]
  omega

theorem edgeVars_lt {n v : ℕ} (h : v ∈ edgeVars n) : v < n * n := by
  unfold edgeVars at h
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 h
  exact eVar_lt _ _

theorem eVar_mem {n : ℕ} {i j : Fin n} (h : i ≠ j) : eVar n i j ∈ edgeVars n := by
  unfold edgeVars
  exact Finset.mem_image.2 ⟨(i, j), by simp [h], rfl⟩

/-- Clique variable range. -/
def qVars (n k : ℕ) : Finset ℕ := Finset.Ico (n * n) (n * n + k * n)

/-- Color variable range. -/
def rVars (n k m : ℕ) : Finset ℕ := Finset.Ico (n * n + k * n) (n * n + k * n + n * m)

theorem qVar_mem {n k : ℕ} (u : Fin k) (i : Fin n) : qVar n u i ∈ qVars n k := by
  unfold qVar qVars
  have hu := u.isLt; have hi := i.isLt
  have : u.val * n + i.val < k * n := by
    have : u.val * n + n ≤ k * n := by
      have := Nat.mul_le_mul_right n (show u.val + 1 ≤ k by omega)
      simpa [Nat.succ_mul] using this
    omega
  simp only [Finset.mem_Ico]; omega

theorem rVar_mem {n k m : ℕ} (i : Fin n) (c : Fin m) : rVar n k i c ∈ rVars n k m := by
  unfold rVar rVars
  have hi := i.isLt; have hc := c.isLt
  have : i.val * m + c.val < n * m := by
    have : i.val * m + m ≤ n * m := by
      have := Nat.mul_le_mul_right m (show i.val + 1 ≤ n by omega)
      simpa [Nat.succ_mul] using this
    omega
  simp only [Finset.mem_Ico]; omega

theorem clique_lits {n k : ℕ} : ∀ C ∈ cliqueCNF n k, ∀ l ∈ C,
    l.var ∈ edgeVars n ∪ qVars n k ∧ (l.var ∈ edgeVars n → l.pos = true) := by
  have hq : ∀ (u : Fin k) (i : Fin n) (b : Bool),
      (⟨qVar n u i, b⟩ : Literal).var ∈ edgeVars n ∪ qVars n k ∧
        ((⟨qVar n u i, b⟩ : Literal).var ∈ edgeVars n → (⟨qVar n u i, b⟩ : Literal).pos = true) := by
    intro u i b
    refine ⟨Finset.mem_union_right _ (qVar_mem u i), fun h => ?_⟩
    have h1 := edgeVars_lt h
    have h2 := qVar_mem (n := n) u i
    unfold qVars at h2; simp only [Finset.mem_Ico] at h2
    exact absurd h1 (by simp only at h2 ⊢; omega)
  intro C hC l hl
  simp only [cliqueCNF, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and] at hC
  rcases hC with (⟨u, rfl⟩ | ⟨t, _, rfl⟩) | ⟨t, ht, rfl⟩
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hl
    exact hq u i true
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact hq _ _ false
    · exact hq _ _ false
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact hq _ _ false
    · exact hq _ _ false
    · exact ⟨Finset.mem_union_left _ (eVar_mem ht.2), fun _ => rfl⟩

theorem color_lits {n k m : ℕ} : ∀ C ∈ colorCNF n k m, ∀ l ∈ C,
    l.var ∈ edgeVars n ∪ rVars n k m := by
  intro C hC l hl
  simp only [colorCNF, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and] at hC
  rcases hC with ⟨i, rfl⟩ | ⟨t, ht, rfl⟩
  · obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hl
    exact Finset.mem_union_right _ (rVar_mem _ _)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact Finset.mem_union_right _ (rVar_mem _ _)
    · exact Finset.mem_union_right _ (rVar_mem _ _)
    · exact Finset.mem_union_left _ (eVar_mem ht)

theorem disj_PQ (n k : ℕ) : Disjoint (edgeVars n) (qVars n k) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  have := edgeVars_lt h1
  unfold qVars at h2; simp only [Finset.mem_Ico] at h2; omega

theorem disj_PR (n k m : ℕ) : Disjoint (edgeVars n) (rVars n k m) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  have := edgeVars_lt h1
  unfold rVars at h2; simp only [Finset.mem_Ico] at h2; omega

theorem disj_QR (n k m : ℕ) : Disjoint (qVars n k) (rVars n k m) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  unfold qVars at h1; unfold rVars at h2
  simp only [Finset.mem_Ico] at h1 h2; omega

theorem card_vars_le (n k m : ℕ) :
    (edgeVars n ∪ qVars n k ∪ rVars n k m).card ≤ n * n + k * n + n * m := by
  have h1 : (edgeVars n).card ≤ n * n := by
    calc (edgeVars n).card ≤ (Finset.range (n * n)).card :=
          Finset.card_le_card (fun v hv => Finset.mem_range.2 (edgeVars_lt hv))
      _ = n * n := Finset.card_range _
  have h2 : (qVars n k).card = k * n := by unfold qVars; simp
  have h3 : (rVars n k m).card = n * m := by unfold rVars; simp
  calc (edgeVars n ∪ qVars n k ∪ rVars n k m).card
      ≤ (edgeVars n ∪ qVars n k).card + (rVars n k m).card := Finset.card_union_le _ _
    _ ≤ (edgeVars n).card + (qVars n k).card + (rVars n k m).card := by
        have := Finset.card_union_le (edgeVars n) (qVars n k); omega
    _ ≤ n * n + k * n + n * m := by omega

theorem poly_le_pow' (q : Polynomial ℕ) : ∃ D d : ℕ, ∀ t, q.eval t ≤ D * (t + 1) ^ d := by
  refine ⟨∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i, q.natDegree, fun t => ?_⟩
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ q.natDegree := by simpa [Nat.lt_succ_iff] using hi
  refine Nat.mul_le_mul_left _ ?_
  calc t ^ i ≤ (t + 1) ^ i := Nat.pow_le_pow_left (Nat.le_succ t) i
    _ ≤ (t + 1) ^ q.natDegree := Nat.pow_le_pow_right (Nat.succ_pos t) hi'

theorem ccK_le (n : ℕ) : ccK n ≤ n := (Nat.sqrt_le_self _).trans (Nat.sqrt_le_self _)

/-- The R3 packaging: monotone interpolation for CP plus the monotone real circuit
lower bound give super polynomial CP refutations of clique coloring. -/
theorem cp_superpoly_of_interp_lb (hI : CPMonotoneInterpolation) (hL : MonoRealCliqueLB) :
    CPCliqueColoringSuperpoly := by
  obtain ⟨q, hq⟩ := hI
  obtain ⟨D, d, hD⟩ := poly_le_pow' q
  intro c
  set c' := (c + 2) * d + 1 with hc'
  obtain ⟨N1, hN1⟩ := hL c'
  refine ⟨max N1 (D * 5 ^ d + 1), fun n hn L hLr => ?_⟩
  have hn1 : N1 ≤ n := le_of_max_le_left hn
  have hn2 : D * 5 ^ d + 1 ≤ n := le_of_max_le_right hn
  have hnpos : 1 ≤ n := by omega
  by_contra hlt
  rw [not_lt] at hlt
  set k := ccK n with hk
  obtain ⟨C, hmono, hin, hsize, hsep⟩ := hq (cliqueCNF n k) (colorCNF n k (k - 1)) (edgeVars n)
    (qVars n k) (rVars n k (k - 1)) L clique_lits color_lits (disj_PQ n k) (disj_PR n k (k - 1))
    (disj_QR n k (k - 1)) hLr
  have hlb := hN1 n hn1 C hmono hin hsep
  -- size bound: L.length + card + 1 ≤ 5 * n ^ (c + 2)
  have hkn : k ≤ n := ccK_le n
  have hcard := card_vars_le n k (k - 1)
  have hkn2 : k * n ≤ n * n := Nat.mul_le_mul_right _ hkn
  have hmn2 : n * (k - 1) ≤ n * n := Nat.mul_le_mul_left _ (by omega)
  have hpc : n ^ c ≤ n ^ (c + 2) := Nat.pow_le_pow_right hnpos (by omega)
  have hn2' : n * n ≤ n ^ (c + 2) := by
    rw [← pow_two]; exact Nat.pow_le_pow_right hnpos (by omega)
  have h1 : 1 ≤ n ^ (c + 2) := Nat.one_le_pow _ _ hnpos
  have ht : L.length + (edgeVars n ∪ qVars n k ∪ rVars n k (k - 1)).card + 1 ≤
      5 * n ^ (c + 2) := by omega
  have hpow : (L.length + (edgeVars n ∪ qVars n k ∪ rVars n k (k - 1)).card + 1) ^ d ≤
      (5 * n ^ (c + 2)) ^ d := Nat.pow_le_pow_left ht d
  have hsz : C.length ≤ D * 5 ^ d * n ^ ((c + 2) * d) := by
    calc C.length ≤ q.eval (L.length + (edgeVars n ∪ qVars n k ∪ rVars n k (k - 1)).card) := hsize
      _ ≤ D * (L.length + (edgeVars n ∪ qVars n k ∪ rVars n k (k - 1)).card + 1) ^ d := hD _
      _ ≤ D * (5 * n ^ (c + 2)) ^ d := Nat.mul_le_mul_left _ hpow
      _ = D * 5 ^ d * n ^ ((c + 2) * d) := by rw [mul_pow, ← pow_mul]; ring
  have hfin : D * 5 ^ d * n ^ ((c + 2) * d) ≤ n ^ c' := by
    rw [hc', pow_succ, mul_comm (n ^ ((c + 2) * d)) n]
    exact Nat.mul_le_mul_right _ (by omega)
  omega

end

namespace CuttingPlanesFrontier

/-- R3 obligation 1 (Pudlák 1997, monotone feasible interpolation for CP). See
docs/ladder/r3-cutting-planes-checklist.md for the micro lemma plan. -/
theorem cp_monotone_interpolation : CPMonotoneInterpolation := by
  sorry

/-- R3 obligation 2 (monotone real circuits separating cliques from colorings). -/
theorem monoReal_clique_lb : MonoRealCliqueLB := by
  sorry

/-- R3 target, from the two obligations by `cp_superpoly_of_interp_lb`. -/
theorem cp_cliqueColoring_superpoly : CPCliqueColoringSuperpoly :=
  cp_superpoly_of_interp_lb cp_monotone_interpolation monoReal_clique_lb

end CuttingPlanesFrontier

end SATurday.ProofComplexity
