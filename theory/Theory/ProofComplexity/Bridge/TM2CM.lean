import Theory.ProofComplexity.Bridge.Tableau
import Theory.ProofComplexity.Bridge.CookLevin

/-!
# From a `FinTM2` to the coded machine `CM` (Ladder Rung R5, hard direction)

The first part is a window interpreter for `TM2.stepAux`: a statement chain only reads
and rewrites the top `c` cells of every stack, so its effect is a pair
(pops, pushed list) per stack computed from the top window.

LOG: R5 Bridge TM2CM module (window interpreter, symbol coding, simulation)
-/

open Turing

namespace SATurday.Bridge
namespace CL

section Interp

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

open TM2

/-- Number of nodes of a statement chain. -/
def _root_.Turing.TM2.Stmt.nodes : Stmt Γ Λ σ → ℕ
  | .push _ _ q => q.nodes + 1
  | .peek _ _ q => q.nodes + 1
  | .pop _ _ q => q.nodes + 1
  | .load _ q => q.nodes + 1
  | .branch _ q₁ q₂ => max q₁.nodes q₂.nodes + 1
  | .goto _ => 1
  | .halt => 1

theorem _root_.Turing.TM2.Stmt.nodes_pos (s : Stmt Γ Λ σ) : 0 < s.nodes := by
  cases s <;> simp [Stmt.nodes]

/-- Per stack effect: number of popped cells and the pushed list (top first). -/
abbrev Eff (Γ : K → Type) := ∀ k, ℕ × List (Γ k)

/-- Top of the stack `k` after the effect, read through the window `W`. -/
def curHead (W : ∀ k, List (Γ k)) (E : Eff Γ) (k : K) : Option (Γ k) :=
  ((E k).2 ++ (W k).drop (E k).1).head?

/-- Effect of a pop. -/
def popE {α : Type} : ℕ × List α → ℕ × List α
  | (j, []) => (j + 1, [])
  | (j, _ :: r) => (j, r)

/-- Window interpreter: result label, variable and accumulated effects. -/
def effAux (W : ∀ k, List (Γ k)) : Stmt Γ Λ σ → σ → Eff Γ → Option Λ × σ × Eff Γ
  | .push k f q, v, E => effAux W q v (Function.update E k ((E k).1, f v :: (E k).2))
  | .peek k f q, v, E => effAux W q (f v (curHead W E k)) E
  | .pop k f q, v, E => effAux W q (f v (curHead W E k)) (Function.update E k (popE (E k)))
  | .load a q, v, E => effAux W q (a v) E
  | .branch f q₁ q₂, v, E => cond (f v) (effAux W q₁ v E) (effAux W q₂ v E)
  | .goto f, v, E => (some (f v), v, E)
  | .halt, v, E => (none, v, E)

/-- Stacks described by a base and an effect. -/
def applyE (S : ∀ k, List (Γ k)) (E : Eff Γ) : ∀ k, List (Γ k) := fun k => (E k).2 ++ (S k).drop (E k).1

theorem curHead_applyE (c : ℕ) (S : ∀ k, List (Γ k)) (E : Eff Γ) (k : K) (hj : (E k).1 < c) :
    (applyE S E k).head? = curHead (fun k => (S k).take c) E k := by
  unfold applyE curHead
  simp only [List.head?_append]
  congr 1
  rw [List.head?_drop, List.head?_drop, List.getElem?_take]
  simp [hj]

theorem applyE_update_push (S : ∀ k, List (Γ k)) (E : Eff Γ) (k : K) (a : Γ k) :
    Function.update (applyE S E) k (a :: applyE S E k) =
      applyE S (Function.update E k ((E k).1, a :: (E k).2)) := by
  funext j
  by_cases h : j = k
  · subst h; simp [applyE]
  · simp [applyE, Function.update_of_ne h]

theorem applyE_update_pop (S : ∀ k, List (Γ k)) (E : Eff Γ) (k : K) :
    Function.update (applyE S E) k (applyE S E k).tail =
      applyE S (Function.update E k (popE (E k))) := by
  funext j
  by_cases h : j = k
  · subst h
    rcases hE : E j with ⟨jj, n⟩
    cases n with
    | nil => simp [applyE, popE, hE]
    | cons a r => simp [applyE, popE, hE]
  · simp [applyE, Function.update_of_ne h]

theorem stepAux_effAux (c : ℕ) (S : ∀ k, List (Γ k)) :
    ∀ (s : Stmt Γ Λ σ) (v : σ) (E : Eff Γ), (∀ k, (E k).1 + s.nodes ≤ c) →
      stepAux s v (applyE S E) =
        ⟨(effAux (fun k => (S k).take c) s v E).1, (effAux (fun k => (S k).take c) s v E).2.1,
          applyE S (effAux (fun k => (S k).take c) s v E).2.2⟩ := by
  intro s
  induction s with
  | push k f q ih =>
      intro v E hE
      simp only [stepAux, effAux]
      rw [applyE_update_push]
      apply ih
      intro k'
      by_cases h : k' = k
      · subst h; simp only [Function.update_self]; have := hE k'; simp [Stmt.nodes] at this; omega
      · simp only [Function.update_of_ne h]; have := hE k'; simp [Stmt.nodes] at this; omega
  | peek k f q ih =>
      intro v E hE
      have hk : (E k).1 < c := by have := hE k; simp [Stmt.nodes] at this; omega
      simp only [stepAux, effAux]
      rw [curHead_applyE c S E k hk]
      apply ih
      intro k'; have := hE k'; simp [Stmt.nodes] at this; omega
  | pop k f q ih =>
      intro v E hE
      have hk : (E k).1 < c := by have := hE k; simp [Stmt.nodes] at this; omega
      simp only [stepAux, effAux]
      rw [curHead_applyE c S E k hk, applyE_update_pop]
      apply ih
      intro k'
      by_cases h : k' = k
      · subst h
        simp only [Function.update_self]
        have := hE k'
        simp only [Stmt.nodes] at this
        rcases hEk : E k' with ⟨jj, n⟩
        rw [hEk] at this
        cases n <;> simp [popE] at this ⊢ <;> omega
      · simp only [Function.update_of_ne h]; have := hE k'; simp [Stmt.nodes] at this; omega
  | load a q ih =>
      intro v E hE
      simp only [stepAux, effAux]
      apply ih
      intro k'; have := hE k'; simp [Stmt.nodes] at this; omega
  | branch f q₁ q₂ ih₁ ih₂ =>
      intro v E hE
      simp only [stepAux, effAux]
      cases f v
      · simp only [cond]; apply ih₂; intro k'; have := hE k'; simp [Stmt.nodes] at this; omega
      · simp only [cond]; apply ih₁; intro k'; have := hE k'; simp [Stmt.nodes] at this; omega
  | goto f => intro v E hE; simp [stepAux, effAux]
  | halt => intro v E hE; simp [stepAux, effAux]

/-- Every value pushed by the chain satisfies `P`. -/
def _root_.Turing.TM2.Stmt.pushOk (P : ∀ k, Γ k → Prop) : Stmt Γ Λ σ → Prop
  | .push k f q => (∀ v, P k (f v)) ∧ q.pushOk P
  | .peek _ _ q => q.pushOk P
  | .pop _ _ q => q.pushOk P
  | .load _ q => q.pushOk P
  | .branch _ q₁ q₂ => q₁.pushOk P ∧ q₂.pushOk P
  | .goto _ => True
  | .halt => True

theorem effAux_pushed (P : ∀ k, Γ k → Prop) (W : ∀ k, List (Γ k)) :
    ∀ (s : Stmt Γ Λ σ) (v : σ) (E : Eff Γ), s.pushOk P → (∀ k, ∀ g ∈ (E k).2, P k g) →
      ∀ k, ∀ g ∈ ((effAux W s v E).2.2 k).2, P k g := by
  intro s
  induction s with
  | push k f q ih =>
      intro v E hs hE
      simp only [effAux]
      apply ih _ _ hs.2
      intro k' g hg
      by_cases h : k' = k
      · subst h
        simp only [Function.update_self, List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact hs.1 v
        · exact hE k' g hg
      · simp only [Function.update_of_ne h] at hg; exact hE k' g hg
  | peek k f q ih => intro v E hs hE; simp only [effAux]; exact ih _ _ hs hE
  | pop k f q ih =>
      intro v E hs hE
      simp only [effAux]
      apply ih _ _ hs
      intro k' g hg
      by_cases h : k' = k
      · subst h
        simp only [Function.update_self] at hg
        rcases hEk : E k' with ⟨jj, n⟩
        rw [hEk] at hg
        cases n with
        | nil => simp [popE] at hg
        | cons a r =>
            simp only [popE] at hg
            exact hE k' g (by rw [hEk]; exact List.mem_cons_of_mem _ hg)
      · simp only [Function.update_of_ne h] at hg; exact hE k' g hg
  | load a q ih => intro v E hs hE; simp only [effAux]; exact ih _ _ hs hE
  | branch f q₁ q₂ ih₁ ih₂ =>
      intro v E hs hE
      simp only [effAux]
      cases f v
      · exact ih₂ _ _ hs.2 hE
      · exact ih₁ _ _ hs.1 hE
  | goto f => intro v E hs hE; simp only [effAux]; exact hE
  | halt => intro v E hs hE; simp only [effAux]; exact hE

theorem effAux_potential (W : ∀ k, List (Γ k)) :
    ∀ (s : Stmt Γ Λ σ) (v : σ) (E : Eff Γ) (k : K),
      ((effAux W s v E).2.2 k).1 + ((effAux W s v E).2.2 k).2.length ≤
        (E k).1 + (E k).2.length + s.nodes := by
  intro s
  induction s with
  | push k f q ih =>
      intro v E k'
      simp only [effAux]
      have := ih v (Function.update E k ((E k).1, f v :: (E k).2)) k'
      by_cases h : k' = k
      · subst h; simp only [Function.update_self, List.length_cons, Stmt.nodes] at this ⊢; omega
      · simp only [Function.update_of_ne h, Stmt.nodes] at this ⊢; omega
  | peek k f q ih =>
      intro v E k'; simp only [effAux, Stmt.nodes]; have := ih (f v (curHead W E k)) E k'; omega
  | pop k f q ih =>
      intro v E k'
      simp only [effAux]
      have := ih (f v (curHead W E k)) (Function.update E k (popE (E k))) k'
      by_cases h : k' = k
      · subst h
        rcases hEk : E k' with ⟨jj, n⟩
        simp only [hEk, Function.update_self, Stmt.nodes] at this ⊢
        cases n <;> simp [popE] at this ⊢ <;> omega
      · simp only [Function.update_of_ne h, Stmt.nodes] at this ⊢; omega
  | load a q ih =>
      intro v E k'; simp only [effAux, Stmt.nodes]; have := ih (a v) E k'; omega
  | branch f q₁ q₂ ih₁ ih₂ =>
      intro v E k'
      simp only [effAux, Stmt.nodes]
      cases f v
      · simp only [cond]; have := ih₂ v E k'; omega
      · simp only [cond]; have := ih₁ v E k'; omega
  | goto f => intro v E k'; simp [effAux, Stmt.nodes]
  | halt => intro v E k'; simp [effAux, Stmt.nodes]

end Interp

/-! ## The coded machine of a `FinTM2` -/

section Build

open Classical

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable (tm : FinTM2)

/-- All stack pushes of a statement chain, with their value function. -/
def pushSites : TM2.Stmt tm.Γ tm.Λ tm.σ → List (Σ k : tm.K, tm.σ → tm.Γ k)
  | .push k f q => ⟨k, f⟩ :: pushSites q
  | .peek _ _ q => pushSites q
  | .pop _ _ q => pushSites q
  | .load _ q => pushSites q
  | .branch _ q₁ q₂ => pushSites q₁ ++ pushSites q₂
  | .goto _ => []
  | .halt => []

/-- All push sites of the machine. -/
noncomputable def allSites : List (Σ k : tm.K, tm.σ → tm.Γ k) :=
  (Finset.univ : Finset tm.Λ).toList.flatMap fun l => pushSites tm (tm.m l)

/-- Every symbol that can ever occur on a stack. -/
noncomputable def symAll : List (Σ k : tm.K, tm.Γ k) :=
  (Finset.univ : Finset (tm.Γ tm.k₀)).toList.map (fun g => (⟨tm.k₀, g⟩ : Σ k : tm.K, tm.Γ k)) ++
  (allSites tm).flatMap fun p =>
    (Finset.univ : Finset tm.σ).toList.map fun v => (⟨p.1, p.2 v⟩ : Σ k : tm.K, tm.Γ k)

theorem mem_symAll_input (g : tm.Γ tm.k₀) : (⟨tm.k₀, g⟩ : Σ k : tm.K, tm.Γ k) ∈ symAll tm := by
  simp [symAll]

theorem mem_allSites {l : tm.Λ} {p : Σ k : tm.K, tm.σ → tm.Γ k}
    (hp : p ∈ pushSites tm (tm.m l)) : p ∈ allSites tm := by
  simp only [allSites, List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and]
  exact ⟨l, hp⟩

theorem mem_symAll_push {p : Σ k : tm.K, tm.σ → tm.Γ k} (hp : p ∈ allSites tm) (v : tm.σ) :
    (⟨p.1, p.2 v⟩ : Σ k : tm.K, tm.Γ k) ∈ symAll tm := by
  simp only [symAll, List.mem_append, List.mem_flatMap, List.mem_map, Finset.mem_toList,
    Finset.mem_univ, true_and]
  right
  exact ⟨p, hp, v, rfl⟩

/-- Global symbol code. -/
noncomputable def encS (p : Σ k : tm.K, tm.Γ k) : ℕ := (symAll tm).idxOf p

/-- Decode a global code at stack `k`. -/
noncomputable def decK (k : tm.K) (n : ℕ) : Option (tm.Γ k) :=
  match (symAll tm)[n]? with
  | some ⟨k', g⟩ => if h : k' = k then some (cast (congrArg tm.Γ h) g) else none
  | none => none

theorem decK_encS (k : tm.K) (g : tm.Γ k) (h : (⟨k, g⟩ : Σ k : tm.K, tm.Γ k) ∈ symAll tm) :
    decK tm k (encS tm ⟨k, g⟩) = some g := by
  unfold decK encS
  rw [List.getElem?_idxOf h]
  simp

theorem encS_lt (p : Σ k : tm.K, tm.Γ k) (h : p ∈ symAll tm) : encS tm p < (symAll tm).length :=
  List.idxOf_lt_length_of_mem h

/-- Control states. -/
abbrev Ctl : Type := Option tm.Λ × tm.σ

/-- Number of controls. -/
noncomputable def nQ : ℕ := Fintype.card (Ctl tm)

/-- Enumeration of controls. -/
noncomputable def eC : Ctl tm ≃ Fin (nQ tm) := Fintype.equivFin _

/-- Control code. -/
noncomputable def ctlCode (c : Ctl tm) : ℕ := (eC tm c).val

/-- Control decoding. -/
noncomputable def ctlDec (q : ℕ) : Option (Ctl tm) :=
  if h : q < nQ tm then some ((eC tm).symm ⟨q, h⟩) else none

theorem ctlCode_lt (c : Ctl tm) : ctlCode tm c < nQ tm := (eC tm c).isLt

theorem ctlDec_ctlCode (c : Ctl tm) : ctlDec tm (ctlCode tm c) = some c := by
  unfold ctlDec ctlCode
  rw [dif_pos (eC tm c).isLt]
  simp

/-- Number of stacks. -/
noncomputable def nK : ℕ := Fintype.card tm.K

/-- Enumeration of stacks. -/
noncomputable def eK : tm.K ≃ Fin (nK tm) := Fintype.equivFin _

/-- Stack index. -/
noncomputable def kIdx (k : tm.K) : ℕ := (eK tm k).val

/-- Stack of an index. -/
noncomputable def kOf (k' : ℕ) : Option tm.K :=
  if h : k' < nK tm then some ((eK tm).symm ⟨k', h⟩) else none

theorem kOf_kIdx (k : tm.K) : kOf tm (kIdx tm k) = some k := by
  unfold kOf kIdx
  rw [dif_pos (eK tm k).isLt]
  simp

theorem kIdx_lt (k : tm.K) : kIdx tm k < nK tm := (eK tm k).isLt

theorem kIdx_inj {k k' : tm.K} (h : kIdx tm k = kIdx tm k') : k = k' := by
  unfold kIdx at h
  exact (eK tm).injective (Fin.ext h)

/-- Window depth: one more than any statement chain. -/
noncomputable def cc : ℕ := (Finset.univ : Finset tm.Λ).sup (fun l => (tm.m l).nodes) + 1

theorem nodes_lt_cc (l : tm.Λ) : (tm.m l).nodes < cc tm := by
  unfold cc
  have : (tm.m l).nodes ≤ (Finset.univ : Finset tm.Λ).sup (fun l => (tm.m l).nodes) :=
    Finset.le_sup (f := fun l => (tm.m l).nodes) (Finset.mem_univ l)
  omega

/-- Codes of the top window of stack `k` read from a flattened pattern. -/
noncomputable def winCodes (p : List ℕ) (k : tm.K) : List ℕ :=
  (List.range (cc tm)).map fun d => p.getD (kIdx tm k * cc tm + d) (symAll tm).length

/-- Decoded top window. -/
noncomputable def winOf (p : List ℕ) (k : tm.K) : List (tm.Γ k) :=
  ((winCodes tm p k).takeWhile fun n => decide (n < (symAll tm).length)).filterMap (decK tm k)

/-- The transition of the coded machine. -/
noncomputable def tmDelta (q : ℕ) (p : List ℕ) : ℕ × List (ℕ × List ℕ) :=
  match ctlDec tm q with
  | some (some l, v) =>
      ((ctlCode tm ((effAux (fun k => winOf tm p k) (tm.m l) v (fun _ => (0, []))).1,
          (effAux (fun k => winOf tm p k) (tm.m l) v (fun _ => (0, []))).2.1)),
        (List.range (nK tm)).map fun k' =>
          match kOf tm k' with
          | some k =>
              (((effAux (fun k => winOf tm p k) (tm.m l) v (fun _ => (0, []))).2.2 k).1,
                ((effAux (fun k => winOf tm p k) (tm.m l) v (fun _ => (0, []))).2.2 k).2.map
                  fun g => encS tm ⟨k, g⟩)
          | none => (0, []))
  | _ => (q, [])

/-- The coded machine of `tm` for chosen input and output alphabet identifications. -/
noncomputable def tmCM (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) : CM where
  K := nK tm
  A := (symAll tm).length
  Q := nQ tm
  c := cc tm
  q0 := ctlCode tm (some tm.main, tm.initialState)
  halt := fun q => match ctlDec tm q with
    | some (none, _) => true
    | _ => false
  δ := tmDelta tm
  kin := kIdx tm tm.k₀
  kout := kIdx tm tm.k₁
  inSym := fun b => encS tm ⟨tm.k₀, ia.symm b⟩
  outTrue := encS tm ⟨tm.k₁, oa.symm true⟩

/-- The effect of the step at control `(some l, v)` on stack `k`. -/
noncomputable def effK (l : tm.Λ) (v : tm.σ) (p : List ℕ) (k : tm.K) : ℕ × List ℕ :=
  let r := effAux (fun k => winOf tm p k) (tm.m l) v (fun _ => (0, []))
  ((r.2.2 k).1, (r.2.2 k).2.map fun g => encS tm ⟨k, g⟩)

theorem tmDelta_some {q : ℕ} {l : tm.Λ} {v : tm.σ} (hq : ctlDec tm q = some (some l, v))
    (p : List ℕ) :
    (tmDelta tm q p).1 = ctlCode tm ((effAux (fun k => winOf tm p k) (tm.m l) v
      (fun _ => (0, []))).1, (effAux (fun k => winOf tm p k) (tm.m l) v (fun _ => (0, []))).2.1) ∧
    ∀ k' : ℕ, ((tmDelta tm q p).2).getD k' (0, []) =
      match kOf tm k' with
      | some k => effK tm l v p k
      | none => (0, []) := by
  unfold tmDelta
  rw [hq]
  refine ⟨rfl, ?_⟩
  intro k'
  by_cases h : k' < nK tm
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h, if_true,
      Option.map_some, Option.getD_some]
    rfl
  · have hr : (List.range (nK tm))[k']? = none := List.getElem?_eq_none (by simp; omega)
    have : kOf tm k' = none := by unfold kOf; rw [dif_neg h]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, hr, this]

theorem tmDelta_other {q : ℕ} (hq : ∀ l v, ctlDec tm q ≠ some (some l, v)) (p : List ℕ) :
    tmDelta tm q p = (q, []) := by
  unfold tmDelta
  cases h : ctlDec tm q with
  | none => rfl
  | some c =>
      obtain ⟨o, v⟩ := c
      cases o with
      | none => rfl
      | some l => exact absurd h (hq l v)

theorem pushOk_of_sites : ∀ (s : TM2.Stmt tm.Γ tm.Λ tm.σ),
    (∀ p ∈ pushSites tm s, ∀ v, (⟨p.1, p.2 v⟩ : Σ k : tm.K, tm.Γ k) ∈ symAll tm) →
      s.pushOk (fun k g => (⟨k, g⟩ : Σ k : tm.K, tm.Γ k) ∈ symAll tm) := by
  intro s
  induction s with
  | push k f q ih =>
      intro h
      refine ⟨fun v => h ⟨k, f⟩ (by simp [pushSites]) v, ih fun p hp v => h p (by simp [pushSites, hp]) v⟩
  | peek k f q ih => intro h; exact ih fun p hp v => h p (by simpa [pushSites] using hp) v
  | pop k f q ih => intro h; exact ih fun p hp v => h p (by simpa [pushSites] using hp) v
  | load a q ih => intro h; exact ih fun p hp v => h p (by simpa [pushSites] using hp) v
  | branch f q₁ q₂ ih₁ ih₂ =>
      intro h
      exact ⟨ih₁ fun p hp v => h p (by simp [pushSites, hp]) v,
        ih₂ fun p hp v => h p (by simp [pushSites, hp]) v⟩
  | goto f => intro _; trivial
  | halt => intro _; trivial

theorem pushOk_m (l : tm.Λ) :
    (tm.m l).pushOk (fun k g => (⟨k, g⟩ : Σ k : tm.K, tm.Γ k) ∈ symAll tm) :=
  pushOk_of_sites tm _ fun p hp v => mem_symAll_push tm (mem_allSites tm hp) v

theorem tmCM_WF (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) {W : ℕ}
    (hW : 2 * cc tm ≤ W) : (tmCM tm ia oa).WF W := by
  have hin : ∀ b, encS tm ⟨tm.k₀, ia.symm b⟩ < (symAll tm).length :=
    fun b => encS_lt tm _ (mem_symAll_input tm _)
  refine
    { hc := hW
      hq0 := ctlCode_lt tm _
      hδq := ?_
      hδs := ?_
      hδj := ?_
      hin := hin
      hinj := ?_
      hkin := kIdx_lt tm _
      hkout := kIdx_lt tm _
      hc1 := Nat.succ_pos _
      houtT := List.idxOf_le_length }
  · intro q hq p
    by_cases h : ∃ l v, ctlDec tm q = some (some l, v)
    · obtain ⟨l, v, hl⟩ := h
      show (tmDelta tm q p).1 < nQ tm
      rw [(tmDelta_some tm hl p).1]
      exact ctlCode_lt tm _
    · push_neg at h
      show (tmDelta tm q p).1 < nQ tm
      rw [tmDelta_other tm h p]
      exact hq
  · intro q p k s hs
    by_cases h : ∃ l v, ctlDec tm q = some (some l, v)
    · obtain ⟨l, v, hl⟩ := h
      have hg := (tmDelta_some tm hl p).2 k
      change s ∈ (((tmDelta tm q p).2).getD k (0, [])).2 at hs
      rw [hg] at hs
      cases hk : kOf tm k with
      | none => rw [hk] at hs; simp at hs
      | some k' =>
          rw [hk] at hs
          simp only [effK, List.mem_map] at hs
          obtain ⟨g, hgm, rfl⟩ := hs
          have hP := effAux_pushed (fun k g => (⟨k, g⟩ : Σ k : tm.K, tm.Γ k) ∈ symAll tm)
            (fun k => winOf tm p k) (tm.m l) v (fun _ => (0, [])) (pushOk_m tm l)
            (by intro k g hg; simp at hg) k' g hgm
          exact encS_lt tm _ hP
    · push_neg at h
      change s ∈ (((tmDelta tm q p).2).getD k (0, [])).2 at hs
      rw [tmDelta_other tm h p] at hs
      simp at hs
  · intro q p k
    by_cases h : ∃ l v, ctlDec tm q = some (some l, v)
    · obtain ⟨l, v, hl⟩ := h
      have hg := (tmDelta_some tm hl p).2 k
      show (((tmDelta tm q p).2).getD k (0, [])).1 ≤ cc tm ∧ (((tmDelta tm q p).2).getD k (0, [])).2.length ≤ cc tm
      rw [hg]
      cases hk : kOf tm k with
      | none => simp
      | some k' =>
          simp only [effK, List.length_map]
          have := effAux_potential (fun k => winOf tm p k) (tm.m l) v (fun _ => (0, [])) k'
          have hn := nodes_lt_cc tm l
          simp only [List.length_nil, Nat.zero_add] at this
          constructor <;> omega
    · push_neg at h
      show (((tmDelta tm q p).2).getD k (0, [])).1 ≤ cc tm ∧ (((tmDelta tm q p).2).getD k (0, [])).2.length ≤ cc tm
      rw [tmDelta_other tm h p]
      simp
  · intro heq
    have h1 : encS tm ⟨tm.k₀, ia.symm false⟩ = encS tm ⟨tm.k₀, ia.symm true⟩ := heq
    have h2 := (List.idxOf_inj (mem_symAll_input tm _)).1 h1
    have h3 : ia.symm false = ia.symm true := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
    have := ia.symm.injective h3
    simp at this

/-- Array of stack contents, indexed from the top, blank beyond the height. -/
noncomputable def arrOf (W : ℕ) (S : ∀ k, List (tm.Γ k)) : Arr := fun k' d =>
  if d < W then
    (match kOf tm k' with
     | some k => (match (S k)[d]? with
         | some g => encS tm ⟨k, g⟩
         | none => (symAll tm).length)
     | none => (symAll tm).length)
  else (symAll tm).length

/-- Configuration of the coded machine. -/
noncomputable def cfgA (W : ℕ) (c : tm.Cfg) : ℕ × Arr :=
  (ctlCode tm (c.l, c.var), arrOf tm W c.stk)

/-- The step function that stays put when halted. -/
def stepF (c : tm.Cfg) : tm.Cfg := (tm.step c).getD c

/-- All symbols on the stacks are reachable. -/
def GoodS (S : ∀ k, List (tm.Γ k)) : Prop :=
  ∀ k, ∀ g ∈ S k, (⟨k, g⟩ : Σ k : tm.K, tm.Γ k) ∈ symAll tm

theorem arrOf_kIdx (W : ℕ) (S : ∀ k, List (tm.Γ k)) (k : tm.K) (d : ℕ) :
    arrOf tm W S (kIdx tm k) d =
      if d < W then (match (S k)[d]? with
        | some g => encS tm ⟨k, g⟩
        | none => (symAll tm).length) else (symAll tm).length := by
  unfold arrOf
  rw [kOf_kIdx]

theorem arrOf_ge (W : ℕ) (S : ∀ k, List (tm.Γ k)) {k' : ℕ} (h : nK tm ≤ k') (d : ℕ) :
    arrOf tm W S k' d = (symAll tm).length := by
  unfold arrOf
  have : kOf tm k' = none := by unfold kOf; rw [dif_neg (by omega)]
  rw [this]
  split_ifs <;> rfl

theorem pat_getD (W : ℕ) (S : ∀ k, List (tm.Γ k)) (ia : tm.Γ tm.k₀ ≃ Bool)
    (oa : tm.Γ tm.k₁ ≃ Bool) (k : tm.K) (d : ℕ) (hd : d < cc tm) :
    ((tmCM tm ia oa).pat (arrOf tm W S)).getD (kIdx tm k * cc tm + d) (symAll tm).length =
      arrOf tm W S (kIdx tm k) d := by
  have hlt : kIdx tm k * cc tm + d < nK tm * cc tm := by
    have := kIdx_lt tm k
    have h1 : (kIdx tm k + 1) * cc tm ≤ nK tm * cc tm := Nat.mul_le_mul_right _ this
    nlinarith
  unfold CM.pat
  rw [List.getD_eq_getElem?_getD]
  have hrng : kIdx tm k * cc tm + d < (tmCM tm ia oa).K * (tmCM tm ia oa).c := hlt
  rw [List.getElem?_map, List.getElem?_range hrng]
  simp only [Option.map_some, Option.getD_some]
  have hc : 0 < cc tm := Nat.succ_pos _
  have e1 : (kIdx tm k * cc tm + d) / (tmCM tm ia oa).c = kIdx tm k := by
    show (kIdx tm k * cc tm + d) / cc tm = _
    rw [Nat.mul_comm, Nat.mul_add_div hc, Nat.div_eq_of_lt hd]; simp
  have e2 : (kIdx tm k * cc tm + d) % (tmCM tm ia oa).c = d := by
    show (kIdx tm k * cc tm + d) % cc tm = _
    rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hd
  rw [e1, e2]

/-- Code of the cell `d` of a list (blank beyond the end). -/
noncomputable def codeAt (k : tm.K) (L : List (tm.Γ k)) (d : ℕ) : ℕ :=
  match L[d]? with
  | some g => encS tm ⟨k, g⟩
  | none => (symAll tm).length

theorem takeWhile_codeAt (k : tm.K) :
    ∀ (L : List (tm.Γ k)) (n : ℕ), (∀ g ∈ L, (⟨k, g⟩ : Σ k : tm.K, tm.Γ k) ∈ symAll tm) →
      ((List.range n).map (codeAt tm k L)).takeWhile (fun m => decide (m < (symAll tm).length)) =
        (L.take n).map (fun g => encS tm ⟨k, g⟩) := by
  intro L
  induction L with
  | nil =>
      intro n _
      cases n with
      | zero => simp
      | succ n => simp [List.range_succ_eq_map, codeAt]
  | cons g L ih =>
      intro n hL
      cases n with
      | zero => simp
      | succ n =>
          have hg := encS_lt tm _ (hL g (by simp))
          have : (List.range (n + 1)).map (codeAt tm k (g :: L)) =
              encS tm ⟨k, g⟩ :: (List.range n).map (codeAt tm k L) := by
            rw [List.range_succ_eq_map, List.map_cons, List.map_map]
            congr 1
          rw [this, List.takeWhile_cons_of_pos (by simpa using hg), List.take_succ_cons, List.map_cons,
            ih n (fun g' hg' => hL g' (by simp [hg']))]

theorem filterMap_decK (k : tm.K) :
    ∀ (L : List (tm.Γ k)), (∀ g ∈ L, (⟨k, g⟩ : Σ k : tm.K, tm.Γ k) ∈ symAll tm) →
      (L.map (fun g => encS tm ⟨k, g⟩)).filterMap (decK tm k) = L := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons g L ih =>
      intro hL
      simp only [List.map_cons, List.filterMap_cons, decK_encS tm k g (hL g (by simp))]
      rw [ih (fun g' hg' => hL g' (by simp [hg']))]

theorem winOf_arrOf (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) {W : ℕ} (hW : cc tm ≤ W)
    (S : ∀ k, List (tm.Γ k)) (hG : GoodS tm S) (k : tm.K) :
    winOf tm ((tmCM tm ia oa).pat (arrOf tm W S)) k = (S k).take (cc tm) := by
  unfold winOf winCodes
  have hmap : (List.range (cc tm)).map (fun d =>
      ((tmCM tm ia oa).pat (arrOf tm W S)).getD (kIdx tm k * cc tm + d) (symAll tm).length) =
      (List.range (cc tm)).map (codeAt tm k (S k)) := by
    apply List.map_congr_left
    intro d hd
    simp only [List.mem_range] at hd
    rw [pat_getD tm W S ia oa k d hd, arrOf_kIdx, if_pos (by omega)]
    rfl
  rw [hmap, takeWhile_codeAt tm k (S k) _ (hG k)]
  have hGt : ∀ g ∈ (S k).take (cc tm), (⟨k, g⟩ : Σ k : tm.K, tm.Γ k) ∈ symAll tm :=
    fun g hg => hG k g (List.mem_of_mem_take hg)
  exact filterMap_decK tm k _ hGt

theorem newCell_of (cm : CM) {W k d : ℕ} (hk : k < cm.K) (hd : d < W) (e : ℕ × List ℕ) (a : Arr) :
    cm.newCell W e a k d =
      if h : d < e.2.length then e.2[d] else
        (if d - e.2.length + e.1 < W then a k (d - e.2.length + e.1) else cm.A) := by
  unfold CM.newCell
  simp [hk, hd]

theorem newCell_stack (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) {W : ℕ}
    (S S' : ∀ k, List (tm.Γ k)) (k : tm.K) (j : ℕ) (new : List (tm.Γ k))
    (hS' : S' k = new ++ (S k).drop j) (hH : (S k).length < W) (d : ℕ) :
    (tmCM tm ia oa).newCell W (j, new.map fun g => encS tm ⟨k, g⟩) (arrOf tm W S) (kIdx tm k) d =
      arrOf tm W S' (kIdx tm k) d := by
  by_cases hd : d < W
  · have hK : kIdx tm k < (tmCM tm ia oa).K := kIdx_lt tm k
    rw [newCell_of _ hK hd]
    rw [arrOf_kIdx tm W S' k d, if_pos hd, hS']
    by_cases hn : d < new.length
    · have hn' : d < (new.map fun g => encS tm ⟨k, g⟩).length := by simpa using hn
      rw [dif_pos hn']
      simp [List.getElem?_append_left hn, List.getElem?_eq_getElem hn]
    · have hn' : ¬ d < (new.map fun g => encS tm ⟨k, g⟩).length := by simpa using hn
      rw [dif_neg hn']
      simp only [List.length_map]
      rw [List.getElem?_append_right (by omega), List.getElem?_drop]
      have e : j + (d - new.length) = d - new.length + j := by omega
      by_cases hs : d - new.length + j < W
      · rw [if_pos hs, arrOf_kIdx tm W S k _, if_pos hs, e]
      · rw [if_neg hs]
        have : (S k)[j + (d - new.length)]? = none := by
          apply List.getElem?_eq_none; omega
        rw [this]; rfl
  · have hK : kIdx tm k < (tmCM tm ia oa).K := kIdx_lt tm k
    unfold CM.newCell
    rw [arrOf_kIdx tm W S' k d, if_neg hd]
    simp [hd]
    rfl

theorem newCell_zero (cm : CM) {W : ℕ} (a : Arr)
    (hA : ∀ k d, ¬ (k < cm.K ∧ d < W) → a k d = cm.A) (k d : ℕ) :
    cm.newCell W (0, []) a k d = a k d := by
  by_cases h : k < cm.K ∧ d < W
  · unfold CM.newCell
    simp [h]
  · unfold CM.newCell
    simp only [h, if_false]
    exact (hA k d h).symm

theorem arrOf_outside (W : ℕ) (S : ∀ k, List (tm.Γ k)) (ia : tm.Γ tm.k₀ ≃ Bool)
    (oa : tm.Γ tm.k₁ ≃ Bool) (k d : ℕ) (h : ¬ (k < (tmCM tm ia oa).K ∧ d < W)) :
    arrOf tm W S k d = (tmCM tm ia oa).A := by
  by_cases hk : k < nK tm
  · have hd : ¬ d < W := fun hd => h ⟨hk, hd⟩
    unfold arrOf; rw [if_neg hd]; rfl
  · exact arrOf_ge tm W S (by omega) d

theorem sim_step (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) {W : ℕ}
    (hW : 2 * cc tm ≤ W) (c : tm.Cfg) (hG : GoodS tm c.stk)
    (hH : ∀ k, (c.stk k).length + cc tm ≤ W) :
    (tmCM tm ia oa).stepA W (ctlCode tm (c.l, c.var)) (arrOf tm W c.stk) =
      cfgA tm W (stepF tm c) := by
  obtain ⟨l?, v, S⟩ := c
  cases l? with
  | none =>
      have hstep : tm.step (⟨none, v, S⟩ : tm.Cfg) = none := rfl
      have hF : stepF tm (⟨none, v, S⟩ : tm.Cfg) = ⟨none, v, S⟩ := by
        unfold stepF; rw [hstep]; rfl
      rw [hF]
      have hq : ∀ l v', ctlDec tm (ctlCode tm (none, v)) ≠ some (some l, v') := by
        intro l v'; rw [ctlDec_ctlCode]; simp
      have hδ' : (tmCM tm ia oa).δ (ctlCode tm (none, v)) ((tmCM tm ia oa).pat (arrOf tm W S)) =
          (ctlCode tm (none, v), []) := tmDelta_other tm hq _
      unfold CM.stepA cfgA
      simp only []
      rw [hδ']
      refine Prod.ext rfl ?_
      funext k' d
      have he : (tmCM tm ia oa).eff (ctlCode tm (none, v))
          ((tmCM tm ia oa).pat (arrOf tm W S)) k' = (0, []) := by
        unfold CM.eff; rw [hδ']; simp
      show (tmCM tm ia oa).newCell W ((tmCM tm ia oa).eff _ _ k') (arrOf tm W S) k' d = _
      rw [he]
      exact newCell_zero _ _ (fun k d h => arrOf_outside tm W S ia oa k d h) k' d
  | some l =>
      have hw : ∀ k, winOf tm ((tmCM tm ia oa).pat (arrOf tm W S)) k = (S k).take (cc tm) :=
        fun k => winOf_arrOf tm ia oa (by omega) S hG k
      have hq : ctlDec tm (ctlCode tm (some l, v)) = some (some l, v) := ctlDec_ctlCode tm _
      set p := (tmCM tm ia oa).pat (arrOf tm W S) with hp
      obtain ⟨hδ1, hδ2⟩ := tmDelta_some tm hq p
      set r := effAux (fun k => winOf tm p k) (tm.m l) v (fun _ => (0, [])) with hr
      have hr' : r = effAux (fun k => (S k).take (cc tm)) (tm.m l) v (fun _ => (0, [])) := by
        rw [hr]
        have : (fun k => winOf tm p k) = fun k => (S k).take (cc tm) := funext hw
        rw [this]
      have hstep := stepAux_effAux (cc tm) S (tm.m l) v (fun _ => (0, []))
        (by intro k; simp; exact (nodes_lt_cc tm l).le)
      have hS0 : applyE S (fun _ => ((0 : ℕ), ([] : List _))) = S := by
        funext k; simp [applyE]
      rw [hS0, ← hr'] at hstep
      have hF : stepF tm (⟨some l, v, S⟩ : tm.Cfg) = ⟨r.1, r.2.1, applyE S r.2.2⟩ := by
        unfold stepF
        show (some (TM2.stepAux (tm.m l) v S)).getD _ = _
        rw [hstep]; rfl
      rw [hF]
      unfold CM.stepA cfgA
      simp only []
      refine Prod.ext hδ1 ?_
      funext k' d
      show (tmCM tm ia oa).newCell W ((tmCM tm ia oa).eff _ _ k') (arrOf tm W S) k' d = _
      by_cases hk : k' < nK tm
      · by_cases hd : d < W
        · -- the interesting case
          set k : tm.K := (eK tm).symm ⟨k', hk⟩ with hkdef
          have hkidx : kIdx tm k = k' := by
            unfold kIdx; rw [hkdef]; simp
          have heff : (tmCM tm ia oa).eff (ctlCode tm (some l, v)) p k' =
              ((r.2.2 k).1, (r.2.2 k).2.map fun g => encS tm ⟨k, g⟩) := by
            unfold CM.eff
            have := hδ2 k'
            change ((tmDelta tm _ p).2).getD k' (0, []) = _
            rw [this, ← hkidx, kOf_kIdx]
            rfl
          rw [heff, ← hkidx]
          exact newCell_stack tm ia oa S (applyE S r.2.2) k (r.2.2 k).1 (r.2.2 k).2 rfl
            (by have h1 : (S k).length + cc tm ≤ W := hH k
                have h2 : 0 < cc tm := Nat.succ_pos _
                omega) d
        · have hK : ¬ (k' < (tmCM tm ia oa).K ∧ d < W) := fun h => hd h.2
          unfold CM.newCell
          simp only [hK, if_false]
          exact (arrOf_outside tm W _ ia oa k' d hK).symm
      · have hK : ¬ (k' < (tmCM tm ia oa).K ∧ d < W) := fun h => hk h.1
        unfold CM.newCell
        simp only [hK, if_false]
        exact (arrOf_outside tm W _ ia oa k' d hK).symm

theorem goodS_stepF (c : tm.Cfg) (hG : GoodS tm c.stk) : GoodS tm (stepF tm c).stk := by
  obtain ⟨l?, v, S⟩ := c
  cases l? with
  | none =>
      have hstep : tm.step (⟨none, v, S⟩ : tm.Cfg) = none := rfl
      have hF : stepF tm (⟨none, v, S⟩ : tm.Cfg) = ⟨none, v, S⟩ := by
        unfold stepF; rw [hstep]; rfl
      rw [hF]; exact hG
  | some l =>
      have hstep := stepAux_effAux (cc tm) S (tm.m l) v (fun _ => (0, []))
        (by intro k; simp; exact (nodes_lt_cc tm l).le)
      have hS0 : applyE S (fun _ => ((0 : ℕ), ([] : List _))) = S := by
        funext k; simp [applyE]
      rw [hS0] at hstep
      have hF : stepF tm (⟨some l, v, S⟩ : tm.Cfg) =
          ⟨(effAux (fun k => (S k).take (cc tm)) (tm.m l) v (fun _ => (0, []))).1,
           (effAux (fun k => (S k).take (cc tm)) (tm.m l) v (fun _ => (0, []))).2.1,
           applyE S (effAux (fun k => (S k).take (cc tm)) (tm.m l) v (fun _ => (0, []))).2.2⟩ := by
        unfold stepF
        show (some (TM2.stepAux (tm.m l) v S)).getD _ = _
        rw [hstep]; rfl
      rw [hF]
      intro k g hg
      simp only [applyE, List.mem_append] at hg
      rcases hg with hg | hg
      · exact effAux_pushed _ _ (tm.m l) v _ (pushOk_m tm l)
          (by intro k g hg; simp at hg) k g hg
      · exact hG k g (List.mem_of_mem_drop hg)

/-- The real run, frozen after halting. -/
def runF (n : ℕ) (c : tm.Cfg) : tm.Cfg := (stepF tm)^[n] c

theorem goodS_runF (c : tm.Cfg) (hG : GoodS tm c.stk) (n : ℕ) : GoodS tm (runF tm n c).stk := by
  induction n with
  | zero => exact hG
  | succ n ih =>
      unfold runF at *
      rw [Function.iterate_succ_apply']
      exact goodS_stepF tm _ ih

theorem sim_run (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) {W : ℕ}
    (hW : 2 * cc tm ≤ W) (c₀ : tm.Cfg) (hG : GoodS tm c₀.stk)
    (hq : (tmCM tm ia oa).q0 = ctlCode tm (c₀.l, c₀.var)) (n : ℕ)
    (hH : ∀ t < n, ∀ k, ((runF tm t c₀).stk k).length + cc tm ≤ W) :
    (tmCM tm ia oa).runA W (arrOf tm W c₀.stk) n = cfgA tm W (runF tm n c₀) := by
  induction n with
  | zero => simp [CM.runA, cfgA, runF, hq]
  | succ n ih =>
      have ih' := ih (fun t ht => hH t (by omega))
      simp only [CM.runA]
      rw [ih']
      have hGn := goodS_runF tm c₀ hG n
      have := sim_step tm ia oa hW (runF tm n c₀) hGn (hH n (by omega))
      unfold cfgA at this ⊢
      simp only [] at this ⊢
      rw [this]
      unfold runF
      rw [Function.iterate_succ_apply']

theorem iterate_none (j : ℕ) : (flip bind tm.step)^[j] (none : Option tm.Cfg) = none := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply]; exact ih

theorem runF_of_evals (c c' : tm.Cfg) :
    ∀ (j : ℕ), (flip bind tm.step)^[j] (some c) = some c' → runF tm j c = c' := by
  intro j
  induction j generalizing c with
  | zero => intro h; simp at h; subst h; rfl
  | succ j ih =>
      intro h
      rw [Function.iterate_succ_apply] at h
      have h1 : (flip bind tm.step) (some c) = tm.step c := rfl
      rw [h1] at h
      cases hs : tm.step c with
      | none =>
          rw [hs] at h
          rw [iterate_none] at h; simp at h
      | some c₁ =>
          rw [hs] at h
          have := ih c₁ h
          unfold runF at this ⊢
          rw [Function.iterate_succ_apply]
          have hF : stepF tm c = c₁ := by unfold stepF; rw [hs]; rfl
          rw [hF]; exact this

theorem stepF_haltList (out : List (tm.Γ tm.k₁)) : stepF tm (haltList tm out) = haltList tm out := by
  unfold stepF
  have : tm.step (haltList tm out) = none := rfl
  rw [this]; rfl

theorem runF_haltList (out : List (tm.Γ tm.k₁)) (n : ℕ) :
    runF tm n (haltList tm out) = haltList tm out := by
  induction n with
  | zero => rfl
  | succ n ih => unfold runF at *; rw [Function.iterate_succ_apply', ih, stepF_haltList]

theorem runF_add (a b : ℕ) (c : tm.Cfg) : runF tm (a + b) c = runF tm a (runF tm b c) := by
  unfold runF; rw [Function.iterate_add_apply]

theorem stepF_of_none (c : tm.Cfg) (hh : c.l = none) : stepF tm c = c := by
  obtain ⟨l?, v, S⟩ := c
  simp only at hh
  subst hh
  have : tm.step (⟨none, v, S⟩ : tm.Cfg) = none := rfl
  unfold stepF; rw [this]; rfl

theorem runF_ge (j B : ℕ) (hB : j ≤ B) (c c' : tm.Cfg) (h : runF tm j c = c')
    (hh : c'.l = none) : runF tm B c = c' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hB
  rw [Nat.add_comm, runF_add, h]
  induction d with
  | zero => rfl
  | succ d ih =>
      unfold runF at *
      rw [Function.iterate_succ_apply', ih (by omega), stepF_of_none tm c' hh]

theorem pushCount_le_nodes {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (s : TM2.Stmt Γ Λ σ) : TM2Bound.pushCount s ≤ s.nodes := by
  induction s with
  | push k f q ih => simp [TM2Bound.pushCount, TM2.Stmt.nodes]; omega
  | peek k f q ih => simp [TM2Bound.pushCount, TM2.Stmt.nodes]; omega
  | pop k f q ih => simp [TM2Bound.pushCount, TM2.Stmt.nodes]; omega
  | load a q ih => simp [TM2Bound.pushCount, TM2.Stmt.nodes]; omega
  | branch f q₁ q₂ ih₁ ih₂ => simp [TM2Bound.pushCount, TM2.Stmt.nodes]; omega
  | goto f => simp [TM2Bound.pushCount, TM2.Stmt.nodes]
  | halt => simp [TM2Bound.pushCount, TM2.Stmt.nodes]

theorem stepBudget_lt_cc : TM2Bound.stepBudget tm < cc tm := by
  unfold TM2Bound.stepBudget cc
  have : (Finset.univ : Finset tm.Λ).sup (fun l => TM2Bound.pushCount (tm.m l)) ≤
      (Finset.univ : Finset tm.Λ).sup (fun l => (tm.m l).nodes) := by
    apply Finset.sup_le
    intro l _
    exact le_trans (pushCount_le_nodes (tm.m l))
      (Finset.le_sup (f := fun l => (tm.m l).nodes) (Finset.mem_univ l))
  omega

theorem total_stepF (c : tm.Cfg) :
    TM2Bound.total (stepF tm c).stk ≤ TM2Bound.total c.stk + TM2Bound.stepBudget tm := by
  unfold stepF
  cases h : tm.step c with
  | none => simp
  | some c' =>
      have := TM2Bound.step_total_le tm c c' h
      simpa using this

theorem total_runF (c : tm.Cfg) (n : ℕ) :
    TM2Bound.total (runF tm n c).stk ≤ TM2Bound.total c.stk + n * TM2Bound.stepBudget tm := by
  induction n with
  | zero => simp [runF]
  | succ n ih =>
      unfold runF at *
      rw [Function.iterate_succ_apply']
      have := total_stepF tm ((stepF tm)^[n] c)
      rw [Nat.succ_mul]
      omega

theorem length_le_total (S : ∀ k, List (tm.Γ k)) (k : tm.K) : (S k).length ≤ TM2Bound.total S := by
  unfold TM2Bound.total
  exact Finset.single_le_sum (f := fun i => (S i).length) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ k)

theorem initList_stk_k0 (s : List (tm.Γ tm.k₀)) : (initList tm s).stk tm.k₀ = s := by
  unfold initList; simp

theorem initList_stk_ne (s : List (tm.Γ tm.k₀)) {k : tm.K} (h : k ≠ tm.k₀) :
    (initList tm s).stk k = [] := by
  unfold initList; simp [h]

theorem haltList_stk_k1 (s : List (tm.Γ tm.k₁)) : (haltList tm s).stk tm.k₁ = s := by
  unfold haltList; simp

theorem haltList_stk_ne (s : List (tm.Γ tm.k₁)) {k : tm.K} (h : k ≠ tm.k₁) :
    (haltList tm s).stk k = [] := by
  unfold haltList; simp [h]

theorem initArr_eq (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) (W : ℕ) (x w : List Bool) :
    (tmCM tm ia oa).initArr W x w =
      arrOf tm W (initList tm ((encodePair (x, w)).map ia.symm)).stk := by
  funext k' d
  unfold CM.initArr
  by_cases hk : k' < nK tm
  · set k : tm.K := (eK tm).symm ⟨k', hk⟩ with hkdef
    have hkidx : kIdx tm k = k' := by unfold kIdx; rw [hkdef]; simp
    have hkof : kOf tm k' = some k := by unfold kOf; rw [dif_pos hk]
    by_cases hkk : k = tm.k₀
    · have hkof' : kOf tm k' = some tm.k₀ := by rw [hkof, hkk]
      have hkin : k' = (tmCM tm ia oa).kin := by
        show k' = kIdx tm tm.k₀
        rw [← hkidx, hkk]
      by_cases hd : d < W
      · have hcond : k' = (tmCM tm ia oa).kin ∧ k' < (tmCM tm ia oa).K ∧ d < W :=
          ⟨hkin, hk, hd⟩
        rw [if_pos hcond]
        unfold arrOf
        rw [if_pos hd, hkof']
        simp only [initList_stk_k0]
        by_cases hlen : d < (encodePair (x, w)).length
        · rw [if_pos hlen]
          have : ((encodePair (x, w)).map ia.symm)[d]? = some (ia.symm ((encodePair (x, w)).getD d false)) := by
            rw [List.getElem?_map, List.getElem?_eq_getElem hlen]
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
          rw [this]
          rfl
        · rw [if_neg hlen]
          have : ((encodePair (x, w)).map ia.symm)[d]? = none := by
            rw [List.getElem?_map]
            simp [List.getElem?_eq_none (by omega : (encodePair (x, w)).length ≤ d)]
          rw [this]
          rfl
      · have hcond : ¬ (k' = (tmCM tm ia oa).kin ∧ k' < (tmCM tm ia oa).K ∧ d < W) :=
          fun h => hd h.2.2
        rw [if_neg hcond]
        unfold arrOf
        rw [if_neg hd]; rfl
    · have hkin : ¬ k' = (tmCM tm ia oa).kin := by
        intro h
        apply hkk
        apply kIdx_inj tm
        rw [hkidx]; exact h
      have hcond : ¬ (k' = (tmCM tm ia oa).kin ∧ k' < (tmCM tm ia oa).K ∧ d < W) :=
        fun h => hkin h.1
      rw [if_neg hcond]
      unfold arrOf
      rw [hkof]
      by_cases hd : d < W
      · rw [if_pos hd]
        simp only [initList_stk_ne tm _ hkk]
        simp; rfl
      · rw [if_neg hd]; rfl
  · have hcond : ¬ (k' = (tmCM tm ia oa).kin ∧ k' < (tmCM tm ia oa).K ∧ d < W) :=
      fun h => hk h.2.1
    rw [if_neg hcond, arrOf_ge tm W _ (by omega)]
    rfl

theorem tmCM_halt (ia : tm.Γ tm.k₀ ≃ Bool) (oa : tm.Γ tm.k₁ ≃ Bool) (c : Ctl tm) :
    (tmCM tm ia oa).halt (ctlCode tm c) = true ↔ c.1 = none := by
  show (match ctlDec tm (ctlCode tm c) with
    | some (none, _) => true
    | _ => false) = true ↔ _
  rw [ctlDec_ctlCode]
  obtain ⟨o, v⟩ := c
  cases o <;> simp

theorem heights_of_blank (W : ℕ) (hc : 0 < cc tm) (hW : 2 * cc tm ≤ W)
    (S : ∀ k, List (tm.Γ k)) (hG : GoodS tm S)
    (hb : ∀ k : tm.K, ∀ d, W - 2 * cc tm ≤ d → d < W →
      arrOf tm W S (kIdx tm k) d = (symAll tm).length) :
    ∀ k, (S k).length + 2 * cc tm ≤ W := by
  intro k
  by_contra hlt
  have hd : W - 2 * cc tm < (S k).length := by omega
  have hdW : W - 2 * cc tm < W := by omega
  have := hb k (W - 2 * cc tm) le_rfl hdW
  rw [arrOf_kIdx, if_pos hdW, List.getElem?_eq_getElem hd] at this
  simp only at this
  have hlt2 := encS_lt tm _ (hG k _ (List.getElem_mem hd))
  omega

theorem total_initList (s : List (tm.Γ tm.k₀)) : TM2Bound.total (initList tm s).stk = s.length := by
  unfold TM2Bound.total
  rw [Finset.sum_eq_single tm.k₀]
  · rw [initList_stk_k0]
  · intro k _ hk; rw [initList_stk_ne tm s hk]; rfl
  · intro h; exact absurd (Finset.mem_univ _) h

theorem goodS_initList (s : List (tm.Γ tm.k₀)) : GoodS tm (initList tm s).stk := by
  intro k g hg
  by_cases hk : k = tm.k₀
  · subst hk
    rw [initList_stk_k0] at hg
    exact mem_symAll_input tm g
  · rw [initList_stk_ne tm s hk] at hg; simp at hg

theorem evals_prefix (c c' : tm.Cfg) (steps : ℕ) (h : (flip bind tm.step)^[steps] (some c) = some c')
    (j : ℕ) (hj : j ≤ steps) : ∃ cj, (flip bind tm.step)^[j] (some c) = some cj := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_comm, Function.iterate_add_apply] at h
  cases hh : (flip bind tm.step)^[j] (some c) with
  | none => rw [hh, iterate_none] at h; simp at h
  | some cj => exact ⟨cj, rfl⟩

theorem not_halted_before (c c' : tm.Cfg) (steps : ℕ)
    (h : (flip bind tm.step)^[steps] (some c) = some c') (j : ℕ) (hj : j < steps) :
    (runF tm j c).l ≠ none := by
  obtain ⟨cj, hcj⟩ := evals_prefix tm c c' steps h j hj.le
  have hr := runF_of_evals tm c cj j hcj
  rw [hr]
  intro hnone
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hj)
  rw [Nat.add_comm, Function.iterate_add_apply, Function.iterate_succ_apply'] at h
  rw [hcj] at h
  have : (flip bind tm.step) (some cj) = none := by
    show tm.step cj = none
    obtain ⟨l?, v, S⟩ := cj
    simp only at hnone
    subst hnone
    rfl
  rw [this, iterate_none] at h
  simp at h

end Build

/-! ## Correctness of the coded machine for a poly time verifier -/

section Correct

open Classical

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable {f : List Bool × List Bool → Bool}
  (h : TM2ComputableInPolyTime encodePair bitEnc f)

/-- The coded machine of a verifier. -/
noncomputable def verCM : CM := tmCM h.tm h.inputAlphabet h.outputAlphabet

theorem verCM_c : (verCM h).c = cc h.tm := rfl

theorem verCM_WF {W : ℕ} (hW : 2 * cc h.tm ≤ W) : (verCM h).WF W :=
  tmCM_WF h.tm h.inputAlphabet h.outputAlphabet hW

theorem accept_of_true (x w : List Bool) (hv : f (x, w) = true) {W B : ℕ}
    (hW : 2 * cc h.tm ≤ W)
    (hW2 : (encodePair (x, w)).length +
      h.time.eval (encodePair (x, w)).length * TM2Bound.stepBudget h.tm + 2 * cc h.tm ≤ W)
    (hB : h.time.eval (encodePair (x, w)).length ≤ B) :
    (verCM h).NoOverflow W B ((verCM h).initArr W x w) ∧
      (verCM h).Accepts ((verCM h).runA W ((verCM h).initArr W x w) B).1
        ((verCM h).runA W ((verCM h).initArr W x w) B).2 := by
  have hout := h.outputsFun (x, w)
  obtain ⟨⟨steps, hevals⟩, hle⟩ := hout
  set tm := h.tm with htm
  set ia := h.inputAlphabet with hia
  set oa := h.outputAlphabet with hoa
  set enc := encodePair (x, w) with henc
  let s : List (tm.Γ tm.k₀) := List.map ia.invFun enc
  have hs : s = enc.map ia.symm := rfl
  let c₀ : tm.Cfg := initList tm s
  let out : List (tm.Γ tm.k₁) := List.map oa.invFun (bitEnc (f (x, w)))
  have hevals' : (flip bind tm.step)^[steps] (some c₀) = some (haltList tm out) := hevals
  have hle' : steps ≤ h.time.eval enc.length := hle
  have hsteps : runF tm steps c₀ = haltList tm out := runF_of_evals tm c₀ _ steps hevals'
  have hhalt : ∀ t, steps ≤ t → runF tm t c₀ = haltList tm out := by
    intro t ht
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [Nat.add_comm, runF_add, hsteps, runF_haltList]
  have hGc : GoodS tm c₀.stk := goodS_initList tm s
  have hq : (verCM h).q0 = ctlCode tm (c₀.l, c₀.var) := rfl
  -- height bound
  have hlen : s.length = enc.length := by simp [hs]
  have hheight : ∀ t, ∀ k, ((runF tm t c₀).stk k).length ≤
      enc.length + h.time.eval enc.length * TM2Bound.stepBudget tm := by
    intro t k
    have htot : ∀ t, steps ≤ t → TM2Bound.total (runF tm t c₀).stk ≤
        enc.length + h.time.eval enc.length * TM2Bound.stepBudget tm := by
      intro t ht
      rw [hhalt t ht, ← hsteps]
      have := total_runF tm c₀ steps
      rw [total_initList, hlen] at this
      have h2 : steps * TM2Bound.stepBudget tm ≤ h.time.eval enc.length * TM2Bound.stepBudget tm :=
        Nat.mul_le_mul_right _ hle'
      omega
    by_cases ht : steps ≤ t
    · exact le_trans (length_le_total tm _ k) (htot t ht)
    · have := total_runF tm c₀ t
      rw [total_initList, hlen] at this
      have h2 : t * TM2Bound.stepBudget tm ≤ h.time.eval enc.length * TM2Bound.stepBudget tm :=
        Nat.mul_le_mul_right _ (by omega)
      exact le_trans (length_le_total tm _ k) (by omega)
  have hH : ∀ t < B, ∀ k, ((runF tm t c₀).stk k).length + cc tm ≤ W := by
    intro t _ k; have := hheight t k; omega
  have hsim : ∀ n ≤ B, (verCM h).runA W ((verCM h).initArr W x w) n = cfgA tm W (runF tm n c₀) := by
    intro n hn
    have hia_eq : (verCM h).initArr W x w = arrOf tm W c₀.stk := initArr_eq tm ia oa W x w
    rw [hia_eq]
    exact sim_run tm ia oa hW c₀ hGc hq n (fun t ht => hH t (by omega))
  refine ⟨?_, ?_⟩
  · intro t ht k hk d hd1 hd2
    have hd1' : W - 2 * cc tm ≤ d := hd1
    rw [hsim t ht]
    show arrOf tm W (runF tm t c₀).stk k d = (symAll tm).length
    by_cases hk' : k < nK tm
    · set kk : tm.K := (eK tm).symm ⟨k, hk'⟩ with hkk
      have hkof : kOf tm k = some kk := by unfold kOf; rw [dif_pos hk']
      unfold arrOf
      rw [if_pos hd2, hkof]
      have : ((runF tm t c₀).stk kk)[d]? = none := by
        apply List.getElem?_eq_none
        have := hheight t kk
        have hh : 2 * cc tm ≤ W := hW
        omega
      simp only [this]
    · exact arrOf_ge tm W _ (by omega) d
  · have hB' : steps ≤ B := le_trans hle' hB
    rw [hsim B le_rfl, hhalt B hB']
    have hcc : 0 < cc tm := Nat.succ_pos _
    have hW0 : 0 < W := by omega
    have hoc : out = [oa.symm true] := by
      simp [out, hv, bitEnc]
    refine ⟨?_, ?_, ?_⟩
    · exact (tmCM_halt tm ia oa ((haltList tm out).l, (haltList tm out).var)).2 rfl
    · show arrOf tm W (haltList tm out).stk (kIdx tm tm.k₁) 0 = encS tm ⟨tm.k₁, oa.symm true⟩
      rw [arrOf_kIdx, if_pos hW0, haltList_stk_k1, hoc]
      rfl
    · show arrOf tm W (haltList tm out).stk (kIdx tm tm.k₁) 1 = (symAll tm).length
      rw [arrOf_kIdx]
      by_cases h1 : 1 < W
      · rw [if_pos h1, haltList_stk_k1, hoc]; rfl
      · rw [if_neg h1]

theorem true_of_accepts (x w : List Bool) {W B : ℕ} (hW : 2 * cc h.tm ≤ W)
    (hno : (verCM h).NoOverflow W B ((verCM h).initArr W x w))
    (hacc : (verCM h).Accepts ((verCM h).runA W ((verCM h).initArr W x w) B).1
      ((verCM h).runA W ((verCM h).initArr W x w) B).2) :
    f (x, w) = true := by
  have hout := h.outputsFun (x, w)
  obtain ⟨⟨steps, hevals⟩, hle⟩ := hout
  set tm := h.tm with htm
  set ia := h.inputAlphabet with hia
  set oa := h.outputAlphabet with hoa
  set enc := encodePair (x, w) with henc
  let s : List (tm.Γ tm.k₀) := List.map ia.invFun enc
  let c₀ : tm.Cfg := initList tm s
  let out : List (tm.Γ tm.k₁) := List.map oa.invFun (bitEnc (f (x, w)))
  have hevals' : (flip bind tm.step)^[steps] (some c₀) = some (haltList tm out) := hevals
  have hsteps : runF tm steps c₀ = haltList tm out := runF_of_evals tm c₀ _ steps hevals'
  have hhalt : ∀ t, steps ≤ t → runF tm t c₀ = haltList tm out := by
    intro t ht
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [Nat.add_comm, runF_add, hsteps, runF_haltList]
  have hGc : GoodS tm c₀.stk := goodS_initList tm s
  have hq : (verCM h).q0 = ctlCode tm (c₀.l, c₀.var) := rfl
  have hcc : 0 < cc tm := Nat.succ_pos _
  have hia_eq : (verCM h).initArr W x w = arrOf tm W c₀.stk := initArr_eq tm ia oa W x w
  -- heights, by strong induction
  have hH : ∀ t ≤ B, (verCM h).runA W ((verCM h).initArr W x w) t = cfgA tm W (runF tm t c₀) ∧
      ∀ k, ((runF tm t c₀).stk k).length + 2 * cc tm ≤ W := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
        intro ht
        have hsim : (verCM h).runA W ((verCM h).initArr W x w) t = cfgA tm W (runF tm t c₀) := by
          rw [hia_eq]
          exact sim_run tm ia oa hW c₀ hGc hq t (fun t' ht' k => by
            have := (ih t' ht' (by omega)).2 k; omega)
        refine ⟨hsim, ?_⟩
        apply heights_of_blank tm W hcc hW _ (goodS_runF tm c₀ hGc t)
        intro k d hd1 hd2
        have := hno t ht (kIdx tm k) (kIdx_lt tm k) d hd1 hd2
        rw [hsim] at this
        exact this
  have hsimB : (verCM h).runA W ((verCM h).initArr W x w) B = cfgA tm W (runF tm B c₀) :=
    (hH B le_rfl).1
  rw [hsimB] at hacc
  obtain ⟨hh1, hh2, hh3⟩ := hacc
  have hnone : (runF tm B c₀).l = none :=
    (tmCM_halt tm ia oa ((runF tm B c₀).l, (runF tm B c₀).var)).1 hh1
  have hB' : steps ≤ B := by
    by_contra hlt
    exact not_halted_before tm c₀ _ steps hevals' B (by omega) hnone
  rw [hhalt B hB'] at hh2
  have hGB := goodS_runF tm c₀ hGc B
  rw [hhalt B hB'] at hGB
  have hW0 : 0 < W := by omega
  have hcell : arrOf tm W (haltList tm out).stk (kIdx tm tm.k₁) 0 =
      encS tm ⟨tm.k₁, oa.symm (f (x, w))⟩ := by
    rw [arrOf_kIdx, if_pos hW0, haltList_stk_k1]
    simp [out, bitEnc]
  have h2 : arrOf tm W (haltList tm out).stk (kIdx tm tm.k₁) 0 = encS tm ⟨tm.k₁, oa.symm true⟩ := hh2
  rw [hcell] at h2
  have hmem : (⟨tm.k₁, oa.symm (f (x, w))⟩ : Σ k : tm.K, tm.Γ k) ∈ symAll tm := by
    apply hGB tm.k₁
    rw [haltList_stk_k1]
    simp [out, bitEnc]
  have h3 := (List.idxOf_inj hmem).1 h2
  have h4 : oa.symm (f (x, w)) = oa.symm true := eq_of_heq (Sigma.mk.inj_iff.1 h3).2
  have := oa.symm.injective h4
  exact this

end Correct

end CL
end SATurday.Bridge
