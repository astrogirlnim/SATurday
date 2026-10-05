import Theory.ProofComplexity.Bridge.CookReckhow

/-!
# Cook Levin side of the Cook Reckhow bridge (Ladder Rung R5, Block C, hard direction)

Step 1: any `TM2ComputableInPolyTime` machine has output length bounded by a
polynomial in the input length (`outBound_of_computable`). This is the missing
generic lemma behind the `outBound` side conditions of `comp_enc`, and lets the
proof map `f` of a proof system be composed without a hand supplied bound.

LOG: R5 Bridge CookLevin module (output length bound, proofCheck FinTM2)
-/

open Turing
open scoped Polynomial

namespace SATurday.Bridge
namespace TM2Bound

open Turing.TM2

section
variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type}

/-- Largest number of pushes along one execution path of a statement. -/
def pushCount : Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushCount q + 1
  | .peek _ _ q => pushCount q
  | .pop _ _ q => pushCount q
  | .load _ q => pushCount q
  | .branch _ q₁ q₂ => max (pushCount q₁) (pushCount q₂)
  | .goto _ => 0
  | .halt => 0

/-- Total number of cells on all stacks. -/
def total (S : ∀ k, List (Γ k)) : ℕ := ∑ k, (S k).length

theorem total_update_push (S : ∀ k, List (Γ k)) (k : K) (a : Γ k) :
    total (Function.update S k (a :: S k)) = total S + 1 := by
  unfold total
  have : ∀ j, (Function.update S k (a :: S k) j).length =
      (S j).length + if j = k then 1 else 0 := by
    intro j
    by_cases h : j = k
    · subst h; simp
    · simp [Function.update_of_ne h, h]
  rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib]
  simp

theorem total_update_tail_le (S : ∀ k, List (Γ k)) (k : K) :
    total (Function.update S k (S k).tail) ≤ total S := by
  unfold total
  apply Finset.sum_le_sum
  intro j _
  by_cases h : j = k
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem stepAux_total_le (s : Stmt Γ Λ σ) :
    ∀ (v : σ) (S : ∀ k, List (Γ k)),
      total (stepAux s v S).stk ≤ total S + pushCount s := by
  induction s with
  | push k f q ih =>
      intro v S
      have := ih v (Function.update S k (f v :: S k))
      rw [total_update_push] at this
      simp only [stepAux, pushCount]
      omega
  | peek k f q ih =>
      intro v S
      simpa [stepAux, pushCount] using ih (f v (S k).head?) S
  | pop k f q ih =>
      intro v S
      have := ih (f v (S k).head?) (Function.update S k (S k).tail)
      have h2 := total_update_tail_le S k
      simp only [stepAux, pushCount]
      omega
  | load a q ih =>
      intro v S
      simpa [stepAux, pushCount] using ih (a v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
      intro v S
      cases h : f v <;> simp only [stepAux, pushCount, h, cond]
      · have := ih₂ v S; omega
      · have := ih₁ v S; omega
  | goto f => intro v S; simp [stepAux, pushCount]
  | halt => intro v S; simp [stepAux, pushCount]

section Machine

attribute [local instance] FinTM2.kFin FinTM2.ΛFin

/-- Per step push budget of a machine: the worst statement over all labels. -/
def stepBudget (tm : FinTM2) : ℕ :=
  Finset.univ.sup fun l => pushCount (tm.m l)

theorem step_total_le (tm : FinTM2) (c c' : tm.Cfg) (h : tm.step c = some c') :
    total c'.stk ≤ total c.stk + stepBudget tm := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [FinTM2.step, Turing.TM2.step] at h
  | some l =>
      simp only [FinTM2.step, Turing.TM2.step] at h
      have h' := Option.some.inj h
      subst h'
      have h1 := stepAux_total_le (tm.m l) v S
      have h2 : pushCount (tm.m l) ≤ stepBudget tm :=
        Finset.le_sup (f := fun l => pushCount (tm.m l)) (Finset.mem_univ l)
      change total (stepAux (tm.m l) v S).stk ≤ total S + stepBudget tm
      omega

theorem iterate_total_le (tm : FinTM2) :
    ∀ (n : ℕ) (c c' : tm.Cfg), (flip bind tm.step)^[n] (some c) = some c' →
      total c'.stk ≤ total c.stk + n * stepBudget tm := by
  intro n
  induction n with
  | zero => intro c c' h; simp at h; subst h; simp
  | succ n ih =>
      intro c c' h
      rw [Function.iterate_succ_apply'] at h
      cases hm : (flip bind tm.step)^[n] (some c) with
      | none => rw [hm] at h; simp [flip] at h
      | some d =>
          rw [hm] at h
          simp only [flip, Option.bind_some] at h
          have h1 := ih c d hm
          have h2 := step_total_le tm d c' h
          rw [Nat.succ_mul]
          omega

theorem total_initList (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    total (initList tm s).stk = s.length := by
  unfold total
  rw [Finset.sum_eq_single tm.k₀]
  · simp [initList]
  · intro k _ hk; simp [initList, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem length_le_total_haltList (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    s.length ≤ total (haltList tm s).stk := by
  unfold total
  have := Finset.single_le_sum (f := fun k => ((haltList tm s).stk k).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ tm.k₁)
  simpa [haltList] using this

/-- Output length of a machine run in `m` steps is at most input plus `m * budget`. -/
theorem output_length_le (tm : FinTM2) (s : List (tm.Γ tm.k₀)) (s' : List (tm.Γ tm.k₁))
    (m : ℕ) (h : TM2OutputsInTime tm s (some s') m) :
    s'.length ≤ s.length + m * stepBudget tm := by
  have hev := h.evals_in_steps
  simp only [Option.map_some] at hev
  have h1 := iterate_total_le tm h.steps _ _ hev
  have h2 := length_le_total_haltList tm s'
  rw [total_initList] at h1
  have h3 : h.steps * stepBudget tm ≤ m * stepBudget tm :=
    Nat.mul_le_mul_right _ h.steps_le_m
  omega

end Machine

end

end TM2Bound

/-- Every poly time certificate has a polynomial output length bound. -/
theorem outBound_of_computable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (h : TM2ComputableInPolyTime ea eb f) :
    ∃ q : Polynomial ℕ, ∀ a, (eb (f a)).length ≤ q.eval (ea a).length := by
  refine ⟨Polynomial.X + Polynomial.C (TM2Bound.stepBudget h.tm) * h.time, ?_⟩
  intro a
  have := TM2Bound.output_length_le h.tm _ _ _ (h.outputsFun a)
  simp only [List.length_map] at this
  simpa [Polynomial.eval_add, Polynomial.eval_mul, mul_comm] using this

/-! ## `proofCheck` as a certified FinTM2

Run `f` on the proof component, swap the pair, compare bit for bit. The output
bound of `f` needed by `comp_enc` comes from `outBound_of_computable`. -/

/-- The Cook Reckhow proof checker is poly time whenever the proof map is. -/
noncomputable def proofCheckComputableInPolyTime {f : List Bool → List Bool}
    (hf : TM2ComputableInPolyTime idBitEnc idBitEnc f) :
    TM2ComputableInPolyTime encodePair bitEnc
      (fun pw => proofCheck f pw.1 pw.2) := by
  let q : Polynomial ℕ := Classical.choose (outBound_of_computable hf)
  have hq : ∀ s : List Bool, (f s).length ≤ q.eval s.length := by
    intro s
    simpa [idBitEnc] using Classical.choose_spec (outBound_of_computable hf) s
  have h1 := mapSndComputableInPolyTime hf q hq
  have hSwap : TM2ComputableInPolyTime encodePair encodePair
      (fun r : List Bool × List Bool => (r.2, r.1)) :=
    swapPairEncComputableInPolyTime idBitEnc idBitEnc
  have h12 := comp_enc h1 hSwap (2 * Polynomial.X + 1 + q)
    (by
      intro pw
      have hπ : pw.2.length ≤ (encodePair pw).length := by
        rw [length_encodePair]; omega
      have := poly_eval_mono q hπ
      have h2 := hq pw.2
      simp only [length_encodePair, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one] at *
      omega)
  have h123 := comp_enc h12 bitsEqualPairComputableInPolyTime
    (2 * q + Polynomial.X + 1)
    (by
      intro pw
      have hπ : pw.2.length ≤ (encodePair pw).length := by
        rw [length_encodePair]; omega
      have hφ : pw.1.length ≤ (encodePair pw).length := by
        rw [length_encodePair]; omega
      have := poly_eval_mono q hπ
      have h2 := hq pw.2
      simp only [length_encodePair, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one] at *
      omega)
  exact recodeOutput h123 bitEnc (fun pw => proofCheck f pw.1 pw.2)
    (fun pw => by
      show bitEnc (proofCheck f pw.1 pw.2) = bitEnc (bitsEqualPair (f pw.2, pw.1))
      rw [proofCheck_eq_bitsEqualPair])

/-- Hard half of theorem 1, packaging done: a polynomially bounded proof system
puts `TAUT` in NP, with no side hypothesis. -/
theorem TAUT_in_NP_of_polyBounded' {f : List Bool → List Bool}
    (hf : IsPropProofSystem f) (hb : PolynomiallyBounded f) : InNP TAUT :=
  TAUT_in_NP_of_polyBounded hf hb (proofCheckComputableInPolyTime hf.poly)

end SATurday.Bridge
