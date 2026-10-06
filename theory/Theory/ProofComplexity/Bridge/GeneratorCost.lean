import Theory.ProofComplexity.Bridge.Generator

/-!
# Cost bounds for register programs (Ladder Rung R5)

`FP.Within M p a` says every register that `p` reads, when started from `a`, is at most `M`.
Then `FP.cost p a ≤ FP.costM M p`, and `costM` is a polynomial in `M`.

LOG: R5 Bridge GeneratorCost module (Within, costM, costPoly)
-/

open SATurday.Bridge.SP
open scoped Polynomial

namespace SATurday.Bridge
namespace CL

/-- Every register read by the program is at most `M`, along the run from `a`. -/
inductive _root_.SATurday.Bridge.SP.FP.Within (M : ℕ) : FP → AS → Prop
  | skip (a : AS) : Within M .skip a
  | seq (p q : FP) (a : AS) : Within M p a → Within M q (p.run a) → Within M (.seq p q) a
  | emit (bs : List Bool) (a : AS) : Within M (.emit bs) a
  | emitVar (r o : ℕ) (a : AS) : a.reg r ≤ M → Within M (.emitVar r o) a
  | addConst (r k : ℕ) (a : AS) : Within M (.addConst r k) a
  | subConst (r k : ℕ) (a : AS) : Within M (.subConst r k) a
  | addReg (r s : ℕ) (a : AS) : a.reg s ≤ M → Within M (.addReg r s) a
  | subReg (r s : ℕ) (a : AS) : a.reg s ≤ M → Within M (.subReg r s) a
  | clr (r : ℕ) (a : AS) : a.reg r ≤ M → Within M (.clr r) a
  | forLoop (cnt : ℕ) (body : FP) (a : AS) : a.reg cnt ≤ M →
      (∀ j < a.reg cnt, Within M body (body.run^[j] a)) → Within M (.forLoop cnt body) a
  | forBits (pf pt : FP) (a : AS) : a.bits.length ≤ M →
      (∀ i < a.bits.length, ∀ b r,
        (forBitsAux (fun b => if b then pt.run else pf.run) i a).bits = b :: r →
        Within M (if b then pt else pf)
          { forBitsAux (fun b => if b then pt.run else pf.run) i a with bits := r }) →
      Within M (.forBits pf pt) a
  | countBits (m : ℕ) (a : AS) : a.reg m ≤ M → a.bits.length ≤ M → a.inp.length ≤ M →
      Within M (.countBits m) a

/-- State independent cost bound, for registers and counts at most `M`. -/
def _root_.SATurday.Bridge.SP.FP.costM (M : ℕ) : FP → ℕ
  | .skip => 1
  | .seq p q => p.costM M + q.costM M
  | .emit bs => bs.length + 1
  | .emitVar _ o => 5 * M + o + 8
  | .addConst _ k => k + 1
  | .subConst _ k => 2 * k + 1
  | .addReg _ _ => 5 * M + 2
  | .subReg _ _ => 6 * M + 2
  | .clr _ => 2 * M + 1
  | .forLoop _ body => 6 * M + 3 + M * body.costM M
  | .forBits pf pt => M * (pf.costM M + pt.costM M + 1) + 1
  | .countBits _ => 2 * M + 2 * M + 5 * M + 4

theorem forBitsCost_le (M : ℕ) (pf pt : FP)
    (hf : ∀ a, pf.Within M a → pf.cost a ≤ pf.costM M)
    (ht : ∀ a, pt.Within M a → pt.cost a ≤ pt.costM M) :
    ∀ (k : ℕ) (a : AS),
      (∀ i < k, ∀ b r, (forBitsAux (fun b => if b then pt.run else pf.run) i a).bits = b :: r →
        (if b then pt else pf).Within M
          { forBitsAux (fun b => if b then pt.run else pf.run) i a with bits := r }) →
      forBitsCost (fun b => if b then pt.run else pf.run) (fun b => if b then pt.cost else pf.cost)
        k a ≤ k * (pf.costM M + pt.costM M + 1) + 1 := by
  intro k
  induction k with
  | zero => intro a _; simp [forBitsCost]
  | succ k ih =>
      intro a h
      simp only [forBitsCost]
      cases hb : a.bits with
      | nil => simp
      | cons b r =>
          simp only []
          have h0 := h 0 (by omega) b r (by simp [forBitsAux, hb])
          simp only [forBitsAux] at h0
          have hcost : (if b then pt.cost else pf.cost) { a with bits := r } ≤
              pf.costM M + pt.costM M := by
            cases b
            · simp only [Bool.false_eq_true, if_false] at h0 ⊢
              have := hf _ h0
              omega
            · simp only [if_true] at h0 ⊢
              have := ht _ h0
              omega
          have hrest := ih ((if b then pt.run else pf.run) { a with bits := r }) (by
            intro i hi
            intro b' r' hb'
            have := h (i + 1) (by omega) b' r' (by simpa [forBitsAux, hb] using hb')
            simpa [forBitsAux, hb] using this)
          nlinarith

theorem cost_le_costM (M : ℕ) : ∀ (p : FP) (a : AS), p.Within M a → p.cost a ≤ p.costM M := by
  intro p
  induction p with
  | skip => intro a _; simp [FP.cost, FP.costM]
  | seq p q ihp ihq =>
      intro a h
      cases h with
      | seq _ _ _ h1 h2 =>
      simp only [FP.cost, FP.costM]
      exact Nat.add_le_add (ihp a h1) (ihq _ h2)
  | emit bs => intro a _; simp [FP.cost, FP.costM]
  | emitVar r o =>
      intro a h
      cases h with
      | emitVar _ _ _ h => simp only [FP.cost, FP.costM]; omega
  | addConst r k => intro a _; simp [FP.cost, FP.costM]
  | subConst r k => intro a _; simp [FP.cost, FP.costM]
  | addReg r s =>
      intro a h; cases h with
      | addReg _ _ _ h => simp only [FP.cost, FP.costM]; omega
  | subReg r s =>
      intro a h; cases h with
      | subReg _ _ _ h => simp only [FP.cost, FP.costM]; omega
  | clr r =>
      intro a h; cases h with
      | clr _ _ h => simp only [FP.cost, FP.costM]; omega
  | forLoop cnt body ih =>
      intro a h
      cases h with
      | forLoop _ _ _ hc hj =>
      simp only [FP.cost, FP.costM]
      have hsum : ∑ i ∈ Finset.range (a.reg cnt), body.cost (body.run^[i] a) ≤
          a.reg cnt * body.costM M := by
        calc ∑ i ∈ Finset.range (a.reg cnt), body.cost (body.run^[i] a)
            ≤ ∑ i ∈ Finset.range (a.reg cnt), body.costM M :=
              Finset.sum_le_sum fun i hi => ih _ (hj i (Finset.mem_range.1 hi))
          _ = a.reg cnt * body.costM M := by simp
      have := Nat.mul_le_mul_right (body.costM M) hc
      omega
  | forBits pf pt ihf iht =>
      intro a h
      cases h with
      | forBits _ _ _ hl hw =>
      simp only [FP.cost, FP.costM]
      have := forBitsCost_le M pf pt ihf iht a.bits.length a hw
      have h2 : a.bits.length * (pf.costM M + pt.costM M + 1) ≤ M * (pf.costM M + pt.costM M + 1) :=
        Nat.mul_le_mul_right _ hl
      omega
  | countBits m =>
      intro a h
      cases h with
      | countBits _ _ h1 h2 h3 =>
      simp only [FP.cost, FP.costM]; omega

end CL
end SATurday.Bridge
