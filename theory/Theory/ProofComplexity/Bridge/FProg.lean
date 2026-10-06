import Theory.ProofComplexity.Bridge.StackProg

/-!
# Unary register programs over `StackProg` (Ladder Rung R5, Cook Levin generator tooling)

`FP` is a tiny language of unary registers and a bit output tape. Its abstract
semantics `FP.run` is a pure function on `AS`, and `FP.compile` produces a
`StackProg` whose `Exec` run realises it with a cost bound. The generator of the
tableau formula is then written and verified at the abstract level.

LOG: R5 Bridge FProg module (unary register programs, compile to stack programs)
-/

namespace SATurday.Bridge
namespace SP

variable {n : ℕ}

theorem upd_self (S : St n) (k : Fin n) (l : List Bool) : upd S k l k = l := by
  simp [upd]

theorem upd_ne (S : St n) {k j : Fin n} (l : List Bool) (h : j ≠ k) : upd S k l j = S j := by
  simp [upd, Function.update_of_ne h]

theorem upd_upd_same (S : St n) (k : Fin n) (l l' : List Bool) :
    upd (upd S k l) k l' = upd S k l' := by
  funext j; simp [upd]

theorem upd_comm (S : St n) {k j : Fin n} (h : k ≠ j) (l l' : List Bool) :
    upd (upd S k l) j l' = upd (upd S j l') k l := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [upd, Function.update_of_ne (Ne.symm h)]
  · by_cases hk : i = k
    · subst hk; simp [upd, Function.update_of_ne h]
    · simp [upd, Function.update_of_ne hi, Function.update_of_ne hk]

/-- Loop over a unary counter: `loop k skip body` runs `body` once per element. -/
theorem exec_loop_count (k : Fin n) (body : Prog n) (m cb : ℕ) (F : ℕ → St n)
    (hk : ∀ i ≤ m, F i k = List.replicate (m - i) true)
    (hstep : ∀ i < m, ∃ c, Exec body (upd (F i) k (List.replicate (m - i - 1) true)) (F (i + 1)) c ∧
      c ≤ cb) :
    ∃ c, Exec (.loop k .skip body) (F 0) (F m) c ∧ c ≤ m * (cb + 1) + 1 := by
  have key : ∀ j, j ≤ m → ∃ c, Exec (.loop k .skip body) (F (m - j)) (F m) c ∧
      c ≤ j * (cb + 1) + 1 := by
    intro j
    induction j with
    | zero =>
        intro _
        refine ⟨1, ?_, by omega⟩
        have := hk m le_rfl
        simp only [Nat.sub_self, List.replicate_zero] at this
        exact Exec.loop_nil this
    | succ j ih =>
        intro hj
        obtain ⟨c₂, h₂, hc₂⟩ := ih (by omega)
        have hi : m - (j + 1) < m := by omega
        obtain ⟨c₁, h₁, hc₁⟩ := hstep (m - (j + 1)) hi
        have hidx : m - (j + 1) + 1 = m - j := by omega
        rw [hidx] at h₁
        have hrep : List.replicate (m - (m - (j + 1))) true =
            true :: List.replicate (m - (m - (j + 1)) - 1) true := by
          have : m - (m - (j + 1)) = j + 1 := by omega
          rw [this]; simp [List.replicate_succ]
        have hkk := hk (m - (j + 1)) (by omega)
        rw [hrep] at hkk
        have hr : m - (m - (j + 1)) - 1 = j := by omega
        rw [hr] at hkk
        have hr2 : m - (m - (j + 1)) - 1 = j := hr
        have h₁' : Exec body (upd (F (m - (j + 1))) k (List.replicate j true)) (F (m - j)) c₁ := by
          have : m - (m - (j + 1)) - 1 = j := hr
          have e : m - (m - (j + 1)) - 1 = m - (m - (j + 1)) - 1 := rfl
          simpa [Nat.sub_sub, show m - (m - (j + 1)) - 1 = j from hr, hidx] using h₁
        refine ⟨c₁ + c₂ + 1, Exec.loop_true hkk h₁' h₂, ?_⟩
        nlinarith
  have := key m le_rfl
  simpa using this

/-- Push the given bits in order. -/
def pushes (k : Fin n) : List Bool → Prog n
  | [] => .skip
  | b :: bs => .seq (.push k b) (pushes k bs)

theorem exec_pushes (k : Fin n) (bs : List Bool) (S : St n) :
    Exec (pushes k bs) S (upd S k (bs.reverse ++ S k)) (bs.length + 1) := by
  induction bs generalizing S with
  | nil =>
      have e : upd S k (S k) = S := by funext j; simp [upd]
      simp only [pushes, List.reverse_nil, List.nil_append, List.length_nil, Nat.zero_add]
      rw [e]
      exact Exec.skip S
  | cons b bs ih =>
      have h1 := Exec.push S k b
      have h2 := ih (upd S k (b :: S k))
      have := Exec.seq h1 h2
      have e : upd (upd S k (b :: S k)) k (bs.reverse ++ upd S k (b :: S k) k) =
          upd S k ((b :: bs).reverse ++ S k) := by
        funext j; simp [upd]
      rw [e] at this
      simpa [pushes, Nat.add_comm, Nat.add_left_comm] using this

theorem rep_append_cons (i : ℕ) (l : List Bool) :
    List.replicate i true ++ true :: l = true :: (List.replicate i true ++ l) := by
  induction i with
  | zero => simp
  | succ i ih => simp [List.replicate_succ, ih]

/-- Move a unary counter to another stack (one `true` per element). -/
theorem exec_pump (src dst : Fin n) (hne : src ≠ dst) (m : ℕ) (S : St n)
    (hs : S src = List.replicate m true) :
    ∃ c, c ≤ 2 * m + 1 ∧ Exec (.loop src .skip (.push dst true)) S
      (upd (upd S src []) dst (List.replicate m true ++ S dst)) c := by
  let F : ℕ → St n := fun i =>
    upd (upd S src (List.replicate (m - i) true)) dst (List.replicate i true ++ S dst)
  have hF0 : F 0 = S := by
    funext j
    by_cases h1 : j = src
    · subst h1; simp [F, upd, Function.update_of_ne hne, hs]
    · by_cases h2 : j = dst
      · subst h2; simp [F, upd]
      · simp [F, upd, Function.update_of_ne h1, Function.update_of_ne h2]
  obtain ⟨c, hc, hcb⟩ := exec_loop_count src (.push dst true) m 1 F
    (by intro i _; simp [F, upd, Function.update_of_ne hne])
    (by
      intro i hi
      refine ⟨1, ?_, le_rfl⟩
      have := Exec.push (upd (F i) src (List.replicate (m - i - 1) true)) dst true
      convert this using 1
      funext j
      by_cases h1 : j = src
      · subst h1; simp [F, upd, Function.update_of_ne hne, show m - (i + 1) = m - i - 1 by omega]
      · by_cases h2 : j = dst
        · subst h2
          simp [F, upd, Function.update_of_ne (Ne.symm hne), List.replicate_succ]
        · simp [F, upd, Function.update_of_ne h1, Function.update_of_ne h2])
  rw [hF0] at hc
  refine ⟨c, by nlinarith, ?_⟩
  have hFm : F m = upd (upd S src []) dst (List.replicate m true ++ S dst) := by
    simp [F]
  rw [hFm] at hc
  exact hc

theorem upd_apply (S : St n) (k j : Fin n) (l : List Bool) :
    upd S k l j = if j = k then l else S j := by
  simp [upd, Function.update_apply]

/-- `r += s` using `t` as scratch (all distinct). -/
def addRegP (r s t : Fin n) : Prog n :=
  .seq (.loop s .skip (.push t true))
    (.loop t .skip (.seq (.push s true) (.push r true)))

theorem exec_addReg (r s t : Fin n) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (m : ℕ)
    (S : St n) (hs : S s = List.replicate m true) (ht : S t = []) :
    ∃ c, c ≤ 5 * m + 2 ∧ Exec (addRegP r s t) S (upd S r (List.replicate m true ++ S r)) c := by
  obtain ⟨c₁, hc₁, h₁⟩ := exec_pump s t hst m S hs
  set S₁ := upd (upd S s []) t (List.replicate m true ++ S t) with hS₁
  let F : ℕ → St n := fun i =>
    upd (upd (upd S t (List.replicate (m - i) true)) s (List.replicate i true))
      r (List.replicate i true ++ S r)
  have hF0 : F 0 = S₁ := by
    funext j
    simp only [F, hS₁, upd_apply, ht]
    split_ifs <;> simp_all
  obtain ⟨c₂, h₂, hc₂⟩ := exec_loop_count t (.seq (.push s true) (.push r true)) m 2 F
    (by
      intro i _
      simp only [F, upd_apply]
      split_ifs <;> simp_all)
    (by
      intro i hi
      refine ⟨2, ?_, le_rfl⟩
      have h1 := Exec.push (upd (F i) t (List.replicate (m - i - 1) true)) s true
      have h2 := Exec.push (upd (upd (F i) t (List.replicate (m - i - 1) true)) s
        (true :: upd (F i) t (List.replicate (m - i - 1) true) s)) r true
      have := Exec.seq h1 h2
      convert this using 1
      funext j
      simp only [F, upd_apply]
      split_ifs <;> simp_all [List.replicate_succ, show m - (i + 1) = m - i - 1 by omega])
  rw [hF0] at h₂
  have hFm : F m = upd S r (List.replicate m true ++ S r) := by
    funext j
    simp only [F, upd_apply, Nat.sub_self, List.replicate_zero]
    split_ifs <;> simp_all
  rw [hFm] at h₂
  exact ⟨c₁ + c₂, by omega, Exec.seq h₁ h₂⟩

/-- Pop `k` a fixed number of times. -/
def popsP (k : Fin n) : ℕ → Prog n
  | 0 => .skip
  | m + 1 => .seq (.pop3 k .skip .skip .skip) (popsP k m)

theorem upd_of_eq_nil (S : St n) (k : Fin n) (hk : S k = []) : upd S k [] = S := by
  funext j; by_cases h : j = k
  · subst h; simp [upd, hk]
  · simp [upd, Function.update_of_ne h]

theorem exec_pop_skip (k : Fin n) (S : St n) :
    Exec (.pop3 k .skip .skip .skip) S (upd S k (S k).tail) 2 := by
  cases hk : S k with
  | nil =>
      have h := Exec.pop_nil (c := 1) (pe := .skip) (pf := .skip) (pt := .skip) hk (Exec.skip S)
      simp only [List.tail_nil]
      rw [upd_of_eq_nil S k hk]
      exact h
  | cons b r =>
      simp only [List.tail_cons]
      cases b
      · exact Exec.pop_false (c := 1) hk (Exec.skip _)
      · exact Exec.pop_true (c := 1) hk (Exec.skip _)

theorem tail_drop_eq (l : List Bool) (m : ℕ) : l.tail.drop m = l.drop (m + 1) := by
  cases l <;> simp

theorem exec_pops (k : Fin n) (m : ℕ) (S : St n) :
    Exec (popsP k m) S (upd S k ((S k).drop m)) (2 * m + 1) := by
  induction m generalizing S with
  | zero =>
      have e : upd S k ((S k).drop 0) = S := by funext j; simp [upd]
      rw [e]; exact Exec.skip S
  | succ m ih =>
      have h1 := exec_pop_skip k S
      have h2 := ih (upd S k (S k).tail)
      have := Exec.seq h1 h2
      have e : upd (upd S k (S k).tail) k ((upd S k (S k).tail k).drop m) =
          upd S k ((S k).drop (m + 1)) := by
        funext j; simp [upd, tail_drop_eq]
      rw [e] at this
      simp only [popsP]
      convert this using 1
      omega

/-- `r := r - s` (truncated), using `t` as scratch. -/
def subRegP (r s t : Fin n) : Prog n :=
  .seq (.loop s .skip (.seq (.push t true) (.pop3 r .skip .skip .skip)))
    (.loop t .skip (.push s true))

theorem exec_subReg (r s t : Fin n) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (m : ℕ)
    (S : St n) (hs : S s = List.replicate m true) (ht : S t = []) :
    ∃ c, c ≤ 6 * m + 2 ∧ Exec (subRegP r s t) S (upd S r ((S r).drop m)) c := by
  let F : ℕ → St n := fun i =>
    upd (upd (upd S s (List.replicate (m - i) true)) t (List.replicate i true))
      r ((S r).drop i)
  have hF0 : F 0 = S := by
    funext j
    simp only [F, upd_apply]
    split_ifs <;> simp_all
  obtain ⟨c₁, h₁, hc₁⟩ := exec_loop_count s (.seq (.push t true) (.pop3 r .skip .skip .skip)) m 3 F
    (by
      intro i _
      simp only [F, upd_apply]
      split_ifs <;> simp_all)
    (by
      intro i hi
      refine ⟨3, ?_, le_rfl⟩
      have h1 := Exec.push (upd (F i) s (List.replicate (m - i - 1) true)) t true
      have h2 := exec_pop_skip r (upd (upd (F i) s (List.replicate (m - i - 1) true)) t
        (true :: upd (F i) s (List.replicate (m - i - 1) true) t))
      have := Exec.seq h1 h2
      convert this using 1
      funext j
      simp only [F, upd_apply]
      split_ifs <;> simp_all [List.replicate_succ, tail_drop_eq, show m - (i + 1) = m - i - 1 by omega])
  rw [hF0] at h₁
  have hFm : F m = upd (upd (upd S s []) t (List.replicate m true)) r ((S r).drop m) := by
    simp [F]
  rw [hFm] at h₁
  obtain ⟨c₂, hc₂, h₂⟩ := exec_pump t s (Ne.symm hst) m
    (upd (upd (upd S s []) t (List.replicate m true)) r ((S r).drop m))
    (by simp only [upd_apply]; split_ifs <;> simp_all)
  have e : upd (upd (upd (upd (upd S s []) t (List.replicate m true)) r ((S r).drop m)) t [])
      s (List.replicate m true ++ (upd (upd (upd S s []) t (List.replicate m true)) r
        ((S r).drop m)) s) = upd S r ((S r).drop m) := by
    funext j
    simp only [upd_apply]
    split_ifs <;> simp_all
  rw [e] at h₂
  exact ⟨c₁ + c₂, by omega, Exec.seq h₁ h₂⟩

/-- Emit `false false true^(|reg| + o) false` onto `out`; `reg` is restored. -/
def emitVarP (out reg tmp : Fin n) (o : ℕ) : Prog n :=
  .seq (pushes out [false, false])
    (.seq (.loop reg .skip (.seq (.push tmp true) (.push out true)))
      (.seq (.loop tmp .skip (.push reg true))
        (.seq (pushes out (List.replicate o true)) (.push out false))))

theorem exec_emitVar (out reg tmp : Fin n) (o : ℕ) (hor : out ≠ reg) (hot : out ≠ tmp)
    (hrt : reg ≠ tmp) (m : ℕ) (S : St n) (hs : S reg = List.replicate m true)
    (ht : S tmp = []) :
    ∃ c, c ≤ 5 * m + o + 8 ∧ Exec (emitVarP out reg tmp o) S
      (upd S out (([false, false] ++ List.replicate (m + o) true ++ [false]).reverse ++ S out)) c := by
  -- step 1
  have h1 := exec_pushes out [false, false] S
  set S₁ := upd S out ([false, false].reverse ++ S out) with hS₁
  -- step 2
  let F : ℕ → St n := fun i =>
    upd (upd (upd S₁ reg (List.replicate (m - i) true)) tmp (List.replicate i true))
      out (List.replicate i true ++ S₁ out)
  have hF0 : F 0 = S₁ := by
    funext j
    simp only [F, upd_apply, hS₁]
    split_ifs <;> simp_all
  obtain ⟨c₂, h₂, hc₂⟩ := exec_loop_count reg (.seq (.push tmp true) (.push out true)) m 2 F
    (by
      intro i _
      simp only [F, upd_apply, hS₁]
      split_ifs <;> simp_all)
    (by
      intro i hi
      refine ⟨2, ?_, le_rfl⟩
      have e1 := Exec.push (upd (F i) reg (List.replicate (m - i - 1) true)) tmp true
      have e2 := Exec.push (upd (upd (F i) reg (List.replicate (m - i - 1) true)) tmp
        (true :: upd (F i) reg (List.replicate (m - i - 1) true) tmp)) out true
      have := Exec.seq e1 e2
      convert this using 1
      funext j
      simp only [F, upd_apply, hS₁]
      split_ifs <;> simp_all [List.replicate_succ, show m - (i + 1) = m - i - 1 by omega])
  rw [hF0] at h₂
  set S₂ := F m with hS₂
  -- step 3: restore reg from tmp
  have hS₂t : S₂ tmp = List.replicate m true := by
    simp only [hS₂, F, upd_apply, hS₁]
    split_ifs <;> simp_all
  obtain ⟨c₃, hc₃, h₃⟩ := exec_pump tmp reg hrt.symm m S₂ hS₂t
  set S₃ := upd (upd S₂ tmp []) reg (List.replicate m true ++ S₂ reg) with hS₃
  -- steps 4 and 5
  have h4 := exec_pushes out (List.replicate o true) S₃
  set S₄ := upd S₃ out ((List.replicate o true).reverse ++ S₃ out) with hS₄
  have h5 := Exec.push S₄ out false
  have hfin := Exec.seq h4 h5
  have hfin3 := Exec.seq h₃ hfin
  have hfin2 := Exec.seq h₂ hfin3
  have hfull := Exec.seq h1 hfin2
  have e : upd S₄ out (false :: S₄ out) =
      upd S out (([false, false] ++ List.replicate (m + o) true ++ [false]).reverse ++ S out) := by
    funext j
    by_cases hjo : j = out
    · subst hjo
      have a1 : S₁ j = [false, false] ++ S j := by simp [hS₁, upd_apply]
      have a2 : S₂ j = List.replicate m true ++ S₁ j := by
        simp [hS₂, F, upd_apply]
      have a3 : S₃ j = S₂ j := by
        rw [hS₃]; simp only [upd_apply]; rw [if_neg hor, if_neg hot]
      have a4 : S₄ j = List.replicate o true ++ S₃ j := by
        simp [hS₄, upd_apply]
      have hrep : List.replicate (m + o) true = List.replicate o true ++ List.replicate m true := by
        rw [Nat.add_comm, List.replicate_add]
      have hcomm : List.replicate o true ++ List.replicate m true =
          List.replicate m true ++ List.replicate o true := by
        rw [← List.replicate_add, ← List.replicate_add, Nat.add_comm]
      rw [upd_self, upd_self, a4, a3, a2, a1, hrep]
      simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.append_assoc, List.cons_append, List.singleton_append,
        List.reverse_singleton]
      congr 1
      rw [← List.append_assoc, hcomm, List.append_assoc]
    · rw [upd_ne _ _ hjo, upd_ne _ _ hjo]
      have a4 : S₄ j = S₃ j := by rw [hS₄]; exact upd_ne _ _ hjo
      rw [a4]
      by_cases hjr : j = reg
      · subst hjr
        have a2 : S₂ j = [] := by
          rw [hS₂]
          simp only [F, upd_apply, hjo, hrt, if_false, if_true, Nat.sub_self, List.replicate_zero]
        have a3 : S₃ j = List.replicate m true ++ S₂ j := by
          rw [hS₃]; simp only [upd_apply, if_true]
        rw [a3, a2, hs]; simp
      · by_cases hjt : j = tmp
        · subst hjt
          have a3 : S₃ j = [] := by
            rw [hS₃]; simp only [upd_apply, hjr, if_false, if_true]
          rw [a3, ht]
        · have a2 : S₂ j = S j := by
            rw [hS₂]
            simp only [F, upd_apply, hjo, hjr, hjt, if_false, hS₁]
          have a3 : S₃ j = S₂ j := by
            rw [hS₃]; simp only [upd_apply, hjr, hjt, if_false]
          rw [a3, a2]
  rw [e] at hfull
  exact ⟨_, by simp only [List.length_cons, List.length_nil, List.length_replicate]; omega, hfull⟩

/-! ## The register language -/

/-- Unary register programs with an output tape and an input bit list. -/
inductive FP : Type
  | skip
  | seq (p q : FP)
  | emit (bs : List Bool)
  | emitVar (r o : ℕ)
  | addConst (r k : ℕ)
  | subConst (r k : ℕ)
  | addReg (r s : ℕ)
  | subReg (r s : ℕ)
  | clr (r : ℕ)
  | forLoop (cnt : ℕ) (body : FP)
  | forBits (pf pt : FP)
  | countBits (m : ℕ)

/-- Abstract state: register values, emitted bits, unread input, bits queued for
iteration (the input reversed by `countBits`). -/
structure AS where
  reg : ℕ → ℕ
  out : List Bool
  inp : List Bool
  bits : List Bool

/-- Iterate a bit dependent step over the remaining input bits. -/
def forBitsAux (f : Bool → AS → AS) : ℕ → AS → AS
  | 0, a => a
  | k + 1, a =>
      match a.bits with
      | [] => a
      | b :: r => forBitsAux f k (f b { a with bits := r })

/-- Abstract semantics. -/
def FP.run : FP → AS → AS
  | .skip, a => a
  | .seq p q, a => q.run (p.run a)
  | .emit bs, a => { a with out := a.out ++ bs }
  | .emitVar r o, a =>
      { a with out := a.out ++ ([false, false] ++ List.replicate (a.reg r + o) true ++ [false]) }
  | .addConst r k, a => { a with reg := Function.update a.reg r (a.reg r + k) }
  | .subConst r k, a => { a with reg := Function.update a.reg r (a.reg r - k) }
  | .addReg r s, a => { a with reg := Function.update a.reg r (a.reg r + a.reg s) }
  | .subReg r s, a => { a with reg := Function.update a.reg r (a.reg r - a.reg s) }
  | .clr r, a => { a with reg := Function.update a.reg r 0 }
  | .forLoop cnt body, a => body.run^[a.reg cnt] a
  | .forBits pf pt, a =>
      forBitsAux (fun b => if b then pt.run else pf.run) a.bits.length a
  | .countBits m, a =>
      { a with reg := Function.update a.reg m a.inp.length, bits := a.inp.reverse, inp := [] }

/-- Register `c` is read or written. -/
def FP.mentions (c : ℕ) : FP → Prop
  | .skip => False
  | .seq p q => p.mentions c ∨ q.mentions c
  | .emit _ => False
  | .emitVar r _ => r = c
  | .addConst r _ => r = c
  | .subConst r _ => r = c
  | .addReg r s => r = c ∨ s = c
  | .subReg r s => r = c ∨ s = c
  | .clr r => r = c
  | .forLoop cnt body => cnt = c ∨ body.mentions c
  | .forBits pf pt => pf.mentions c ∨ pt.mentions c
  | .countBits m => m = c

/-- No input bit access. -/
def FP.noBits : FP → Prop
  | .seq p q => p.noBits ∧ q.noBits
  | .forLoop _ body => body.noBits
  | .forBits _ _ => False
  | .countBits _ => False
  | _ => True

/-- Well formedness: registers below `NR`, distinctness, loop depth below `D`. -/
def FP.Ok (NR : ℕ) : ℕ → FP → Prop
  | _, .skip => True
  | d, .seq p q => p.Ok NR d ∧ q.Ok NR d
  | _, .emit _ => True
  | _, .emitVar r _ => r < NR
  | _, .addConst r _ => r < NR
  | _, .subConst r _ => r < NR
  | _, .addReg r s => r < NR ∧ s < NR ∧ r ≠ s
  | _, .subReg r s => r < NR ∧ s < NR ∧ r ≠ s
  | _, .clr r => r < NR
  | d, .forLoop cnt body => cnt < NR ∧ d < 3 ∧ body.Ok NR (d + 1)
  | d, .forBits pf pt => pf.noBits ∧ pt.noBits ∧ pf.Ok NR d ∧ pt.Ok NR d
  | _, .countBits m => m < NR

/-- Loop over the bits of a stack, with a bit dependent body. -/
theorem exec_loop_list (k : Fin n) (pf pt : Prog n) (l : List Bool) (cb : ℕ) (F : ℕ → St n)
    (hk : ∀ i ≤ l.length, F i k = l.drop i)
    (hstep : ∀ i (hi : i < l.length), ∃ c,
      Exec (if l[i] then pt else pf) (upd (F i) k (l.drop (i + 1))) (F (i + 1)) c ∧ c ≤ cb) :
    ∃ c, Exec (.loop k pf pt) (F 0) (F l.length) c ∧ c ≤ l.length * (cb + 1) + 1 := by
  have key : ∀ j, j ≤ l.length → ∃ c, Exec (.loop k pf pt) (F (l.length - j)) (F l.length) c ∧
      c ≤ j * (cb + 1) + 1 := by
    intro j
    induction j with
    | zero =>
        intro _
        refine ⟨1, ?_, by omega⟩
        have := hk l.length le_rfl
        simp only [Nat.sub_zero, List.drop_length] at this ⊢
        exact Exec.loop_nil this
    | succ j ih =>
        intro hj
        obtain ⟨c₂, h₂, hc₂⟩ := ih (by omega)
        have hi : l.length - (j + 1) < l.length := by omega
        obtain ⟨c₁, h₁, hc₁⟩ := hstep (l.length - (j + 1)) hi
        have hidx : l.length - (j + 1) + 1 = l.length - j := by omega
        rw [hidx] at h₁
        have hkk := hk (l.length - (j + 1)) (by omega)
        have hd : l.drop (l.length - (j + 1)) = l[l.length - (j + 1)] :: l.drop (l.length - j) := by
          rw [List.drop_eq_getElem_cons hi, hidx]
        rw [hd] at hkk
        have hb : ∀ b : Bool, b = l[l.length - (j + 1)] →
            Exec (if b then pt else pf) (upd (F (l.length - (j + 1))) k (l.drop (l.length - j)))
              (F (l.length - j)) c₁ := by
          intro b hb; rw [hb]; exact h₁
        refine ⟨c₁ + c₂ + 1, ?_, by nlinarith⟩
        cases hbit : l[l.length - (j + 1)] with
        | false =>
            rw [hbit] at hkk
            have := hb false hbit.symm
            simp only [Bool.false_eq_true, if_false] at this
            exact Exec.loop_false hkk this h₂
        | true =>
            rw [hbit] at hkk
            have := hb true hbit.symm
            simp only [if_true] at this
            exact Exec.loop_true hkk this h₂
  have := key l.length le_rfl
  simpa using this

/-! ## Machine layout and compilation -/

/-- Stack names: registers `0 .. NR-1`, then output, scratch, three loop savers,
input bits, final output, reversal scratch. -/
def mkF (NR r : ℕ) : Fin (NR + 8) := ⟨r % (NR + 8), Nat.mod_lt _ (by omega)⟩

theorem mkF_val {NR r : ℕ} (h : r < NR + 8) : (mkF NR r).val = r := Nat.mod_eq_of_lt h

theorem mkF_inj {NR a b : ℕ} (ha : a < NR + 8) (hb : b < NR + 8) :
    mkF NR a = mkF NR b ↔ a = b := by
  constructor
  · intro h
    have := congrArg Fin.val h
    rwa [mkF_val ha, mkF_val hb] at this
  · rintro rfl; rfl

theorem mkF_ne {NR a b : ℕ} (ha : a < NR + 8) (hb : b < NR + 8) (h : a ≠ b) :
    mkF NR a ≠ mkF NR b := fun e => h ((mkF_inj ha hb).1 e)

/-- Register stack. -/
def rS (NR r : ℕ) : Fin (NR + 8) := mkF NR r
/-- Output accumulator (reversed). -/
def oS (NR : ℕ) : Fin (NR + 8) := mkF NR NR
/-- Scratch. -/
def tS (NR : ℕ) : Fin (NR + 8) := mkF NR (NR + 1)
/-- Loop counter saver at depth `d`. -/
def sS (NR d : ℕ) : Fin (NR + 8) := mkF NR (NR + 2 + d)
/-- Input bits. -/
def iS (NR : ℕ) : Fin (NR + 8) := mkF NR (NR + 5)
/-- Final output. -/
def fS (NR : ℕ) : Fin (NR + 8) := mkF NR (NR + 6)
/-- Reversal scratch. -/
def xS (NR : ℕ) : Fin (NR + 8) := mkF NR (NR + 7)

/-- Compilation of register programs at loop depth `d`. -/
def FP.compile (NR : ℕ) : ℕ → FP → Prog (NR + 8)
  | _, .skip => .skip
  | d, .seq p q => .seq (p.compile NR d) (q.compile NR d)
  | _, .emit bs => pushes (oS NR) bs
  | _, .emitVar r o => emitVarP (oS NR) (rS NR r) (tS NR) o
  | _, .addConst r k => pushes (rS NR r) (List.replicate k true)
  | _, .subConst r k => popsP (rS NR r) k
  | _, .addReg r s => addRegP (rS NR r) (rS NR s) (tS NR)
  | _, .subReg r s => subRegP (rS NR r) (rS NR s) (tS NR)
  | _, .clr r => .loop (rS NR r) .skip .skip
  | d, .forLoop cnt body =>
      .seq (.loop (rS NR cnt) .skip (.seq (.push (sS NR d) true) (.push (tS NR) true)))
        (.seq (.loop (tS NR) .skip (.push (rS NR cnt) true))
          (.loop (sS NR d) .skip (body.compile NR (d + 1))))
  | d, .forBits pf pt => .loop (xS NR) (pf.compile NR d) (pt.compile NR d)
  | _, .countBits m =>
      .seq (.loop (rS NR m) .skip .skip)
        (.seq (.loop (xS NR) .skip .skip)
          (.loop (iS NR) (.seq (.push (xS NR) false) (.push (rS NR m) true))
            (.seq (.push (xS NR) true) (.push (rS NR m) true))))

/-- The machine state realises the abstract state at loop depth `d`. -/
def SatD (NR d : ℕ) (a : AS) (S : St (NR + 8)) : Prop :=
  (∀ r < NR, S (rS NR r) = List.replicate (a.reg r) true) ∧
  S (oS NR) = a.out.reverse ∧ S (tS NR) = [] ∧
  (∀ e, d ≤ e → e < 3 → S (sS NR e) = []) ∧
  S (iS NR) = a.inp ∧ S (xS NR) = a.bits

/-! ### Distinctness of the named stacks -/

section Distinct
variable {NR : ℕ}

theorem rS_ne_oS {r : ℕ} (hr : r < NR) : rS NR r ≠ oS NR :=
  mkF_ne (by omega) (by omega) (by omega)
theorem rS_ne_tS {r : ℕ} (hr : r < NR) : rS NR r ≠ tS NR :=
  mkF_ne (by omega) (by omega) (by omega)
theorem rS_ne_sS {r : ℕ} (hr : r < NR) {e : ℕ} (he : e < 3) : rS NR r ≠ sS NR e :=
  mkF_ne (by omega) (by omega) (by omega)
theorem rS_ne_iS {r : ℕ} (hr : r < NR) : rS NR r ≠ iS NR :=
  mkF_ne (by omega) (by omega) (by omega)
theorem rS_ne_xS {r : ℕ} (hr : r < NR) : rS NR r ≠ xS NR :=
  mkF_ne (by omega) (by omega) (by omega)
theorem rS_ne_fS {r : ℕ} (hr : r < NR) : rS NR r ≠ fS NR :=
  mkF_ne (by omega) (by omega) (by omega)
theorem rS_ne_rS {r s : ℕ} (hr : r < NR) (hs : s < NR) (h : r ≠ s) : rS NR r ≠ rS NR s :=
  mkF_ne (by omega) (by omega) h
theorem oS_ne_tS : oS NR ≠ tS NR := mkF_ne (by omega) (by omega) (by omega)
theorem oS_ne_sS {e : ℕ} (he : e < 3) : oS NR ≠ sS NR e := mkF_ne (by omega) (by omega) (by omega)
theorem oS_ne_iS : oS NR ≠ iS NR := mkF_ne (by omega) (by omega) (by omega)
theorem oS_ne_xS : oS NR ≠ xS NR := mkF_ne (by omega) (by omega) (by omega)
theorem oS_ne_fS : oS NR ≠ fS NR := mkF_ne (by omega) (by omega) (by omega)
theorem tS_ne_sS {e : ℕ} (he : e < 3) : tS NR ≠ sS NR e := mkF_ne (by omega) (by omega) (by omega)
theorem tS_ne_iS : tS NR ≠ iS NR := mkF_ne (by omega) (by omega) (by omega)
theorem tS_ne_xS : tS NR ≠ xS NR := mkF_ne (by omega) (by omega) (by omega)
theorem tS_ne_fS : tS NR ≠ fS NR := mkF_ne (by omega) (by omega) (by omega)
theorem sS_ne_iS {e : ℕ} (he : e < 3) : sS NR e ≠ iS NR := mkF_ne (by omega) (by omega) (by omega)
theorem sS_ne_xS {e : ℕ} (he : e < 3) : sS NR e ≠ xS NR := mkF_ne (by omega) (by omega) (by omega)
theorem sS_ne_fS {e : ℕ} (he : e < 3) : sS NR e ≠ fS NR := mkF_ne (by omega) (by omega) (by omega)
theorem sS_ne_sS {e e' : ℕ} (he : e < 3) (he' : e' < 3) (h : e ≠ e') : sS NR e ≠ sS NR e' :=
  mkF_ne (by omega) (by omega) (by omega)
theorem iS_ne_xS : iS NR ≠ xS NR := mkF_ne (by omega) (by omega) (by omega)
theorem iS_ne_fS : iS NR ≠ fS NR := mkF_ne (by omega) (by omega) (by omega)
theorem xS_ne_fS : xS NR ≠ fS NR := mkF_ne (by omega) (by omega) (by omega)

end Distinct

/-! ### Updating the abstract and the machine state together -/

theorem SatD.upd_reg {NR d : ℕ} {a : AS} {S : St (NR + 8)} (h : SatD NR d a S) {r : ℕ}
    (hr : r < NR) (v : ℕ) :
    SatD NR d { a with reg := Function.update a.reg r v }
      (upd S (rS NR r) (List.replicate v true)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r' hr'
    by_cases hrr : r' = r
    · subst hrr; simp [upd_self]
    · rw [upd_ne _ _ (rS_ne_rS hr' hr hrr)]
      simp [Function.update_of_ne hrr, h1 r' hr']
  · rw [upd_ne _ _ (Ne.symm (rS_ne_oS hr))]; exact h2
  · rw [upd_ne _ _ (Ne.symm (rS_ne_tS hr))]; exact h3
  · intro e he1 he2
    rw [upd_ne _ _ (Ne.symm (rS_ne_sS hr he2))]; exact h4 e he1 he2
  · rw [upd_ne _ _ (Ne.symm (rS_ne_iS hr))]; exact h5
  · rw [upd_ne _ _ (Ne.symm (rS_ne_xS hr))]; exact h6

theorem SatD.upd_out {NR d : ℕ} {a : AS} {S : St (NR + 8)} (h : SatD NR d a S) (bs : List Bool) :
    SatD NR d { a with out := a.out ++ bs } (upd S (oS NR) (bs.reverse ++ S (oS NR))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [upd_ne _ _ (rS_ne_oS hr)]; exact h1 r hr
  · simp [upd_self, h2]
  · rw [upd_ne _ _ (Ne.symm oS_ne_tS)]; exact h3
  · intro e he1 he2
    rw [upd_ne _ _ (Ne.symm (oS_ne_sS he2))]; exact h4 e he1 he2
  · rw [upd_ne _ _ (Ne.symm oS_ne_iS)]; exact h5
  · rw [upd_ne _ _ (Ne.symm oS_ne_xS)]; exact h6

/-! ### Cost and the compilation theorem -/

/-- Cost of the bit loop, mirroring `forBitsAux`. -/
def forBitsCost (f : Bool → AS → AS) (cf : Bool → AS → ℕ) : ℕ → AS → ℕ
  | 0, _ => 1
  | k + 1, a =>
      match a.bits with
      | [] => 1
      | b :: r => cf b { a with bits := r } + 1 + forBitsCost f cf k (f b { a with bits := r })

/-- An upper bound for the number of instructions. -/
def FP.cost : FP → AS → ℕ
  | .skip, _ => 1
  | .seq p q, a => p.cost a + q.cost (p.run a)
  | .emit bs, _ => bs.length + 1
  | .emitVar r o, a => 5 * a.reg r + o + 8
  | .addConst _ k, _ => k + 1
  | .subConst _ k, _ => 2 * k + 1
  | .addReg _ s, a => 5 * a.reg s + 2
  | .subReg _ s, a => 6 * a.reg s + 2
  | .clr r, a => 2 * a.reg r + 1
  | .forLoop cnt body, a =>
      6 * a.reg cnt + 3 + ∑ i ∈ Finset.range (a.reg cnt), body.cost (body.run^[i] a)
  | .forBits pf pt, a =>
      forBitsCost (fun b => if b then pt.run else pf.run)
        (fun b => if b then pt.cost else pf.cost) a.bits.length a
  | .countBits m, a => 2 * a.reg m + 2 * a.bits.length + 5 * a.inp.length + 4

theorem frame_reg {NR : ℕ} (S : St (NR + 8)) {r : ℕ} (hr : r < NR) (l : List Bool) :
    (∀ e, e < 3 → upd S (rS NR r) l (sS NR e) = S (sS NR e)) ∧
      upd S (rS NR r) l (fS NR) = S (fS NR) :=
  ⟨fun e he => upd_ne _ _ (Ne.symm (rS_ne_sS hr he)), upd_ne _ _ (Ne.symm (rS_ne_fS hr))⟩

theorem frame_out {NR : ℕ} (S : St (NR + 8)) (l : List Bool) :
    (∀ e, e < 3 → upd S (oS NR) l (sS NR e) = S (sS NR e)) ∧
      upd S (oS NR) l (fS NR) = S (fS NR) :=
  ⟨fun e he => upd_ne _ _ (Ne.symm (oS_ne_sS he)), upd_ne _ _ (Ne.symm oS_ne_fS)⟩

theorem SatD.weaken {NR d : ℕ} {a : AS} {S : St (NR + 8)} (h : SatD NR d a S) :
    SatD NR (d + 1) a S := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, fun e he1 he2 => h4 e (by omega) he2, h5, h6⟩

theorem SatD.upd_sav {NR D : ℕ} {a : AS} {S : St (NR + 8)} (h : SatD NR D a S) {e : ℕ}
    (he : e < D) (he3 : e < 3) (l : List Bool) : SatD NR D a (upd S (sS NR e) l) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rw [upd_ne _ _ (rS_ne_sS hr he3)]; exact h1 r hr
  · rw [upd_ne _ _ (oS_ne_sS he3)]; exact h2
  · rw [upd_ne _ _ (tS_ne_sS he3)]; exact h3
  · intro e' he1' he2'
    rw [upd_ne _ _ (sS_ne_sS he2' he3 (by omega))]; exact h4 e' he1' he2'
  · rw [upd_ne _ _ (sS_ne_iS he3).symm]; exact h5
  · rw [upd_ne _ _ (sS_ne_xS he3).symm]; exact h6

theorem SatD.of_succ {NR d : ℕ} {a : AS} {S : St (NR + 8)} (h : SatD NR (d + 1) a S)
    (h0 : S (sS NR d) = []) : SatD NR d a S := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, h3, ?_, h5, h6⟩
  intro e he1 he2
  by_cases hed : e = d
  · subst hed; exact h0
  · exact h4 e (by omega) he2

theorem exec_forLoop_main (NR d : ℕ) (hd : d < 3) (bodyP : Prog (NR + 8)) (body : FP)
    (hbody : ∀ (a : AS) (S : St (NR + 8)), SatD NR (d + 1) a S →
      ∃ S' c, Exec bodyP S S' c ∧ SatD NR (d + 1) (body.run a) S' ∧
        (∀ e, e < d + 1 → e < 3 → S' (sS NR e) = S (sS NR e)) ∧ S' (fS NR) = S (fS NR) ∧
        c ≤ body.cost a) :
    ∀ j (a : AS) (S : St (NR + 8)), SatD NR (d + 1) a S → S (sS NR d) = List.replicate j true →
      ∃ S' c, Exec (.loop (sS NR d) .skip bodyP) S S' c ∧
        SatD NR (d + 1) (body.run^[j] a) S' ∧ S' (sS NR d) = [] ∧
        (∀ e, e < d → e < 3 → S' (sS NR e) = S (sS NR e)) ∧ S' (fS NR) = S (fS NR) ∧
        c ≤ (∑ i ∈ Finset.range j, body.cost (body.run^[i] a)) + j + 1 := by
  intro j
  induction j with
  | zero =>
      intro a S hS hs
      exact ⟨S, 1, Exec.loop_nil hs, hS, hs, fun _ _ _ => rfl, rfl, by simp⟩
  | succ j ih =>
      intro a S hS hs
      have hs' : S (sS NR d) = true :: List.replicate j true := by
        rw [hs]; simp [List.replicate_succ]
      have hS₀ := hS.upd_sav (e := d) (by omega) hd (List.replicate j true)
      obtain ⟨S₁, c₁, h₁, hS₁, hf₁, hk₁, hc₁⟩ := hbody a _ hS₀
      have hsav : S₁ (sS NR d) = List.replicate j true := by
        rw [hf₁ d (by omega) hd]; simp [upd_self]
      obtain ⟨S₂, c₂, h₂, hS₂, hs₂, hf₂, hk₂, hc₂⟩ := ih (body.run a) S₁ hS₁ hsav
      refine ⟨S₂, c₁ + c₂ + 1, Exec.loop_true hs' h₁ h₂, ?_, hs₂, ?_, ?_, ?_⟩
      · rw [Function.iterate_succ_apply]; exact hS₂
      · intro e he he3
        rw [hf₂ e he he3, hf₁ e (by omega) he3, upd_ne _ _ (sS_ne_sS he3 hd (by omega))]
      · rw [hk₂, hk₁, upd_ne _ _ (sS_ne_fS hd).symm]
      · rw [Finset.sum_range_succ']
        simp only [Function.iterate_succ_apply]
        simp only [Function.iterate_zero, id] at *
        omega

theorem FP.noBits_run : ∀ (p : FP), p.noBits → ∀ a : AS,
    (p.run a).bits = a.bits ∧ (p.run a).inp = a.inp := by
  intro p
  induction p with
  | seq p q ihp ihq =>
      intro h a
      have h1 := ihp h.1 a
      have h2 := ihq h.2 (p.run a)
      exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
  | forLoop cnt body ih =>
      intro h a
      have key : ∀ j (a : AS), (body.run^[j] a).bits = a.bits ∧ (body.run^[j] a).inp = a.inp := by
        intro j
        induction j with
        | zero => intro a; simp
        | succ j ihj =>
            intro a
            rw [Function.iterate_succ_apply]
            have h1 := ihj (body.run a)
            have h2 := ih h a
            exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
      exact key _ a
  | forBits _ _ _ _ => intro h; exact absurd h id
  | countBits _ => intro h; exact absurd h id
  | _ => intros; simp [FP.run]

theorem SatD.set_bits {NR d : ℕ} {a : AS} {S : St (NR + 8)} (h : SatD NR d a S) (l : List Bool) :
    SatD NR d { a with bits := l } (upd S (xS NR) l) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr; rw [upd_ne _ _ (rS_ne_xS hr)]; exact h1 r hr
  · rw [upd_ne _ _ oS_ne_xS]; exact h2
  · rw [upd_ne _ _ tS_ne_xS]; exact h3
  · intro e he1 he2; rw [upd_ne _ _ (sS_ne_xS he2)]; exact h4 e he1 he2
  · rw [upd_ne _ _ iS_ne_xS]; exact h5
  · simp [upd_self]

theorem exec_forBits (NR d : ℕ) (pfP ptP : Prog (NR + 8)) (pf pt : FP)
    (hpf : pf.noBits) (hpt : pt.noBits)
    (hf : ∀ (a : AS) (S : St (NR + 8)), SatD NR d a S →
      ∃ S' c, Exec pfP S S' c ∧ SatD NR d (pf.run a) S' ∧
        (∀ e, e < d → e < 3 → S' (sS NR e) = S (sS NR e)) ∧ S' (fS NR) = S (fS NR) ∧
        c ≤ pf.cost a)
    (ht : ∀ (a : AS) (S : St (NR + 8)), SatD NR d a S →
      ∃ S' c, Exec ptP S S' c ∧ SatD NR d (pt.run a) S' ∧
        (∀ e, e < d → e < 3 → S' (sS NR e) = S (sS NR e)) ∧ S' (fS NR) = S (fS NR) ∧
        c ≤ pt.cost a) :
    ∀ k (a : AS) (S : St (NR + 8)), SatD NR d a S → a.bits.length = k →
      ∃ S' c, Exec (.loop (xS NR) pfP ptP) S S' c ∧
        SatD NR d (forBitsAux (fun b => if b then pt.run else pf.run) k a) S' ∧
        (∀ e, e < d → e < 3 → S' (sS NR e) = S (sS NR e)) ∧ S' (fS NR) = S (fS NR) ∧
        c ≤ forBitsCost (fun b => if b then pt.run else pf.run)
          (fun b => if b then pt.cost else pf.cost) k a := by
  intro k
  induction k with
  | zero =>
      intro a S hS hk
      have hb : a.bits = [] := List.eq_nil_of_length_eq_zero hk
      have hx : S (xS NR) = [] := by rw [hS.2.2.2.2.2, hb]
      exact ⟨S, 1, Exec.loop_nil hx, by simpa [forBitsAux] using hS, fun _ _ _ => rfl, rfl,
        by simp [forBitsCost]⟩
  | succ k ih =>
      intro a S hS hk
      cases hb : a.bits with
      | nil => rw [hb] at hk; simp at hk
      | cons b r =>
          have hx : S (xS NR) = b :: r := by rw [hS.2.2.2.2.2, hb]
          have hlen : r.length = k := by rw [hb] at hk; simpa using hk
          have hS₀ := hS.set_bits r
          have ha' : ({ a with bits := r } : AS).bits = r := rfl
          cases b with
          | false =>
              obtain ⟨S₁, c₁, h₁, hS₁, hf₁, hk₁, hc₁⟩ := hf _ _ hS₀
              have hbits := (FP.noBits_run pf hpf { a with bits := r })
              have hx₁ : S₁ (xS NR) = r := by rw [hS₁.2.2.2.2.2, hbits.1]
              have hlen₁ : (pf.run { a with bits := r }).bits.length = k := by
                rw [hbits.1]; exact hlen
              obtain ⟨S₂, c₂, h₂, hS₂, hf₂, hk₂, hc₂⟩ := ih _ S₁ hS₁ hlen₁
              refine ⟨S₂, c₁ + c₂ + 1, Exec.loop_false hx ?_ h₂, ?_, ?_, ?_, ?_⟩
              · simpa using h₁
              · simp only [forBitsAux, hb]
                simpa using hS₂
              · intro e he he3
                have := hf₁ e he he3
                rw [hf₂ e he he3, hf₁ e he he3, upd_ne _ _ (sS_ne_xS he3)]
              · rw [hk₂, hk₁, upd_ne _ _ xS_ne_fS.symm]
              · simp only [forBitsCost, hb]
                simp at hc₁ hc₂ ⊢
                omega
          | true =>
              obtain ⟨S₁, c₁, h₁, hS₁, hf₁, hk₁, hc₁⟩ := ht _ _ hS₀
              have hbits := (FP.noBits_run pt hpt { a with bits := r })
              have hx₁ : S₁ (xS NR) = r := by rw [hS₁.2.2.2.2.2, hbits.1]
              have hlen₁ : (pt.run { a with bits := r }).bits.length = k := by
                rw [hbits.1]; exact hlen
              obtain ⟨S₂, c₂, h₂, hS₂, hf₂, hk₂, hc₂⟩ := ih _ S₁ hS₁ hlen₁
              refine ⟨S₂, c₁ + c₂ + 1, Exec.loop_true hx ?_ h₂, ?_, ?_, ?_, ?_⟩
              · simpa using h₁
              · simp only [forBitsAux, hb]
                simpa using hS₂
              · intro e he he3
                have := hf₁ e he he3
                rw [hf₂ e he he3, hf₁ e he he3, upd_ne _ _ (sS_ne_xS he3)]
              · rw [hk₂, hk₁, upd_ne _ _ xS_ne_fS.symm]
              · simp only [forBitsCost, hb]
                simp at hc₁ hc₂ ⊢
                omega

theorem oS_ne_rS_aux {NR r : ℕ} (hr : r < NR) : oS NR ≠ rS NR r := (rS_ne_oS hr).symm
theorem tS_ne_rS_aux {NR r : ℕ} (hr : r < NR) : tS NR ≠ rS NR r := (rS_ne_tS hr).symm
theorem sS_ne_rS_aux {NR r e : ℕ} (hr : r < NR) (he : e < 3) : sS NR e ≠ rS NR r :=
  (rS_ne_sS hr he).symm
theorem fS_ne_rS_aux {NR r : ℕ} (hr : r < NR) : fS NR ≠ rS NR r := (rS_ne_fS hr).symm

theorem exec_compile (NR : ℕ) : ∀ (p : FP) (d : ℕ), p.Ok NR d → ∀ (a : AS) (S : St (NR + 8)),
    SatD NR d a S →
    ∃ S' c, Exec (p.compile NR d) S S' c ∧ SatD NR d (p.run a) S' ∧
      (∀ e, e < d → e < 3 → S' (sS NR e) = S (sS NR e)) ∧ S' (fS NR) = S (fS NR) ∧
        c ≤ p.cost a := by
  intro p
  induction p with
  | skip =>
      intro d _ a S hS
      exact ⟨S, 1, Exec.skip S, hS, fun _ _ _ => rfl, rfl, le_rfl⟩
  | seq p q ihp ihq =>
      intro d hok a S hS
      obtain ⟨S₁, c₁, h₁, hS₁, hf₁, hk₁, hc₁⟩ := ihp d hok.1 a S hS
      obtain ⟨S₂, c₂, h₂, hS₂, hf₂, hk₂, hc₂⟩ := ihq d hok.2 (p.run a) S₁ hS₁
      exact ⟨S₂, c₁ + c₂, Exec.seq h₁ h₂, hS₂, fun e he he3 => (hf₂ e he he3).trans (hf₁ e he he3),
        hk₂.trans hk₁, by simp only [FP.cost]; omega⟩
  | emit bs =>
      intro d _ a S hS
      refine ⟨_, bs.length + 1, exec_pushes (oS NR) bs S, hS.upd_out bs, ?_, ?_, le_rfl⟩
      · intro e _ he3; rw [upd_ne _ _ (Ne.symm (oS_ne_sS he3))]
      · rw [upd_ne _ _ (Ne.symm oS_ne_fS)]
  | emitVar r o =>
      intro d hok a S hS
      have hr : r < NR := hok
      obtain ⟨c, hc, h⟩ := exec_emitVar (oS NR) (rS NR r) (tS NR) o (Ne.symm (rS_ne_oS hr))
        oS_ne_tS (rS_ne_tS hr) (a.reg r) S (hS.1 r hr) hS.2.2.1
      refine ⟨_, c, h, hS.upd_out ([false, false] ++ List.replicate (a.reg r + o) true ++ [false]),
        fun e _ he3 => (frame_out S _).1 e he3, (frame_out S _).2, ?_⟩
      simp only [FP.cost]; omega
  | addConst r k =>
      intro d hok a S hS
      have hr : r < NR := hok
      have h := exec_pushes (rS NR r) (List.replicate k true) S
      have e : (List.replicate k true).reverse ++ S (rS NR r) =
          List.replicate (a.reg r + k) true := by
        rw [hS.1 r hr, List.reverse_replicate, ← List.replicate_add, Nat.add_comm]
      rw [e] at h
      refine ⟨_, _, h, hS.upd_reg hr (a.reg r + k), fun e _ he3 => (frame_reg S hr _).1 e he3,
        (frame_reg S hr _).2, ?_⟩
      simp only [FP.cost, List.length_replicate]; omega
  | subConst r k =>
      intro d hok a S hS
      have hr : r < NR := hok
      have h := exec_pops (rS NR r) k S
      have e : (S (rS NR r)).drop k = List.replicate (a.reg r - k) true := by
        rw [hS.1 r hr, List.drop_replicate]
      rw [e] at h
      refine ⟨_, _, h, hS.upd_reg hr (a.reg r - k), fun e _ he3 => (frame_reg S hr _).1 e he3,
        (frame_reg S hr _).2, ?_⟩
      simp only [FP.cost]; omega
  | addReg r s =>
      intro d hok a S hS
      obtain ⟨hr, hs, hrs⟩ := hok
      obtain ⟨c, hc, h⟩ := exec_addReg (rS NR r) (rS NR s) (tS NR) (rS_ne_rS hr hs hrs)
        (rS_ne_tS hr) (rS_ne_tS hs) (a.reg s) S (hS.1 s hs) hS.2.2.1
      have e : List.replicate (a.reg s) true ++ S (rS NR r) =
          List.replicate (a.reg r + a.reg s) true := by
        rw [hS.1 r hr, ← List.replicate_add, Nat.add_comm]
      rw [e] at h
      refine ⟨_, c, h, hS.upd_reg hr (a.reg r + a.reg s), fun e _ he3 => (frame_reg S hr _).1 e he3,
        (frame_reg S hr _).2, ?_⟩
      simp only [FP.cost]; omega
  | subReg r s =>
      intro d hok a S hS
      obtain ⟨hr, hs, hrs⟩ := hok
      obtain ⟨c, hc, h⟩ := exec_subReg (rS NR r) (rS NR s) (tS NR) (rS_ne_rS hr hs hrs)
        (rS_ne_tS hr) (rS_ne_tS hs) (a.reg s) S (hS.1 s hs) hS.2.2.1
      have e : (S (rS NR r)).drop (a.reg s) = List.replicate (a.reg r - a.reg s) true := by
        rw [hS.1 r hr, List.drop_replicate]
      rw [e] at h
      refine ⟨_, c, h, hS.upd_reg hr (a.reg r - a.reg s), fun e _ he3 => (frame_reg S hr _).1 e he3,
        (frame_reg S hr _).2, ?_⟩
      simp only [FP.cost]; omega
  | clr r =>
      intro d hok a S hS
      have hr : r < NR := hok
      have h := exec_loop_clear (rS NR r) (S (rS NR r)) S rfl
      have e : (S (rS NR r)).length = a.reg r := by rw [hS.1 r hr]; simp
      rw [e] at h
      have h' : Exec ((FP.clr r).compile NR d) S (upd S (rS NR r) (List.replicate 0 true))
          (2 * a.reg r + 1) := by
        simpa [FP.compile] using h
      refine ⟨_, _, h', hS.upd_reg hr 0, fun e _ he3 => (frame_reg S hr _).1 e he3,
        (frame_reg S hr _).2, le_rfl⟩
  | forLoop cnt body ih =>
      intro d hok a S hS
      obtain ⟨hcnt, hd, hbOk⟩ := hok
      set m := a.reg cnt with hm
      have hSc : S (rS NR cnt) = List.replicate m true := hS.1 cnt hcnt
      have hSt : S (tS NR) = [] := hS.2.2.1
      have hSs : S (sS NR d) = [] := hS.2.2.2.1 d le_rfl hd
      have hrt := rS_ne_tS hcnt
      have hrs := rS_ne_sS hcnt hd
      have hts : tS NR ≠ sS NR d := tS_ne_sS hd
      -- copy phase
      let F : ℕ → St (NR + 8) := fun i =>
        upd (upd (upd S (rS NR cnt) (List.replicate (m - i) true)) (sS NR d)
          (List.replicate i true)) (tS NR) (List.replicate i true)
      have hF0 : F 0 = S := by
        funext j
        simp only [F, upd_apply]
        by_cases h1 : j = tS NR
        · subst h1; simp [hSt]
        · by_cases h2 : j = sS NR d
          · subst h2; simp [hSs, h1]
          · by_cases h3 : j = rS NR cnt
            · subst h3; simp [hSc, h1, h2]
            · simp [h1, h2, h3]
      obtain ⟨c₁, h₁, hc₁⟩ := exec_loop_count (rS NR cnt)
        (.seq (.push (sS NR d) true) (.push (tS NR) true)) m 2 F
        (by
          intro i _
          simp [F, upd_apply, hrt, hrs])
        (by
          intro i hi
          refine ⟨2, ?_, le_rfl⟩
          have e1 := Exec.push (upd (F i) (rS NR cnt) (List.replicate (m - i - 1) true))
            (sS NR d) true
          have e2 := Exec.push (upd (upd (F i) (rS NR cnt) (List.replicate (m - i - 1) true))
            (sS NR d) (true :: upd (F i) (rS NR cnt) (List.replicate (m - i - 1) true) (sS NR d)))
            (tS NR) true
          have := Exec.seq e1 e2
          convert this using 1
          funext j
          simp only [F, upd_apply]
          by_cases h1 : j = tS NR
          · subst h1; simp [hrt.symm, hts, List.replicate_succ]
          · by_cases h2 : j = sS NR d
            · subst h2; simp [hrs.symm, h1, List.replicate_succ]
            · by_cases h3 : j = rS NR cnt
              · subst h3; simp [h1, h2, show m - (i + 1) = m - i - 1 by omega]
              · simp [h1, h2, h3])
      rw [hF0] at h₁
      have hS₁t : F m (tS NR) = List.replicate m true := by simp [F, upd_apply]
      obtain ⟨c₂, hc₂, h₂⟩ := exec_pump (tS NR) (rS NR cnt) hrt.symm m (F m) hS₁t
      have hS₂ : upd (upd (F m) (tS NR) []) (rS NR cnt)
          (List.replicate m true ++ F m (rS NR cnt)) =
          upd S (sS NR d) (List.replicate m true) := by
        funext j
        by_cases h1 : j = rS NR cnt
        · subst h1
          simp [F, upd_apply, hrt, hrs, hSc]
        · by_cases h2 : j = tS NR
          · subst h2; simp [upd_apply, hSt, hrt.symm, hts]
          · by_cases h3 : j = sS NR d
            · subst h3; simp [F, upd_apply, hrs.symm, hts.symm]
            · simp [F, upd_apply, h1, h2, h3]
      rw [hS₂] at h₂
      have hSat : SatD NR (d + 1) a (upd S (sS NR d) (List.replicate m true)) :=
        hS.weaken.upd_sav (by omega) hd _
      obtain ⟨S₃, c₃, h₃, hS₃, hs₃, hf₃, hk₃, hc₃⟩ := exec_forLoop_main NR d hd
        (body.compile NR (d + 1)) body (fun a' S' hS' => ih (d + 1) hbOk a' S' hS') m a _ hSat
        (by simp [upd_self])
      refine ⟨S₃, c₁ + (c₂ + c₃), Exec.seq h₁ (Exec.seq h₂ h₃), ?_, ?_, ?_, ?_⟩
      · exact hS₃.of_succ hs₃
      · intro e he he3
        rw [hf₃ e he he3, upd_ne _ _ (sS_ne_sS he3 hd (by omega))]
      · rw [hk₃, upd_ne _ _ (sS_ne_fS hd).symm]
      · simp only [FP.cost]
        rw [← hm]
        omega  | forBits pf pt ihf iht =>
      intro d hok a S hS
      obtain ⟨hpf, hpt, hokf, hokt⟩ := hok
      exact exec_forBits NR d (pf.compile NR d) (pt.compile NR d) pf pt hpf hpt
        (ihf d hokf) (iht d hokt) a.bits.length a S hS rfl
  | countBits m =>
      intro d hok a S hS
      have hm : m < NR := hok
      have hrx : rS NR m ≠ xS NR := rS_ne_xS hm
      have hri : rS NR m ≠ iS NR := rS_ne_iS hm
      have hix : iS NR ≠ xS NR := iS_ne_xS
      have e1 := exec_loop_clear (rS NR m) (S (rS NR m)) S rfl
      have hl1 : (S (rS NR m)).length = a.reg m := by rw [hS.1 m hm]; simp
      rw [hl1] at e1
      set S₁ := upd S (rS NR m) [] with hS₁
      have hx₁ : S₁ (xS NR) = a.bits := by
        rw [hS₁, upd_ne _ _ hrx.symm]; exact hS.2.2.2.2.2
      have e2 := exec_loop_clear (xS NR) (S₁ (xS NR)) S₁ rfl
      rw [hx₁] at e2
      set S₂ := upd S₁ (xS NR) [] with hS₂
      have hi₂ : S₂ (iS NR) = a.inp := by
        rw [hS₂, upd_ne _ _ hix, hS₁, upd_ne _ _ hri.symm]
        exact hS.2.2.2.2.1
      let F : ℕ → St (NR + 8) := fun i =>
        upd (upd (upd S₂ (iS NR) (a.inp.drop i)) (xS NR) ((a.inp.take i).reverse))
          (rS NR m) (List.replicate i true)
      have hF0 : F 0 = S₂ := by
        funext j
        simp only [F, upd_apply]
        by_cases h1 : j = rS NR m
        · subst h1; simp [hS₂, hS₁, upd_apply, hrx, hrx.symm, hri, hri.symm]
        · by_cases h2 : j = xS NR
          · subst h2; simp [hS₂, upd_apply]
          · by_cases h3 : j = iS NR
            · subst h3; simp [hi₂, h1, h2]
            · simp [h1, h2, h3]
      obtain ⟨c₃, h₃, hc₃⟩ := exec_loop_list (iS NR)
        (.seq (.push (xS NR) false) (.push (rS NR m) true))
        (.seq (.push (xS NR) true) (.push (rS NR m) true)) a.inp 2 F
        (by
          intro i _
          simp only [F, upd_apply]
          simp [hri.symm, hix])
        (by
          intro i hi
          refine ⟨2, ?_, le_rfl⟩
          have htake : (a.inp.take (i + 1)).reverse = a.inp[i] :: (a.inp.take i).reverse := by
            rw [List.take_succ]
            simp [List.getElem?_eq_getElem hi]
          cases hb : a.inp[i] with
          | false =>
              simp only [Bool.false_eq_true, if_false]
              have e1' := Exec.push (upd (F i) (iS NR) (a.inp.drop (i + 1))) (xS NR) false
              have e2' := Exec.push (upd (upd (F i) (iS NR) (a.inp.drop (i + 1))) (xS NR)
                (false :: upd (F i) (iS NR) (a.inp.drop (i + 1)) (xS NR))) (rS NR m) true
              have := Exec.seq e1' e2'
              convert this using 1
              funext j
              simp only [F, upd_apply]
              by_cases h1 : j = rS NR m
              · subst h1; simp [List.replicate_succ, hrx, hrx.symm, hri, hri.symm]
              · by_cases h2 : j = xS NR
                · subst h2; simp [h1, htake, hb, hrx, hrx.symm, hix, hix.symm]
                · by_cases h3 : j = iS NR
                  · subst h3; simp [h1, h2, hix, hix.symm, hri, hri.symm]
                  · simp [h1, h2, h3]
          | true =>
              simp only [if_true]
              have e1' := Exec.push (upd (F i) (iS NR) (a.inp.drop (i + 1))) (xS NR) true
              have e2' := Exec.push (upd (upd (F i) (iS NR) (a.inp.drop (i + 1))) (xS NR)
                (true :: upd (F i) (iS NR) (a.inp.drop (i + 1)) (xS NR))) (rS NR m) true
              have := Exec.seq e1' e2'
              convert this using 1
              funext j
              simp only [F, upd_apply]
              by_cases h1 : j = rS NR m
              · subst h1; simp [List.replicate_succ, hrx, hrx.symm, hri, hri.symm]
              · by_cases h2 : j = xS NR
                · subst h2; simp [h1, htake, hb, hrx, hrx.symm, hix, hix.symm]
                · by_cases h3 : j = iS NR
                  · subst h3; simp [h1, h2, hix, hix.symm, hri, hri.symm]
                  · simp [h1, h2, h3])
      rw [hF0] at h₃
      have key : ∀ j, j ≠ rS NR m → j ≠ iS NR → j ≠ xS NR → F a.inp.length j = S j := by
        intro j h1 h2 h3
        simp [F, hS₂, hS₁, upd_apply, h1, h2, h3]
      have hFr : F a.inp.length (rS NR m) = List.replicate a.inp.length true := by
        simp [F, upd_apply]
      have hFi : F a.inp.length (iS NR) = [] := by
        simp [F, upd_apply, hri.symm, hix]
      have hFx : F a.inp.length (xS NR) = a.inp.reverse := by
        simp [F, upd_apply, hrx.symm]
      refine ⟨F a.inp.length, _, Exec.seq e1 (Exec.seq e2 h₃), ?_, ?_, ?_, ?_⟩
      · obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hS
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro r hr
          by_cases hrm : r = m
          · subst hrm; simp [FP.run, hFr]
          · have hne := rS_ne_rS hr hm hrm
            rw [key _ hne (rS_ne_iS hr) (rS_ne_xS hr)]
            simp [FP.run, Function.update_of_ne hrm, g1 r hr]
        · rw [key _ (oS_ne_rS_aux hm) oS_ne_iS oS_ne_xS]
          simp [FP.run, g2]
        · rw [key _ (tS_ne_rS_aux hm) tS_ne_iS tS_ne_xS]
          simp [FP.run, g3]
        · intro e he1 he2
          rw [key _ (sS_ne_rS_aux hm he2) (sS_ne_iS he2) (sS_ne_xS he2)]
          exact g4 e (by omega) he2
        · simp [FP.run, hFi]
        · simp [FP.run, hFx]
      · intro e he he3
        exact key _ (sS_ne_rS_aux hm he3) (sS_ne_iS he3) (sS_ne_xS he3)
      · exact key _ (fS_ne_rS_aux hm) iS_ne_fS.symm xS_ne_fS.symm
      · simp only [FP.cost]; omega

end SP
end SATurday.Bridge
