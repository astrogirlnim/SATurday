import Theory.ProofComplexity.Bridge.Complexity

/-!
# Structured stack programs compiled to `FinTM2` (Ladder Rung R5, Cook Levin tooling)

A tiny structured language over `n` Boolean stacks with one cost per executed
instruction, a flat assembly it compiles to, and (later in this file) the
compilation to a `FinTM2` with a proved cost bound. Programs are verified at
the level of the big step relation `Exec`, which is far cheaper than hand
building a `FinTM2` phase by phase.

LOG: R5 Bridge StackProg module (structured Bool stack programs, assembly, Exec)
-/

open Turing

namespace SATurday.Bridge
namespace SP

/-- A state: `n` Boolean stacks (head of the list is the top). -/
abbrev St (n : ℕ) := Fin n → List Bool

/-- Flat assembly. Every instruction costs one step. -/
inductive Instr (n : ℕ) : Type
  | push (k : Fin n) (b : Bool) (nx : ℕ)
  | pop3 (k : Fin n) (e f t : ℕ)
  | jmp (nx : ℕ)
  | halt
deriving DecidableEq

/-- Structured programs. -/
inductive Prog (n : ℕ) : Type
  | skip
  | push (k : Fin n) (b : Bool)
  /-- pop `k`; run the first branch if it was empty, then the `false` and `true` branches. -/
  | pop3 (k : Fin n) (pe pf pt : Prog n)
  | seq (p q : Prog n)
  /-- repeatedly pop `k`, running `pf` / `pt`, until the stack is empty. -/
  | loop (k : Fin n) (pf pt : Prog n)

variable {n : ℕ}

/-- Number of assembly instructions. -/
def Prog.size : Prog n → ℕ
  | .skip => 1
  | .push _ _ => 1
  | .pop3 _ pe pf pt => 1 + pe.size + pf.size + pt.size
  | .seq p q => p.size + q.size
  | .loop _ pf pt => 1 + pf.size + pt.size

theorem Prog.size_pos (p : Prog n) : 0 < p.size := by
  induction p <;> simp [Prog.size] <;> omega

/-- Code placed at `s` that falls through to `e`. -/
def Prog.code : Prog n → ℕ → ℕ → List (Instr n)
  | .skip, _, e => [.jmp e]
  | .push k b, _, e => [.push k b e]
  | .pop3 k pe pf pt, s, e =>
      .pop3 k (s + 1) (s + 1 + pe.size) (s + 1 + pe.size + pf.size) ::
        (pe.code (s + 1) e ++ pf.code (s + 1 + pe.size) e ++
          pt.code (s + 1 + pe.size + pf.size) e)
  | .seq p q, s, e => p.code s (s + p.size) ++ q.code (s + p.size) e
  | .loop k pf pt, s, e =>
      .pop3 k e (s + 1) (s + 1 + pf.size) ::
        (pf.code (s + 1) s ++ pt.code (s + 1 + pf.size) s)

theorem Prog.length_code (p : Prog n) (s e : ℕ) : (p.code s e).length = p.size := by
  induction p generalizing s e with
  | skip => simp [Prog.code, Prog.size]
  | push => simp [Prog.code, Prog.size]
  | pop3 k pe pf pt ihe ihf iht =>
      simp [Prog.code, Prog.size, ihe, ihf, iht]; omega
  | seq p q ihp ihq => simp [Prog.code, Prog.size, ihp, ihq]
  | loop k pf pt ihf iht =>
      simp [Prog.code, Prog.size, ihf, iht]; omega

/-- Replace the content of one stack. -/
def upd (S : St n) (k : Fin n) (l : List Bool) : St n := Function.update S k l

/-- Big step semantics with the instruction count. -/
inductive Exec : Prog n → St n → St n → ℕ → Prop
  | skip (S) : Exec .skip S S 1
  | push (S k b) : Exec (.push k b) S (upd S k (b :: S k)) 1
  | pop_nil {S S' k pe pf pt c} : S k = [] → Exec pe S S' c →
      Exec (.pop3 k pe pf pt) S S' (c + 1)
  | pop_false {S S' k pe pf pt c r} : S k = false :: r →
      Exec pf (upd S k r) S' c → Exec (.pop3 k pe pf pt) S S' (c + 1)
  | pop_true {S S' k pe pf pt c r} : S k = true :: r →
      Exec pt (upd S k r) S' c → Exec (.pop3 k pe pf pt) S S' (c + 1)
  | seq {p q S S₁ S₂ c₁ c₂} : Exec p S S₁ c₁ → Exec q S₁ S₂ c₂ →
      Exec (.seq p q) S S₂ (c₁ + c₂)
  | loop_nil {S k pf pt} : S k = [] → Exec (.loop k pf pt) S S 1
  | loop_false {S S₁ S₂ k pf pt c₁ c₂ r} : S k = false :: r →
      Exec pf (upd S k r) S₁ c₁ → Exec (.loop k pf pt) S₁ S₂ c₂ →
      Exec (.loop k pf pt) S S₂ (c₁ + c₂ + 1)
  | loop_true {S S₁ S₂ k pf pt c₁ c₂ r} : S k = true :: r →
      Exec pt (upd S k r) S₁ c₁ → Exec (.loop k pf pt) S₁ S₂ c₂ →
      Exec (.loop k pf pt) S S₂ (c₁ + c₂ + 1)

/-! ## Assembly semantics -/

/-- Placement of a block of instructions at an absolute address. -/
def Placed (code : ℕ → Option (Instr n)) (l : List (Instr n)) (s : ℕ) : Prop :=
  ∀ j (h : j < l.length), code (s + j) = some (l[j])

theorem Placed.append_left {code : ℕ → Option (Instr n)} {l₁ l₂ : List (Instr n)} {s : ℕ}
    (h : Placed code (l₁ ++ l₂) s) : Placed code l₁ s := by
  intro j hj
  have := h j (by simp; omega)
  simpa [List.getElem_append_left hj] using this

theorem Placed.append_right {code : ℕ → Option (Instr n)} {l₁ l₂ : List (Instr n)} {s : ℕ}
    (h : Placed code (l₁ ++ l₂) s) : Placed code l₂ (s + l₁.length) := by
  intro j hj
  have := h (l₁.length + j) (by simp; omega)
  rw [← Nat.add_assoc] at this
  simpa [List.getElem_append_right (by omega : l₁.length ≤ l₁.length + j)] using this

theorem Placed.head {code : ℕ → Option (Instr n)} {i : Instr n} {l : List (Instr n)} {s : ℕ}
    (h : Placed code (i :: l) s) : code s = some i := by
  simpa using h 0 (by simp)

theorem Placed.tail {code : ℕ → Option (Instr n)} {i : Instr n} {l : List (Instr n)} {s : ℕ}
    (h : Placed code (i :: l) s) : Placed code l (s + 1) := by
  intro j hj
  have := h (j + 1) (by simp; omega)
  simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

/-- One instruction step. -/
inductive Step (code : ℕ → Option (Instr n)) : ℕ × St n → ℕ × St n → Prop
  | push {pc S k b nx} : code pc = some (.push k b nx) →
      Step code (pc, S) (nx, upd S k (b :: S k))
  | pop_nil {pc S k e f t} : code pc = some (.pop3 k e f t) → S k = [] →
      Step code (pc, S) (e, S)
  | pop_false {pc S k e f t r} : code pc = some (.pop3 k e f t) → S k = false :: r →
      Step code (pc, S) (f, upd S k r)
  | pop_true {pc S k e f t r} : code pc = some (.pop3 k e f t) → S k = true :: r →
      Step code (pc, S) (t, upd S k r)
  | jmp {pc S nx} : code pc = some (.jmp nx) → Step code (pc, S) (nx, S)

/-- `c` instruction steps. -/
inductive Steps (code : ℕ → Option (Instr n)) : ℕ → ℕ × St n → ℕ × St n → Prop
  | refl (a) : Steps code 0 a a
  | cons {c a b d} : Step code a b → Steps code c b d → Steps code (c + 1) a d

theorem Steps.trans {code : ℕ → Option (Instr n)} {c₁ c₂ : ℕ} {a b d : ℕ × St n}
    (h₁ : Steps code c₁ a b) (h₂ : Steps code c₂ b d) : Steps code (c₁ + c₂) a d := by
  induction h₁ with
  | refl => simpa using h₂
  | cons hs _ ih =>
      have := Steps.cons hs (ih h₂)
      convert this using 1; omega

theorem Steps.single {code : ℕ → Option (Instr n)} {a b : ℕ × St n}
    (h : Step code a b) : Steps code 1 a b :=
  Steps.cons h (Steps.refl _)

/-- Compilation is correct for the big step semantics. -/
theorem exec_steps {code : ℕ → Option (Instr n)} {p : Prog n} {S S' : St n} {c : ℕ}
    (h : Exec p S S' c) :
    ∀ s e, Placed code (p.code s e) s → Steps code c (s, S) (e, S') := by
  induction h with
  | skip S =>
      intro s e hp
      exact Steps.single (Step.jmp hp.head)
  | push S k b =>
      intro s e hp
      exact Steps.single (Step.push hp.head)
  | @pop_nil S S' k pe pf pt c hk _ ih =>
      intro s e hp
      have hh := hp.head
      have hrest := hp.tail
      have h1 := hrest.append_left.append_left
      have := ih (s + 1) e h1
      exact Steps.cons (Step.pop_nil hh hk) this
  | @pop_false S S' k pe pf pt c r hk _ ih =>
      intro s e hp
      have hh := hp.head
      have hrest := hp.tail
      have h2 := hrest.append_left.append_right
      rw [Prog.length_code] at h2
      have := ih (s + 1 + pe.size) e (by simpa [Nat.add_assoc] using h2)
      exact Steps.cons (Step.pop_false hh hk) this
  | @pop_true S S' k pe pf pt c r hk _ ih =>
      intro s e hp
      have hh := hp.head
      have hrest := hp.tail
      have h3 := hrest.append_right
      rw [List.length_append, Prog.length_code, Prog.length_code] at h3
      have := ih (s + 1 + pe.size + pf.size) e (by simpa [Nat.add_assoc] using h3)
      exact Steps.cons (Step.pop_true hh hk) this
  | @seq p q S S₁ S₂ c₁ c₂ _ _ ih₁ ih₂ =>
      intro s e hp
      have h1 := hp.append_left
      have h2 := hp.append_right
      rw [Prog.length_code] at h2
      exact (ih₁ s (s + p.size) h1).trans (ih₂ (s + p.size) e h2)
  | @loop_nil S k pf pt hk =>
      intro s e hp
      exact Steps.single (Step.pop_nil hp.head hk)
  | @loop_false S S₁ S₂ k pf pt c₁ c₂ r hk _ _ ih₁ ih₂ =>
      intro s e hp
      have hh := hp.head
      have hrest := hp.tail
      have h1 := hrest.append_left
      have := ih₁ (s + 1) s h1
      have := (Steps.cons (Step.pop_false hh hk) this).trans (ih₂ s e hp)
      convert this using 1; omega
  | @loop_true S S₁ S₂ k pf pt c₁ c₂ r hk _ _ ih₁ ih₂ =>
      intro s e hp
      have hh := hp.head
      have hrest := hp.tail
      have h2 := hrest.append_right
      rw [Prog.length_code] at h2
      have := ih₁ (s + 1 + pf.size) s (by simpa [Nat.add_assoc] using h2)
      have := (Steps.cons (Step.pop_true hh hk) this).trans (ih₂ s e hp)
      convert this using 1; omega

/-! ## The `FinTM2` of an assembly listing -/

/-- Assembly as a total function on addresses. -/
def asm (code : List (Instr n)) : ℕ → Option (Instr n) := fun pc => code[pc]?

/-- Clamped label: addresses past the end are the halt address. -/
def lab (code : List (Instr n)) (nx : ℕ) : Fin (code.length + 1) :=
  ⟨min nx code.length, by omega⟩

theorem lab_val_of_le (code : List (Instr n)) {nx : ℕ} (h : nx ≤ code.length) :
    (lab code nx).val = nx := by
  simp [lab, Nat.min_eq_left h]

/-- The statement run at an address. -/
def stmtOf (code : List (Instr n)) (pc : Fin (code.length + 1)) :
    TM2.Stmt (fun _ : Fin n => Bool) (Fin (code.length + 1)) (Option Bool) :=
  match code[pc.val]? with
  | some (.push k b nx) => .push k (fun _ => b) (.goto fun _ => lab code nx)
  | some (.pop3 k e f t) =>
      .pop k (fun _ o => o)
        (.goto fun o => match o with
          | none => lab code e
          | some false => lab code f
          | some true => lab code t)
  | some (.jmp nx) => .goto fun _ => lab code nx
  | _ => .load (fun _ => none) .halt

/-- The machine: `n` Boolean stacks, one label per instruction plus a halt label. -/
def mkTM (k₀ k₁ : Fin n) (code : List (Instr n)) : FinTM2 where
  K := Fin n
  k₀ := k₀
  k₁ := k₁
  Γ := fun _ => Bool
  Λ := Fin (code.length + 1)
  main := 0
  σ := Option Bool
  initialState := none
  m := stmtOf code

/-- Configuration at an address. -/
def cfgAt (k₀ k₁ : Fin n) (code : List (Instr n)) (pc : ℕ) (v : Option Bool) (S : St n) :
    (mkTM k₀ k₁ code).Cfg :=
  ⟨some (lab code pc), v, S⟩

theorem Step.code_some {code : ℕ → Option (Instr n)} {a b : ℕ × St n}
    (h : Step code a b) : ∃ i, code a.1 = some i := by
  cases h with
  | push hc => exact ⟨_, hc⟩
  | pop_nil hc _ => exact ⟨_, hc⟩
  | pop_false hc _ => exact ⟨_, hc⟩
  | pop_true hc _ => exact ⟨_, hc⟩
  | jmp hc => exact ⟨_, hc⟩

theorem Steps.start_le {code : List (Instr n)} {c : ℕ} {b d : ℕ × St n}
    (h : Steps (asm code) c b d) (hd : d.1 ≤ code.length) : b.1 ≤ code.length := by
  cases h with
  | refl => exact hd
  | cons hs _ =>
      obtain ⟨i, hi⟩ := hs.code_some
      have : b.1 < code.length := by
        simp only [asm] at hi
        exact (List.getElem?_eq_some_iff.1 hi).1
      omega

theorem step_cfg {k₀ k₁ : Fin n} {code : List (Instr n)} {a b : ℕ × St n}
    (h : Step (asm code) a b) (hb : b.1 ≤ code.length) (v : Option Bool) :
    ∃ v', (mkTM k₀ k₁ code).step (cfgAt k₀ k₁ code a.1 v a.2) =
      some (cfgAt k₀ k₁ code b.1 v' b.2) := by
  cases h with
  | @push pc S k bb nx hc =>
      have hpc : pc < code.length := (List.getElem?_eq_some_iff.1 hc).1
      simp only [asm] at hc
      refine ⟨v, ?_⟩
      simp [cfgAt, FinTM2.step, TM2.step, mkTM, stmtOf, lab_val_of_le code hpc.le, hc,
        TM2.stepAux, upd]
      rfl
  | @pop_nil pc S k e f t hc hk =>
      have hpc : pc < code.length := (List.getElem?_eq_some_iff.1 hc).1
      simp only [asm] at hc
      refine ⟨none, ?_⟩
      have hU : Function.update S k [] = S := by
        funext j
        by_cases h : j = k
        · subst h; simp [hk]
        · simp [Function.update_of_ne h]
      simp [cfgAt, FinTM2.step, TM2.step, mkTM, stmtOf, lab_val_of_le code hpc.le, hc,
        TM2.stepAux, hk]
      exact congrArg (fun T : St n =>
        (some ⟨some (lab code e), none, T⟩ : Option (mkTM k₀ k₁ code).Cfg)) hU
  | @pop_false pc S k e f t r hc hk =>
      have hpc : pc < code.length := (List.getElem?_eq_some_iff.1 hc).1
      simp only [asm] at hc
      refine ⟨some false, ?_⟩
      simp [cfgAt, FinTM2.step, TM2.step, mkTM, stmtOf, lab_val_of_le code hpc.le, hc,
        TM2.stepAux, hk, upd]
      rfl
  | @pop_true pc S k e f t r hc hk =>
      have hpc : pc < code.length := (List.getElem?_eq_some_iff.1 hc).1
      simp only [asm] at hc
      refine ⟨some true, ?_⟩
      simp [cfgAt, FinTM2.step, TM2.step, mkTM, stmtOf, lab_val_of_le code hpc.le, hc,
        TM2.stepAux, hk, upd]
      rfl
  | @jmp pc S nx hc =>
      have hpc : pc < code.length := (List.getElem?_eq_some_iff.1 hc).1
      simp only [asm] at hc
      refine ⟨v, ?_⟩
      simp [cfgAt, FinTM2.step, TM2.step, mkTM, stmtOf, lab_val_of_le code hpc.le, hc,
        TM2.stepAux]
      rfl

/-- Several steps. -/
theorem steps_cfg {k₀ k₁ : Fin n} {code : List (Instr n)} {c : ℕ} {a d : ℕ × St n}
    (h : Steps (asm code) c a d) (hd : d.1 ≤ code.length) (v : Option Bool) :
    ∃ v', (flip bind (mkTM k₀ k₁ code).step)^[c]
        (some (cfgAt k₀ k₁ code a.1 v a.2)) =
      some (cfgAt k₀ k₁ code d.1 v' d.2) := by
  induction h generalizing v with
  | refl a => exact ⟨v, rfl⟩
  | @cons c a b d hs ht ih =>
      have hb : b.1 ≤ code.length := ht.start_le hd
      obtain ⟨v₁, h₁⟩ := step_cfg (k₀ := k₀) (k₁ := k₁) hs hb v
      obtain ⟨v₂, h₂⟩ := ih hd v₁
      refine ⟨v₂, ?_⟩
      rw [Function.iterate_succ_apply]
      have h₁' : (flip bind (mkTM k₀ k₁ code).step)
          (some (cfgAt k₀ k₁ code a.1 v a.2)) =
          some (cfgAt k₀ k₁ code b.1 v₁ b.2) := h₁
      rw [h₁']
      exact h₂

/-! ## Cleanup: empty every stack except the output -/

theorem exec_loop_clear (k : Fin n) :
    ∀ (l : List Bool) (S : St n), S k = l →
      Exec (.loop k .skip .skip) S (upd S k []) (2 * l.length + 1) := by
  intro l
  induction l with
  | nil =>
      intro S hk
      have hU : upd S k [] = S := by
        funext j
        by_cases h : j = k
        · subst h; simp [upd, hk]
        · simp [upd, Function.update_of_ne h]
      rw [hU]
      exact Exec.loop_nil hk
  | cons b r ih =>
      intro S hk
      have hrest := ih (upd S k r) (by simp [upd])
      have hU : upd (upd S k r) k [] = upd S k [] := by
        funext j; simp [upd]
      rw [hU] at hrest
      cases b with
      | false =>
          have := Exec.loop_false (k := k) (pf := .skip) (pt := .skip) hk
            (Exec.skip (upd S k r)) hrest
          rw [List.length_cons]
          convert this using 1; omega
      | true =>
          have := Exec.loop_true (k := k) (pf := .skip) (pt := .skip) hk
            (Exec.skip (upd S k r)) hrest
          rw [List.length_cons]
          convert this using 1; omega

/-- Empty the listed stacks other than `k₁`. -/
def drainList (k₁ : Fin n) : List (Fin n) → Prog n
  | [] => .skip
  | j :: l => if j = k₁ then drainList k₁ l else .seq (.loop j .skip .skip) (drainList k₁ l)

theorem exec_drainList (k₁ : Fin n) :
    ∀ (l : List (Fin n)), l.Nodup → ∀ S : St n, ∃ c,
      c ≤ 2 * (l.map fun j => (S j).length).sum + l.length + 1 ∧
      Exec (drainList k₁ l) S (fun i => if i ∈ l ∧ i ≠ k₁ then [] else S i) c := by
  intro l
  induction l with
  | nil =>
      intro _ S
      refine ⟨1, by simp, ?_⟩
      simpa [drainList] using Exec.skip S
  | cons j l ih =>
      intro hnd S
      have hjl : j ∉ l := (List.nodup_cons.1 hnd).1
      have hl : l.Nodup := (List.nodup_cons.1 hnd).2
      by_cases hj : j = k₁
      · subst hj
        obtain ⟨c, hc, he⟩ := ih hl S
        refine ⟨c, by simp at *; omega, ?_⟩
        have : (fun i => if i ∈ j :: l ∧ i ≠ j then [] else S i) =
            (fun i => if i ∈ l ∧ i ≠ j then [] else S i) := by
          funext i; by_cases h : i = j <;> simp [h]
        rw [this]
        simpa [drainList] using he
      · obtain ⟨c, hc, he⟩ := ih hl (upd S j [])
        have h1 := exec_loop_clear j (S j) S rfl
        have hsum : (l.map fun i => ((upd S j []) i).length) =
            (l.map fun i => (S i).length) := by
          apply List.map_congr_left
          intro i hi
          have : i ≠ j := fun h => hjl (h ▸ hi)
          simp [upd, Function.update_of_ne this]
        rw [hsum] at hc
        refine ⟨(2 * (S j).length + 1) + c, ?_, ?_⟩
        · simp only [List.map_cons, List.sum_cons, List.length_cons]; omega
        · have hex := Exec.seq h1 he
          have : (fun i => if i ∈ j :: l ∧ i ≠ k₁ then [] else S i) =
              (fun i => if i ∈ l ∧ i ≠ k₁ then [] else (upd S j []) i) := by
            funext i
            by_cases hij : i = j
            · subst hij; simp [upd, hj]
            · simp [upd, Function.update_of_ne hij, hij]
          rw [this]
          simpa [drainList, hj] using hex

/-- Empty every stack except `k₁`. -/
def drainAll (k₁ : Fin n) : Prog n := drainList k₁ (List.finRange n)

theorem exec_drainAll (k₁ : Fin n) (S : St n) : ∃ c,
    c ≤ 2 * ((List.finRange n).map fun j => (S j).length).sum + n + 1 ∧
    Exec (drainAll k₁) S (fun i => if i ≠ k₁ then [] else S i) c := by
  obtain ⟨c, hc, he⟩ := exec_drainList k₁ (List.finRange n) (List.nodup_finRange n) S
  refine ⟨c, by simpa using hc, ?_⟩
  have : (fun i => if i ∈ List.finRange n ∧ i ≠ k₁ then [] else S i) =
      (fun i => if i ≠ k₁ then [] else S i) := by
    funext i; simp
  rw [this] at he
  exact he

/-! ## The machine of a program -/

/-- Program followed by cleanup. -/
def fullProg (P : Prog n) (k₁ : Fin n) : Prog n := .seq P (drainAll k₁)

/-- Assembly of a program: body, cleanup, halt. -/
def fullCode (P : Prog n) (k₁ : Fin n) : List (Instr n) :=
  (fullProg P k₁).code 0 (fullProg P k₁).size ++ [Instr.halt]

/-- The machine computing with program `P` (input on `k₀`, output on `k₁`). -/
def progTM (k₀ k₁ : Fin n) (P : Prog n) : FinTM2 :=
  mkTM k₀ k₁ (fullCode P k₁)

/-- Initial stacks: the input on `k₀`. -/
def initSt (k₀ : Fin n) (s : List Bool) : St n := fun k => if k = k₀ then s else []

theorem fullCode_length (P : Prog n) (k₁ : Fin n) :
    (fullCode P k₁).length = (fullProg P k₁).size + 1 := by
  simp [fullCode, Prog.length_code]

theorem placed_fullCode (P : Prog n) (k₁ : Fin n) :
    Placed (asm (fullCode P k₁)) ((fullProg P k₁).code 0 (fullProg P k₁).size) 0 := by
  intro j hj
  simp only [asm, fullCode, zero_add]
  rw [List.getElem?_append_left hj]
  simp

theorem placed_halt (P : Prog n) (k₁ : Fin n) :
    asm (fullCode P k₁) (fullProg P k₁).size = some Instr.halt := by
  simp only [asm, fullCode]
  rw [List.getElem?_append_right (by rw [Prog.length_code])]
  simp [Prog.length_code]

theorem initList_progTM (k₀ k₁ : Fin n) (P : Prog n) (s : List Bool) :
    initList (progTM k₀ k₁ P) s =
      cfgAt k₀ k₁ (fullCode P k₁) 0 none (initSt k₀ s) := by
  have hl : (0 : Fin ((fullCode P k₁).length + 1)) = lab (fullCode P k₁) 0 :=
    Fin.ext (by simp [lab])
  simp only [initList, cfgAt, progTM, mkTM]
  congr 1

theorem haltList_progTM (k₀ k₁ : Fin n) (P : Prog n) (S' : St n) :
    haltList (progTM k₀ k₁ P) (S' k₁) =
      ⟨none, none, fun i => if i ≠ k₁ then [] else S' i⟩ := by
  simp only [haltList, progTM, mkTM]
  congr 1
  funext k
  by_cases h : k = k₁
  · subst h; simp
  · simp [h]

/-- Main compilation theorem: an `Exec` derivation gives a certified machine run. -/
theorem progTM_outputs (k₀ k₁ : Fin n) (P : Prog n) (s : List Bool) (S' : St n) (c : ℕ)
    (h : Exec P (initSt k₀ s) S' c) :
    Nonempty (TM2OutputsInTime (progTM k₀ k₁ P) s (some (S' k₁))
      (c + 2 * ((List.finRange n).map fun j => (S' j).length).sum + n + 2)) := by
  obtain ⟨cd, hcd, hd⟩ := exec_drainAll k₁ S'
  have hfull : Exec (fullProg P k₁) (initSt k₀ s) (fun i => if i ≠ k₁ then [] else S' i)
      (c + cd) := Exec.seq h hd
  have hsteps := exec_steps (code := asm (fullCode P k₁)) hfull 0 (fullProg P k₁).size
    (placed_fullCode P k₁)
  have hle : (fullProg P k₁).size ≤ (fullCode P k₁).length := by
    rw [fullCode_length]; omega
  obtain ⟨v', hv'⟩ := steps_cfg (k₀ := k₀) (k₁ := k₁) hsteps hle none
  -- the final halt step
  have hlab : (lab (fullCode P k₁) (fullProg P k₁).size).val = (fullProg P k₁).size :=
    lab_val_of_le _ hle
  have hhalt : (mkTM k₀ k₁ (fullCode P k₁)).step
      (cfgAt k₀ k₁ (fullCode P k₁) (fullProg P k₁).size v'
        (fun i => if i ≠ k₁ then [] else S' i)) =
      some ⟨none, none, fun i => if i ≠ k₁ then [] else S' i⟩ := by
    have hc := placed_halt P k₁
    simp only [asm] at hc
    simp [cfgAt, FinTM2.step, TM2.step, mkTM, stmtOf, hlab, hc, TM2.stepAux]
    rfl
  refine ⟨⟨⟨c + cd + 1, ?_⟩, ?_⟩⟩
  · rw [Function.iterate_succ_apply', initList_progTM]
    have : (flip bind (progTM k₀ k₁ P).step)^[c + cd]
        (some (cfgAt k₀ k₁ (fullCode P k₁) 0 none (initSt k₀ s))) =
        some (cfgAt k₀ k₁ (fullCode P k₁) (fullProg P k₁).size v'
          (fun i => if i ≠ k₁ then [] else S' i)) := hv'
    rw [this]
    simp only [Option.map_some, haltList_progTM]
    exact hhalt
  · simp only [List.map_cons] at *
    omega

/-! ## Cost bounds: total stack size -/

/-- Total number of cells over all stacks. -/
def total (S : St n) : ℕ := ∑ i, (S i).length

theorem total_upd (S : St n) (k : Fin n) (l : List Bool) :
    total (upd S k l) + (S k).length = total S + l.length := by
  unfold total upd
  have h : ∀ j, (Function.update S k l j).length =
      Function.update (fun j => (S j).length) k l.length j := by
    intro j
    by_cases hj : j = k
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  rw [Finset.sum_update_of_mem (Finset.mem_univ k)]
  have := Finset.add_sum_erase Finset.univ (fun j => (S j).length) (Finset.mem_univ k)
  have h2 : (Finset.univ \ {k}) = Finset.univ.erase k := by
    ext x; simp
  rw [h2]
  beta_reduce at this ⊢
  omega

theorem exec_total_le {P : Prog n} {S S' : St n} {c : ℕ} (h : Exec P S S' c) :
    total S' ≤ total S + c := by
  induction h with
  | skip S => omega
  | push S k b =>
      have := total_upd S k (b :: S k); simp at this; omega
  | @pop_nil S S' k pe pf pt c hk _ ih => omega
  | @pop_false S S' k pe pf pt c r hk _ ih =>
      have := total_upd S k r; rw [hk] at this; simp at this; omega
  | @pop_true S S' k pe pf pt c r hk _ ih =>
      have := total_upd S k r; rw [hk] at this; simp at this; omega
  | seq _ _ ih₁ ih₂ => omega
  | loop_nil _ => omega
  | @loop_false S S₁ S₂ k pf pt c₁ c₂ r hk _ _ ih₁ ih₂ =>
      have := total_upd S k r; rw [hk] at this; simp at this; omega
  | @loop_true S S₁ S₂ k pf pt c₁ c₂ r hk _ _ ih₁ ih₂ =>
      have := total_upd S k r; rw [hk] at this; simp at this; omega

theorem total_initSt (k₀ : Fin n) (s : List Bool) : total (initSt k₀ s) = s.length := by
  unfold total initSt
  rw [Finset.sum_eq_single k₀]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## From programs to `TM2ComputableInPolyTime` -/

/-- Program `P` computes `f` within `T` instructions. -/
structure Computes (k₀ k₁ : Fin n) (P : Prog n) (f : List Bool → List Bool)
    (T : Polynomial ℕ) : Prop where
  run : ∀ s, ∃ S' c, Exec P (initSt k₀ s) S' c ∧ S' k₁ = f s ∧ c ≤ T.eval s.length

def TM2OutputsInTime.mono' {tm : FinTM2} {l : List (tm.Γ tm.k₀)}
    {l' : Option (List (tm.Γ tm.k₁))} {m m' : ℕ} (h : TM2OutputsInTime tm l l' m)
    (hm : m ≤ m') : TM2OutputsInTime tm l l' m' :=
  ⟨h.toEvalsTo, le_trans h.steps_le_m hm⟩

def TM2OutputsInTime.congr' {tm : FinTM2} {l₁ l₂ : List (tm.Γ tm.k₀)}
    {o₁ o₂ : Option (List (tm.Γ tm.k₁))} {m : ℕ} (h : TM2OutputsInTime tm l₁ o₁ m)
    (e1 : l₁ = l₂) (e2 : o₁ = o₂) : TM2OutputsInTime tm l₂ o₂ m := by
  subst e1; subst e2; exact h

/-- Time polynomial of the compiled machine. -/
noncomputable def timeOf (n : ℕ) (T : Polynomial ℕ) : Polynomial ℕ :=
  3 * T + 2 * Polynomial.X + Polynomial.C (n + 2)

noncomputable def Computes.toPoly {k₀ k₁ : Fin n} {P : Prog n} {f : List Bool → List Bool}
    {T : Polynomial ℕ} (h : Computes k₀ k₁ P f T) :
    TM2ComputableInPolyTime idBitEnc idBitEnc f where
  tm := progTM k₀ k₁ P
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timeOf n T
  outputsFun s := by
    have hne : Nonempty (TM2OutputsInTime (progTM k₀ k₁ P) s (some (f s))
        ((timeOf n T).eval s.length)) := by
      obtain ⟨S', c, hex, hout, hc⟩ := h.run s
      obtain ⟨o⟩ := progTM_outputs k₀ k₁ P s S' c hex
      rw [hout] at o
      refine ⟨TM2OutputsInTime.mono' o ?_⟩
      have h1 := exec_total_le hex
      rw [total_initSt] at h1
      have h2 : ((List.finRange n).map fun j => (S' j).length).sum = total S' := by
        unfold total; rw [Fin.sum_univ_def]
      rw [h2]
      simp only [timeOf, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.eval_ofNat]
      omega
    have o := Classical.choice hne
    have e : ∀ l : List Bool, l = List.map (⇑(Equiv.refl Bool).symm) l := by
      intro l
      induction l with
      | nil => rfl
      | cons a t ih => exact congrArg (List.cons a) ih
    exact TM2OutputsInTime.congr' o (e s) (congrArg some (e (f s)))

end SP
end SATurday.Bridge
