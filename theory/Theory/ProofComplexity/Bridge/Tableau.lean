import Theory.ProofComplexity.Bridge.FormulaEncoding
import Theory.ProofComplexity.Bridge.Encoding
import Mathlib.Tactic

/-!
# Cook Levin tableau (Ladder Rung R5, hard direction), semantic layer

Formula templates with relative variable leaves (`TF`), the coded machine `CM`,
its finite array step, and the tableau constraint families. The satisfiability
equivalence with an accepting run is proved here; the generator that emits the
bit string lives elsewhere.

LOG: R5 Bridge Tableau module (TF templates, CM, array step)
-/

namespace SATurday.Bridge
namespace CL

/-! ## Formula templates -/

/-- A formula whose variables are `register value + offset`. -/
inductive TF : Type
  | leaf (r o : ℕ)
  | not (a : TF)
  | and (a b : TF)
  | or (a b : TF)

/-- Instantiate a template with a register valuation `V r o = value r + o`. -/
def TF.inst (V : ℕ → ℕ → ℕ) : TF → PropFormula
  | .leaf r o => .var (V r o)
  | .not a => .not (a.inst V)
  | .and a b => .and (a.inst V) (b.inst V)
  | .or a b => .or (a.inst V) (b.inst V)

/-- Truth of a template under an assignment. -/
def TF.holds (σ : ℕ → Bool) (V : ℕ → ℕ → ℕ) (φ : TF) : Prop :=
  PropFormula.eval σ (φ.inst V) = true

/-- Always true template. -/
def TF.tt : TF := .or (.leaf 0 0) (.not (.leaf 0 0))

/-- Conjunction, ending in `tt`. -/
def conjT : List TF → TF
  | [] => TF.tt
  | φ :: l => .and φ (conjT l)

/-- Disjunction, ending in `ff`. -/
def disjT : List TF → TF
  | [] => .not TF.tt
  | φ :: l => .or φ (disjT l)

/-- Implication. -/
def impT (a b : TF) : TF := .or (.not a) b

variable {σ : ℕ → Bool} {V : ℕ → ℕ → ℕ}

@[simp] theorem TF.holds_leaf (r o : ℕ) :
    TF.holds σ V (.leaf r o) ↔ σ (V r o) = true := by
  simp [TF.holds, TF.inst, PropFormula.eval]

@[simp] theorem TF.holds_not (a : TF) :
    TF.holds σ V (.not a) ↔ ¬ TF.holds σ V a := by
  simp [TF.holds, TF.inst, PropFormula.eval]

@[simp] theorem TF.holds_and (a b : TF) :
    TF.holds σ V (.and a b) ↔ TF.holds σ V a ∧ TF.holds σ V b := by
  simp [TF.holds, TF.inst, PropFormula.eval]

@[simp] theorem TF.holds_or (a b : TF) :
    TF.holds σ V (.or a b) ↔ TF.holds σ V a ∨ TF.holds σ V b := by
  simp [TF.holds, TF.inst, PropFormula.eval]

@[simp] theorem TF.holds_tt : TF.holds σ V TF.tt := by
  simp [TF.tt]

theorem holds_conjT (l : List TF) :
    TF.holds σ V (conjT l) ↔ ∀ φ ∈ l, TF.holds σ V φ := by
  induction l with
  | nil => simp [conjT]
  | cons φ l ih => simp [conjT, ih]

theorem holds_disjT (l : List TF) :
    TF.holds σ V (disjT l) ↔ ∃ φ ∈ l, TF.holds σ V φ := by
  induction l with
  | nil => simp [disjT]
  | cons φ l ih => simp [disjT, ih]

theorem holds_impT (a b : TF) :
    TF.holds σ V (impT a b) ↔ (TF.holds σ V a → TF.holds σ V b) := by
  simp [impT]
  tauto

/-- Exactly one of the listed leaves at `(r, o)` for `o` in the list holds. -/
def exactlyOne (r : ℕ) (offs : List ℕ) : TF :=
  .and (disjT (offs.map (fun o => .leaf r o)))
    (conjT ((offs.flatMap fun o => offs.filterMap fun o' =>
      if o < o' then some (TF.not (.and (.leaf r o) (.leaf r o'))) else none)))

/-! ## Coded machine and its finite array step -/

/-- A machine with `K` stacks over symbols `0 .. A-1` (blank is `A`), controls `0 .. Q-1`,
and a transition that reads a window of depth `c` on every stack. -/
structure CM where
  K : ℕ
  A : ℕ
  Q : ℕ
  c : ℕ
  q0 : ℕ
  halt : ℕ → Bool
  δ : ℕ → List ℕ → ℕ × List (ℕ × List ℕ)
  kin : ℕ
  kout : ℕ
  inSym : Bool → ℕ
  outTrue : ℕ

/-- Stack contents as arrays indexed from the top: `a k d`. -/
abbrev Arr := ℕ → ℕ → ℕ

namespace CM

variable (cm : CM)

/-- Flattened top window of all stacks. -/
def pat (a : Arr) : List ℕ := (List.range (cm.K * cm.c)).map fun i => a (i / cm.c) (i % cm.c)

/-- Pop count and pushed symbols (top first) of stack `k`. -/
def eff (q : ℕ) (p : List ℕ) (k : ℕ) : ℕ × List ℕ := ((cm.δ q p).2).getD k (0, [])

/-- New cell value after an effect, in a width `W` window. -/
def newCell (W : ℕ) (e : ℕ × List ℕ) (a : Arr) (k d : ℕ) : ℕ :=
  if k < cm.K ∧ d < W then
    (if h : d < e.2.length then e.2[d] else
      (if d - e.2.length + e.1 < W then a k (d - e.2.length + e.1) else cm.A))
  else cm.A

/-- One step on arrays. -/
def stepA (W : ℕ) (q : ℕ) (a : Arr) : ℕ × Arr :=
  ((cm.δ q (cm.pat a)).1, fun k d => cm.newCell W (cm.eff q (cm.pat a) k) a k d)

/-- The first `n` steps from an initial array. -/
def runA (W : ℕ) (a0 : Arr) : ℕ → ℕ × Arr
  | 0 => (cm.q0, a0)
  | n + 1 => cm.stepA W (runA W a0 n).1 (runA W a0 n).2

/-- Initial array for input pair `encodePair (x, w)` on stack `kin`. -/
def initArr (W : ℕ) (x w : List Bool) : Arr := fun k d =>
  if k = cm.kin ∧ k < cm.K ∧ d < W then
    (if d < (encodePair (x, w)).length then cm.inSym ((encodePair (x, w)).getD d false) else cm.A)
  else cm.A

/-- No cell in the last `c` columns is ever occupied. -/
def NoOverflow (W B : ℕ) (a0 : Arr) : Prop :=
  ∀ t ≤ B, ∀ k < cm.K, ∀ d, W - 2 * cm.c ≤ d → d < W → (cm.runA W a0 t).2 k d = cm.A

/-- Acceptance of a configuration. -/
def Accepts (q : ℕ) (a : Arr) : Prop :=
  cm.halt q = true ∧ a cm.kout 0 = cm.outTrue ∧ a cm.kout 1 = cm.A

/-- Well formedness. -/
structure WF (W : ℕ) : Prop where
  hc : 2 * cm.c ≤ W
  hq0 : cm.q0 < cm.Q
  hδq : ∀ q < cm.Q, ∀ p, (cm.δ q p).1 < cm.Q
  hδs : ∀ q p k, ∀ s ∈ (cm.eff q p k).2, s < cm.A
  hδj : ∀ q p k, (cm.eff q p k).1 ≤ cm.c ∧ (cm.eff q p k).2.length ≤ cm.c
  hin : ∀ b, cm.inSym b < cm.A
  hinj : cm.inSym false ≠ cm.inSym true
  hkin : cm.kin < cm.K
  hkout : cm.kout < cm.K
  hc1 : 1 ≤ cm.c
  houtT : cm.outTrue ≤ cm.A

end CM

/-- All flattened windows of length `n` over symbols `0 .. A`. -/
def allPats (A : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (List.range (A + 1)).flatMap fun s => (allPats A n).map (s :: ·)

theorem mem_allPats {A n : ℕ} {p : List ℕ} :
    p ∈ allPats A n ↔ p.length = n ∧ ∀ s ∈ p, s ≤ A := by
  induction n generalizing p with
  | zero => cases p <;> simp [allPats]
  | succ n ih =>
      cases p with
      | nil => simp [allPats]
      | cons a t =>
          simp only [allPats, List.mem_flatMap, List.mem_range, List.mem_map, List.cons.injEq,
            ih, List.length_cons, List.mem_cons, forall_eq_or_imp]
          constructor
          · rintro ⟨s, hs, t', ⟨hl, hall⟩, rfl, rfl⟩
            exact ⟨by omega, by omega, hall⟩
          · rintro ⟨hl, ha, hall⟩
            exact ⟨a, by omega, t, ⟨by omega, hall⟩, rfl, rfl⟩

/-! ## Encoding positions -/

theorem encodePair_getD (x w : List Bool) (d : ℕ) :
    (encodePair (x, w)).getD d false =
      if d < 2 * x.length then (if d % 2 = 0 then true else x.getD (d / 2) false)
      else if d = 2 * x.length then false else w.getD (d - 2 * x.length - 1) false := by
  induction x generalizing d with
  | nil =>
      cases d with
      | zero => simp [encodePair]
      | succ d => simp [encodePair]
  | cons b x ih =>
      have hE : encodePair (b :: x, w) = true :: b :: encodePair (x, w) := by
        simp [encodePair]
      rw [hE]
      cases d with
      | zero => simp
      | succ d =>
          cases d with
          | zero =>
              have h : 1 < 2 * (x.length + 1) := by omega
              simp [h]
          | succ d =>
              simp only [List.getD_cons_succ, ih, List.length_cons]
              have e1 : d + 1 + 1 = (d) + 2 := by omega
              by_cases h1 : d < 2 * x.length
              · have h2 : d + 1 + 1 < 2 * (x.length + 1) := by omega
                simp only [h1, h2, if_true]
                have : (d + 1 + 1) % 2 = d % 2 := by omega
                rw [this]
                have : (d + 1 + 1) / 2 = d / 2 + 1 := by omega
                rw [this]
                by_cases h3 : d % 2 = 0 <;> simp [h3]
              · have h2 : ¬ d + 1 + 1 < 2 * (x.length + 1) := by omega
                simp only [h1, h2, if_false]
                by_cases h4 : d = 2 * x.length
                · have : d + 1 + 1 = 2 * (x.length + 1) := by omega
                  rw [if_pos h4, if_pos this]
                · have h5 : ¬ d + 1 + 1 = 2 * (x.length + 1) := by omega
                  simp only [h4, h5, if_false]
                  congr 1; omega

theorem length_encodePair' (x w : List Bool) :
    (encodePair (x, w)).length = 2 * x.length + 1 + w.length := by
  rw [length_encodePair]

/-! ## Variable layout and constraint families (Prop level) -/

namespace CM

variable (cm : CM)

/-- Variables per time frame. -/
def Fr (W : ℕ) : ℕ := cm.Q + cm.K * (W * (cm.A + 1))

/-- Control variable. -/
def vC (W t q : ℕ) : ℕ := t * cm.Fr W + q

/-- Cell variable: time, stack, depth from the top, symbol. -/
def vA (W t k d a : ℕ) : ℕ := t * cm.Fr W + cm.Q + (k * W + d) * (cm.A + 1) + a

theorem vC_div_mod (W t q : ℕ) (hq : q < cm.Fr W) :
    cm.vC W t q / cm.Fr W = t ∧ cm.vC W t q % cm.Fr W = q := by
  unfold vC
  have hpos : 0 < cm.Fr W := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hq]; simp
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]

theorem vA_lt_Fr (W k d a : ℕ) (hk : k < cm.K) (hd : d < W) (ha : a ≤ cm.A) :
    cm.Q + (k * W + d) * (cm.A + 1) + a < cm.Fr W := by
  unfold Fr
  have h1 : k * W + d + 1 ≤ cm.K * W := by nlinarith
  have h2 : (k * W + d + 1) * (cm.A + 1) ≤ cm.K * W * (cm.A + 1) := Nat.mul_le_mul_right _ h1
  have h3 : cm.K * (W * (cm.A + 1)) = cm.K * W * (cm.A + 1) := by ring
  rw [h3]
  nlinarith

end CM

/-- Exactly one index below `n` is true. -/
def ExactlyOne (f : ℕ → Bool) (n : ℕ) : Prop :=
  (∃ i < n, f i = true) ∧ ∀ i < n, ∀ j < n, f i = true → f j = true → i = j

namespace CM

variable (cm : CM)

/-- The guard of a case: control `q` and window pattern `p` at time `t`. -/
def Guard (σ : ℕ → Bool) (W t q : ℕ) (p : List ℕ) : Prop :=
  σ (cm.vC W t q) = true ∧
    ∀ i < cm.K * cm.c, σ (cm.vA W t (i / cm.c) (i % cm.c) (p.getD i 0)) = true

/-- The tableau constraints. -/
structure Fam (W B : ℕ) (x : List Bool) (σ : ℕ → Bool) : Prop where
  frameC : ∀ t ≤ B, ExactlyOne (fun q => σ (cm.vC W t q)) cm.Q
  frameA : ∀ t ≤ B, ∀ k < cm.K, ∀ d < W,
    ExactlyOne (fun a => σ (cm.vA W t k d a)) (cm.A + 1)
  margin : ∀ t ≤ B, ∀ k < cm.K, ∀ i < 2 * cm.c, σ (cm.vA W t k (W - 2 * cm.c + i) cm.A) = true
  initC : σ (cm.vC W 0 cm.q0) = true
  initX : ∀ i < x.length,
    σ (cm.vA W 0 cm.kin (2 * i) (cm.inSym true)) = true ∧
    σ (cm.vA W 0 cm.kin (2 * i + 1) (cm.inSym (x.getD i false))) = true
  initSep : σ (cm.vA W 0 cm.kin (2 * x.length) (cm.inSym false)) = true
  initW : ∀ d, 2 * x.length + 1 ≤ d → d < W →
    (σ (cm.vA W 0 cm.kin d (cm.inSym false)) = true ∨
      σ (cm.vA W 0 cm.kin d (cm.inSym true)) = true ∨
      σ (cm.vA W 0 cm.kin d cm.A) = true)
  initContig : ∀ d, 2 * x.length + 1 ≤ d → d + 1 < W →
    σ (cm.vA W 0 cm.kin d cm.A) = true → σ (cm.vA W 0 cm.kin (d + 1) cm.A) = true
  initO : ∀ k < cm.K, k ≠ cm.kin → ∀ d < W, σ (cm.vA W 0 k d cm.A) = true
  stepC : ∀ t < B, ∀ q < cm.Q, ∀ p ∈ allPats cm.A (cm.K * cm.c),
    cm.Guard σ W t q p → σ (cm.vC W (t + 1) (cm.δ q p).1) = true
  stepA : ∀ t < B, ∀ q < cm.Q, ∀ p ∈ allPats cm.A (cm.K * cm.c),
    cm.Guard σ W t q p → ∀ k < cm.K, ∀ d, d + cm.c < W →
      (d < (cm.eff q p k).2.length →
        σ (cm.vA W (t + 1) k d ((cm.eff q p k).2.getD d 0)) = true) ∧
      ((cm.eff q p k).2.length ≤ d →
        ∀ a ≤ cm.A,
          σ (cm.vA W t k (d - (cm.eff q p k).2.length + (cm.eff q p k).1) a) = true →
          σ (cm.vA W (t + 1) k d a) = true)
  acc : ∃ q < cm.Q, cm.halt q = true ∧ σ (cm.vC W B q) = true ∧
    σ (cm.vA W B cm.kout 0 cm.outTrue) = true ∧ σ (cm.vA W B cm.kout 1 cm.A) = true

end CM

/-! ## Soundness: a satisfying assignment gives a run -/

namespace CM

variable (cm : CM)

open Classical in
/-- The control state read off an assignment. -/
noncomputable def qO (σ : ℕ → Bool) (W t : ℕ) : ℕ :=
  if h : ∃ q, q < cm.Q ∧ σ (cm.vC W t q) = true then Classical.choose h else 0

open Classical in
/-- The symbol read off an assignment. -/
noncomputable def aO (σ : ℕ → Bool) (W t k d : ℕ) : ℕ :=
  if h : ∃ a, a ≤ cm.A ∧ σ (cm.vA W t k d a) = true then Classical.choose h else cm.A

/-- The array read off an assignment (blank outside the grid). -/
noncomputable def aArr (σ : ℕ → Bool) (W t : ℕ) : Arr := fun k d =>
  if k < cm.K ∧ d < W then cm.aO σ W t k d else cm.A

theorem qO_spec {σ : ℕ → Bool} {W t : ℕ} (h : ExactlyOne (fun q => σ (cm.vC W t q)) cm.Q) :
    cm.qO σ W t < cm.Q ∧ σ (cm.vC W t (cm.qO σ W t)) = true ∧
      ∀ q < cm.Q, σ (cm.vC W t q) = true → q = cm.qO σ W t := by
  classical
  have hex : ∃ q, q < cm.Q ∧ σ (cm.vC W t q) = true := by
    obtain ⟨i, hi, hi'⟩ := h.1; exact ⟨i, hi, hi'⟩
  have hc := Classical.choose_spec hex
  have heq : cm.qO σ W t = Classical.choose hex := by simp [qO, hex]
  rw [heq]
  refine ⟨hc.1, hc.2, ?_⟩
  intro q hq hσ
  exact h.2 q hq _ hc.1 hσ hc.2

theorem aO_spec {σ : ℕ → Bool} {W t k d : ℕ}
    (h : ExactlyOne (fun a => σ (cm.vA W t k d a)) (cm.A + 1)) :
    cm.aO σ W t k d ≤ cm.A ∧ σ (cm.vA W t k d (cm.aO σ W t k d)) = true ∧
      ∀ a ≤ cm.A, σ (cm.vA W t k d a) = true → a = cm.aO σ W t k d := by
  classical
  have hex : ∃ a, a ≤ cm.A ∧ σ (cm.vA W t k d a) = true := by
    obtain ⟨i, hi, hi'⟩ := h.1; exact ⟨i, by omega, hi'⟩
  have hc := Classical.choose_spec hex
  have heq : cm.aO σ W t k d = Classical.choose hex := by simp [aO, hex]
  rw [heq]
  refine ⟨hc.1, hc.2, ?_⟩
  intro a ha hσ
  exact h.2 a (by omega) _ (by have := hc.1; omega) hσ hc.2

theorem aArr_in {σ : ℕ → Bool} {W t k d : ℕ} (hk : k < cm.K) (hd : d < W) :
    cm.aArr σ W t k d = cm.aO σ W t k d := by
  simp [aArr, hk, hd]

theorem pat_mem {σ : ℕ → Bool} {W B : ℕ} {x : List Bool} (hwf : cm.WF W)
    (hF : cm.Fam W B x σ) {t : ℕ} (ht : t ≤ B) :
    cm.pat (cm.aArr σ W t) ∈ allPats cm.A (cm.K * cm.c) := by
  rw [mem_allPats]
  refine ⟨by simp [pat], ?_⟩
  intro s hs
  simp only [pat, List.mem_map, List.mem_range] at hs
  obtain ⟨i, hi, rfl⟩ := hs
  have hc : 0 < cm.c := by
    rcases Nat.eq_zero_or_pos cm.c with h | h
    · rw [h] at hi; simp at hi
    · exact h
  have hk : i / cm.c < cm.K := by
    rw [Nat.div_lt_iff_lt_mul hc]; linarith
  have hd : i % cm.c < W := lt_of_lt_of_le (Nat.mod_lt _ hc) (by have := hwf.hc; omega)
  rw [aArr_in cm hk hd]
  exact (aO_spec cm (hF.frameA t ht _ hk _ hd)).1

theorem guard_aArr {σ : ℕ → Bool} {W B : ℕ} {x : List Bool} (hwf : cm.WF W)
    (hF : cm.Fam W B x σ) {t : ℕ} (ht : t ≤ B) :
    cm.Guard σ W t (cm.qO σ W t) (cm.pat (cm.aArr σ W t)) := by
  refine ⟨(qO_spec cm (hF.frameC t ht)).2.1, ?_⟩
  intro i hi
  have hc : 0 < cm.c := by
    rcases Nat.eq_zero_or_pos cm.c with h | h
    · rw [h] at hi; simp at hi
    · exact h
  have hk : i / cm.c < cm.K := by
    rw [Nat.div_lt_iff_lt_mul hc]; linarith
  have hd : i % cm.c < W := lt_of_lt_of_le (Nat.mod_lt _ hc) (by have := hwf.hc; omega)
  have hget : (cm.pat (cm.aArr σ W t)).getD i 0 = cm.aArr σ W t (i / cm.c) (i % cm.c) := by
    simp [pat, List.getD_eq_getElem?_getD, hi]
  rw [hget, aArr_in cm hk hd]
  exact (aO_spec cm (hF.frameA t ht _ hk _ hd)).2.1

theorem sound_step {σ : ℕ → Bool} {W B : ℕ} {x : List Bool} (hwf : cm.WF W)
    (hF : cm.Fam W B x σ) {t : ℕ} (ht : t < B) :
    cm.stepA W (cm.qO σ W t) (cm.aArr σ W t) =
      (cm.qO σ W (t + 1), cm.aArr σ W (t + 1)) := by
  have htB : t ≤ B := ht.le
  have htB1 : t + 1 ≤ B := ht
  set q := cm.qO σ W t with hq
  set p := cm.pat (cm.aArr σ W t) with hp
  have hqQ : q < cm.Q := (qO_spec cm (hF.frameC t htB)).1
  have hpm : p ∈ allPats cm.A (cm.K * cm.c) := pat_mem cm hwf hF htB
  have hg : cm.Guard σ W t q p := guard_aArr cm hwf hF htB
  -- control
  have hctl : (cm.δ q p).1 = cm.qO σ W (t + 1) := by
    have h1 := hF.stepC t ht q hqQ p hpm hg
    have h2 := hwf.hδq q hqQ p
    exact ((qO_spec cm (hF.frameC (t + 1) htB1)).2.2 _ h2 h1)
  -- cells
  have hmarA : ∀ t' ≤ B, ∀ k < cm.K, ∀ d, W - 2 * cm.c ≤ d → d < W →
      cm.aO σ W t' k d = cm.A := by
    intro t' ht' k hk d h1 h2
    have hm := hF.margin t' ht' k hk (d - (W - 2 * cm.c)) (by omega)
    have hidx : W - 2 * cm.c + (d - (W - 2 * cm.c)) = d := by omega
    rw [hidx] at hm
    exact ((aO_spec cm (hF.frameA t' ht' k hk d h2)).2.2 _ (le_refl _) hm).symm
  have hcell : ∀ k d, cm.newCell W (cm.eff q p k) (cm.aArr σ W t) k d =
      cm.aArr σ W (t + 1) k d := by
    intro k d
    by_cases hkd : k < cm.K ∧ d < W
    · obtain ⟨hk, hd⟩ := hkd
      have hspec := aO_spec cm (hF.frameA (t + 1) htB1 k hk d hd)
      have hj := hwf.hδj q p k
      have hc2 := hwf.hc
      rw [aArr_in cm hk hd]
      unfold newCell
      simp only [hk, hd, and_self, if_true]
      by_cases hdc : d + cm.c < W
      · have hsa := hF.stepA t ht q hqQ p hpm hg k hk d hdc
        by_cases hlen : d < (cm.eff q p k).2.length
        · rw [dif_pos hlen]
          have h1 := hsa.1 hlen
          have hs : (cm.eff q p k).2.getD d 0 < cm.A :=
            hwf.hδs q p k _ (by simp [List.getD_eq_getElem?_getD, hlen])
          have := hspec.2.2 _ hs.le h1
          rw [← this]
          simp [List.getD_eq_getElem?_getD, hlen]
        · rw [dif_neg hlen]
          have hlen' : (cm.eff q p k).2.length ≤ d := by omega
          have hsW : d - (cm.eff q p k).2.length + (cm.eff q p k).1 < W := by omega
          rw [if_pos hsW]
          rw [aArr_in cm hk hsW]
          have hsp := aO_spec cm (hF.frameA t htB k hk _ hsW)
          have h2 := hsa.2 hlen' _ hsp.1 hsp.2.1
          exact hspec.2.2 _ hsp.1 h2
      · have hlen : ¬ d < (cm.eff q p k).2.length := by omega
        rw [dif_neg hlen]
        have hAt1 := hmarA (t + 1) htB1 k hk d (by omega) hd
        rw [hAt1]
        by_cases hsW : d - (cm.eff q p k).2.length + (cm.eff q p k).1 < W
        · rw [if_pos hsW, aArr_in cm hk hsW]
          exact hmarA t htB k hk _ (by omega) hsW
        · rw [if_neg hsW]
    · have : cm.newCell W (cm.eff q p k) (cm.aArr σ W t) k d = cm.A := by
        unfold newCell; simp [hkd]
      rw [this]
      simp [aArr, hkd]
  unfold stepA
  rw [hctl]
  congr 1
  funext k d
  exact hcell k d

theorem getD_map_range (n : ℕ) (g : ℕ → Bool) (j : ℕ) :
    ((List.range n).map g).getD j false = if j < n then g j else false := by
  by_cases h : j < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem exists_w {σ : ℕ → Bool} {W B : ℕ} {x : List Bool} (hwf : cm.WF W)
    (hF : cm.Fam W B x σ) (hW : 2 * x.length + 1 + 2 * cm.c ≤ W) :
    ∃ w : List Bool, 2 * x.length + 1 + w.length + 2 * cm.c ≤ W ∧
      cm.aArr σ W 0 = cm.initArr W x w := by
  classical
  set m := x.length with hm
  let f : ℕ → ℕ := fun d => cm.aO σ W 0 cm.kin d
  have hkin := hwf.hkin
  have hspec : ∀ d, d < W → cm.aO σ W 0 cm.kin d ≤ cm.A ∧
      σ (cm.vA W 0 cm.kin d (cm.aO σ W 0 cm.kin d)) = true ∧
      ∀ a ≤ cm.A, σ (cm.vA W 0 cm.kin d a) = true → a = cm.aO σ W 0 cm.kin d :=
    fun d hd => aO_spec cm (hF.frameA 0 (Nat.zero_le _) _ hkin d hd)
  have hin : ∀ b, cm.inSym b ≤ cm.A := fun b => (hwf.hin b).le
  -- facts about f
  have hfx : ∀ i < m, f (2 * i) = cm.inSym true ∧ f (2 * i + 1) = cm.inSym (x.getD i false) := by
    intro i hi
    have h1 := hF.initX i hi
    have hd1 : 2 * i < W := by omega
    have hd2 : 2 * i + 1 < W := by omega
    exact ⟨((hspec _ hd1).2.2 _ (hin _) h1.1).symm, ((hspec _ hd2).2.2 _ (hin _) h1.2).symm⟩
  have hfsep : f (2 * m) = cm.inSym false := by
    have hd : 2 * m < W := by omega
    exact ((hspec _ hd).2.2 _ (hin _) hF.initSep).symm
  have hfw : ∀ d, 2 * m + 1 ≤ d → d < W →
      f d = cm.inSym false ∨ f d = cm.inSym true ∨ f d = cm.A := by
    intro d h1 h2
    rcases hF.initW d h1 h2 with h | h | h
    · exact Or.inl ((hspec d h2).2.2 _ (hin _) h).symm
    · exact Or.inr (Or.inl ((hspec d h2).2.2 _ (hin _) h).symm)
    · exact Or.inr (Or.inr ((hspec d h2).2.2 _ (le_refl _) h).symm)
  have hfc : ∀ d, 2 * m + 1 ≤ d → d + 1 < W → f d = cm.A → f (d + 1) = cm.A := by
    intro d h1 h2 h3
    have h4 : σ (cm.vA W 0 cm.kin d cm.A) = true := by
      have := (hspec d (by omega)).2.1
      have h3' : cm.aO σ W 0 cm.kin d = cm.A := h3
      rw [h3'] at this; exact this
    have h5 := hF.initContig d h1 h2 h4
    exact ((hspec (d + 1) h2).2.2 _ (le_refl _) h5).symm
  have hfm : ∀ d, W - 2 * cm.c ≤ d → d < W → f d = cm.A := by
    intro d h1 h2
    have := hF.margin 0 (Nat.zero_le _) cm.kin hkin (d - (W - 2 * cm.c)) (by omega)
    have hidx : W - 2 * cm.c + (d - (W - 2 * cm.c)) = d := by omega
    rw [hidx] at this
    exact ((hspec d h2).2.2 _ (le_refl _) this).symm
  have hfo : ∀ k, k < cm.K → k ≠ cm.kin → ∀ d, d < W → cm.aO σ W 0 k d = cm.A := by
    intro k hk hne d hd
    have h := hF.initO k hk hne d hd
    exact ((aO_spec cm (hF.frameA 0 (Nat.zero_le _) k hk d hd)).2.2 _ (le_refl _) h).symm
  -- the end of the witness
  have hex : ∃ d, 2 * m + 1 ≤ d ∧ (W ≤ d ∨ f d = cm.A) := ⟨W, by omega, Or.inl le_rfl⟩
  let h0 := Nat.find hex
  have hh0 : 2 * m + 1 ≤ h0 ∧ (W ≤ h0 ∨ f h0 = cm.A) := Nat.find_spec hex
  have hmin : ∀ d, 2 * m + 1 ≤ d → d < h0 → d < W ∧ f d ≠ cm.A := by
    intro d h1 h2
    have hnot := Nat.find_min hex h2
    refine ⟨?_, ?_⟩
    · by_contra hc
      exact hnot ⟨h1, Or.inl (by omega)⟩
    · intro hc
      exact hnot ⟨h1, Or.inr hc⟩
  have hh0W : h0 ≤ W := Nat.find_min' hex ⟨by omega, Or.inl le_rfl⟩
  have hcont : ∀ d, h0 ≤ d → d < W → f d = cm.A := by
    intro d h1 h2
    induction d, h1 using Nat.le_induction with
    | base =>
        rcases hh0.2 with h | h
        · omega
        · exact h
    | succ d hd ih =>
        exact hfc d (by omega) h2 (ih (by omega))
  have hsize : h0 + 2 * cm.c ≤ W := by
    by_contra hcon
    have hcon' : W < h0 + 2 * cm.c := by omega
    have hc1 : 0 < cm.c := by have := hwf.hc1; omega
    have h1 := hmin (W - 2 * cm.c) (by omega) (by omega)
    exact h1.2 (hfm (W - 2 * cm.c) le_rfl h1.1)
  refine ⟨(List.range (h0 - (2 * m + 1))).map (fun i => decide (f (2 * m + 1 + i) = cm.inSym true)),
    ?_, ?_⟩
  · simp only [List.length_map, List.length_range]; omega
  · funext k d
    unfold aArr initArr
    by_cases hkd : k = cm.kin ∧ k < cm.K ∧ d < W
    · obtain ⟨rfl, hk, hd⟩ := hkd
      simp only [hk, hd, and_self, if_true]
      rw [length_encodePair']
      simp only [List.length_map, List.length_range]
      have hlen : 2 * m + 1 + (h0 - (2 * m + 1)) = h0 := by omega
      rw [hlen]
      change cm.aO σ W 0 cm.kin d = _
      by_cases hd1 : d < h0
      · rw [if_pos hd1, encodePair_getD]
        by_cases hd2 : d < 2 * m
        · rw [if_pos (by simpa [hm] using hd2)]
          have hi : d / 2 < m := by omega
          by_cases hpar : d % 2 = 0
          · simp only [hpar, if_true]
            have := (hfx (d / 2) hi).1
            have e : 2 * (d / 2) = d := by omega
            rw [e] at this
            exact this
          · simp only [hpar, if_false]
            have := (hfx (d / 2) hi).2
            have e : 2 * (d / 2) + 1 = d := by omega
            rw [e] at this
            exact this
        · rw [if_neg (by simpa [hm] using hd2)]
          by_cases hd3 : d = 2 * m
          · rw [if_pos (by simpa [hm] using hd3)]
            subst hd3; exact hfsep
          · rw [if_neg (by simpa [hm] using hd3)]
            have hmin' := hmin d (by omega) hd1
            have hw := hfw d (by omega) hd
            have hidx : 2 * m + 1 + (d - 2 * m - 1) = d := by omega
            rw [getD_map_range, if_pos (by omega), hidx]
            by_cases ht : f d = cm.inSym true
            · have ht' : cm.aO σ W 0 cm.kin d = cm.inSym true := ht
              simp [show f d = cm.aO σ W 0 cm.kin d from rfl, ht']
            · have hf : f d = cm.inSym false := by
                rcases hw with h | h | h
                · exact h
                · exact absurd h ht
                · exact absurd h hmin'.2
              have hf' : cm.aO σ W 0 cm.kin d = cm.inSym false := hf
              have ht' : ¬ cm.aO σ W 0 cm.kin d = cm.inSym true := ht
              simp [show f d = cm.aO σ W 0 cm.kin d from rfl, hf', hwf.hinj]
      · rw [if_neg hd1]
        exact hcont d (by omega) hd
    · simp only [hkd, if_false]
      by_cases hkd' : k < cm.K ∧ d < W
      · simp only [hkd', and_self, if_true]
        have hne : k ≠ cm.kin := fun h => hkd ⟨h, hkd'⟩
        exact hfo k hkd'.1 hne d hkd'.2
      · simp [hkd']

theorem run_eq {σ : ℕ → Bool} {W B : ℕ} {x : List Bool} (hwf : cm.WF W)
    (hF : cm.Fam W B x σ) (a0 : Arr) (ha0 : a0 = cm.aArr σ W 0) :
    ∀ t ≤ B, cm.runA W a0 t = (cm.qO σ W t, cm.aArr σ W t) := by
  intro t
  induction t with
  | zero =>
      intro _
      have hq : cm.q0 = cm.qO σ W 0 :=
        (qO_spec cm (hF.frameC 0 (Nat.zero_le _))).2.2 _ hwf.hq0 hF.initC
      simp [runA, hq, ha0]
  | succ t ih =>
      intro ht
      have := sound_step cm hwf hF (t := t) (by omega)
      simp only [runA]
      rw [ih (by omega)]
      exact this

theorem soundness {σ : ℕ → Bool} {W B : ℕ} {x : List Bool} (hwf : cm.WF W)
    (hF : cm.Fam W B x σ) (hW : 2 * x.length + 1 + 2 * cm.c ≤ W) :
    ∃ w : List Bool, 2 * x.length + 1 + w.length + 2 * cm.c ≤ W ∧
      cm.NoOverflow W B (cm.initArr W x w) ∧
      cm.Accepts (cm.runA W (cm.initArr W x w) B).1 (cm.runA W (cm.initArr W x w) B).2 := by
  obtain ⟨w, hsize, harr⟩ := exists_w cm hwf hF hW
  have hrun := run_eq cm hwf hF (cm.initArr W x w) harr.symm
  refine ⟨w, hsize, ?_, ?_⟩
  · intro t ht k hk d hd1 hd2
    rw [hrun t ht]
    simp only
    rw [aArr_in cm hk hd2]
    have hmar := hF.margin t ht k hk (d - (W - 2 * cm.c)) (by omega)
    have hidx : W - 2 * cm.c + (d - (W - 2 * cm.c)) = d := by omega
    rw [hidx] at hmar
    exact ((aO_spec cm (hF.frameA t ht k hk d hd2)).2.2 _ (le_refl _) hmar).symm
  · rw [hrun B le_rfl]
    obtain ⟨q, hq, hh, hqσ, h0, h1⟩ := hF.acc
    refine ⟨?_, ?_, ?_⟩
    · have := (qO_spec cm (hF.frameC B le_rfl)).2.2 q hq hqσ
      simp only
      rw [← this]; exact hh
    · simp only
      have hk := hwf.hkout
      have hd : 0 < W := by omega
      rw [aArr_in cm hk hd]
      exact ((aO_spec cm (hF.frameA B le_rfl _ hk 0 hd)).2.2 _ hwf.houtT h0).symm
    · simp only
      by_cases hd : 1 < W
      · have hk := hwf.hkout
        rw [aArr_in cm hk hd]
        exact ((aO_spec cm (hF.frameA B le_rfl _ hk 1 hd)).2.2 _ (le_refl _) h1).symm
      · simp [aArr, hd]

/-! ## Completeness: a run gives a satisfying assignment -/

theorem runA_cells_le (hwf : cm.WF W) (a0 : Arr) (h0 : ∀ k d, a0 k d ≤ cm.A) :
    ∀ t k d, (cm.runA W a0 t).2 k d ≤ cm.A := by
  intro t
  induction t with
  | zero => intro k d; exact h0 k d
  | succ t ih =>
      intro k d
      simp only [runA, stepA, newCell]
      by_cases hkd : k < cm.K ∧ d < W
      · simp only [hkd, and_self, if_true]
        by_cases hlen : d < (cm.eff (cm.runA W a0 t).1 (cm.pat (cm.runA W a0 t).2) k).2.length
        · rw [dif_pos hlen]
          exact (hwf.hδs _ _ k _ (List.getElem_mem hlen)).le
        · rw [dif_neg hlen]
          by_cases hs : d - (cm.eff (cm.runA W a0 t).1 (cm.pat (cm.runA W a0 t).2) k).2.length +
              (cm.eff (cm.runA W a0 t).1 (cm.pat (cm.runA W a0 t).2) k).1 < W
          · rw [if_pos hs]; exact ih _ _
          · rw [if_neg hs]
      · simp [hkd]

theorem runA_q_lt (hwf : cm.WF W) (a0 : Arr) :
    ∀ t, (cm.runA W a0 t).1 < cm.Q := by
  intro t
  induction t with
  | zero => exact hwf.hq0
  | succ t ih => exact hwf.hδq _ ih _

theorem initArr_le (hwf : cm.WF W) (x w : List Bool) : ∀ k d, cm.initArr W x w k d ≤ cm.A := by
  intro k d
  unfold initArr
  split_ifs
  · exact (hwf.hin _).le
  · exact le_rfl
  · exact le_rfl

/-- The satisfying assignment built from a run. -/
def sigRun (W B : ℕ) (a0 : Arr) (n : ℕ) : Bool :=
  let t := n / cm.Fr W
  let r := n % cm.Fr W
  if r < cm.Q then decide (t ≤ B ∧ (cm.runA W a0 t).1 = r)
  else decide (t ≤ B ∧ (r - cm.Q) / (cm.A + 1) / W < cm.K ∧
    (cm.runA W a0 t).2 ((r - cm.Q) / (cm.A + 1) / W) ((r - cm.Q) / (cm.A + 1) % W) =
      (r - cm.Q) % (cm.A + 1))

theorem sigRun_vC (W B : ℕ) (a0 : Arr) (t q : ℕ) (hq : q < cm.Q) :
    cm.sigRun W B a0 (cm.vC W t q) = decide (t ≤ B ∧ (cm.runA W a0 t).1 = q) := by
  have hQF : cm.Q ≤ cm.Fr W := by unfold Fr; omega
  have hd := cm.vC_div_mod W t q (by omega)
  unfold sigRun
  simp only [hd.1, hd.2, hq, if_true]

theorem sigRun_vA (W B : ℕ) (a0 : Arr) (hW : 0 < W) (t k d a : ℕ) (hk : k < cm.K)
    (hd : d < W) (ha : a ≤ cm.A) :
    cm.sigRun W B a0 (cm.vA W t k d a) = decide (t ≤ B ∧ (cm.runA W a0 t).2 k d = a) := by
  have hlt := cm.vA_lt_Fr W k d a hk hd ha
  have hn : cm.vA W t k d a = (cm.Q + (k * W + d) * (cm.A + 1) + a) + t * cm.Fr W := by
    unfold vA; ring
  have hdiv : cm.vA W t k d a / cm.Fr W = t := by
    rw [hn, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hlt]; simp
  have hmod : cm.vA W t k d a % cm.Fr W = cm.Q + (k * W + d) * (cm.A + 1) + a := by
    rw [hn, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  have hu : cm.Q + (k * W + d) * (cm.A + 1) + a - cm.Q = (cm.A + 1) * (k * W + d) + a := by
    rw [Nat.mul_comm]; omega
  have h1 : ((cm.A + 1) * (k * W + d) + a) / (cm.A + 1) = k * W + d := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]; simp
  have h2 : ((cm.A + 1) * (k * W + d) + a) % (cm.A + 1) = a := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
  have h3 : (k * W + d) / W = k := by
    rw [Nat.mul_comm k W, Nat.mul_add_div hW, Nat.div_eq_of_lt hd]; simp
  have h4 : (k * W + d) % W = d := by
    rw [Nat.mul_comm k W, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hd
  unfold sigRun
  simp only [hdiv, hmod]
  rw [if_neg (by omega), hu, h1, h2, h3, h4]
  simp [hk]

theorem completeness {W B : ℕ} {x w : List Bool} (hwf : cm.WF W)
    (hW : 2 * x.length + 1 + w.length + 2 * cm.c ≤ W)
    (hno : cm.NoOverflow W B (cm.initArr W x w))
    (hacc : cm.Accepts (cm.runA W (cm.initArr W x w) B).1
      (cm.runA W (cm.initArr W x w) B).2) :
    ∃ σ : ℕ → Bool, cm.Fam W B x σ := by
  have hc1 := hwf.hc1
  have hwc := hwf.hc
  have hW0 : 0 < W := by omega
  set a0 := cm.initArr W x w with ha0
  set σ := cm.sigRun W B a0 with hσdef
  have hQ := runA_q_lt cm hwf a0
  have hle := runA_cells_le cm hwf a0 (initArr_le cm hwf x w)
  have hσC : ∀ t q, q < cm.Q → (σ (cm.vC W t q) = true ↔ t ≤ B ∧ (cm.runA W a0 t).1 = q) := by
    intro t q hq
    rw [hσdef, sigRun_vC cm W B a0 t q hq]; simp
  have hσA : ∀ t k d a, k < cm.K → d < W → a ≤ cm.A →
      (σ (cm.vA W t k d a) = true ↔ t ≤ B ∧ (cm.runA W a0 t).2 k d = a) := by
    intro t k d a hk hd ha
    rw [hσdef, sigRun_vA cm W B a0 hW0 t k d a hk hd ha]; simp
  -- guard characterization
  have hguard : ∀ t, t ≤ B → ∀ q < cm.Q, ∀ p ∈ allPats cm.A (cm.K * cm.c),
      cm.Guard σ W t q p → (cm.runA W a0 t).1 = q ∧ p = cm.pat (cm.runA W a0 t).2 := by
    intro t ht q hq p hp hg
    refine ⟨((hσC t q hq).1 hg.1).2, ?_⟩
    rw [mem_allPats] at hp
    apply List.ext_getElem
    · simp [pat, hp.1]
    · intro i h1 h2
      have hi : i < cm.K * cm.c := by rw [← hp.1]; exact h1
      have hk : i / cm.c < cm.K := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; linarith
      have hd : i % cm.c < W := lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by have := hwf.hc; omega)
      have hpa : p.getD i 0 ≤ cm.A := hp.2 _ (by simp [List.getD_eq_getElem?_getD, h1])
      have := ((hσA t _ _ _ hk hd hpa).1 (hg.2 i hi)).2
      simp only [pat, List.getElem_map, List.getElem_range]
      rw [this]
      simp [List.getD_eq_getElem?_getD, h1]
  refine ⟨σ, ?_⟩
  refine
    { frameC := ?_, frameA := ?_, margin := ?_, initC := ?_, initX := ?_, initSep := ?_,
      initW := ?_, initContig := ?_, initO := ?_, stepC := ?_, stepA := ?_, acc := ?_ }
  · intro t ht
    refine ⟨⟨(cm.runA W a0 t).1, hQ t, (hσC t _ (hQ t)).2 ⟨ht, rfl⟩⟩, ?_⟩
    intro i hi j hj h1 h2
    have e1 := ((hσC t i hi).1 h1).2
    have e2 := ((hσC t j hj).1 h2).2
    omega
  · intro t ht k hk d hd
    refine ⟨⟨(cm.runA W a0 t).2 k d, by have := hle t k d; omega,
      (hσA t k d _ hk hd (hle t k d)).2 ⟨ht, rfl⟩⟩, ?_⟩
    intro i hi j hj h1 h2
    have e1 := ((hσA t k d i hk hd (by omega)).1 h1).2
    have e2 := ((hσA t k d j hk hd (by omega)).1 h2).2
    omega
  · intro t ht k hk i hi
    have := hno t ht k hk (W - 2 * cm.c + i) (by omega) (by omega)
    exact (hσA t k _ _ hk (by omega) le_rfl).2 ⟨ht, this⟩
  · exact (hσC 0 _ hwf.hq0).2 ⟨Nat.zero_le _, rfl⟩
  · -- initX
    intro i hi
    have hi2 : 2 * i + 1 < W := by omega
    have hi1 : 2 * i < W := by omega
    have hrun0 : (cm.runA W a0 0).2 = a0 := rfl
    constructor
    · refine (hσA 0 _ _ _ hwf.hkin hi1 (hwf.hin _).le).2 ⟨Nat.zero_le _, ?_⟩
      rw [hrun0, ha0]
      unfold initArr
      simp only [hwf.hkin, hi1, and_self, true_and, if_true, length_encodePair']
      rw [if_pos (by omega), encodePair_getD, if_pos (by omega), if_pos (by omega)]
    · refine (hσA 0 _ _ _ hwf.hkin hi2 (hwf.hin _).le).2 ⟨Nat.zero_le _, ?_⟩
      rw [hrun0, ha0]
      unfold initArr
      simp only [hwf.hkin, hi2, and_self, true_and, if_true, length_encodePair']
      rw [if_pos (by omega), encodePair_getD, if_pos (by omega), if_neg (by omega)]
      have : (2 * i + 1) / 2 = i := by omega
      rw [this]
  · -- initSep
    have hd : 2 * x.length < W := by omega
    have hrun0 : (cm.runA W a0 0).2 = a0 := rfl
    refine (hσA 0 _ _ _ hwf.hkin hd (hwf.hin _).le).2 ⟨Nat.zero_le _, ?_⟩
    rw [hrun0, ha0]
    unfold initArr
    simp only [hwf.hkin, hd, and_self, true_and, if_true, length_encodePair']
    rw [if_pos (by omega), encodePair_getD, if_neg (by omega), if_pos rfl]
  · -- initW
    intro d h1 h2
    have hrun0 : (cm.runA W a0 0).2 = a0 := rfl
    by_cases hlen : d < 2 * x.length + 1 + w.length
    · have hval : a0 cm.kin d = cm.inSym (w.getD (d - 2 * x.length - 1) false) := by
        rw [ha0]
        unfold initArr
        simp only [hwf.hkin, h2, and_self, true_and, if_true, length_encodePair']
        rw [if_pos hlen, encodePair_getD, if_neg (by omega), if_neg (by omega)]
      cases hb : w.getD (d - 2 * x.length - 1) false
      · left
        refine (hσA 0 _ _ _ hwf.hkin h2 (hwf.hin _).le).2 ⟨Nat.zero_le _, ?_⟩
        rw [hrun0, hval, hb]
      · right; left
        refine (hσA 0 _ _ _ hwf.hkin h2 (hwf.hin _).le).2 ⟨Nat.zero_le _, ?_⟩
        rw [hrun0, hval, hb]
    · right; right
      refine (hσA 0 _ _ _ hwf.hkin h2 le_rfl).2 ⟨Nat.zero_le _, ?_⟩
      rw [hrun0, ha0]
      unfold initArr
      simp only [hwf.hkin, h2, and_self, true_and, if_true, length_encodePair']
      rw [if_neg hlen]
  · -- initContig
    intro d h1 h2 hd
    have hrun0 : (cm.runA W a0 0).2 = a0 := rfl
    have hd' : d < W := by omega
    have e1 := ((hσA 0 _ _ _ hwf.hkin hd' le_rfl).1 hd).2
    rw [hrun0, ha0] at e1
    unfold initArr at e1
    simp only [hwf.hkin, hd', and_self, true_and, if_true, length_encodePair'] at e1
    have hlen : ¬ d < 2 * x.length + 1 + w.length := by
      intro hl
      rw [if_pos hl] at e1
      have := hwf.hin (((encodePair (x, w)).getD d false))
      omega
    refine (hσA 0 _ _ _ hwf.hkin h2 le_rfl).2 ⟨Nat.zero_le _, ?_⟩
    rw [hrun0, ha0]
    unfold initArr
    simp only [hwf.hkin, h2, and_self, true_and, if_true, length_encodePair']
    rw [if_neg (by omega)]
  · -- initO
    intro k hk hne d hd
    have hrun0 : (cm.runA W a0 0).2 = a0 := rfl
    refine (hσA 0 k d _ hk hd le_rfl).2 ⟨Nat.zero_le _, ?_⟩
    rw [hrun0, ha0]
    unfold initArr
    simp [hne]
  · -- stepC
    intro t ht q hq p hp hg
    have hq' := hguard t ht.le q hq p hp hg
    obtain ⟨hqq, hpp⟩ := hq'
    have hstep : (cm.runA W a0 (t + 1)).1 = (cm.δ q p).1 := by
      simp only [runA, stepA]
      rw [hqq, ← hpp]
    exact (hσC (t + 1) _ (hwf.hδq q hq p)).2 ⟨ht, hstep⟩
  · -- stepA
    intro t ht q hq p hp hg k hk d hdc
    obtain ⟨hqq, hpp⟩ := hguard t ht.le q hq p hp hg
    have hd : d < W := by omega
    have hcell : (cm.runA W a0 (t + 1)).2 k d =
        cm.newCell W (cm.eff q p k) (cm.runA W a0 t).2 k d := by
      simp only [runA, stepA]
      rw [hqq, ← hpp]
    constructor
    · intro hlen
      have hmem : (cm.eff q p k).2.getD d 0 ∈ (cm.eff q p k).2 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
        exact List.getElem_mem hlen
      have hs := hwf.hδs q p k _ hmem
      refine (hσA (t + 1) k d _ hk hd hs.le).2 ⟨ht, ?_⟩
      rw [hcell]
      unfold newCell
      simp [hk, hd, hlen, List.getD_eq_getElem?_getD]
    · intro hlen a ha hσa
      have hj := (hwf.hδj q p k).1
      have hsW : d - (cm.eff q p k).2.length + (cm.eff q p k).1 < W := by omega
      have e1 := ((hσA t k _ a hk hsW ha).1 hσa).2
      refine (hσA (t + 1) k d a hk hd ha).2 ⟨ht, ?_⟩
      rw [hcell]
      unfold newCell
      simp only [hk, hd, and_self, if_true]
      rw [dif_neg (by omega), if_pos hsW]
      exact e1
  · -- acc
    obtain ⟨h1, h2, h3⟩ := hacc
    have hk := hwf.hkout
    refine ⟨(cm.runA W a0 B).1, hQ B, h1, (hσC B _ (hQ B)).2 ⟨le_rfl, rfl⟩, ?_, ?_⟩
    · exact (hσA B _ 0 _ hk hW0 hwf.houtT).2 ⟨le_rfl, h2⟩
    · exact (hσA B _ 1 _ hk (by omega) le_rfl).2 ⟨le_rfl, h3⟩

end CM

end CL
end SATurday.Bridge
