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

/-! ## Satisfaction of constraint lists -/

/-- All formulas in the list are true under `σ`. -/
def SatL (σ : ℕ → Bool) (l : List PropFormula) : Prop := ∀ φ ∈ l, PropFormula.eval σ φ = true

theorem SatL_append {σ : ℕ → Bool} {a b : List PropFormula} :
    SatL σ (a ++ b) ↔ SatL σ a ∧ SatL σ b := by
  simp [SatL, or_imp, forall_and]

theorem SatL_flatMap {σ : ℕ → Bool} {α : Type} (l : List α) (f : α → List PropFormula) :
    SatL σ (l.flatMap f) ↔ ∀ a ∈ l, SatL σ (f a) := by
  simp only [SatL, List.mem_flatMap]
  constructor
  · intro h a ha φ hφ; exact h φ ⟨a, ha, hφ⟩
  · rintro h φ ⟨a, ha, hφ⟩; exact h a ha φ hφ

theorem SatL_nil {σ : ℕ → Bool} : SatL σ [] := by simp [SatL]

theorem SatL_cons {σ : ℕ → Bool} {φ : PropFormula} {l : List PropFormula} :
    SatL σ (φ :: l) ↔ PropFormula.eval σ φ = true ∧ SatL σ l := by
  simp [SatL]

/-- Instantiate a template list. -/
def instL (V : ℕ → ℕ → ℕ) (l : List TF) : List PropFormula := l.map (TF.inst V)

theorem SatL_instL {σ : ℕ → Bool} {V : ℕ → ℕ → ℕ} {l : List TF} :
    SatL σ (instL V l) ↔ ∀ φ ∈ l, TF.holds σ V φ := by
  simp [SatL, instL, TF.holds]

theorem holds_exactlyOne {σ : ℕ → Bool} {V : ℕ → ℕ → ℕ} (r n : ℕ) :
    TF.holds σ V (exactlyOne r (List.range n)) ↔
      ExactlyOne (fun i => σ (V r i)) n := by
  unfold exactlyOne ExactlyOne
  simp only [TF.holds_and, holds_disjT, holds_conjT, List.mem_map, List.mem_range,
    List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨⟨φ, ⟨o, ho, rfl⟩, h⟩, hu⟩
    refine ⟨⟨o, ho, by simpa using h⟩, ?_⟩
    intro i hi j hj hi' hj'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := hu (.not (.and (.leaf r i) (.leaf r j))) ⟨i, hi, j, hj, by simp [hlt]⟩
      simp at this
      have h3 := this hi'
      simp [hj'] at h3
    · have := hu (.not (.and (.leaf r j) (.leaf r i))) ⟨j, hj, i, hi, by simp [hlt]⟩
      simp at this
      have h3 := this hj'
      simp [hi'] at h3
  · rintro ⟨⟨o, ho, h⟩, hu⟩
    refine ⟨⟨_, ⟨o, ho, rfl⟩, by simpa using h⟩, ?_⟩
    rintro φ ⟨o1, ho1, o2, ho2, hφ⟩
    split_ifs at hφ with hlt
    · simp only [Option.some.injEq] at hφ
      subst hφ
      simp only [TF.holds_not, TF.holds_and, TF.holds_leaf]
      rintro ⟨h1, h2⟩
      have := hu o1 ho1 o2 ho2 h1 h2
      omega

/-! ## Templates, register valuations and the constraint list -/

namespace CM

variable (cm : CM)

/-- Register values for the template at time `t`, stack `k`, depth offset `dOff`. -/
def valF (W t k dOff r : ℕ) : ℕ :=
  if r = 0 then t * cm.Fr W
  else if r ≤ cm.K then cm.vA W t (r - 1) 0 0
  else if r = cm.K + 1 then (t + 1) * cm.Fr W
  else if r ≤ 2 * cm.K + 1 then cm.vA W (t + 1) (r - cm.K - 2) 0 0
  else if r = 2 * cm.K + 2 then cm.vA W t k dOff 0
  else if r = 2 * cm.K + 3 then cm.vA W (t + 1) k dOff 0
  else 0

/-- Variable naming for templates. -/
def Vf (W t k dOff : ℕ) : ℕ → ℕ → ℕ := fun r o => cm.valF W t k dOff r + o

theorem vA_shift (W t k d e a : ℕ) :
    cm.vA W t k (d + e) a = cm.vA W t k d 0 + e * (cm.A + 1) + a := by
  unfold vA; ring

theorem vA_zero_add (W t k d a : ℕ) : cm.vA W t k d a = cm.vA W t k d 0 + a := by
  unfold vA; ring

theorem vA_base (W t k d a : ℕ) :
    cm.vA W t k d a = cm.vA W t k 0 0 + d * (cm.A + 1) + a := by
  unfold vA; ring

theorem Vf_C0 (W t k dOff o : ℕ) : cm.Vf W t k dOff 0 o = cm.vC W t o := by
  simp [Vf, valF, vC]

theorem Vf_C1 (W t k dOff o : ℕ) : cm.Vf W t k dOff (cm.K + 1) o = cm.vC W (t + 1) o := by
  simp [Vf, valF, vC]

theorem Vf_S (W t k dOff k' o : ℕ) (hk : k' < cm.K) :
    cm.Vf W t k dOff (1 + k') o = cm.vA W t k' 0 0 + o := by
  have h1 : 1 + k' ≠ 0 := by omega
  have h2 : 1 + k' ≤ cm.K := by omega
  simp [Vf, valF, h1, h2]

theorem Vf_S' (W t k dOff k' o : ℕ) (hk : k' < cm.K) :
    cm.Vf W t k dOff (cm.K + 2 + k') o = cm.vA W (t + 1) k' 0 0 + o := by
  have h1 : cm.K + 2 + k' ≠ 0 := by omega
  have h2 : ¬ cm.K + 2 + k' ≤ cm.K := by omega
  have h3 : cm.K + 2 + k' ≠ cm.K + 1 := by omega
  have h4 : cm.K + 2 + k' ≤ 2 * cm.K + 1 := by omega
  simp [Vf, valF, h1, h2, h3, h4]
  congr 2; omega

theorem Vf_D (W t k dOff o : ℕ) :
    cm.Vf W t k dOff (2 * cm.K + 2) o = cm.vA W t k dOff 0 + o := by
  have h1 : 2 * cm.K + 2 ≠ 0 := by omega
  have h2 : ¬ 2 * cm.K + 2 ≤ cm.K := by omega
  have h3 : 2 * cm.K + 2 ≠ cm.K + 1 := by omega
  have h4 : ¬ 2 * cm.K + 2 ≤ 2 * cm.K + 1 := by omega
  simp [Vf, valF, h1, h2, h3, h4]

theorem Vf_D' (W t k dOff o : ℕ) :
    cm.Vf W t k dOff (2 * cm.K + 3) o = cm.vA W (t + 1) k dOff 0 + o := by
  have h1 : 2 * cm.K + 3 ≠ 0 := by omega
  have h2 : ¬ 2 * cm.K + 3 ≤ cm.K := by omega
  have h3 : 2 * cm.K + 3 ≠ cm.K + 1 := by omega
  have h4 : ¬ 2 * cm.K + 3 ≤ 2 * cm.K + 1 := by omega
  have h5 : 2 * cm.K + 3 ≠ 2 * cm.K + 2 := by omega
  simp [Vf, valF, h1, h2, h3, h4, h5]

/-- All (control, window) cases. -/
def casesL : List (ℕ × List ℕ) :=
  (List.range cm.Q).flatMap fun q => (allPats cm.A (cm.K * cm.c)).map fun p => (q, p)

theorem mem_casesL {q : ℕ} {p : List ℕ} :
    (q, p) ∈ cm.casesL ↔ q < cm.Q ∧ p ∈ allPats cm.A (cm.K * cm.c) := by
  simp [casesL]

/-- Template of the guard of a case. -/
def guardT (q : ℕ) (p : List ℕ) : List TF :=
  TF.leaf 0 q :: (List.range (cm.K * cm.c)).map fun i =>
    TF.leaf (1 + i / cm.c) ((i % cm.c) * (cm.A + 1) + p.getD i 0)

/-- Control update constraints for one time step. -/
def stepCtlT : List TF :=
  cm.casesL.map fun qp =>
    impT (conjT (cm.guardT qp.1 qp.2)) (TF.leaf (cm.K + 1) (cm.δ qp.1 qp.2).1)

/-- Cell update constraints at a literal top depth `d < c`. -/
def topT (k d : ℕ) : List TF :=
  cm.casesL.flatMap fun qp =>
    if d < (cm.eff qp.1 qp.2 k).2.length then
      [impT (conjT (cm.guardT qp.1 qp.2))
        (TF.leaf (cm.K + 2 + k) (d * (cm.A + 1) + (cm.eff qp.1 qp.2 k).2.getD d 0))]
    else
      (List.range (cm.A + 1)).map fun a =>
        impT (conjT (cm.guardT qp.1 qp.2 ++
          [TF.leaf (1 + k) ((d - (cm.eff qp.1 qp.2 k).2.length + (cm.eff qp.1 qp.2 k).1) *
            (cm.A + 1) + a)]))
          (TF.leaf (cm.K + 2 + k) (d * (cm.A + 1) + a))

/-- Cell update constraints at depth `c + e` (register `D` at depth offset `e`). -/
def deepT (k : ℕ) : List TF :=
  cm.casesL.flatMap fun qp =>
    (List.range (cm.A + 1)).map fun a =>
      impT (conjT (cm.guardT qp.1 qp.2 ++
        [TF.leaf (2 * cm.K + 2) ((cm.c - (cm.eff qp.1 qp.2 k).2.length +
          (cm.eff qp.1 qp.2 k).1) * (cm.A + 1) + a)]))
        (TF.leaf (2 * cm.K + 3) (cm.c * (cm.A + 1) + a))

/-- Initial constraints. -/
def initL (W : ℕ) (x : List Bool) : List PropFormula :=
  instL (cm.Vf W 0 0 0) [TF.leaf 0 cm.q0] ++
  (List.range x.length).flatMap (fun i =>
    instL (cm.Vf W 0 cm.kin (2 * i))
      [TF.leaf (2 * cm.K + 2) (cm.inSym true),
       TF.leaf (2 * cm.K + 2) ((cm.A + 1) + cm.inSym (x.getD i false))]) ++
  instL (cm.Vf W 0 cm.kin (2 * x.length)) [TF.leaf (2 * cm.K + 2) (cm.inSym false)] ++
  (List.range (W - (2 * x.length + 1))).flatMap (fun e =>
    instL (cm.Vf W 0 cm.kin (2 * x.length + 1 + e))
      [TF.or (TF.leaf (2 * cm.K + 2) (cm.inSym false))
        (TF.or (TF.leaf (2 * cm.K + 2) (cm.inSym true)) (TF.leaf (2 * cm.K + 2) cm.A))]) ++
  (List.range (W - (2 * x.length + 2))).flatMap (fun e =>
    instL (cm.Vf W 0 cm.kin (2 * x.length + 1 + e))
      [impT (TF.leaf (2 * cm.K + 2) cm.A) (TF.leaf (2 * cm.K + 2) ((cm.A + 1) + cm.A))]) ++
  (List.range cm.K).flatMap (fun k =>
    if k = cm.kin then [] else
      (List.range W).flatMap fun d =>
        instL (cm.Vf W 0 k d) [TF.leaf (2 * cm.K + 2) cm.A])

/-- Per frame constraints for times `0 .. B`. -/
def frameL (W B : ℕ) : List PropFormula :=
  (List.range (B + 1)).flatMap fun t =>
    instL (cm.Vf W t 0 0) [exactlyOne 0 (List.range cm.Q)] ++
    (List.range cm.K).flatMap (fun k =>
      (List.range W).flatMap fun d =>
        instL (cm.Vf W t k d) [exactlyOne (2 * cm.K + 2) (List.range (cm.A + 1))]) ++
    (List.range cm.K).flatMap (fun k =>
      instL (cm.Vf W t k (W - 2 * cm.c))
        ((List.range (2 * cm.c)).map fun i => TF.leaf (2 * cm.K + 2) (i * (cm.A + 1) + cm.A)))

/-- Step constraints for times `0 .. B-1`. -/
def stepL (W B : ℕ) : List PropFormula :=
  (List.range B).flatMap fun t =>
    instL (cm.Vf W t 0 0) cm.stepCtlT ++
    (List.range cm.K).flatMap (fun k =>
      (List.range cm.c).flatMap (fun d => instL (cm.Vf W t k 0) (cm.topT k d)) ++
      (List.range (W - 2 * cm.c)).flatMap (fun e => instL (cm.Vf W t k e) (cm.deepT k)))

/-- Acceptance constraints at time `B`. -/
def accL (W B : ℕ) : List PropFormula :=
  instL (cm.Vf W B cm.kout 0)
    [disjT (((List.range cm.Q).filter fun q => cm.halt q).map fun q => TF.leaf 0 q),
     TF.leaf (1 + cm.kout) cm.outTrue,
     TF.leaf (1 + cm.kout) ((cm.A + 1) + cm.A)]

/-- The full list of tableau constraints. -/
def consL (W B : ℕ) (x : List Bool) : List PropFormula :=
  cm.initL W x ++ cm.frameL W B ++ cm.stepL W B ++ cm.accL W B

theorem sat_acc {σ : ℕ → Bool} {W B : ℕ} (hk : cm.kout < cm.K) :
    SatL σ (cm.accL W B) ↔
      (∃ q < cm.Q, cm.halt q = true ∧ σ (cm.vC W B q) = true) ∧
      σ (cm.vA W B cm.kout 0 cm.outTrue) = true ∧ σ (cm.vA W B cm.kout 1 cm.A) = true := by
  unfold accL
  rw [SatL_instL]
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    holds_disjT, TF.holds_leaf, List.mem_map, List.mem_filter, List.mem_range]
  rw [Vf_S cm W B cm.kout 0 cm.kout _ hk, Vf_S cm W B cm.kout 0 cm.kout _ hk]
  have e1 : cm.vA W B cm.kout 0 0 + cm.outTrue = cm.vA W B cm.kout 0 cm.outTrue :=
    (cm.vA_zero_add W B cm.kout 0 cm.outTrue).symm
  have e2 : cm.vA W B cm.kout 0 0 + ((cm.A + 1) + cm.A) = cm.vA W B cm.kout 1 cm.A := by
    rw [cm.vA_base W B cm.kout 1 cm.A]; ring
  rw [e1, e2]
  constructor
  · rintro ⟨⟨φ, ⟨q, ⟨hq, hh⟩, rfl⟩, h⟩, h2, h3⟩
    exact ⟨⟨q, hq, hh, by simpa [Vf_C0] using h⟩, h2, h3⟩
  · rintro ⟨⟨q, hq, hh, h⟩, h2, h3⟩
    exact ⟨⟨_, ⟨q, ⟨hq, hh⟩, rfl⟩, by simpa [Vf_C0] using h⟩, h2, h3⟩

theorem sat_frame {σ : ℕ → Bool} {W B : ℕ} :
    SatL σ (cm.frameL W B) ↔
      (∀ t ≤ B, ExactlyOne (fun q => σ (cm.vC W t q)) cm.Q) ∧
      (∀ t ≤ B, ∀ k < cm.K, ∀ d < W, ExactlyOne (fun a => σ (cm.vA W t k d a)) (cm.A + 1)) ∧
      (∀ t ≤ B, ∀ k < cm.K, ∀ i < 2 * cm.c,
        σ (cm.vA W t k (W - 2 * cm.c + i) cm.A) = true) := by
  unfold frameL
  rw [SatL_flatMap]
  have key : ∀ t, SatL σ (instL (cm.Vf W t 0 0) [exactlyOne 0 (List.range cm.Q)] ++
      (List.range cm.K).flatMap (fun k =>
        (List.range W).flatMap fun d =>
          instL (cm.Vf W t k d) [exactlyOne (2 * cm.K + 2) (List.range (cm.A + 1))]) ++
      (List.range cm.K).flatMap (fun k =>
        instL (cm.Vf W t k (W - 2 * cm.c))
          ((List.range (2 * cm.c)).map fun i =>
            TF.leaf (2 * cm.K + 2) (i * (cm.A + 1) + cm.A)))) ↔
      (ExactlyOne (fun q => σ (cm.vC W t q)) cm.Q ∧
      (∀ k < cm.K, ∀ d < W, ExactlyOne (fun a => σ (cm.vA W t k d a)) (cm.A + 1)) ∧
      (∀ k < cm.K, ∀ i < 2 * cm.c, σ (cm.vA W t k (W - 2 * cm.c + i) cm.A) = true)) := by
    intro t
    rw [SatL_append, SatL_append, SatL_instL, SatL_flatMap, SatL_flatMap]
    simp only [List.mem_singleton, forall_eq, holds_exactlyOne, SatL_flatMap, SatL_instL,
      List.mem_range, List.forall_mem_map, and_assoc]
    have e1 : (fun i => σ (cm.Vf W t 0 0 0 i)) = fun q => σ (cm.vC W t q) := by
      funext i; rw [Vf_C0]
    have e2 : ∀ k d, (fun i => σ (cm.Vf W t k d (2 * cm.K + 2) i)) =
        fun a => σ (cm.vA W t k d a) := by
      intro k d; funext i; rw [Vf_D, ← vA_zero_add]
    have e3 : ∀ k j, σ (cm.Vf W t k (W - 2 * cm.c) (2 * cm.K + 2) (j * (cm.A + 1) + cm.A)) =
        σ (cm.vA W t k (W - 2 * cm.c + j) cm.A) := by
      intro k j; rw [Vf_D, vA_shift, Nat.add_assoc]
    simp only [TF.holds_leaf, e1, e2, e3]
  constructor
  · intro h
    refine ⟨fun t ht => ((key t).1 (h t (by simpa [Nat.lt_succ_iff] using ht))).1,
      fun t ht => ((key t).1 (h t (by simpa [Nat.lt_succ_iff] using ht))).2.1,
      fun t ht => ((key t).1 (h t (by simpa [Nat.lt_succ_iff] using ht))).2.2⟩
  · rintro ⟨h1, h2, h3⟩ t ht
    have ht' : t ≤ B := by simpa [Nat.lt_succ_iff] using ht
    exact (key t).2 ⟨h1 t ht', h2 t ht', h3 t ht'⟩

theorem sat_init {σ : ℕ → Bool} {W : ℕ} {x : List Bool} (hk : cm.kin < cm.K)
    (hW : 2 * x.length + 1 ≤ W) :
    SatL σ (cm.initL W x) ↔
      σ (cm.vC W 0 cm.q0) = true ∧
      (∀ i < x.length,
        σ (cm.vA W 0 cm.kin (2 * i) (cm.inSym true)) = true ∧
        σ (cm.vA W 0 cm.kin (2 * i + 1) (cm.inSym (x.getD i false))) = true) ∧
      σ (cm.vA W 0 cm.kin (2 * x.length) (cm.inSym false)) = true ∧
      (∀ d, 2 * x.length + 1 ≤ d → d < W →
        (σ (cm.vA W 0 cm.kin d (cm.inSym false)) = true ∨
          σ (cm.vA W 0 cm.kin d (cm.inSym true)) = true ∨
          σ (cm.vA W 0 cm.kin d cm.A) = true)) ∧
      (∀ d, 2 * x.length + 1 ≤ d → d + 1 < W →
        σ (cm.vA W 0 cm.kin d cm.A) = true → σ (cm.vA W 0 cm.kin (d + 1) cm.A) = true) ∧
      (∀ k < cm.K, k ≠ cm.kin → ∀ d < W, σ (cm.vA W 0 k d cm.A) = true) := by
  unfold initL
  simp only [SatL_append, SatL_flatMap, SatL_instL, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, TF.holds_leaf, TF.holds_or,
    holds_impT]
  have hD : ∀ d o, cm.Vf W 0 cm.kin d (2 * cm.K + 2) o = cm.vA W 0 cm.kin d 0 + o :=
    fun d o => Vf_D cm W 0 cm.kin d o
  simp only [Vf_C0, hD]
  have hz : ∀ d a, cm.vA W 0 cm.kin d 0 + a = cm.vA W 0 cm.kin d a :=
    fun d a => (cm.vA_zero_add W 0 cm.kin d a).symm
  have hs1 : ∀ d a, cm.vA W 0 cm.kin d (cm.A + 1 + a) = cm.vA W 0 cm.kin (d + 1) a := by
    intro d a; rw [vA_zero_add, vA_zero_add cm W 0 cm.kin (d + 1) a, vA_shift]; ring
  simp only [hz, hs1]
  have hif : ∀ a < cm.K, SatL σ (if a = cm.kin then [] else
      List.flatMap (fun d => instL (cm.Vf W 0 a d) [TF.leaf (2 * cm.K + 2) cm.A])
        (List.range W)) ↔ (a ≠ cm.kin → ∀ d < W, σ (cm.vA W 0 a d cm.A) = true) := by
    intro a _
    by_cases ha : a = cm.kin
    · simp [ha, SatL_nil]
    · rw [if_neg ha, SatL_flatMap]
      simp only [List.mem_range, SatL_instL, List.mem_singleton, forall_eq, TF.holds_leaf,
        Vf_D]
      simp only [ne_eq, ha, not_false_eq_true, forall_const]
      constructor <;> intro h d hd <;> have := h d hd <;> simpa [hz] using this
  have hsh : ∀ P : ℕ → Prop, (∀ a < W - (2 * x.length + 1), P (2 * x.length + 1 + a)) ↔
      (∀ d, 2 * x.length + 1 ≤ d → d < W → P d) := by
    intro P
    constructor
    · intro h d h1 h2
      obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h1
      exact h e (by omega)
    · intro h a ha
      exact h _ (by omega) (by omega)
  have hsh2 : ∀ P : ℕ → Prop, (∀ a < W - (2 * x.length + 2), P (2 * x.length + 1 + a)) ↔
      (∀ d, 2 * x.length + 1 ≤ d → d + 1 < W → P d) := by
    intro P
    constructor
    · intro h d h1 h2
      obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h1
      exact h e (by omega)
    · intro h a ha
      exact h _ (by omega) (by omega)
  rw [hsh (fun d => σ (cm.vA W 0 cm.kin d (cm.inSym false)) = true ∨
      σ (cm.vA W 0 cm.kin d (cm.inSym true)) = true ∨ σ (cm.vA W 0 cm.kin d cm.A) = true),
    hsh2 (fun d => σ (cm.vA W 0 cm.kin d cm.A) = true →
      σ (cm.vA W 0 cm.kin (d + 1) cm.A) = true)]
  rw [show (∀ a < cm.K, SatL σ (if a = cm.kin then [] else
      List.flatMap (fun d => instL (cm.Vf W 0 a d) [TF.leaf (2 * cm.K + 2) cm.A])
        (List.range W))) ↔ (∀ a < cm.K, a ≠ cm.kin → ∀ d < W, σ (cm.vA W 0 a d cm.A) = true) from
    forall_congr' fun a => forall_congr' fun ha => hif a ha]
  simp only [and_assoc]

/-- The cell update clause of one case at `(t, k, d)`. -/
def Clause (σ : ℕ → Bool) (W t : ℕ) (q : ℕ) (p : List ℕ) (k d : ℕ) : Prop :=
  (d < (cm.eff q p k).2.length →
    σ (cm.vA W (t + 1) k d ((cm.eff q p k).2.getD d 0)) = true) ∧
  ((cm.eff q p k).2.length ≤ d →
    ∀ a ≤ cm.A,
      σ (cm.vA W t k (d - (cm.eff q p k).2.length + (cm.eff q p k).1) a) = true →
      σ (cm.vA W (t + 1) k d a) = true)

theorem leaf_C0 {σ : ℕ → Bool} {W t k dOff : ℕ} (q : ℕ) :
    TF.holds σ (cm.Vf W t k dOff) (TF.leaf 0 q) ↔ σ (cm.vC W t q) = true := by
  rw [TF.holds_leaf, Vf_C0]

theorem leaf_C1 {σ : ℕ → Bool} {W t k dOff : ℕ} (q : ℕ) :
    TF.holds σ (cm.Vf W t k dOff) (TF.leaf (cm.K + 1) q) ↔ σ (cm.vC W (t + 1) q) = true := by
  rw [TF.holds_leaf, Vf_C1]

theorem leaf_S {σ : ℕ → Bool} {W t k dOff : ℕ} {k' : ℕ} (hk' : k' < cm.K) (d a : ℕ) :
    TF.holds σ (cm.Vf W t k dOff) (TF.leaf (1 + k') (d * (cm.A + 1) + a)) ↔
      σ (cm.vA W t k' d a) = true := by
  have h : cm.vA W t k' 0 0 + (d * (cm.A + 1) + a) = cm.vA W t k' d a := by
    rw [vA_base cm W t k' d a, Nat.add_assoc]
  rw [TF.holds_leaf, Vf_S cm W t k dOff k' _ hk', h]

theorem leaf_S' {σ : ℕ → Bool} {W t k dOff : ℕ} {k' : ℕ} (hk' : k' < cm.K) (d a : ℕ) :
    TF.holds σ (cm.Vf W t k dOff) (TF.leaf (cm.K + 2 + k') (d * (cm.A + 1) + a)) ↔
      σ (cm.vA W (t + 1) k' d a) = true := by
  have h : cm.vA W (t + 1) k' 0 0 + (d * (cm.A + 1) + a) = cm.vA W (t + 1) k' d a := by
    rw [vA_base cm W (t + 1) k' d a, Nat.add_assoc]
  rw [TF.holds_leaf, Vf_S' cm W t k dOff k' _ hk', h]

theorem leaf_D {σ : ℕ → Bool} {W t k dOff : ℕ} (e a : ℕ) :
    TF.holds σ (cm.Vf W t k dOff) (TF.leaf (2 * cm.K + 2) (e * (cm.A + 1) + a)) ↔
      σ (cm.vA W t k (dOff + e) a) = true := by
  rw [TF.holds_leaf, Vf_D, vA_shift, Nat.add_assoc]

theorem leaf_D' {σ : ℕ → Bool} {W t k dOff : ℕ} (e a : ℕ) :
    TF.holds σ (cm.Vf W t k dOff) (TF.leaf (2 * cm.K + 3) (e * (cm.A + 1) + a)) ↔
      σ (cm.vA W (t + 1) k (dOff + e) a) = true := by
  rw [TF.holds_leaf, Vf_D', vA_shift, Nat.add_assoc]

theorem holds_guardT {σ : ℕ → Bool} {W t k dOff : ℕ} (hc : 0 < cm.c) (q : ℕ) (p : List ℕ) :
    TF.holds σ (cm.Vf W t k dOff) (conjT (cm.guardT q p)) ↔ cm.Guard σ W t q p := by
  rw [holds_conjT]
  unfold guardT Guard
  simp only [List.mem_cons, forall_eq_or_imp, List.mem_map, List.mem_range,
    forall_exists_index, and_imp]
  rw [leaf_C0]
  apply and_congr Iff.rfl
  constructor
  · intro h i hi
    have hk : i / cm.c < cm.K := by
      rw [Nat.div_lt_iff_lt_mul hc]; linarith
    exact (leaf_S cm hk _ _).1 (h _ i hi rfl)
  · intro h φ i hi hφ
    subst hφ
    have hk : i / cm.c < cm.K := by
      rw [Nat.div_lt_iff_lt_mul hc]; linarith
    exact (leaf_S cm hk _ _).2 (h i hi)

theorem holds_conjT_append_leaf {σ : ℕ → Bool} {V : ℕ → ℕ → ℕ} (l : List TF) (x : TF) :
    TF.holds σ V (conjT (l ++ [x])) ↔ TF.holds σ V (conjT l) ∧ TF.holds σ V x := by
  rw [holds_conjT, holds_conjT]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · intro h; exact ⟨fun φ hφ => h φ (Or.inl hφ), h x (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩ φ (hφ | rfl)
    · exact h1 φ hφ
    · exact h2

theorem holds_stepCtlT {σ : ℕ → Bool} {W t : ℕ} (hc : 0 < cm.c) :
    (∀ φ ∈ cm.stepCtlT, TF.holds σ (cm.Vf W t 0 0) φ) ↔
      ∀ q < cm.Q, ∀ p ∈ allPats cm.A (cm.K * cm.c),
        cm.Guard σ W t q p → σ (cm.vC W (t + 1) (cm.δ q p).1) = true := by
  unfold stepCtlT
  simp only [List.forall_mem_map, holds_impT, holds_guardT cm hc, leaf_C1]
  constructor
  · intro h q hq p hp
    exact h (q, p) ((mem_casesL cm).2 ⟨hq, hp⟩)
  · rintro h ⟨q, p⟩ hqp
    obtain ⟨hq, hp⟩ := (mem_casesL cm).1 hqp
    exact h q hq p hp

theorem forall_mem_flatMap' {α β : Type} (l : List α) (f : α → List β) (P : β → Prop) :
    (∀ φ ∈ l.flatMap f, P φ) ↔ ∀ a ∈ l, ∀ φ ∈ f a, P φ := by
  simp only [List.mem_flatMap]
  constructor
  · intro h a ha φ hφ; exact h φ ⟨a, ha, hφ⟩
  · rintro h φ ⟨a, ha, hφ⟩; exact h a ha φ hφ

theorem holds_topT_case {σ : ℕ → Bool} {W t k d : ℕ} (hc : 0 < cm.c) (hk : k < cm.K)
    (q : ℕ) (p : List ℕ) :
    (∀ φ ∈ (if d < (cm.eff q p k).2.length then
      [impT (conjT (cm.guardT q p))
        (TF.leaf (cm.K + 2 + k) (d * (cm.A + 1) + (cm.eff q p k).2.getD d 0))]
      else
      (List.range (cm.A + 1)).map fun a =>
        impT (conjT (cm.guardT q p ++
          [TF.leaf (1 + k) ((d - (cm.eff q p k).2.length + (cm.eff q p k).1) *
            (cm.A + 1) + a)]))
          (TF.leaf (cm.K + 2 + k) (d * (cm.A + 1) + a))),
        TF.holds σ (cm.Vf W t k 0) φ) ↔
      (cm.Guard σ W t q p → cm.Clause σ W t q p k d) := by
  unfold Clause
  by_cases hlen : d < (cm.eff q p k).2.length
  · rw [if_pos hlen]
    simp only [List.mem_singleton, forall_eq, holds_impT, holds_guardT cm hc, leaf_S' cm hk]
    constructor
    · intro h hg; exact ⟨fun _ => h hg, fun h' => absurd hlen (by omega)⟩
    · intro h hg; exact (h hg).1 hlen
  · rw [if_neg hlen]
    simp only [List.forall_mem_map, List.mem_range, holds_impT, holds_conjT_append_leaf,
      holds_guardT cm hc, leaf_S cm hk, leaf_S' cm hk]
    constructor
    · intro h hg
      refine ⟨fun h' => absurd h' hlen, ?_⟩
      intro _ a ha hsrc
      exact h a (by omega) ⟨hg, hsrc⟩
    · intro h a ha ⟨hg, hsrc⟩
      exact (h hg).2 (by omega) a (by omega) hsrc

theorem holds_topT {σ : ℕ → Bool} {W t k d : ℕ} (hc : 0 < cm.c) (hk : k < cm.K) :
    (∀ φ ∈ cm.topT k d, TF.holds σ (cm.Vf W t k 0) φ) ↔
      ∀ q < cm.Q, ∀ p ∈ allPats cm.A (cm.K * cm.c),
        cm.Guard σ W t q p → cm.Clause σ W t q p k d := by
  unfold topT
  rw [forall_mem_flatMap']
  constructor
  · intro h q hq p hp
    exact (holds_topT_case cm hc hk q p).1 (h (q, p) ((mem_casesL cm).2 ⟨hq, hp⟩))
  · rintro h ⟨q, p⟩ hqp
    obtain ⟨hq, hp⟩ := (mem_casesL cm).1 hqp
    exact (holds_topT_case cm hc hk q p).2 (h q hq p hp)

theorem holds_deepT_case {σ : ℕ → Bool} {W t k e : ℕ} (hc : 0 < cm.c)
    (q : ℕ) (p : List ℕ) (hlen : (cm.eff q p k).2.length ≤ cm.c) :
    (∀ φ ∈ (List.range (cm.A + 1)).map (fun a =>
        impT (conjT (cm.guardT q p ++
          [TF.leaf (2 * cm.K + 2) ((cm.c - (cm.eff q p k).2.length + (cm.eff q p k).1) *
            (cm.A + 1) + a)]))
          (TF.leaf (2 * cm.K + 3) (cm.c * (cm.A + 1) + a))),
        TF.holds σ (cm.Vf W t k e) φ) ↔
      (cm.Guard σ W t q p → cm.Clause σ W t q p k (cm.c + e)) := by
  unfold Clause
  simp only [List.forall_mem_map, List.mem_range, holds_impT, holds_conjT_append_leaf,
    holds_guardT cm hc, leaf_D, leaf_D']
  have e1 : e + (cm.c - (cm.eff q p k).2.length + (cm.eff q p k).1) =
      cm.c + e - (cm.eff q p k).2.length + (cm.eff q p k).1 := by omega
  have e2 : e + cm.c = cm.c + e := by omega
  rw [e1, e2]
  constructor
  · intro h hg
    refine ⟨fun h' => absurd h' (by omega), ?_⟩
    intro _ a ha hsrc
    exact h a (by omega) ⟨hg, hsrc⟩
  · intro h a ha ⟨hg, hsrc⟩
    exact (h hg).2 (by omega) a (by omega) hsrc

theorem holds_deepT (hwf : cm.WF W) {σ : ℕ → Bool} {t k e : ℕ} (hc : 0 < cm.c) :
    (∀ φ ∈ cm.deepT k, TF.holds σ (cm.Vf W t k e) φ) ↔
      ∀ q < cm.Q, ∀ p ∈ allPats cm.A (cm.K * cm.c),
        cm.Guard σ W t q p → cm.Clause σ W t q p k (cm.c + e) := by
  unfold deepT
  rw [forall_mem_flatMap']
  constructor
  · intro h q hq p hp
    exact (holds_deepT_case cm hc q p (hwf.hδj q p k).2).1 (h (q, p) ((mem_casesL cm).2 ⟨hq, hp⟩))
  · rintro h ⟨q, p⟩ hqp
    obtain ⟨hq, hp⟩ := (mem_casesL cm).1 hqp
    exact (holds_deepT_case cm hc q p (hwf.hδj q p k).2).2 (h q hq p hp)

theorem sat_step (hwf : cm.WF W) {σ : ℕ → Bool} {B : ℕ} :
    SatL σ (cm.stepL W B) ↔
      (∀ t < B, ∀ q < cm.Q, ∀ p ∈ allPats cm.A (cm.K * cm.c),
        cm.Guard σ W t q p → σ (cm.vC W (t + 1) (cm.δ q p).1) = true) ∧
      (∀ t < B, ∀ q < cm.Q, ∀ p ∈ allPats cm.A (cm.K * cm.c),
        cm.Guard σ W t q p → ∀ k < cm.K, ∀ d, d + cm.c < W → cm.Clause σ W t q p k d) := by
  have hc : 0 < cm.c := hwf.hc1
  have hw2 := hwf.hc
  unfold stepL
  rw [SatL_flatMap]
  have key : ∀ t, SatL σ (instL (cm.Vf W t 0 0) cm.stepCtlT ++
      (List.range cm.K).flatMap (fun k =>
        (List.range cm.c).flatMap (fun d => instL (cm.Vf W t k 0) (cm.topT k d)) ++
        (List.range (W - 2 * cm.c)).flatMap (fun e => instL (cm.Vf W t k e) (cm.deepT k)))) ↔
      ((∀ q < cm.Q, ∀ p ∈ allPats cm.A (cm.K * cm.c),
        cm.Guard σ W t q p → σ (cm.vC W (t + 1) (cm.δ q p).1) = true) ∧
      (∀ q < cm.Q, ∀ p ∈ allPats cm.A (cm.K * cm.c),
        cm.Guard σ W t q p → ∀ k < cm.K, ∀ d, d + cm.c < W → cm.Clause σ W t q p k d)) := by
    intro t
    rw [SatL_append, SatL_instL, holds_stepCtlT cm hc, SatL_flatMap]
    apply and_congr Iff.rfl
    have hk : ∀ k < cm.K, SatL σ ((List.range cm.c).flatMap
        (fun d => instL (cm.Vf W t k 0) (cm.topT k d)) ++
        (List.range (W - 2 * cm.c)).flatMap (fun e => instL (cm.Vf W t k e) (cm.deepT k))) ↔
        (∀ q < cm.Q, ∀ p ∈ allPats cm.A (cm.K * cm.c),
          cm.Guard σ W t q p → ∀ d, d + cm.c < W → cm.Clause σ W t q p k d) := by
      intro k hk
      rw [SatL_append, SatL_flatMap, SatL_flatMap]
      simp only [List.mem_range, SatL_instL]
      have ht : ∀ d, (∀ φ ∈ cm.topT k d, TF.holds σ (cm.Vf W t k 0) φ) ↔
          ∀ q < cm.Q, ∀ p ∈ allPats cm.A (cm.K * cm.c),
            cm.Guard σ W t q p → cm.Clause σ W t q p k d := fun d => holds_topT cm hc hk
      have hd : ∀ e, (∀ φ ∈ cm.deepT k, TF.holds σ (cm.Vf W t k e) φ) ↔
          ∀ q < cm.Q, ∀ p ∈ allPats cm.A (cm.K * cm.c),
            cm.Guard σ W t q p → cm.Clause σ W t q p k (cm.c + e) := fun e => holds_deepT cm hwf hc
      simp only [ht, hd]
      constructor
      · rintro ⟨h1, h2⟩ q hq p hp hg d hdc
        by_cases hdl : d < cm.c
        · exact h1 d hdl q hq p hp hg
        · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hdl)
          exact h2 e (by omega) q hq p hp hg
      · intro h
        exact ⟨fun d hdl q hq p hp hg => h q hq p hp hg d (by omega),
          fun e he q hq p hp hg => h q hq p hp hg (cm.c + e) (by omega)⟩
    simp only [List.mem_range]
    constructor
    · intro h q hq p hp hg k hkK d hdc
      exact (hk k hkK).1 (h k hkK) q hq p hp hg d hdc
    · intro h k hkK
      exact (hk k hkK).2 (fun q hq p hp hg d hdc => h q hq p hp hg k hkK d hdc)
  constructor
  · intro h
    refine ⟨fun t ht => ((key t).1 (h t (by simpa using ht))).1,
      fun t ht => ((key t).1 (h t (by simpa using ht))).2⟩
  · rintro ⟨h1, h2⟩ t ht
    have ht' : t < B := by simpa using ht
    exact (key t).2 ⟨h1 t ht', h2 t ht'⟩

theorem sat_consL_iff (hwf : cm.WF W) {B : ℕ} {x : List Bool} {σ : ℕ → Bool}
    (hx : 2 * x.length + 1 ≤ W) :
    SatL σ (cm.consL W B x) ↔ cm.Fam W B x σ := by
  unfold consL
  rw [SatL_append, SatL_append, SatL_append, sat_init cm hwf.hkin hx, sat_frame, sat_step cm hwf,
    sat_acc cm hwf.hkout]
  constructor
  · rintro ⟨⟨⟨⟨i1, i2, i3, i4, i5, i6⟩, f1, f2, f3⟩, s1, s2⟩, a1⟩
    exact
      { frameC := f1, frameA := f2, margin := f3, initC := i1, initX := i2, initSep := i3,
        initW := i4, initContig := i5, initO := i6, stepC := s1,
        stepA := fun t ht q hq p hp hg k hk d hd => s2 t ht q hq p hp hg k hk d hd,
        acc := by
          obtain ⟨⟨q, hq, hh, h1⟩, h2, h3⟩ := a1
          exact ⟨q, hq, hh, h1, h2, h3⟩ }
  · intro hF
    refine ⟨⟨⟨⟨hF.initC, hF.initX, hF.initSep, hF.initW, hF.initContig, hF.initO⟩,
      hF.frameC, hF.frameA, hF.margin⟩, hF.stepC,
      fun t ht q hq p hp hg k hk d hd => hF.stepA t ht q hq p hp hg k hk d hd⟩, ?_⟩
    obtain ⟨q, hq, hh, h1, h2, h3⟩ := hF.acc
    exact ⟨⟨q, hq, hh, h1⟩, h2, h3⟩

end CM

/-! ## The tableau formula -/

/-- Conjunction of a list of formulas, ending in the seed tautology. -/
def conjF : List PropFormula → PropFormula
  | [] => tautSeed
  | φ :: l => .and φ (conjF l)

theorem eval_conjF (σ : ℕ → Bool) (l : List PropFormula) :
    PropFormula.eval σ (conjF l) = true ↔ SatL σ l := by
  induction l with
  | nil =>
      simp [conjF, SatL_nil]
      simp [tautSeed, PropFormula.eval, Bool.or_not_self]
  | cons φ l ih => simp [conjF, PropFormula.eval, SatL_cons, ih]

/-- The formula whose tautology encodes rejection of every witness. -/
def tabFormula (cm : CM) (W B : ℕ) (x : List Bool) : PropFormula :=
  .not (conjF (cm.consL W B x))

theorem tabFormula_taut_iff (cm : CM) {W B : ℕ} {x : List Bool} (hwf : cm.WF W)
    (hW : 2 * x.length + 1 + 2 * cm.c ≤ W) :
    (tabFormula cm W B x).Tautology ↔
      ¬ ∃ w : List Bool, 2 * x.length + 1 + w.length + 2 * cm.c ≤ W ∧
        cm.NoOverflow W B (cm.initArr W x w) ∧
        cm.Accepts (cm.runA W (cm.initArr W x w) B).1 (cm.runA W (cm.initArr W x w) B).2 := by
  have hx : 2 * x.length + 1 ≤ W := by omega
  constructor
  · intro hT ⟨w, hs, hno, hacc⟩
    obtain ⟨σ, hσ⟩ := cm.completeness hwf hs hno hacc
    have h1 := hT σ
    simp only [tabFormula, PropFormula.eval, Bool.not_eq_true'] at h1
    have h2 : PropFormula.eval σ (conjF (cm.consL W B x)) = true :=
      (eval_conjF σ _).2 ((cm.sat_consL_iff hwf hx).2 hσ)
    rw [h2] at h1
    exact absurd h1 (by simp)
  · intro hn σ
    simp only [tabFormula, PropFormula.eval]
    by_contra hcon
    have hc : PropFormula.eval σ (conjF (cm.consL W B x)) = true := by
      cases h : PropFormula.eval σ (conjF (cm.consL W B x)) <;> simp_all
    have hF := (cm.sat_consL_iff hwf hx).1 ((eval_conjF σ _).1 hc)
    exact hn (cm.soundness hwf hF hW)

end CL
end SATurday.Bridge
