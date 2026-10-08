import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
# Razborov–Smolensky: AC0[p] circuits and low degree approximation (Ladder Rung R4, 1A)

AC0[p] circuits as straight line programs over `n` Boolean inputs (unbounded fan in AND,
OR, MOD_{p,r}, and NOT), and low degree functions over `ZMod p` on the Boolean cube in
multilinear coefficient form.

LOG: R4 Smolensky module (circuits, low degree functions)
-/

namespace SATurday.ProofComplexity

open Finset

noncomputable section

open Classical

/-! ## AC0[p] circuits -/

/-- Gates; children are indices of earlier gates. -/
inductive CG where
  | inp (i : ℕ)
  | neg (j : ℕ)
  | and (l : List ℕ)
  | or (l : List ℕ)
  | mod (r : ℕ) (l : List ℕ)

section Circuits

variable {n : ℕ} (p : ℕ) (g : ℕ → CG)

/-- Value of gate `m` on input `x` (out of range reads are `false`). -/
def cval (x : Fin n → Bool) : ℕ → Bool
  | m => match g m with
    | .inp i => if h : i < n then x ⟨i, h⟩ else false
    | .neg j => !(if h : j < m then cval x j else false)
    | .and l => l.all fun j => if h : j < m then cval x j else false
    | .or l => l.any fun j => if h : j < m then cval x j else false
    | .mod r l => decide ((l.countP fun j => if h : j < m then cval x j else false) % p = r % p)
decreasing_by all_goals exact h

/-- Depth: AND, OR and MOD gates count one level each. -/
def cdepth : ℕ → ℕ
  | m => match g m with
    | .inp _ => 0
    | .neg j => if h : j < m then cdepth j else 0
    | .and l => (l.map fun j => if h : j < m then cdepth j else 0).foldr max 0 + 1
    | .or l => (l.map fun j => if h : j < m then cdepth j else 0).foldr max 0 + 1
    | .mod _ l => (l.map fun j => if h : j < m then cdepth j else 0).foldr max 0 + 1
decreasing_by all_goals exact h

/-- A circuit with gates `0, ..., s - 1` of depth at most `d` computes `f` at its last gate. -/
def CComputes (s d : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  0 < s ∧ (∀ m < s, cdepth g m ≤ d) ∧ ∀ x, cval p g x (s - 1) = f x

end Circuits

/-! ## Low degree functions over `ZMod p` -/

section LowDeg

variable {n : ℕ} {p : ℕ}

/-- `0/1` value of an input bit in `ZMod p`. -/
def bitF (p : ℕ) (x : Fin n → Bool) (i : Fin n) : ZMod p := if x i then 1 else 0

/-- Multilinear monomial. -/
def mono (p : ℕ) (I : Finset (Fin n)) (x : Fin n → Bool) : ZMod p := ∏ i ∈ I, bitF p x i

/-- Functions represented by multilinear polynomials of degree at most `D`. -/
def LowDeg (p n D : ℕ) (f : (Fin n → Bool) → ZMod p) : Prop :=
  ∃ c : Finset (Fin n) → ZMod p, (∀ I, c I ≠ 0 → I.card ≤ D) ∧
    ∀ x, f x = ∑ I : Finset (Fin n), c I * mono p I x

theorem bitF_idem (x : Fin n → Bool) (i : Fin n) : bitF p x i * bitF p x i = bitF p x i := by
  unfold bitF; split_ifs <;> simp

theorem mono_mul (I J : Finset (Fin n)) (x : Fin n → Bool) :
    mono p I x * mono p J x = mono p (I ∪ J) x := by
  unfold mono
  have h1 : ∏ i ∈ I, bitF p x i = (∏ i ∈ I \ J, bitF p x i) * ∏ i ∈ I ∩ J, bitF p x i := by
    rw [← Finset.prod_union (Finset.disjoint_sdiff_inter I J), Finset.sdiff_union_inter]
  have h2 : ∏ i ∈ J, bitF p x i = (∏ i ∈ J \ I, bitF p x i) * ∏ i ∈ I ∩ J, bitF p x i := by
    rw [Finset.inter_comm, ← Finset.prod_union (Finset.disjoint_sdiff_inter J I),
      Finset.sdiff_union_inter]
  have h3 : (∏ i ∈ I ∩ J, bitF p x i) * ∏ i ∈ I ∩ J, bitF p x i = ∏ i ∈ I ∩ J, bitF p x i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => bitF_idem x i
  have h4 : I ∪ J = (I \ J) ∪ (J \ I) ∪ (I ∩ J) := by ext; simp; tauto
  have hd1 : Disjoint (I \ J) (J \ I) := by
    rw [Finset.disjoint_left]; intro a ha hb; simp at ha hb; exact ha.2 hb.1
  have hd2 : Disjoint ((I \ J) ∪ (J \ I)) (I ∩ J) := by
    rw [Finset.disjoint_left]; intro a ha hb; simp at ha hb; tauto
  rw [h4, Finset.prod_union hd2, Finset.prod_union hd1, h1, h2]
  calc (∏ i ∈ I \ J, bitF p x i) * (∏ i ∈ I ∩ J, bitF p x i) *
        ((∏ i ∈ J \ I, bitF p x i) * ∏ i ∈ I ∩ J, bitF p x i)
      = (∏ i ∈ I \ J, bitF p x i) * (∏ i ∈ J \ I, bitF p x i) *
          ((∏ i ∈ I ∩ J, bitF p x i) * ∏ i ∈ I ∩ J, bitF p x i) := by ring
    _ = _ := by rw [h3]

theorem LowDeg.mono_deg {D D' : ℕ} (h : D ≤ D') {f : (Fin n → Bool) → ZMod p}
    (hf : LowDeg p n D f) : LowDeg p n D' f := by
  obtain ⟨c, hc, hf⟩ := hf
  exact ⟨c, fun I hI => (hc I hI).trans h, hf⟩

theorem LowDeg.const (k : ZMod p) : LowDeg p n 0 (fun _ => k) := by
  refine ⟨fun I => if I = ∅ then k else 0, fun I hI => ?_, fun x => ?_⟩
  · dsimp only at hI
    split_ifs at hI with h
    · subst h; simp
    · exact absurd rfl hI
  · rw [Finset.sum_eq_single ∅]
    · simp [mono]
    · intro I _ hI; simp [hI]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem LowDeg.var (i : Fin n) : LowDeg p n 1 (fun x => bitF p x i) := by
  refine ⟨fun I => if I = {i} then 1 else 0, fun I hI => ?_, fun x => ?_⟩
  · dsimp only at hI
    split_ifs at hI with h
    · subst h; simp
    · exact absurd rfl hI
  · rw [Finset.sum_eq_single {i}]
    · simp [mono]
    · intro I _ hI; simp [hI]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem LowDeg.add {D : ℕ} {f g : (Fin n → Bool) → ZMod p} (hf : LowDeg p n D f)
    (hg : LowDeg p n D g) : LowDeg p n D (fun x => f x + g x) := by
  obtain ⟨c, hc, hf⟩ := hf
  obtain ⟨d, hd, hg⟩ := hg
  refine ⟨fun I => c I + d I, fun I hI => ?_, fun x => ?_⟩
  · dsimp only at hI
    by_cases h : c I = 0
    · rw [h, zero_add] at hI; exact hd I hI
    · exact hc I h
  · dsimp only
    rw [hf, hg, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun I _ => by ring

theorem LowDeg.smul {D : ℕ} (k : ZMod p) {f : (Fin n → Bool) → ZMod p} (hf : LowDeg p n D f) :
    LowDeg p n D (fun x => k * f x) := by
  obtain ⟨c, hc, hf⟩ := hf
  refine ⟨fun I => k * c I, fun I hI => hc I (fun h => hI (by dsimp only; rw [h, mul_zero])),
    fun x => ?_⟩
  dsimp only
  rw [hf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun I _ => by ring

theorem LowDeg.neg {D : ℕ} {f : (Fin n → Bool) → ZMod p} (hf : LowDeg p n D f) :
    LowDeg p n D (fun x => -f x) := by
  have := hf.smul (-1)
  simpa using this

theorem LowDeg.sub {D : ℕ} {f g : (Fin n → Bool) → ZMod p} (hf : LowDeg p n D f)
    (hg : LowDeg p n D g) : LowDeg p n D (fun x => f x - g x) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

theorem LowDeg.mul {D1 D2 : ℕ} {f g : (Fin n → Bool) → ZMod p} (hf : LowDeg p n D1 f)
    (hg : LowDeg p n D2 g) : LowDeg p n (D1 + D2) (fun x => f x * g x) := by
  obtain ⟨c, hc, hf⟩ := hf
  obtain ⟨d, hd, hg⟩ := hg
  let e : Finset (Fin n) → ZMod p := fun K =>
    ∑ IJ ∈ (Finset.univ ×ˢ Finset.univ).filter (fun IJ : Finset (Fin n) × Finset (Fin n) =>
      IJ.1 ∪ IJ.2 = K), c IJ.1 * d IJ.2
  refine ⟨e, fun K hK => ?_, fun x => ?_⟩
  · obtain ⟨IJ, hIJ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hK
    obtain ⟨_, hK'⟩ := Finset.mem_filter.1 hIJ
    have h1 : c IJ.1 ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have h2 : d IJ.2 ≠ 0 := fun h => hne (by rw [h, mul_zero])
    rw [← hK']
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hc _ h1) (hd _ h2))
  · dsimp only
    rw [hf, hg, Finset.sum_mul_sum]
    rw [← Finset.sum_product']
    simp only [e, Finset.sum_mul]
    rw [← Finset.sum_fiberwise (Finset.univ ×ˢ Finset.univ)
      (fun IJ : Finset (Fin n) × Finset (Fin n) => IJ.1 ∪ IJ.2)]
    refine Finset.sum_congr rfl fun K _ => Finset.sum_congr rfl fun IJ hIJ => ?_
    obtain ⟨_, hK'⟩ := Finset.mem_filter.1 hIJ
    rw [← hK', ← mono_mul]; ring

theorem LowDeg.pow {D : ℕ} {f : (Fin n → Bool) → ZMod p} (hf : LowDeg p n D f) :
    ∀ k : ℕ, LowDeg p n (k * D) (fun x => f x ^ k) := by
  intro k
  induction k with
  | zero => simpa using (LowDeg.const (n := n) (p := p) 1)
  | succ k ih =>
      have := ih.mul hf
      simpa [pow_succ, Nat.succ_mul] using this

theorem LowDeg.prod {D : ℕ} {ι : Type*} (s : Finset ι) {f : ι → (Fin n → Bool) → ZMod p}
    (hf : ∀ i ∈ s, LowDeg p n D (f i)) : LowDeg p n (s.card * D) (fun x => ∏ i ∈ s, f i x) := by
  induction s using Finset.induction_on with
  | empty => simpa using (LowDeg.const (n := n) (p := p) 1)
  | insert a s ha ih =>
      have h1 := (hf a (Finset.mem_insert_self _ _)).mul
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
      rw [Finset.card_insert_of_notMem ha]
      have e : (s.card + 1) * D = D + s.card * D := by ring
      rw [e]
      simpa [Finset.prod_insert ha] using h1

theorem LowDeg.sum {D : ℕ} {ι : Type*} (s : Finset ι) {f : ι → (Fin n → Bool) → ZMod p}
    (hf : ∀ i ∈ s, LowDeg p n D (f i)) : LowDeg p n D (fun x => ∑ i ∈ s, f i x) := by
  induction s using Finset.induction_on with
  | empty => simpa using (LowDeg.const (n := n) (p := p) 0).mono_deg (Nat.zero_le D)
  | insert a s ha ih =>
      have h1 := (hf a (Finset.mem_insert_self _ _)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
      simpa [Finset.sum_insert ha] using h1

end LowDeg

/-! ## Approximating an OR gate -/

section OrApx

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime]

/-- `0/1` value of a Boolean in `ZMod p`. -/
def bz (p : ℕ) (b : Bool) : ZMod p := if b then 1 else 0

/-- Sum of the children values over a subset. -/
def subSum (v : ℕ → (Fin n → Bool) → Bool) (T : Finset ℕ) (x : Fin n → Bool) : ZMod p :=
  ∑ i ∈ T, bz p (v i x)

/-- The OR approximant for a choice of `ℓ` subsets. -/
def orApx {ℓ : ℕ} (v : ℕ → (Fin n → Bool) → Bool) (σ : Fin ℓ → Finset ℕ)
    (x : Fin n → Bool) : ZMod p :=
  1 - ∏ j : Fin ℓ, (1 - (subSum (p := p) v (σ j) x) ^ (p - 1))

/-- The true OR of the children in `S`. -/
def orVal (v : ℕ → (Fin n → Bool) → Bool) (S : Finset ℕ) (x : Fin n → Bool) : Bool :=
  decide (∃ i ∈ S, v i x = true)

theorem pow_card_sub_one {a : ZMod p} (ha : a ≠ 0) : a ^ (p - 1) = 1 :=
  ZMod.pow_card_sub_one_eq_one ha

theorem orApx_of_false {ℓ : ℕ} {v : ℕ → (Fin n → Bool) → Bool} {S : Finset ℕ}
    {σ : Fin ℓ → Finset ℕ} (hσ : ∀ j, σ j ⊆ S) {x : Fin n → Bool}
    (h : orVal v S x = false) : orApx (p := p) v σ x = 0 := by
  unfold orApx
  have hz : ∀ j, subSum (p := p) v (σ j) x = 0 := by
    intro j
    unfold subSum
    refine Finset.sum_eq_zero fun i hi => ?_
    have : v i x = false := by
      by_contra hh
      simp only [orVal, decide_eq_false_iff_not, not_exists, not_and] at h
      exact h i (hσ j hi) (by simpa using hh)
    simp [bz, this]
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  simp [hz, zero_pow hp1]

theorem orApx_of_ne {ℓ : ℕ} {v : ℕ → (Fin n → Bool) → Bool} {σ : Fin ℓ → Finset ℕ}
    {x : Fin n → Bool} {j : Fin ℓ} (h : subSum (p := p) v (σ j) x ≠ 0) :
    orApx (p := p) v σ x = 1 := by
  unfold orApx
  rw [Finset.prod_eq_zero (Finset.mem_univ j) (by rw [pow_card_sub_one h, sub_self]), sub_zero]

/-- At most half of the subsets have zero sum when some child is true. -/
theorem zero_sum_half {v : ℕ → (Fin n → Bool) → Bool} {S : Finset ℕ} {x : Fin n → Bool}
    {i0 : ℕ} (hi0 : i0 ∈ S) (hv : v i0 x = true) :
    2 * (S.powerset.filter fun T => subSum (p := p) v T x = 0).card ≤ 2 ^ S.card := by
  set Z := S.powerset.filter fun T => subSum (p := p) v T x = 0
  set NZ := S.powerset.filter fun T => subSum (p := p) v T x ≠ 0
  let f : Finset ℕ → Finset ℕ := fun T => symmDiff T {i0}
  have hstep : ∀ T ⊆ S, subSum (p := p) v (f T) x = subSum (p := p) v T x + 1 ∨
      subSum (p := p) v (f T) x = subSum (p := p) v T x - 1 := by
    intro T _
    unfold subSum
    by_cases hT : i0 ∈ T
    · right
      have e : f T = T.erase i0 := by
        ext a; simp only [f, Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨h2, h1⟩
          · subst h1; exact absurd hT h2
        · rintro ⟨h1, h2⟩; exact Or.inl ⟨h2, h1⟩
      rw [e, ← Finset.add_sum_erase T _ hT, hv]; simp [bz]
    · left
      have e : f T = insert i0 T := by
        ext a; simp only [f, Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
        constructor
        · rintro (⟨h1, _⟩ | ⟨h1, _⟩)
          · exact Or.inr h1
          · exact Or.inl h1
        · rintro (h1 | h1)
          · subst h1; exact Or.inr ⟨rfl, hT⟩
          · exact Or.inl ⟨h1, fun h => hT (h ▸ h1)⟩
      rw [e, Finset.sum_insert hT, hv]; simp [bz]; ring
  have hmaps : ∀ T ∈ Z, f T ∈ NZ := by
    intro T hT
    obtain ⟨hTS, hz⟩ := Finset.mem_filter.1 hT
    have hTS' : T ⊆ S := Finset.mem_powerset.1 hTS
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 ?_, ?_⟩
    · intro a ha
      simp only [f, Finset.mem_symmDiff, Finset.mem_singleton] at ha
      rcases ha with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hTS' h1
      · subst h1; exact hi0
    · have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
      rcases hstep T hTS' with h | h <;> rw [h, hz]
      · simpa using h1
      · simpa using h1
  have hinj : Set.InjOn f Z := by
    intro A _ B _ h
    have := congrArg (fun T => symmDiff T {i0}) h
    simp only [f, symmDiff_symmDiff_cancel_right] at this
    exact this
  have h1 : Z.card ≤ NZ.card := Finset.card_le_card_of_injOn f hmaps hinj
  have h2 : Z.card + NZ.card = 2 ^ S.card := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_powerset]
  omega

/-- Some choice of `ℓ` subsets approximates OR with error at most `2^n / 2^ℓ`. -/
theorem exists_good_choice (ℓ : ℕ) (v : ℕ → (Fin n → Bool) → Bool) (S : Finset ℕ) :
    ∃ σ : Fin ℓ → Finset ℕ, (∀ j, σ j ⊆ S) ∧
      (Finset.univ.filter fun x : Fin n → Bool =>
        bz p (orVal v S x) ≠ orApx (p := p) v σ x).card * 2 ^ ℓ ≤ 2 ^ n := by
  set Ch := Fintype.piFinset fun _ : Fin ℓ => S.powerset
  let E : (Fin ℓ → Finset ℕ) → Finset (Fin n → Bool) := fun σ =>
    Finset.univ.filter fun x => bz p (orVal v S x) ≠ orApx (p := p) v σ x
  have hCh : Ch.card = (2 ^ S.card) ^ ℓ := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_powerset, Finset.card_univ,
      Fintype.card_fin]
  -- per input count of bad choices
  have hx : ∀ x : Fin n → Bool, (Ch.filter fun σ => x ∈ E σ).card * 2 ^ ℓ ≤ Ch.card := by
    intro x
    by_cases ho : orVal v S x = true
    · obtain ⟨i0, hi0, hv⟩ := of_decide_eq_true ho
      set Z := S.powerset.filter fun T => subSum (p := p) v T x = 0
      have hsub : (Ch.filter fun σ => x ∈ E σ) ⊆ Fintype.piFinset fun _ : Fin ℓ => Z := by
        intro σ hσ
        obtain ⟨hσC, hxE⟩ := Finset.mem_filter.1 hσ
        rw [Fintype.mem_piFinset] at hσC ⊢
        intro j
        refine Finset.mem_filter.2 ⟨hσC j, ?_⟩
        by_contra hne
        have := orApx_of_ne (p := p) (v := v) (σ := σ) (x := x) (j := j) hne
        simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hxE
        rw [this, ho] at hxE
        exact hxE (by simp [bz])
      have hZ := zero_sum_half (p := p) hi0 hv
      calc (Ch.filter fun σ => x ∈ E σ).card * 2 ^ ℓ
          ≤ (Fintype.piFinset fun _ : Fin ℓ => Z).card * 2 ^ ℓ :=
            Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
        _ = (2 * Z.card) ^ ℓ := by
            rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
              mul_pow, mul_comm]
        _ ≤ (2 ^ S.card) ^ ℓ := Nat.pow_le_pow_left hZ ℓ
        _ = Ch.card := hCh.symm
    · have : (Ch.filter fun σ => x ∈ E σ) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro σ hσ hxE
        rw [Fintype.mem_piFinset] at hσ
        have hσS : ∀ j, σ j ⊆ S := fun j => Finset.mem_powerset.1 (hσ j)
        simp only [Bool.not_eq_true] at ho
        simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hxE
        rw [orApx_of_false hσS ho, ho] at hxE
        exact hxE (by simp [bz])
      rw [this]; simp
  -- double counting
  have htot : ∑ σ ∈ Ch, (E σ).card * 2 ^ ℓ ≤ ∑ _σ ∈ Ch, 2 ^ n := by
    have e1 : ∑ σ ∈ Ch, (E σ).card = ∑ x : Fin n → Bool, (Ch.filter fun σ => x ∈ E σ).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp only [E]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp
    rw [← Finset.sum_mul, e1, Finset.sum_mul, Finset.sum_const, smul_eq_mul]
    calc ∑ x : Fin n → Bool, (Ch.filter fun σ => x ∈ E σ).card * 2 ^ ℓ
        ≤ ∑ _x : Fin n → Bool, Ch.card := Finset.sum_le_sum fun x _ => hx x
      _ = Ch.card * 2 ^ n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
            Fintype.card_fin, smul_eq_mul, mul_comm]
  have hne : Ch.Nonempty := ⟨fun _ => ∅, by
    rw [Fintype.mem_piFinset]; intro _; exact Finset.empty_mem_powerset _⟩
  obtain ⟨σ, hσ, hle⟩ := Finset.exists_le_of_sum_le hne htot
  refine ⟨σ, fun j => Finset.mem_powerset.1 ((Fintype.mem_piFinset.1 hσ) j), hle⟩

end OrApx

/-! ## Approximating a whole circuit -/

section CircApx

variable {n : ℕ} {p : ℕ} [hp : Fact p.Prime] (ℓ : ℕ) (g : ℕ → CG)

/-- Children values as read by gate `m`. -/
def rdV (m : ℕ) : ℕ → (Fin n → Bool) → Bool := fun i x =>
  if i < m then cval p g x i else false

/-- Negated children values (for AND gates). -/
def rdVn (m : ℕ) : ℕ → (Fin n → Bool) → Bool := fun i x => !(rdV (p := p) g m i x)

/-- Chosen subsets for an OR gate. -/
def orChoice (m : ℕ) (S : Finset ℕ) : Fin ℓ → Finset ℕ :=
  (exists_good_choice (n := n) (p := p) ℓ (rdV (p := p) g m) S).choose

/-- Chosen subsets for an AND gate (OR of the negated children). -/
def andChoice (m : ℕ) (S : Finset ℕ) : Fin ℓ → Finset ℕ :=
  (exists_good_choice (n := n) (p := p) ℓ (rdVn (p := p) g m) S).choose

/-- The approximant of gate `m`. -/
def apxF : ℕ → (Fin n → Bool) → ZMod p
  | m => fun x => match g m with
    | .inp i => if h : i < n then bitF p x ⟨i, h⟩ else 0
    | .neg j => 1 - (if h : j < m then apxF j x else 0)
    | .or l => 1 - ∏ t : Fin ℓ, (1 - (∑ i ∈ orChoice (n := n) (p := p) ℓ g m l.toFinset t,
        (if h : i < m then apxF i x else 0)) ^ (p - 1))
    | .and l => ∏ t : Fin ℓ, (1 - (∑ i ∈ andChoice (n := n) (p := p) ℓ g m l.toFinset t,
        (1 - (if h : i < m then apxF i x else 0))) ^ (p - 1))
    | .mod r l => 1 - ((l.attach.map fun i => if h : i.1 < m then apxF i.1 x else 0).sum -
        (r : ZMod p)) ^ (p - 1)
decreasing_by all_goals exact h

/-- Error set of gate `m`. -/
def errSet (m : ℕ) : Finset (Fin n → Bool) :=
  match g m with
  | .or l => Finset.univ.filter fun x => bz p (orVal (rdV (p := p) g m) l.toFinset x) ≠
      orApx (p := p) (rdV (p := p) g m) (orChoice (n := n) (p := p) ℓ g m l.toFinset) x
  | .and l => Finset.univ.filter fun x => bz p (orVal (rdVn (p := p) g m) l.toFinset x) ≠
      orApx (p := p) (rdVn (p := p) g m) (andChoice (n := n) (p := p) ℓ g m l.toFinset) x
  | _ => ∅

theorem errSet_card (m : ℕ) : (errSet (n := n) (p := p) ℓ g m).card * 2 ^ ℓ ≤ 2 ^ n := by
  unfold errSet
  cases g m with
  | or l => exact (exists_good_choice (n := n) (p := p) ℓ (rdV (p := p) g m) l.toFinset).choose_spec.2
  | and l => exact (exists_good_choice (n := n) (p := p) ℓ (rdVn (p := p) g m) l.toFinset).choose_spec.2
  | _ => simp

theorem bz_not (b : Bool) : (1 : ZMod p) - bz p b = bz p (!b) := by
  cases b <;> simp [bz]

theorem sum_bz_countP (l : List ℕ) (f : ℕ → Bool) :
    (l.map fun i => bz p (f i)).sum = ((l.countP f : ℕ) : ZMod p) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
      cases f a <;> simp [bz] <;> ring

theorem cval_eq (x : Fin n → Bool) (m : ℕ) : cval p g x m = match g m with
    | .inp i => if h : i < n then x ⟨i, h⟩ else false
    | .neg j => !(rdV (p := p) g m j x)
    | .and l => l.all fun j => rdV (p := p) g m j x
    | .or l => l.any fun j => rdV (p := p) g m j x
    | .mod r l => decide ((l.countP fun j => rdV (p := p) g m j x) % p = r % p) := by
  rw [cval]
  cases g m <;> simp [rdV]

theorem orVal_any (v : ℕ → (Fin n → Bool) → Bool) (l : List ℕ) (x : Fin n → Bool) :
    orVal v l.toFinset x = l.any fun j => v j x := by
  unfold orVal
  rw [Bool.eq_iff_iff]
  simp

/-- Outside the error sets the approximant is exact. -/
theorem apxF_correct : ∀ m (x : Fin n → Bool), (∀ m' ≤ m, x ∉ errSet (n := n) (p := p) ℓ g m') →
    apxF (p := p) ℓ g m x = bz p (cval p g x m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro x hx
  have hrd : ∀ i, (if h : i < m then apxF (p := p) ℓ g i x else 0) = bz p (rdV (p := p) g m i x) := by
    intro i
    unfold rdV
    split_ifs with h
    · exact ih i h x (fun m' hm' => hx m' (by omega))
    · simp [bz]
  have herr := hx m le_rfl
  rw [apxF, cval_eq]
  unfold errSet at herr
  cases hg : g m with
  | inp i =>
      simp only
      split_ifs <;> simp [bitF, bz]
  | neg j =>
      simp only
      rw [hrd, bz_not]
  | or l =>
      simp only
      simp only [hg, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at herr
      simp only [hrd]
      rw [show (1 - ∏ t : Fin ℓ, (1 - (∑ i ∈ orChoice (n := n) (p := p) ℓ g m l.toFinset t,
          bz p (rdV (p := p) g m i x)) ^ (p - 1))) =
          orApx (p := p) (rdV (p := p) g m) (orChoice (n := n) (p := p) ℓ g m l.toFinset) x
        from rfl, ← herr, orVal_any]
  | and l =>
      simp only
      simp only [hg, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at herr
      simp only [hrd, bz_not]
      have e : (∏ t : Fin ℓ, (1 - (∑ i ∈ andChoice (n := n) (p := p) ℓ g m l.toFinset t,
          bz p (rdVn (p := p) g m i x)) ^ (p - 1))) =
          1 - orApx (p := p) (rdVn (p := p) g m) (andChoice (n := n) (p := p) ℓ g m l.toFinset) x := by
        unfold orApx subSum; ring
      rw [show (fun i => bz p (!rdV (p := p) g m i x)) = fun i => bz p (rdVn (p := p) g m i x)
        from rfl, e, ← herr, orVal_any, bz_not]
      congr 1
      unfold rdVn
      rw [Bool.eq_iff_iff]
      simp [List.all_eq_true, List.any_eq_true]
  | mod r l =>
      simp only
      have hs : (l.attach.map fun i => if h : i.1 < m then apxF (p := p) ℓ g i.1 x else 0).sum =
          ((l.countP fun j => rdV (p := p) g m j x : ℕ) : ZMod p) := by
        rw [← sum_bz_countP]
        congr 1
        have hf : (fun i : {j // j ∈ l} => if h : i.1 < m then apxF (p := p) ℓ g i.1 x else 0) =
            fun i => bz p (rdV (p := p) g m i.1 x) := funext fun i => hrd i.1
        rw [hf]
        simp
      rw [hs]
      have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
      by_cases hc : (l.countP fun j => rdV (p := p) g m j x) % p = r % p
      · have : ((l.countP fun j => rdV (p := p) g m j x : ℕ) : ZMod p) = (r : ZMod p) :=
          (ZMod.natCast_eq_natCast_iff' _ _ _).2 hc
        rw [this, sub_self, zero_pow hp1, sub_zero, decide_eq_true hc]; simp [bz]
      · have hne : ((l.countP fun j => rdV (p := p) g m j x : ℕ) : ZMod p) - (r : ZMod p) ≠ 0 := by
          intro h
          exact hc ((ZMod.natCast_eq_natCast_iff' _ _ _).1 (sub_eq_zero.1 h))
        rw [pow_card_sub_one hne, sub_self, decide_eq_false hc]; simp [bz]

theorem apxF_eq (m : ℕ) : apxF (n := n) (p := p) ℓ g m = fun x => match g m with
    | .inp i => if h : i < n then bitF p x ⟨i, h⟩ else 0
    | .neg j => 1 - (if h : j < m then apxF (p := p) ℓ g j x else 0)
    | .or l => 1 - ∏ t : Fin ℓ, (1 - (∑ i ∈ orChoice (n := n) (p := p) ℓ g m l.toFinset t,
        (if h : i < m then apxF (p := p) ℓ g i x else 0)) ^ (p - 1))
    | .and l => ∏ t : Fin ℓ, (1 - (∑ i ∈ andChoice (n := n) (p := p) ℓ g m l.toFinset t,
        (1 - (if h : i < m then apxF (p := p) ℓ g i x else 0))) ^ (p - 1))
    | .mod r l => 1 - ((l.attach.map fun i => if h : i.1 < m then apxF (p := p) ℓ g i.1 x else 0).sum -
        (r : ZMod p)) ^ (p - 1) := by
  funext x
  rw [apxF]

theorem cdepth_eq (m : ℕ) : cdepth g m = match g m with
    | .inp _ => 0
    | .neg j => if j < m then cdepth g j else 0
    | .and l => (l.map fun j => if j < m then cdepth g j else 0).foldr max 0 + 1
    | .or l => (l.map fun j => if j < m then cdepth g j else 0).foldr max 0 + 1
    | .mod _ l => (l.map fun j => if j < m then cdepth g j else 0).foldr max 0 + 1 := by
  rw [cdepth]
  cases g m <;> simp

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.1 h with rfl | h
      · exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)

theorem LowDeg.const_le {D : ℕ} (k : ZMod p) : LowDeg p n D (fun _ => k) :=
  (LowDeg.const k).mono_deg (Nat.zero_le D)

theorem LowDeg.listSum {D : ℕ} {ι : Type*} (l : List ι) {f : ι → (Fin n → Bool) → ZMod p}
    (hf : ∀ i ∈ l, LowDeg p n D (f i)) : LowDeg p n D (fun x => (l.map fun i => f i x).sum) := by
  induction l with
  | nil => simpa using (LowDeg.const_le (n := n) (p := p) (D := D) 0)
  | cons a l ih =>
      have h1 := (hf a (by simp)).add (ih fun i hi => hf i (by simp [hi]))
      simpa using h1

/-- Degree of the approximants: `((p - 1) ℓ)^depth`. -/
theorem apxF_deg (hℓ : 1 ≤ ℓ) : ∀ m, LowDeg p n (((p - 1) * ℓ) ^ cdepth g m)
    (apxF (p := p) ℓ g m) := by
  have hp2 := hp.out.two_le
  have hK : 1 ≤ (p - 1) * ℓ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  -- reading an earlier approximant
  have hrd : ∀ (i D : ℕ), (i < m → ((p - 1) * ℓ) ^ cdepth g i ≤ D) →
      LowDeg p n D (fun x => if h : i < m then apxF (p := p) ℓ g i x else 0) := by
    intro i D hD
    by_cases h : i < m
    · have := (ih i h).mono_deg (hD h)
      refine ⟨this.choose, this.choose_spec.1, fun x => ?_⟩
      dsimp only; rw [dif_pos h]; exact this.choose_spec.2 x
    · simpa [dif_neg h] using (LowDeg.const_le (n := n) (p := p) (D := D) 0)
  rw [apxF_eq, cdepth_eq]
  cases hg : g m with
  | inp i =>
      simp only [pow_zero]
      by_cases h : i < n
      · simpa [dif_pos h] using LowDeg.var (p := p) ⟨i, h⟩
      · simpa [dif_neg h] using (LowDeg.const_le (n := n) (p := p) (D := 1) 0)
  | neg j =>
      simp only
      have h1 := hrd j (((p - 1) * ℓ) ^ (if j < m then cdepth g j else 0)) (fun hj => by
        rw [if_pos hj])
      exact (LowDeg.const_le 1).sub h1
  | or l =>
      simp only
      set M := (l.map fun j => if j < m then cdepth g j else 0).foldr max 0
      have hch : ∀ i ∈ l.toFinset, LowDeg p n (((p - 1) * ℓ) ^ M)
          (fun x => if h : i < m then apxF (p := p) ℓ g i x else 0) := by
        intro i hi
        refine hrd i _ (fun him => Nat.pow_le_pow_right hK ?_)
        have := le_foldr_max (l := l.map fun j => if j < m then cdepth g j else 0)
          (a := if i < m then cdepth g i else 0) (List.mem_map.2 ⟨i, List.mem_toFinset.1 hi, rfl⟩)
        rwa [if_pos him] at this
      have hsum : ∀ t : Fin ℓ, LowDeg p n (((p - 1) * ℓ) ^ M) (fun x =>
          ∑ i ∈ orChoice (n := n) (p := p) ℓ g m l.toFinset t,
            (if h : i < m then apxF (p := p) ℓ g i x else 0)) := by
        intro t
        refine LowDeg.sum _ fun i hi => hch i ?_
        exact (exists_good_choice (n := n) (p := p) ℓ (rdV (p := p) g m) l.toFinset).choose_spec.1
          t hi
      have hfac : ∀ t ∈ (Finset.univ : Finset (Fin ℓ)), LowDeg p n ((p - 1) * ((p - 1) * ℓ) ^ M)
          (fun x => 1 - (∑ i ∈ orChoice (n := n) (p := p) ℓ g m l.toFinset t,
            (if h : i < m then apxF (p := p) ℓ g i x else 0)) ^ (p - 1)) :=
        fun t _ => (LowDeg.const_le 1).sub ((hsum t).pow (p - 1))
      have hprod := LowDeg.prod _ hfac
      rw [Finset.card_univ, Fintype.card_fin] at hprod
      have e : ℓ * ((p - 1) * ((p - 1) * ℓ) ^ M) = ((p - 1) * ℓ) ^ (M + 1) := by ring
      rw [e] at hprod
      exact (LowDeg.const_le 1).sub hprod
  | and l =>
      simp only
      set M := (l.map fun j => if j < m then cdepth g j else 0).foldr max 0
      have hch : ∀ i ∈ l.toFinset, LowDeg p n (((p - 1) * ℓ) ^ M)
          (fun x => 1 - if h : i < m then apxF (p := p) ℓ g i x else 0) := by
        intro i hi
        refine (LowDeg.const_le 1).sub (hrd i _ (fun him => Nat.pow_le_pow_right hK ?_))
        have := le_foldr_max (l := l.map fun j => if j < m then cdepth g j else 0)
          (a := if i < m then cdepth g i else 0) (List.mem_map.2 ⟨i, List.mem_toFinset.1 hi, rfl⟩)
        rwa [if_pos him] at this
      have hsum : ∀ t : Fin ℓ, LowDeg p n (((p - 1) * ℓ) ^ M) (fun x =>
          ∑ i ∈ andChoice (n := n) (p := p) ℓ g m l.toFinset t,
            (1 - if h : i < m then apxF (p := p) ℓ g i x else 0)) := by
        intro t
        refine LowDeg.sum _ fun i hi => hch i ?_
        exact (exists_good_choice (n := n) (p := p) ℓ (rdVn (p := p) g m) l.toFinset).choose_spec.1
          t hi
      have hfac : ∀ t ∈ (Finset.univ : Finset (Fin ℓ)), LowDeg p n ((p - 1) * ((p - 1) * ℓ) ^ M)
          (fun x => 1 - (∑ i ∈ andChoice (n := n) (p := p) ℓ g m l.toFinset t,
            (1 - if h : i < m then apxF (p := p) ℓ g i x else 0)) ^ (p - 1)) :=
        fun t _ => (LowDeg.const_le 1).sub ((hsum t).pow (p - 1))
      have hprod := LowDeg.prod _ hfac
      rw [Finset.card_univ, Fintype.card_fin] at hprod
      have e : ℓ * ((p - 1) * ((p - 1) * ℓ) ^ M) = ((p - 1) * ℓ) ^ (M + 1) := by ring
      rw [e] at hprod
      exact hprod
  | mod r l =>
      simp only
      set M := (l.map fun j => if j < m then cdepth g j else 0).foldr max 0
      have hch : ∀ i ∈ l.attach, LowDeg p n (((p - 1) * ℓ) ^ M)
          (fun x => if h : i.1 < m then apxF (p := p) ℓ g i.1 x else 0) := by
        intro i _
        refine hrd i.1 _ (fun him => Nat.pow_le_pow_right hK ?_)
        have := le_foldr_max (l := l.map fun j => if j < m then cdepth g j else 0)
          (a := if i.1 < m then cdepth g i.1 else 0) (List.mem_map.2 ⟨i.1, i.2, rfl⟩)
        rwa [if_pos him] at this
      have hs := LowDeg.listSum l.attach hch
      have h1 := (hs.sub (LowDeg.const_le (r : ZMod p))).pow (p - 1)
      have h2 := (LowDeg.const_le 1).sub h1
      refine h2.mono_deg ?_
      rw [pow_succ]
      calc (p - 1) * ((p - 1) * ℓ) ^ M ≤ (p - 1) * ℓ * ((p - 1) * ℓ) ^ M :=
            Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hℓ)
        _ = ((p - 1) * ℓ) ^ M * ((p - 1) * ℓ) := by ring

/-- Circuit approximation: a depth `d`, size `s` AC0[p] circuit computing `f` agrees with a
function of degree `((p - 1) ℓ)^d` outside at most `s 2^n / 2^ℓ` inputs. -/
theorem circuit_approx (hℓ : 1 ≤ ℓ) {s d : ℕ} {f : (Fin n → Bool) → Bool}
    (hC : CComputes p g s d f) :
    ∃ P : (Fin n → Bool) → ZMod p, LowDeg p n (((p - 1) * ℓ) ^ d) P ∧
      (Finset.univ.filter fun x => P x ≠ bz p (f x)).card * 2 ^ ℓ ≤ s * 2 ^ n := by
  obtain ⟨hs, hd, hf⟩ := hC
  have hK : 1 ≤ (p - 1) * ℓ := by
    have := hp.out.two_le; exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  refine ⟨apxF (p := p) ℓ g (s - 1), (apxF_deg (p := p) ℓ g hℓ (s - 1)).mono_deg
    (Nat.pow_le_pow_right hK (hd _ (by omega))), ?_⟩
  have hsub : (Finset.univ.filter fun x => apxF (p := p) ℓ g (s - 1) x ≠ bz p (f x)) ⊆
      (Finset.range s).biUnion fun m => errSet (n := n) (p := p) ℓ g m := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    by_contra hno
    apply hx
    rw [← hf x]
    refine apxF_correct (p := p) ℓ g (s - 1) x fun m' hm' hxm => hno ?_
    exact Finset.mem_biUnion.2 ⟨m', Finset.mem_range.2 (by omega), hxm⟩
  calc _ ≤ ((Finset.range s).biUnion fun m => errSet (n := n) (p := p) ℓ g m).card * 2 ^ ℓ :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
    _ ≤ (∑ m ∈ Finset.range s, (errSet (n := n) (p := p) ℓ g m).card) * 2 ^ ℓ :=
        Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ m ∈ Finset.range s, (errSet (n := n) (p := p) ℓ g m).card * 2 ^ ℓ := Finset.sum_mul _ _ _
    _ ≤ ∑ _m ∈ Finset.range s, 2 ^ n := Finset.sum_le_sum fun m _ => errSet_card (p := p) ℓ g m
    _ = s * 2 ^ n := by simp

end CircApx

end

end SATurday.ProofComplexity
