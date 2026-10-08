import Theory.ProofComplexity.SmolenskyParity
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Razborov–Smolensky for `p = 2`: AC0[⊕] cannot compute MOD_3 (Ladder Rung R4, 1A.7)

Smolensky's argument over a finite field `K` of characteristic `2` containing a cube root of
unity `ω ≠ 1` (here `GaloisField 2 2 = F_4`):

* restricting two inputs of a MOD_3 circuit to constants gives circuits (one level deeper) for
  the three residues `|x| ≡ r (mod 3)` (`restrictG`);
* with `y_i = ω^{x_i} ∈ {1, ω}`, `∏ y_i = ω^{|x|} = Σ_r ω^r [|x| ≡ r]`, and `y⁻¹ = y²` is affine in
  `x_i`; so on the common agreement set of the three approximations every function has degree
  at most `m/2 + D` (`rep_on_agree3`), and the agreement set is small.

LOG: R4 Smolensky2 module (AC0[2] vs MOD_3)
-/

namespace SATurday.ProofComplexity

open Finset

noncomputable section

/-! ## Restricting two inputs to constants -/

section Restrict

variable {n : ℕ}

/-- Extend an input with two constant bits. -/
def extIn (x : Fin n → Bool) (c : ℕ → Bool) : Fin (n + 2) → Bool :=
  fun j => if h : j.val < n then x ⟨j.val, h⟩ else c (j.val - n)

/-- The circuit with inputs `n, n + 1` replaced by the constants `c 0, c 1`. -/
def restrictG (n : ℕ) (c : ℕ → Bool) (g : ℕ → CG) : ℕ → CG := fun m =>
  match g m with
  | .inp i => if i < n then .inp i else if i < n + 2 then (if c (i - n) then .and [] else .or [])
      else .inp i
  | .neg j => .neg j
  | .and l => .and l
  | .or l => .or l
  | .mod r l => .mod r l

theorem cval_restrict (c : ℕ → Bool) (g : ℕ → CG) (x : Fin n → Bool) :
    ∀ m, cval 2 (restrictG n c g) x m = cval 2 g (extIn x c) m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  have hrd : ∀ j, rdV (n := n) (p := 2) (restrictG n c g) m j x =
      rdV (n := n + 2) (p := 2) g m j (extIn x c) := by
    intro j; unfold rdV; split_ifs with h
    · exact ih j h
    · rfl
  rw [cval_eq, cval_eq]
  cases hg : g m with
  | inp i =>
    simp only [restrictG, hg]
    by_cases h1 : i < n
    · simp only [if_pos h1, cval_eq]
      rw [dif_pos h1, dif_pos (by omega)]
      simp [extIn, h1]
    · by_cases h2 : i < n + 2
      · simp only [if_neg h1, if_pos h2]
        rw [dif_pos h2]
        have hx : extIn x c ⟨i, h2⟩ = c (i - n) := by simp [extIn, h1]
        rw [hx]
        cases c (i - n) <;> simp [cval_eq, restrictG, hg, h1, h2]
      · simp only [if_neg h1, if_neg h2]
        rw [dif_neg h2, dif_neg h1]
  | neg j => simp only [restrictG, hg, hrd]
  | and l => simp only [restrictG, hg, hrd]
  | or l => simp only [restrictG, hg, hrd]
  | mod r l => simp only [restrictG, hg, hrd]

theorem foldr_max_map_le (l : List ℕ) (a b : ℕ → ℕ) (h : ∀ j ∈ l, a j ≤ b j + 1) :
    (l.map a).foldr max 0 ≤ (l.map b).foldr max 0 + 1 := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.foldr_cons]
    have h1 := h j (by simp)
    have h2 := ih fun i hi => h i (List.mem_cons_of_mem _ hi)
    omega

theorem cdepth_restrict (c : ℕ → Bool) (g : ℕ → CG) :
    ∀ m, cdepth (restrictG n c g) m ≤ cdepth g m + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  have hch : ∀ j, (if j < m then cdepth (restrictG n c g) j else 0) ≤
      (if j < m then cdepth g j else 0) + 1 := by
    intro j; split_ifs with h
    · exact ih j h
    · omega
  rw [cdepth_eq, cdepth_eq]
  cases hg : g m with
  | inp i =>
    simp only [restrictG, hg]
    split_ifs <;> simp
  | neg j => simp only [restrictG, hg]; exact hch j
  | and l =>
    simp only [restrictG, hg]
    have := foldr_max_map_le l (fun j => if j < m then cdepth (restrictG n c g) j else 0)
      (fun j => if j < m then cdepth g j else 0) fun j _ => hch j
    convert Nat.add_le_add_right this 1 using 2
  | or l =>
    simp only [restrictG, hg]
    have := foldr_max_map_le l (fun j => if j < m then cdepth (restrictG n c g) j else 0)
      (fun j => if j < m then cdepth g j else 0) fun j _ => hch j
    convert Nat.add_le_add_right this 1 using 2
  | mod r l =>
    simp only [restrictG, hg]
    have := foldr_max_map_le l (fun j => if j < m then cdepth (restrictG n c g) j else 0)
      (fun j => if j < m then cdepth g j else 0) fun j _ => hch j
    convert Nat.add_le_add_right this 1 using 2

theorem ccomputes_restrict {g : ℕ → CG} {s d : ℕ} {f : (Fin (n + 2) → Bool) → Bool}
    (h : CComputes (n := n + 2) 2 g s d f) (c : ℕ → Bool) :
    CComputes (n := n) 2 (restrictG n c g) s (d + 1) (fun x => f (extIn x c)) := by
  obtain ⟨hs, hd, hf⟩ := h
  exact ⟨hs, fun m hm => (cdepth_restrict c g m).trans (by have := hd m hm; omega),
    fun x => by rw [cval_restrict, hf]⟩

end Restrict

/-! ## Low degree functions over a field `K` -/

namespace S2

open Classical

section LowDegK

variable {K : Type} [Field K] {n : ℕ}

def bitK (x : Fin n → Bool) (i : Fin n) : K := if x i then 1 else 0

def monoK (I : Finset (Fin n)) (x : Fin n → Bool) : K := ∏ i ∈ I, bitK x i

/-- Functions given by multilinear polynomials over `K` of degree at most `D`. -/
def LowDegK (K : Type) [Field K] (n D : ℕ) (f : (Fin n → Bool) → K) : Prop :=
  ∃ c : Finset (Fin n) → K, (∀ I, c I ≠ 0 → I.card ≤ D) ∧ ∀ x, f x = ∑ I, c I * monoK I x

theorem bitK_idem (x : Fin n → Bool) (i : Fin n) : bitK (K := K) x i * bitK x i = bitK x i := by
  unfold bitK; split_ifs <;> simp

theorem monoK_mul (I J : Finset (Fin n)) (x : Fin n → Bool) :
    monoK (K := K) I x * monoK J x = monoK (I ∪ J) x := by
  unfold monoK
  have h1 : ∏ i ∈ I, bitK (K := K) x i = (∏ i ∈ I \ J, bitK (K := K) x i) * ∏ i ∈ I ∩ J, bitK (K := K) x i := by
    rw [← Finset.prod_union (Finset.disjoint_sdiff_inter I J), Finset.sdiff_union_inter]
  have h2 : ∏ i ∈ J, bitK (K := K) x i = (∏ i ∈ J \ I, bitK (K := K) x i) * ∏ i ∈ I ∩ J, bitK (K := K) x i := by
    rw [Finset.inter_comm, ← Finset.prod_union (Finset.disjoint_sdiff_inter J I),
      Finset.sdiff_union_inter]
  have h3 : (∏ i ∈ I ∩ J, bitK (K := K) x i) * ∏ i ∈ I ∩ J, bitK (K := K) x i = ∏ i ∈ I ∩ J, bitK (K := K) x i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => bitK_idem x i
  have h4 : I ∪ J = (I \ J) ∪ (J \ I) ∪ (I ∩ J) := by ext; simp; tauto
  have hd1 : Disjoint (I \ J) (J \ I) := by
    rw [Finset.disjoint_left]; intro a ha hb; simp at ha hb; exact ha.2 hb.1
  have hd2 : Disjoint ((I \ J) ∪ (J \ I)) (I ∩ J) := by
    rw [Finset.disjoint_left]; intro a ha hb; simp at ha hb; tauto
  rw [h4, Finset.prod_union hd2, Finset.prod_union hd1, h1, h2]
  calc (∏ i ∈ I \ J, bitK (K := K) x i) * (∏ i ∈ I ∩ J, bitK (K := K) x i) *
        ((∏ i ∈ J \ I, bitK (K := K) x i) * ∏ i ∈ I ∩ J, bitK (K := K) x i)
      = (∏ i ∈ I \ J, bitK (K := K) x i) * (∏ i ∈ J \ I, bitK (K := K) x i) *
          ((∏ i ∈ I ∩ J, bitK (K := K) x i) * ∏ i ∈ I ∩ J, bitK (K := K) x i) := by ring
    _ = _ := by rw [h3]

theorem LowDegK.mono_deg {D D' : ℕ} (h : D ≤ D') {f : (Fin n → Bool) → K}
    (hf : LowDegK K n D f) : LowDegK K n D' f := by
  obtain ⟨c, hc, hf⟩ := hf
  exact ⟨c, fun I hI => (hc I hI).trans h, hf⟩

theorem LowDegK.const (k : K) : LowDegK K n 0 (fun _ => k) := by
  refine ⟨fun I => if I = ∅ then k else 0, fun I hI => ?_, fun x => ?_⟩
  · dsimp only at hI
    split_ifs at hI with h
    · subst h; simp
    · exact absurd rfl hI
  · rw [Finset.sum_eq_single ∅]
    · simp [monoK]
    · intro I _ hI; simp [hI]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem LowDegK.var (i : Fin n) : LowDegK K n 1 (fun x => bitK x i) := by
  refine ⟨fun I => if I = {i} then 1 else 0, fun I hI => ?_, fun x => ?_⟩
  · dsimp only at hI
    split_ifs at hI with h
    · subst h; simp
    · exact absurd rfl hI
  · rw [Finset.sum_eq_single {i}]
    · simp [monoK]
    · intro I _ hI; simp [hI]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem LowDegK.add {D : ℕ} {f g : (Fin n → Bool) → K} (hf : LowDegK K n D f)
    (hg : LowDegK K n D g) : LowDegK K n D (fun x => f x + g x) := by
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

theorem LowDegK.smul {D : ℕ} (k : K) {f : (Fin n → Bool) → K} (hf : LowDegK K n D f) :
    LowDegK K n D (fun x => k * f x) := by
  obtain ⟨c, hc, hf⟩ := hf
  refine ⟨fun I => k * c I, fun I hI => hc I (fun h => hI (by dsimp only; rw [h, mul_zero])),
    fun x => ?_⟩
  dsimp only
  rw [hf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun I _ => by ring

theorem LowDegK.neg {D : ℕ} {f : (Fin n → Bool) → K} (hf : LowDegK K n D f) :
    LowDegK K n D (fun x => -f x) := by
  have := hf.smul (-1)
  simpa using this

theorem LowDegK.sub {D : ℕ} {f g : (Fin n → Bool) → K} (hf : LowDegK K n D f)
    (hg : LowDegK K n D g) : LowDegK K n D (fun x => f x - g x) := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

theorem LowDegK.mul {D1 D2 : ℕ} {f g : (Fin n → Bool) → K} (hf : LowDegK K n D1 f)
    (hg : LowDegK K n D2 g) : LowDegK K n (D1 + D2) (fun x => f x * g x) := by
  obtain ⟨c, hc, hf⟩ := hf
  obtain ⟨d, hd, hg⟩ := hg
  let e : Finset (Fin n) → K := fun K =>
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
    rw [← hK', ← monoK_mul]; ring

theorem LowDegK.pow {D : ℕ} {f : (Fin n → Bool) → K} (hf : LowDegK K n D f) :
    ∀ k : ℕ, LowDegK K n (k * D) (fun x => f x ^ k) := by
  intro k
  induction k with
  | zero => simpa using (LowDegK.const (n := n) (K := K) 1)
  | succ k ih =>
      have := ih.mul hf
      simpa [pow_succ, Nat.succ_mul] using this

theorem LowDegK.prod {D : ℕ} {ι : Type*} (s : Finset ι) {f : ι → (Fin n → Bool) → K}
    (hf : ∀ i ∈ s, LowDegK K n D (f i)) : LowDegK K n (s.card * D) (fun x => ∏ i ∈ s, f i x) := by
  induction s using Finset.induction_on with
  | empty => simpa using (LowDegK.const (n := n) (K := K) 1)
  | insert a s ha ih =>
      have h1 := (hf a (Finset.mem_insert_self _ _)).mul
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
      rw [Finset.card_insert_of_notMem ha]
      have e : (s.card + 1) * D = D + s.card * D := by ring
      rw [e]
      simpa [Finset.prod_insert ha] using h1

theorem LowDegK.sum {D : ℕ} {ι : Type*} (s : Finset ι) {f : ι → (Fin n → Bool) → K}
    (hf : ∀ i ∈ s, LowDegK K n D (f i)) : LowDegK K n D (fun x => ∑ i ∈ s, f i x) := by
  induction s using Finset.induction_on with
  | empty => simpa using (LowDegK.const (n := n) (K := K) 0).mono_deg (Nat.zero_le D)
  | insert a s ha ih =>
      have h1 := (hf a (Finset.mem_insert_self _ _)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
      simpa [Finset.sum_insert ha] using h1

theorem LowDegK.const_le {D : ℕ} (k : K) : LowDegK K n D (fun _ => k) :=
  (LowDegK.const k).mono_deg (Nat.zero_le D)

end LowDegK

/-! ## The `{1, ω}` basis -/

section Basis

variable {K : Type} [Field K] {n : ℕ} {ω : K}

/-- `ω^b`. -/
def yv (ω : K) (b : Bool) : K := if b then ω else 1

/-- `∏_{i ∈ S} ω^{x_i}`. -/
def Y (ω : K) (S : Finset (Fin n)) (x : Fin n → Bool) : K := ∏ i ∈ S, yv ω (x i)

theorem yv_eq (ω : K) (b : Bool) (x : Fin n → Bool) (i : Fin n) (hb : x i = b) :
    yv ω b = 1 + (ω - 1) * bitK x i := by
  subst hb; unfold yv bitK; split_ifs <;> ring

theorem Y_lowDeg (ω : K) (S : Finset (Fin n)) : LowDegK K n S.card (Y ω S) := by
  have h : ∀ i ∈ S, LowDegK K n 1 (fun x => yv ω (x i)) := by
    intro i _
    have := (LowDegK.const_le (n := n) (D := 1) (1 : K)).add ((LowDegK.var (K := K) i).smul (ω - 1))
    refine ⟨this.choose, this.choose_spec.1, fun x => ?_⟩
    show yv ω (x i) = _
    rw [yv_eq ω (x i) x i rfl]; exact this.choose_spec.2 x
  have := LowDegK.prod S h
  simpa [Y] using this

theorem yv_sq_lowDeg (ω : K) (i : Fin n) : LowDegK K n 1 (fun x => yv ω (x i) ^ 2) := by
  have := (LowDegK.const_le (n := n) (D := 1) (1 : K)).add ((LowDegK.var (K := K) i).smul (ω ^ 2 - 1))
  refine ⟨this.choose, this.choose_spec.1, fun x => ?_⟩
  rw [← this.choose_spec.2 x]
  show yv ω (x i) ^ 2 = 1 + (ω ^ 2 - 1) * bitK x i
  unfold yv bitK; cases x i <;> simp

theorem Y_univ (ω : K) (x : Fin n → Bool) :
    Y ω univ x = ω ^ (univ.filter fun i => x i = true).card := by
  unfold Y yv
  rw [prod_ite, prod_const_one, mul_one, prod_const]

theorem Y_split (hω3 : ω ^ 3 = 1) (S : Finset (Fin n)) (x : Fin n → Bool) :
    Y ω S x = Y ω univ x * ∏ i ∈ Sᶜ, yv ω (x i) ^ 2 := by
  have h1 : Y ω univ x = Y ω S x * Y ω Sᶜ x := by
    unfold Y; rw [prod_mul_prod_compl]
  have h2 : Y ω Sᶜ x * ∏ i ∈ Sᶜ, yv ω (x i) ^ 2 = 1 := by
    unfold Y; rw [← prod_mul_distrib]
    refine prod_eq_one fun i _ => ?_
    unfold yv; split_ifs
    · rw [← pow_succ']; exact hω3
    · simp
  rw [h1, mul_assoc, h2, mul_one]

/-- Every function is a combination of the `Y S`. -/
theorem basis (hω1 : ω ≠ 1) (f : (Fin n → Bool) → K) :
    ∃ e : Finset (Fin n) → K, ∀ x, f x = ∑ S : Finset (Fin n), e S * Y ω S x := by
  have hne : ω - 1 ≠ 0 := sub_ne_zero.2 hω1
  set β : Bool → K := fun a => ((if a then 1 else 0) - (if a then 0 else 1)) / (ω - 1)
  set α : Bool → K := fun a => (if a then 0 else 1) - β a
  have hδ : ∀ a b : Bool, (if b = a then (1 : K) else 0) = β a * yv ω b + α a := by
    intro a b
    simp only [α, β, yv]
    cases a <;> cases b <;> simp <;> field_simp <;> ring
  have hpt : ∀ x a : Fin n → Bool, (if x = a then (1 : K) else 0) =
      ∏ i, (β (a i) * yv ω (x i) + α (a i)) := by
    intro x a
    simp only [← hδ]
    split_ifs with h
    · subst h; simp
    · obtain ⟨i, hi⟩ : ∃ i, x i ≠ a i := by
        by_contra hc; push Not at hc; exact h (funext hc)
      exact (prod_eq_zero (mem_univ i) (if_neg hi)).symm
  refine ⟨fun S => ∑ a : Fin n → Bool, f a * ((∏ i ∈ S, β (a i)) * ∏ i ∈ univ \ S, α (a i)),
    fun x => ?_⟩
  have hx : f x = ∑ a : Fin n → Bool, f a * (if x = a then (1 : K) else 0) := by
    rw [sum_eq_single x]
    · simp
    · intro a _ ha; rw [if_neg (Ne.symm ha), mul_zero]
    · intro h; exact absurd (mem_univ x) h
  rw [hx]
  simp only [hpt, prod_add, powerset_univ, mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun S _ => sum_congr rfl fun a _ => ?_
  unfold Y
  rw [prod_mul_distrib]
  ring

/-- On the agreement set of a degree `D` function with `ω^{|x|}`, every function has degree at
most `⌊n/2⌋ + D`. -/
theorem rep_on_agree3 (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) {D : ℕ} {P : (Fin n → Bool) → K}
    (hP : LowDegK K n D P) {G : Finset (Fin n → Bool)} (hG : ∀ x ∈ G, P x = Y ω univ x)
    (f : (Fin n → Bool) → K) :
    ∃ h : (Fin n → Bool) → K, LowDegK K n (n / 2 + D) h ∧ ∀ x ∈ G, f x = h x := by
  obtain ⟨e, he⟩ := basis hω1 f
  let term : Finset (Fin n) → (Fin n → Bool) → K := fun S x =>
    if S.card ≤ n / 2 then Y ω S x else P x * ∏ i ∈ Sᶜ, yv ω (x i) ^ 2
  refine ⟨fun x => ∑ S : Finset (Fin n), e S * term S x, ?_, fun x hx => ?_⟩
  · refine LowDegK.sum _ fun S _ => LowDegK.smul (e S) ?_
    by_cases hS : S.card ≤ n / 2
    · have := (Y_lowDeg ω S).mono_deg (show S.card ≤ n / 2 + D by omega)
      refine ⟨this.choose, this.choose_spec.1, fun x => ?_⟩
      simp only [term, if_pos hS]; exact this.choose_spec.2 x
    · have h2 := LowDegK.prod Sᶜ fun i _ => yv_sq_lowDeg (n := n) ω i
      have hc : Sᶜ.card ≤ n / 2 := by rw [card_compl, Fintype.card_fin]; omega
      have := (hP.mul h2).mono_deg (show D + Sᶜ.card * 1 ≤ n / 2 + D by omega)
      refine ⟨this.choose, this.choose_spec.1, fun x => ?_⟩
      simp only [term, if_neg hS]; exact this.choose_spec.2 x
  · rw [he x]
    refine sum_congr rfl fun S _ => ?_
    simp only [term]
    split_ifs with hS
    · rfl
    · rw [Y_split hω3 S x, hG x hx]

theorem agree_card_le3 [Fintype K] (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) {D : ℕ}
    {P : (Fin n → Bool) → K} (hP : LowDegK K n D P) {G : Finset (Fin n → Bool)}
    (hG : ∀ x ∈ G, P x = Y ω univ x) :
    G.card ≤ (univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + D).card := by
  set T := univ.filter fun S : Finset (Fin n) => S.card ≤ n / 2 + D
  let Φ : (T → K) → (G → K) := fun c x => ∑ S : T, c S * monoK S.1 x.1
  have hsurj : Function.Surjective Φ := by
    intro φ
    let f : (Fin n → Bool) → K := fun x => if hx : x ∈ G then φ ⟨x, hx⟩ else 0
    obtain ⟨h, ⟨c, hc, hh⟩, hfh⟩ := rep_on_agree3 hω1 hω3 hP hG f
    refine ⟨fun S => c S.1, funext fun x => ?_⟩
    show ∑ S : T, c S.1 * monoK S.1 x.1 = φ x
    have e1 : ∑ S : T, c S.1 * monoK (K := K) S.1 x.1 = ∑ S ∈ T, c S * monoK S x.1 :=
      sum_coe_sort T (fun S => c S * monoK S x.1)
    have e2 : ∑ S ∈ T, c S * monoK (K := K) S x.1 = ∑ S : Finset (Fin n), c S * monoK S x.1 := by
      refine sum_subset (subset_univ _) fun S _ hS => ?_
      have : c S = 0 := by
        by_contra hne; exact hS (mem_filter.2 ⟨mem_univ _, hc S hne⟩)
      rw [this, zero_mul]
    rw [e1, e2, ← hh, ← hfh x.1 x.2]
    simp [f, x.2]
  have hcard := Fintype.card_le_of_surjective Φ hsurj
  simp only [Fintype.card_fun, Fintype.card_coe] at hcard
  have hK : 1 < Fintype.card K := Fintype.one_lt_card
  exact (Nat.pow_le_pow_iff_right hK).1 hcard

end Basis


end S2

/-! ## MOD_3 is hard for AC0[2] -/

section Final

open Classical S2

/-- Number of ones. -/
def cnt3 {n : ℕ} (x : Fin n → Bool) : ℕ := (univ.filter fun i => x i = true).card

/-- `MOD_3`: the number of ones is divisible by `3`. -/
def mod3 {n : ℕ} (x : Fin n → Bool) : Bool := decide (cnt3 x % 3 = 0)

theorem cnt3_ext {m : ℕ} (x : Fin m → Bool) (c : ℕ → Bool) :
    cnt3 (extIn x c) = cnt3 x + (if c 0 then 1 else 0) + (if c 1 then 1 else 0) := by
  unfold cnt3
  rw [card_filter, card_filter, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp [extIn, Fin.val_last]

/-- Lifting low degree functions from `ZMod 2` to an algebra. -/
theorem lift_lowDeg {K : Type} [Field K] [Algebra (ZMod 2) K] {m D : ℕ}
    {P : (Fin m → Bool) → ZMod 2} (hP : LowDeg 2 m D P) :
    LowDegK K m D (fun x => algebraMap (ZMod 2) K (P x)) := by
  obtain ⟨c, hc, hP⟩ := hP
  refine ⟨fun I => algebraMap (ZMod 2) K (c I), fun I hI => hc I (fun h => hI (by simp only; rw [h, map_zero])),
    fun x => ?_⟩
  simp only
  rw [hP x, map_sum]
  refine sum_congr rfl fun I _ => ?_
  rw [map_mul]
  congr 1
  unfold mono monoK; rw [map_prod]
  refine prod_congr rfl fun i _ => ?_
  unfold bitF bitK; split_ifs <;> simp

/-- AC0[2] circuits computing `MOD_3` have super polynomial size. -/
def Mod3AC02LB : Prop :=
  ∀ d c : ℕ, ∃ N, ∀ n ≥ N, ∀ (g : ℕ → CG) (s : ℕ),
    CComputes (n := n) 2 g s d mod3 → n ^ c < s

theorem exists_cube_root : ∃ ω : GaloisField 2 2, ω ≠ 1 ∧ ω ^ 3 = 1 := by
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 2) = 4 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 2 (by norm_num)]; norm_num
  have : ((univ : Finset (GaloisField 2 2)) \ {0, 1}).Nonempty := by
    rw [← card_pos, card_sdiff_of_subset (subset_univ _), card_univ, hcard]
    have := card_le_two (a := (0 : GaloisField 2 2)) (b := 1); omega
  obtain ⟨ω, hω⟩ := this
  simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and, not_or] at hω
  refine ⟨ω, hω.2, ?_⟩
  have := FiniteField.pow_card_sub_one_eq_one ω hω.1
  rwa [hcard] at this

/-- **Razborov–Smolensky, `p = 2`**: AC0[2] circuits computing MOD_3 need super polynomial
size. -/
theorem smolensky_mod3 : Mod3AC02LB := by
  intro d c
  set Kc := (c + 5) ^ (d + 1)
  obtain ⟨T, hT⟩ := eventually_poly_lt_two_pow (128 * Kc * Kc) (2 * (d + 1))
  refine ⟨2 ^ (T + 1) + 4, fun n hn g s hC => ?_⟩
  have h4 : 4 ≤ n := le_trans (Nat.le_add_left 4 _) hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set n := m + 2 with hndef
  have hn1 : 1 ≤ n := by omega
  set t := Nat.log 2 n
  have htT : T ≤ t := by
    have : T + 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by omega)
    omega
  have h2t : 2 ^ t ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hnt : n < 2 ^ (t + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  set ℓ := (c + 5) * (t + 1)
  have hℓ : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  set D := ℓ ^ (d + 1)
  by_contra hlt
  push Not at hlt
  -- the three residue circuits
  let cc : Fin 3 → ℕ → Bool := fun k i => if k.val = 0 then false else
    if k.val = 1 then (i = 0) else true
  have hres : ∀ k : Fin 3, ∃ P : (Fin m → Bool) → ZMod 2, LowDeg 2 m D P ∧
      (univ.filter fun x => P x ≠ bz 2 (mod3 (extIn x (cc k)))).card * 2 ^ ℓ ≤ s * 2 ^ m := by
    intro k
    obtain ⟨P, hP, hE⟩ := circuit_approx (p := 2) ℓ (restrictG m (cc k) g) hℓ
      (ccomputes_restrict hC (cc k))
    refine ⟨P, ?_, hE⟩
    simpa [D] using hP
  choose P hP hE using hres
  set F := GaloisField 2 2
  letI : Fintype F := Fintype.ofFinite _
  obtain ⟨ω, hω1, hω3⟩ := exists_cube_root
  let ι := algebraMap (ZMod 2) F
  set Q : (Fin m → Bool) → F := fun x => ι (P 0 x) + ω ^ 2 * ι (P 1 x) + ω * ι (P 2 x)
  have hQ : LowDegK F m D Q :=
    ((lift_lowDeg (hP 0)).add ((lift_lowDeg (hP 1)).smul (ω ^ 2))).add
      ((lift_lowDeg (hP 2)).smul ω)
  set G := univ.filter fun x : Fin m → Bool => ∀ k : Fin 3, P k x = bz 2 (mod3 (extIn x (cc k)))
  set E := univ.filter fun x : Fin m → Bool => ¬ ∀ k : Fin 3, P k x = bz 2 (mod3 (extIn x (cc k)))
  have hQG : ∀ x ∈ G, Q x = S2.Y ω univ x := by
    intro x hx
    have h := (mem_filter.1 hx).2
    rw [S2.Y_univ]
    have hc0 : cnt3 (extIn x (cc 0)) = cnt3 x := by rw [cnt3_ext]; simp [cc]
    have hc1 : cnt3 (extIn x (cc 1)) = cnt3 x + 1 := by rw [cnt3_ext]; simp [cc]
    have hc2 : cnt3 (extIn x (cc 2)) = cnt3 x + 2 := by rw [cnt3_ext]; simp [cc]
    have hcnt : (univ.filter fun i => x i = true).card = cnt3 x := rfl
    simp only [Q, h 0, h 1, h 2, mod3, hc0, hc1, hc2, hcnt]
    have hpow : ω ^ cnt3 x = ω ^ (cnt3 x % 3) := by
      conv_lhs => rw [← Nat.div_add_mod (cnt3 x) 3, pow_add, pow_mul, hω3, one_pow, one_mul]
    rw [hpow]
    have h3 := Nat.mod_lt (cnt3 x) (by norm_num : 0 < 3)
    interval_cases hr : cnt3 x % 3 <;> simp [bz, ι, hr, Nat.add_mod] <;> ring
  have hGcard := S2.agree_card_le3 hω1 hω3 hQ hQG
  have hTc := low_card_le m D
  have hGE : G.card + E.card = 2 ^ m := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin m → Bool)))
      (fun x => ∀ k : Fin 3, P k x = bz 2 (mod3 (extIn x (cc k))))
    rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
    exact this
  -- the error set is small
  have hEsub : E ⊆ (univ.filter fun x => P 0 x ≠ bz 2 (mod3 (extIn x (cc 0)))) ∪
      (univ.filter fun x => P 1 x ≠ bz 2 (mod3 (extIn x (cc 1)))) ∪
      (univ.filter fun x => P 2 x ≠ bz 2 (mod3 (extIn x (cc 2)))) := by
    intro x hx
    simp only [E, mem_filter, mem_univ, true_and, not_forall] at hx
    obtain ⟨k, hk⟩ := hx
    simp only [mem_union, mem_filter, mem_univ, true_and]
    fin_cases k
    · exact Or.inl (Or.inl hk)
    · exact Or.inl (Or.inr hk)
    · exact Or.inr hk
  have hE3 : E.card * 2 ^ ℓ ≤ 3 * (s * 2 ^ m) := by
    have := (card_le_card hEsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
    calc E.card * 2 ^ ℓ ≤ (_ + _ + _) * 2 ^ ℓ := Nat.mul_le_mul_right _ this
      _ = _ := by ring
      _ ≤ s * 2 ^ m + s * 2 ^ m + s * 2 ^ m := Nat.add_le_add (Nat.add_le_add (hE 0) (hE 1)) (hE 2)
      _ = 3 * (s * 2 ^ m) := by ring
  have h2l : 24 * n ^ c ≤ 2 ^ ℓ := by
    have h1 : (n + 1) ^ (c + 5) ≤ 2 ^ ℓ := by
      calc (n + 1) ^ (c + 5) ≤ (2 ^ (t + 1)) ^ (c + 5) := Nat.pow_le_pow_left hnt (c + 5)
        _ = 2 ^ ℓ := by
            show (2 ^ (t + 1)) ^ (c + 5) = 2 ^ ((c + 5) * (t + 1))
            rw [← pow_mul]; ring_nf
    have h2 : 24 * n ^ c ≤ (n + 1) ^ (c + 5) := by
      calc 24 * n ^ c ≤ (n + 1) ^ 5 * (n + 1) ^ c :=
            Nat.mul_le_mul (le_trans (by norm_num) (Nat.pow_le_pow_left (show 2 ≤ n + 1 by omega) 5))
              (Nat.pow_le_pow_left (by omega) c)
        _ = (n + 1) ^ (c + 5) := by ring
    omega
  have hEs : 8 * E.card ≤ 2 ^ m := by
    have h1 : E.card * (24 * n ^ c) ≤ E.card * 2 ^ ℓ := Nat.mul_le_mul_left _ h2l
    have h2 : 3 * (s * 2 ^ m) ≤ 3 * (n ^ c * 2 ^ m) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hlt)
    have hnc : 0 < n ^ c := by positivity
    have : (E.card * 8) * n ^ c ≤ 2 ^ m * n ^ c := by nlinarith
    have := Nat.le_of_mul_le_mul_right this hnc
    omega
  -- the binomial term is small
  have hD : 32 * (D + 1) ^ 2 ≤ m + 1 := by
    have hDK : D + 1 ≤ 2 * Kc * (t + 1) ^ (d + 1) := by
      have e : D = Kc * (t + 1) ^ (d + 1) := by simp only [D, Kc, ℓ]; rw [← mul_pow]
      have hK1 : 1 ≤ Kc * (t + 1) ^ (d + 1) := by
        have : 1 ≤ Kc := Nat.one_le_pow _ _ (by omega)
        have : 1 ≤ (t + 1) ^ (d + 1) := Nat.one_le_pow _ _ (by omega)
        nlinarith
      have e2 : 2 * Kc * (t + 1) ^ (d + 1) = 2 * (Kc * (t + 1) ^ (d + 1)) := by ring
      rw [e, e2]; omega
    have hpoly := hT t htT
    calc 32 * (D + 1) ^ 2 ≤ 32 * (2 * Kc * (t + 1) ^ (d + 1)) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hDK 2)
      _ = 128 * Kc * Kc * (t + 1) ^ (2 * (d + 1)) := by ring
      _ ≤ m + 1 := by omega
  have hCm := choose_half_sq_le m
  have hW : 4 * ((D + 1) * m.choose (m / 2)) ≤ 2 ^ m := by
    have h1 : (4 * ((D + 1) * m.choose (m / 2))) ^ 2 * 2 ≤ (2 ^ m) ^ 2 * 2 := by
      calc (4 * ((D + 1) * m.choose (m / 2))) ^ 2 * 2
          = (32 * (D + 1) ^ 2) * m.choose (m / 2) ^ 2 := by ring
        _ ≤ (m + 1) * m.choose (m / 2) ^ 2 := Nat.mul_le_mul_right _ hD
        _ = m.choose (m / 2) ^ 2 * (m + 1) := by ring
        _ ≤ 2 * 4 ^ m := hCm
        _ = (2 ^ m) ^ 2 * 2 := by
            rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
    have h2 := Nat.le_of_mul_le_mul_right h1 (by norm_num : 0 < 2)
    exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).1 h2
  have hX : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hT2 : (univ.filter fun S : Finset (Fin m) => S.card ≤ m / 2 + D).card * 2 ≤
      2 ^ m + 2 * ((D + 1) * m.choose (m / 2)) := by convert hTc
  omega

end Final

end

end SATurday.ProofComplexity
