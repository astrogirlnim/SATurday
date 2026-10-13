import Theory.ProofComplexity.PCMultilinear
import Theory.ProofComplexity.GreenBinom

/-!
# Immunity of the mod `q` predicate (Ladder Rung R4, AR-B)

Alekhnovich-Razborov Theorem 4.4 through the elementary route of Beck-Li (arXiv:1304.0713, Section 5):
over a field `F` with `(q : F) ≠ 0`, every nonzero multilinear `g` vanishing on the Boolean points
whose weight on an `n`-set `A` is `≡ s (mod q)` has degree at least `⌊(n + 1) / q⌋`
(`green_immune`).  The proof is by induction on `n`: either `g` is invariant under all
transpositions of `A` (then it is a combination of binomials of the weight and the rank lemma of
`GreenBinom` applies), or `g - (i j) g = (x_i - x_j) h` with `h` a nonzero polynomial on `A \ {i,j}`
of degree one less vanishing on the class `s - 1`.  No averaging is used, so it works in every
characteristic.

LOG: R4 AR-B GreenImmunity
-/

namespace SATurday.ProofComplexity.Green

open Finset SATurday.ProofComplexity.PCL

noncomputable section
open Classical

variable {F : Type} [Field F]

/-- The variables of `A` set to `1` by the Boolean point `a`. -/
def fl (A : Finset ℕ) (a : Set ℕ) : Finset ℕ := A.filter fun x => x ∈ a

theorem mem_fl {A : Finset ℕ} {a : Set ℕ} {x : ℕ} : x ∈ fl A a ↔ x ∈ A ∧ x ∈ a := by
  unfold fl; rw [Finset.mem_filter]

theorem fl_coe {A t : Finset ℕ} (h : t ⊆ A) : fl A (↑t : Set ℕ) = t := by
  ext x; rw [mem_fl]; simp only [Finset.mem_coe]
  exact ⟨fun h => h.2, fun hx => ⟨h hx, hx⟩⟩

/-- The class of Boolean points of `A`-weight `≡ s (mod q)`. -/
def ZA (q : ℕ) (A : Finset ℕ) (s : ZMod q) : Set (Set ℕ) :=
  {a | (((fl A a).card : ℕ) : ZMod q) = s}

/-- `g` is supported on subsets of `A`. -/
def Sup (A : Finset ℕ) (g : ML F) : Prop := ∀ T ∈ g.support, T ⊆ A

/-- Evaluation of a polynomial supported in `A` as a sum over the powerset of the true variables. -/
theorem evA {A : Finset ℕ} {g : ML F} (hA : Sup A g) (a : Set ℕ) :
    ev a g = ∑ T ∈ (fl A a).powerset, g T := by
  rw [ev_apply, ← Finset.sum_filter]
  apply Finset.sum_subset
  · intro T hT
    rw [Finset.mem_filter] at hT
    rw [Finset.mem_powerset]
    intro x hx
    rw [mem_fl]
    exact ⟨hA T hT.1 hx, hT.2 (by exact_mod_cast hx)⟩
  · intro T hT hn
    by_contra hne
    apply hn
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · exact Finsupp.mem_support_iff.2 hne
    · intro x hx
      have := (mem_fl.1 ((Finset.mem_powerset.1 hT) (by exact_mod_cast hx))).2
      exact this

/-! ## Transpositions -/

/-- The image of a term under the transposition `(i j)`. -/
def sw (i j : ℕ) (T : Finset ℕ) : Finset ℕ := T.image (Equiv.swap i j)

theorem mem_sw {i j : ℕ} {T : Finset ℕ} {x : ℕ} : x ∈ sw i j T ↔ Equiv.swap i j x ∈ T := by
  unfold sw
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩; simpa using hy
  · intro h; exact ⟨_, h, by simp⟩

theorem card_sw (i j : ℕ) (T : Finset ℕ) : (sw i j T).card = T.card :=
  Finset.card_image_of_injective _ (Equiv.injective _)

theorem sw_eq_self {i j : ℕ} {T : Finset ℕ} (h : (i ∈ T ↔ j ∈ T)) : sw i j T = T := by
  ext x
  rw [mem_sw]
  by_cases hi : x = i
  · subst hi; simp [h]
  · by_cases hj : x = j
    · subst hj; simp [h]
    · simp [Equiv.swap_apply_of_ne_of_ne hi hj]

theorem sw_eq_insert {i j : ℕ} {T : Finset ℕ} (hi : i ∈ T) (hj : j ∉ T) :
    sw i j T = insert j (T.erase i) := by
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  ext x
  rw [mem_sw, Finset.mem_insert, Finset.mem_erase]
  by_cases h1 : x = i
  · subst h1; simp [hj, hij]
  · by_cases h2 : x = j
    · subst h2; simp [hi]
    · simp [Equiv.swap_apply_of_ne_of_ne h1 h2, h1, h2]

theorem sw_mem_sub {A : Finset ℕ} {i j : ℕ} (hi : i ∈ A) (hj : j ∈ A) {T : Finset ℕ}
    (hT : T ⊆ A) : sw i j T ⊆ A := by
  intro x hx
  rw [mem_sw] at hx
  have := hT hx
  by_cases h1 : x = i
  · subst h1; exact hi
  · by_cases h2 : x = j
    · subst h2; exact hj
    · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2] at this

/-! ## The symmetric case -/

theorem sym_card {A : Finset ℕ} {g : ML F} (hA : Sup A g)
    (hs : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∀ T, g (sw i j T) = g T) :
    ∀ (d : ℕ) (T T' : Finset ℕ), (T \ T').card = d → T ⊆ A → T' ⊆ A → T.card = T'.card →
      g T = g T' := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro T T' hd hT hT' hc
    by_cases h0 : T \ T' = ∅
    · have hsub : T ⊆ T' := Finset.sdiff_eq_empty_iff_subset.1 h0
      rw [Finset.eq_of_subset_of_card_le hsub hc.ge]
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 h0
      rw [Finset.mem_sdiff] at hx
      have h1 := Finset.card_sdiff_add_card_inter T T'
      have h2 := Finset.card_sdiff_add_card_inter T' T
      rw [Finset.inter_comm] at h2
      have hpos : 0 < (T' \ T).card := by
        have : 0 < (T \ T').card := Finset.card_pos.2 ⟨x, Finset.mem_sdiff.2 hx⟩
        omega
      obtain ⟨y, hy⟩ := Finset.card_pos.1 hpos
      rw [Finset.mem_sdiff] at hy
      have hxy : x ≠ y := fun h => hy.2 (h ▸ hx.1)
      have hxA : x ∈ A := hT hx.1
      have hyA : y ∈ A := hT' hy.1
      set T1 := sw x y T with hT1
      have hT1A : T1 ⊆ A := sw_mem_sub hxA hyA hT
      have hT1c : T1.card = T'.card := by rw [hT1, card_sw]; exact hc
      have hgT : g T1 = g T := hs x hxA y hyA hxy T
      have hT1eq : T1 = insert y (T.erase x) := sw_eq_insert hx.1 hy.2
      have hsub : T1 \ T' ⊆ (T \ T').erase x := by
        intro z hz
        rw [Finset.mem_sdiff] at hz
        rw [hT1eq, Finset.mem_insert, Finset.mem_erase] at hz
        rw [Finset.mem_erase, Finset.mem_sdiff]
        rcases hz.1 with h | h
        · exact absurd (h ▸ hy.1) hz.2
        · exact ⟨h.1, h.2, hz.2⟩
      have hlt : (T1 \ T').card < d := by
        rw [← hd]
        exact lt_of_le_of_lt (Finset.card_le_card hsub)
          (Finset.card_erase_lt_of_mem (Finset.mem_sdiff.2 hx))
      rw [← hgT]
      exact ih _ hlt T1 T' rfl hT1A hT' hT1c

theorem sym_exists {A : Finset ℕ} {g : ML F} (hA : Sup A g)
    (hs : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∀ T, g (sw i j T) = g T) :
    ∃ c : ℕ → F, ∀ T ⊆ A, g T = c T.card := by
  refine ⟨fun k => if h : ∃ T, T ⊆ A ∧ T.card = k then g h.choose else 0, fun T hT => ?_⟩
  have h : ∃ T', T' ⊆ A ∧ T'.card = T.card := ⟨T, hT, rfl⟩
  show g T = (if h : ∃ T', T' ⊆ A ∧ T'.card = T.card then g h.choose else 0)
  rw [dif_pos h]
  exact sym_card hA hs _ T _ rfl hT h.choose_spec.1 h.choose_spec.2.symm

theorem natCast_progression {q : ℕ} [NeZero q] (s : ZMod q) (i : ℕ) :
    (((s.val + i * q : ℕ)) : ZMod q) = s := by
  push_cast
  simp

/-- The degree bound for polynomials invariant under all transpositions of `A`. -/
theorem sym_deg {q : ℕ} [NeZero q] (hq : (q : F) ≠ 0) {A : Finset ℕ} {g : ML F} (hA : Sup A g)
    (hs : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∀ T, g (sw i j T) = g T) (s : ZMod q) (hg : g ≠ 0)
    (hv : ∀ a ∈ ZA q A s, ev a g = 0) : (A.card + 1) / q ≤ deg g := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨c, hc⟩ := sym_exists hA hs
  set e := deg g with he
  set c' : ℕ → F := fun k => if k ≤ e then c k else 0 with hc'
  have hgc : ∀ T ⊆ A, g T = c' T.card := by
    intro T hT
    by_cases hle : T.card ≤ e
    · simp [hc', hle, hc T hT]
    · have : T ∉ g.support := fun h => hle (le_deg h)
      simp [hc', hle, Finsupp.notMem_support_iff.1 this]
  have hc'z : ∀ k, e + 1 ≤ k → c' k = 0 := by
    intro k hk; simp [hc', show ¬ k ≤ e by omega]
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hdiv : (e + 1) * q ≤ A.card + 1 := by
    have := Nat.div_mul_le_self (A.card + 1) q
    nlinarith [Nat.succ_le_of_lt hlt, Nat.mul_le_mul_right q (Nat.succ_le_of_lt hlt)]
  have hz : ∀ i < e + 1, phi (e + 1) c' (s.val + i * q) = 0 := by
    intro i hi
    have hsv : s.val < q := ZMod.val_lt s
    have hw : s.val + i * q ≤ A.card := by
      have : i * q + q ≤ e * q + q := by nlinarith
      nlinarith
    obtain ⟨t, htA, htc⟩ := Finset.exists_subset_card_eq (s := A) hw
    have hmem : (↑t : Set ℕ) ∈ ZA q A s := by
      unfold ZA
      simp only [Set.mem_setOf_eq]
      rw [fl_coe htA, htc]
      exact natCast_progression s i
    have h0 := hv _ hmem
    rw [evA hA] at h0
    rw [fl_coe htA] at h0
    have h1 : ∑ T ∈ t.powerset, g T = ∑ T ∈ t.powerset, c' T.card :=
      Finset.sum_congr rfl fun T hT => hgc T ((Finset.mem_powerset.1 hT).trans htA)
    rw [h1, Finset.sum_powerset_apply_card (fun k => c' k), htc] at h0
    set w := s.val + i * q
    have h2 : ∑ k ∈ range (w + 1), (w.choose k) • c' k = phi (e + 1) c' w := by
      unfold phi
      have hf : ∀ k, (w.choose k) • c' k = c' k * (w.choose k : F) := by
        intro k; rw [nsmul_eq_mul]; ring
      simp only [hf]
      have hz1 : ∀ k, w + 1 ≤ k → c' k * (w.choose k : F) = 0 := by
        intro k hk; simp [Nat.choose_eq_zero_of_lt (show w < k by omega)]
      have hz2 : ∀ k, e + 1 ≤ k → c' k * (w.choose k : F) = 0 := by
        intro k hk; simp [hc'z k hk]
      have key : ∀ M, ∀ f : ℕ → F, (∀ k, M ≤ k → f k = 0) → ∀ M', M ≤ M' →
          ∑ k ∈ range M', f k = ∑ k ∈ range M, f k := by
        intro M f hf M' hM'
        symm
        apply Finset.sum_subset (Finset.range_subset_range.2 hM')
        intro k hk hn
        exact hf k (by simpa using hn)
      rw [← key (w + 1) _ hz1 (max (w + 1) (e + 1)) (le_max_left _ _),
        ← key (e + 1) _ hz2 (max (w + 1) (e + 1)) (le_max_right _ _)]
    rw [← h2]; exact h0
  have hall := rank_lemma hq (e + 1) c' s.val hc'z hz
  apply hg
  ext T
  by_cases hT : T ∈ g.support
  · have := hgc T (hA T hT)
    rw [this, hall]; rfl
  · simpa using Finsupp.notMem_support_iff.1 hT


/-! ## The difference polynomial `h` -/

theorem sw_comm (i j : ℕ) (T : Finset ℕ) : sw i j T = sw j i T := by
  unfold sw; rw [Equiv.swap_comm]

/-- `h(T) = g(T ∪ {i}) - g(T ∪ {j})` for `T ⊆ (A \ {i}) \ {j}` (so that `g - (i j) g = (x_i - x_j) h`). -/
def hdiff (g : ML F) (A : Finset ℕ) (i j : ℕ) : ML F :=
  Finsupp.onFinset (g.support.image (fun T => T.erase i) ∪ g.support.image (fun T => T.erase j))
    (fun T => if T ⊆ (A.erase i).erase j then g (insert i T) - g (insert j T) else 0) (by
      intro T hT
      dsimp only at hT
      by_cases hT' : T ⊆ (A.erase i).erase j
      · rw [if_pos hT'] at hT
        have hiT : i ∉ T := fun h => by have := hT' h; simp at this
        have hjT : j ∉ T := fun h => by have := hT' h; simp at this
        by_cases h1 : g (insert i T) = 0
        · have h2 : g (insert j T) ≠ 0 := by
            intro h2; apply hT; rw [h1, h2]; simp
          apply Finset.mem_union_right
          exact Finset.mem_image.2
            ⟨insert j T, Finsupp.mem_support_iff.2 h2, Finset.erase_insert hjT⟩
        · apply Finset.mem_union_left
          exact Finset.mem_image.2
            ⟨insert i T, Finsupp.mem_support_iff.2 h1, Finset.erase_insert hiT⟩
      · rw [if_neg hT'] at hT; exact absurd rfl hT)

theorem hdiff_apply (g : ML F) (A : Finset ℕ) (i j : ℕ) (T : Finset ℕ) :
    hdiff g A i j T =
      if T ⊆ (A.erase i).erase j then g (insert i T) - g (insert j T) else 0 := by
  simp [hdiff]

theorem Sup_hdiff (g : ML F) (A : Finset ℕ) (i j : ℕ) : Sup ((A.erase i).erase j) (hdiff g A i j) := by
  intro T hT
  by_contra h
  apply (Finsupp.mem_support_iff.1 hT)
  rw [hdiff_apply, if_neg h]

theorem hdiff_ne_of {A : Finset ℕ} {g : ML F} (hA : Sup A g) {i j : ℕ} (hij : i ≠ j) (T0 : Finset ℕ)
    (hi : i ∉ T0) (hj : j ∉ T0) (hne : g (insert i T0) ≠ g (insert j T0)) :
    hdiff g A i j ≠ 0 := by
  have hsub : T0 ⊆ (A.erase i).erase j := by
    have hmem : ∀ x ∈ T0, x ∈ A → x ∈ (A.erase i).erase j := by
      intro x hx hxA
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨fun h => hj (h ▸ hx), fun h => hi (h ▸ hx), hxA⟩
    by_cases h1 : g (insert i T0) = 0
    · have h2 : g (insert j T0) ≠ 0 := fun h2 => hne (by rw [h1, h2])
      intro x hx
      exact hmem x hx (hA _ (Finsupp.mem_support_iff.2 h2) (Finset.mem_insert_of_mem hx))
    · intro x hx
      exact hmem x hx (hA _ (Finsupp.mem_support_iff.2 h1) (Finset.mem_insert_of_mem hx))
  intro h0
  have := hdiff_apply g A i j T0
  rw [h0, if_pos hsub] at this
  exact hne (sub_eq_zero.1 this.symm)

theorem hdiff_ne {A : Finset ℕ} {g : ML F} (hA : Sup A g) {i j : ℕ} (hij : i ≠ j) {T : Finset ℕ}
    (hT : g (sw i j T) ≠ g T) : hdiff g A i j ≠ 0 := by
  by_cases hiT : i ∈ T
  · by_cases hjT : j ∈ T
    · exact absurd (by rw [sw_eq_self ⟨fun _ => hjT, fun _ => hiT⟩]) hT
    · rw [sw_eq_insert hiT hjT] at hT
      refine hdiff_ne_of hA hij (T.erase i) (by simp) (by simp [hjT]) ?_
      rw [Finset.insert_erase hiT]
      exact fun h => hT h.symm
  · by_cases hjT : j ∈ T
    · rw [sw_comm, sw_eq_insert hjT hiT] at hT
      refine hdiff_ne_of hA hij (T.erase j) (by simp [hiT]) (by simp) ?_
      rw [Finset.insert_erase hjT]
      exact hT
    · exact absurd (by rw [sw_eq_self ⟨fun h => absurd h hiT, fun h => absurd h hjT⟩]) hT

theorem card_diff_lt {A : Finset ℕ} {g : ML F} {i j : ℕ} (hh : hdiff g A i j ≠ 0) :
    deg (hdiff g A i j) + 1 ≤ deg g := by
  obtain ⟨T, hT, hTe⟩ := Finset.exists_mem_eq_sup (hdiff g A i j).support
    (Finsupp.support_nonempty_iff.2 hh) Finset.card
  have hne := Finsupp.mem_support_iff.1 hT
  rw [hdiff_apply] at hne
  by_cases hsub : T ⊆ (A.erase i).erase j
  · rw [if_pos hsub] at hne
    have hiT : i ∉ T := fun h => by have := hsub h; simp at this
    have hjT : j ∉ T := fun h => by have := hsub h; simp at this
    show (hdiff g A i j).support.sup Finset.card + 1 ≤ deg g
    rw [hTe]
    by_cases h1 : g (insert i T) = 0
    · have h2 : g (insert j T) ≠ 0 := fun h2 => hne (by rw [h1, h2]; simp)
      have := le_deg (Finsupp.mem_support_iff.2 h2)
      rwa [Finset.card_insert_of_notMem hjT] at this
    · have := le_deg (Finsupp.mem_support_iff.2 h1)
      rwa [Finset.card_insert_of_notMem hiT] at this
  · rw [if_neg hsub] at hne; exact absurd rfl hne

theorem ev_diff {A : Finset ℕ} {g : ML F} (hA : Sup A g) {i j : ℕ} (hiA : i ∈ A) (hjA : j ∈ A)
    (hij : i ≠ j) (B : Finset ℕ) (hB : B ⊆ (A.erase i).erase j) :
    ev (((B : Set ℕ)) ∪ {i}) g - ev ((B : Set ℕ) ∪ {j}) g = ev (B : Set ℕ) (hdiff g A i j) := by
  have hBA : B ⊆ A := fun x hx => by have := hB hx; simp at this; exact this.2.2
  have hiB : i ∉ B := fun h => by have := hB h; simp at this
  have hjB : j ∉ B := fun h => by have := hB h; simp at this
  have f1 : ∀ k ∈ A, k ∉ B → fl A ((B : Set ℕ) ∪ {k}) = insert k B := by
    intro k hk _
    ext x
    simp only [mem_fl, Set.mem_union, Finset.mem_coe, Set.mem_singleton_iff,
      Finset.mem_insert]
    constructor
    · rintro ⟨_, h | h⟩
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · exact ⟨h ▸ hk, Or.inr h⟩
      · exact ⟨hBA h, Or.inl h⟩
  rw [evA hA, evA hA, f1 i hiA hiB, f1 j hjA hjB, Finset.sum_powerset_insert hiB,
    Finset.sum_powerset_insert hjB, evA (Sup_hdiff g A i j)]
  have f2 : fl ((A.erase i).erase j) (B : Set ℕ) = B := fl_coe hB
  rw [f2, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [hdiff_apply, if_pos ((Finset.mem_powerset.1 hT).trans hB)]

theorem hdiff_vanish {q : ℕ} {A : Finset ℕ} {g : ML F} (hA : Sup A g) {i j : ℕ} (hiA : i ∈ A)
    (hjA : j ∈ A) (hij : i ≠ j) (s : ZMod q) (hv : ∀ a ∈ ZA q A s, ev a g = 0) :
    ∀ a ∈ ZA q ((A.erase i).erase j) (s - 1), ev a (hdiff g A i j) = 0 := by
  intro a ha
  set B := fl ((A.erase i).erase j) a with hBdef
  have hB : B ⊆ (A.erase i).erase j := fun x hx => (mem_fl.1 hx).1
  have hiB : i ∉ B := fun h => by have := hB h; simp at this
  have hjB : j ∉ B := fun h => by have := hB h; simp at this
  have hBA : B ⊆ A := fun x hx => by have := hB hx; simp at this; exact this.2.2
  have hcard : ((B.card : ℕ) : ZMod q) = s - 1 := ha
  have f1 : ∀ k ∈ A, k ∉ B → fl A ((B : Set ℕ) ∪ {k}) = insert k B := by
    intro k hk _
    ext x
    simp only [mem_fl, Set.mem_union, Finset.mem_coe, Set.mem_singleton_iff,
      Finset.mem_insert]
    constructor
    · rintro ⟨_, h | h⟩
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · exact ⟨h ▸ hk, Or.inr h⟩
      · exact ⟨hBA h, Or.inl h⟩
  have mem : ∀ k ∈ A, k ∉ B → ((B : Set ℕ) ∪ {k}) ∈ ZA q A s := by
    intro k hk hkB
    unfold ZA
    simp only [Set.mem_setOf_eq]
    rw [f1 k hk hkB, Finset.card_insert_of_notMem hkB]
    push_cast; rw [hcard]; ring
  have := ev_diff hA hiA hjA hij B hB
  rw [hv _ (mem i hiA hiB), hv _ (mem j hjA hjB), sub_zero] at this
  have hh : ev a (hdiff g A i j) = ev (B : Set ℕ) (hdiff g A i j) := by
    rw [evA (Sup_hdiff g A i j), evA (Sup_hdiff g A i j)]
    rw [fl_coe hB]
  rw [hh, ← this]

/-! ## The main induction -/

theorem green_main {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) (hq : (q : F) ≠ 0) :
    ∀ (n : ℕ) (A : Finset ℕ), A.card = n → ∀ (s : ZMod q) (g : ML F), g ≠ 0 → Sup A g →
      (∀ a ∈ ZA q A s, ev a g = 0) → (n + 1) / q ≤ deg g := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A hn s g hg hA hv
    by_cases hs : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∀ T, g (sw i j T) = g T
    · rw [← hn]; exact sym_deg hq hA hs s hg hv
    · push_neg at hs
      obtain ⟨i, hiA, j, hjA, hij, T, hT⟩ := hs
      have hh := hdiff_ne hA hij hT
      have n2 : 2 ≤ n := by
        have := Finset.one_lt_card.2 ⟨i, hiA, j, hjA, hij⟩
        omega
      have hcard : ((A.erase i).erase j).card = n - 2 := by
        rw [Finset.card_erase_of_mem (by simp [hij.symm, hjA]), Finset.card_erase_of_mem hiA]
        omega
      have ih' := ih (n - 2) (by omega) _ hcard (s - 1) _ hh (Sup_hdiff g A i j)
        (hdiff_vanish hA hiA hjA hij s hv)
      have hd := card_diff_lt (A := A) hh
      have hq0 : 0 < q := by omega
      have : (n + 1) / q ≤ (n - 2 + 1) / q + 1 := by
        rw [← Nat.add_div_right _ hq0]
        exact Nat.div_le_div_right (by omega)
      omega

/-! ## Reduction to polynomials supported on `A` -/

theorem restrict_exists {q : ℕ} {A : Finset ℕ} {s : ZMod q} {g : ML F} (hg : g ≠ 0)
    (hv : ∀ a ∈ ZA q A s, ev a g = 0) :
    ∃ g' : ML F, g' ≠ 0 ∧ Sup A g' ∧ deg g' ≤ deg g ∧ ∀ a ∈ ZA q A s, ev a g' = 0 := by
  obtain ⟨T0, hT0, hmin⟩ := Finset.exists_min_image g.support Finset.card
    (Finsupp.support_nonempty_iff.2 hg)
  set W : Set ℕ := ↑(A ∪ T0) with hW
  set g1 : ML F := kW W g with hg1
  set g' : ML F := Finsupp.mapDomain (fun T => T ∩ A) g1 with hg'
  set pt : Set ℕ → Set ℕ := fun b => (b ∩ ↑A) ∪ (↑T0 \ ↑A) with hpt
  have hptW : ∀ b, pt b ⊆ W := by
    intro b x hx
    rcases hx with ⟨_, hxA⟩ | ⟨hx0, _⟩
    · simp [hW, hxA]
    · simp [hW, hx0]
  have key : ∀ b : Set ℕ, ev b g' = ev (pt b) g := by
    intro b
    have e1 : ev (pt b) g = ev (pt b) g1 := by
      rw [hg1, ev_kW, Set.inter_eq_left.2 (hptW b)]
    rw [e1]
    show Finsupp.linearCombination F (evT b) (Finsupp.mapDomain (fun T => T ∩ A) g1) =
      Finsupp.linearCombination F (evT (pt b)) g1
    rw [Finsupp.linearCombination_mapDomain]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr fun T hT => ?_
    have hTW : (↑T : Set ℕ) ⊆ W := by
      rw [hg1, support_kW, Finset.mem_filter] at hT; exact hT.2
    show g1 T • evT b (T ∩ A) = g1 T • evT (pt b) T
    have : ((↑(T ∩ A) : Set ℕ) ⊆ b) ↔ ((↑T : Set ℕ) ⊆ pt b) := by
      constructor
      · intro h x hx
        by_cases hxA : x ∈ A
        · left; exact ⟨h (by simp [hx, hxA]), hxA⟩
        · right
          have := hTW hx
          simp only [hW, Finset.coe_union, Set.mem_union, Finset.mem_coe] at this
          exact ⟨this.resolve_left hxA, hxA⟩
      · intro h x hx
        have hxT : x ∈ T := (Finset.mem_inter.1 (by exact_mod_cast hx)).1
        have hxA : x ∈ A := (Finset.mem_inter.1 (by exact_mod_cast hx)).2
        rcases h hxT with ⟨hb, _⟩ | ⟨_, hn⟩
        · exact hb
        · exact absurd hxA hn
    simp only [evT, this]
  have hgA : ∀ b ∈ ZA q A s, pt b ∈ ZA q A s := by
    intro b hb
    unfold ZA at *
    simp only [Set.mem_setOf_eq] at *
    have : fl A (pt b) = fl A b := by
      ext x
      simp only [mem_fl, hpt, Set.mem_union, Set.mem_inter_iff, Set.mem_diff,
        Finset.mem_coe]
      constructor
      · rintro ⟨hxA, h | h⟩
        · exact ⟨hxA, h.1⟩
        · exact absurd hxA h.2
      · rintro ⟨hxA, h⟩; exact ⟨hxA, Or.inl ⟨h, hxA⟩⟩
    rw [this]; exact hb
  refine ⟨g', ?_, ?_, ?_, fun b hb => by rw [key]; exact hv _ (hgA b hb)⟩
  · intro h0
    have h1 : ev (↑T0 : Set ℕ) g' = 0 := by rw [h0]; simp
    rw [key] at h1
    have hpt0 : pt (↑T0 : Set ℕ) = ↑T0 := by
      ext x; simp only [hpt, Set.mem_union, Set.mem_inter_iff, Set.mem_diff, Finset.mem_coe]
      tauto
    rw [hpt0, ev_apply, Finset.sum_eq_single T0] at h1
    · simp at h1
      exact (Finsupp.mem_support_iff.1 hT0) h1
    · intro T hT hne
      split_ifs with hs
      · exfalso
        have hsub : T ⊆ T0 := by exact_mod_cast hs
        exact hne (Finset.eq_of_subset_of_card_le hsub (hmin T hT))
      · rfl
    · intro hn; exact absurd hT0 hn
  · intro T hT
    obtain ⟨T1, hT1, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hT)
    exact Finset.inter_subset_right
  · refine deg_le fun T hT => ?_
    obtain ⟨T1, hT1, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hT)
    have : T1 ∈ g.support := by
      rw [hg1, support_kW, Finset.mem_filter] at hT1; exact hT1.1
    exact (Finset.card_le_card Finset.inter_subset_left).trans (le_deg this)

/-- **Immunity of the mod `q` class** (Beck-Li 5, Alekhnovich-Razborov 4.4 shape).  Over a field in
which `q` is invertible, a nonzero multilinear polynomial vanishing on all Boolean points whose
weight on the `n`-set `A` is `≡ s (mod q)` has degree at least `⌊(n+1)/q⌋`. -/
theorem green_immune {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) (hq : (q : F) ≠ 0) (A : Finset ℕ)
    (s : ZMod q) {g : ML F} (hg : g ≠ 0) (hv : ∀ a ∈ ZA q A s, ev a g = 0) :
    (A.card + 1) / q ≤ deg g := by
  obtain ⟨g', h0, hS, hd, hv'⟩ := restrict_exists hg hv
  exact (green_main hq2 hq _ A rfl s g' h0 hS hv').trans hd

end

end SATurday.ProofComplexity.Green
