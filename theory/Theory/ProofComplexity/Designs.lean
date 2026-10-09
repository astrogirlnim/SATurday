import Theory.ProofComplexity.QPart

/-!
# Designs of large degree for the counting principle (Ladder Rung R4, 1D.2)

Buss–Impagliazzo–Krajíček–Pudlák–Razborov–Sgall 1997, Lemma 4.3 and Theorem 4.5. Over `ZMod p`
with `p ∤ q`, a degree `d` design on `N` nodes gives a degree `2 d + 1` design on `(p + q) N`
nodes: each node becomes a cyclically ordered block of `p + q` nodes, a selection `σ` of one
node per block decides which q-sets are cross edges (one node in each of `q` blocks, all at the
same level `1, …, p` after the selected node) or inner edges (the `q` nodes of a block at the
other levels), and the new design averages the pulled back designs `s_σ` over all selections.

* `sym_zero`: sums over selections of a quantity supported on the selections putting some
  fixed nodes at a common level `1, …, p`, and invariant under moving those blocks, vanish mod p.
* `step_design`: the doubling step (`2 d + 1`).

LOG: R4 Designs module (BIKPPRS designs)
-/

namespace SATurday.ProofComplexity

namespace QP

open Finset

noncomputable section

open Classical

/-! ## Levels and the symmetry lemma -/

section Sym

variable {N K : ℕ} [NeZero K]

/-- Levels `1, …, p`. -/
def inLv (p : ℕ) (z : ZMod K) : Prop := 1 ≤ z.val ∧ z.val ≤ p

theorem card_inLv {p : ℕ} (hpK : p < K) :
    (univ.filter fun z : ZMod K => inLv p z).card = p := by
  have : (univ.filter fun z : ZMod K => inLv p z) = (Icc 1 p).image fun i : ℕ => (i : ZMod K) := by
    ext z
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_Icc, inLv]
    constructor
    · intro h; exact ⟨z.val, h, ZMod.natCast_zmod_val z⟩
    · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
      rw [ZMod.val_cast_of_lt (by omega)]; exact ⟨h1, h2⟩
  rw [this, card_image_of_injOn, Nat.card_Icc]
  · omega
  intro i hi j hj hij
  simp only [coe_Icc, Set.mem_Icc] at hi hj
  have := congrArg ZMod.val hij
  simp only at this
  rwa [ZMod.val_cast_of_lt (show i < K by omega), ZMod.val_cast_of_lt (show j < K by omega)] at this

/-- Shift the selection on the coordinates of `A`. -/
def shiftA (A : Finset (Fin N)) (c : ZMod K) (σ : Fin N → ZMod K) : Fin N → ZMod K :=
  fun u => if u ∈ A then σ u + c else σ u

def shiftE (A : Finset (Fin N)) (c : ZMod K) : (Fin N → ZMod K) ≃ (Fin N → ZMod K) where
  toFun := shiftA A c
  invFun := shiftA A (-c)
  left_inv σ := by funext u; simp only [shiftA]; split_ifs <;> ring
  right_inv σ := by funext u; simp only [shiftA]; split_ifs <;> ring

/-- **Symmetry**: a function of the selection supported on the selections putting the nodes
`x u` (`u ∈ A`) at a common level in `1, …, p`, and invariant under moving the blocks of `A`
among such selections, sums to `0` modulo `p`. -/
theorem sym_zero {p : ℕ} (hpK : p < K) (A : Finset (Fin N)) (hA : A.Nonempty)
    (x : Fin N → ZMod K) (g : (Fin N → ZMod K) → ZMod p)
    (h1 : ∀ σ, g σ ≠ 0 → ∃ j, inLv p j ∧ ∀ u ∈ A, x u - σ u = j)
    (h2 : ∀ σ σ', (∀ u ∉ A, σ u = σ' u) → (∃ j, inLv p j ∧ ∀ u ∈ A, x u - σ u = j) →
      (∃ j, inLv p j ∧ ∀ u ∈ A, x u - σ' u = j) → g σ = g σ') :
    ∑ σ, g σ = 0 := by
  set J := univ.filter fun z : ZMod K => inLv p z
  let P : ZMod K → (Fin N → ZMod K) → Prop := fun j σ => ∀ u ∈ A, x u - σ u = j
  obtain ⟨u0, hu0⟩ := hA
  have hsplit : ∀ σ, g σ = ∑ j ∈ J, if P j σ then g σ else 0 := by
    intro σ
    by_cases hg : g σ = 0
    · simp [hg]
    · obtain ⟨j0, hj0, hP⟩ := h1 σ hg
      rw [sum_eq_single j0]
      · rw [if_pos hP]
      · intro j _ hj
        rw [if_neg]
        intro hPj
        exact hj ((hPj u0 hu0).symm.trans (hP u0 hu0))
      · intro h; exact absurd (mem_filter.2 ⟨mem_univ _, hj0⟩) h
  rw [sum_congr rfl fun σ _ => hsplit σ, sum_comm]
  have heq : ∀ j ∈ J, ∀ j' ∈ J, (∑ σ, if P j σ then g σ else 0) =
      ∑ σ, if P j' σ then g σ else 0 := by
    intro j hj j' hj'
    rw [← Equiv.sum_comp (shiftE A (j - j')) (fun σ => if P j' σ then g σ else 0)]
    refine sum_congr rfl fun σ _ => ?_
    have hiff : P j' (shiftA A (j - j') σ) ↔ P j σ := by
      simp only [P, shiftA]
      constructor
      · intro h u hu; have := h u hu; rw [if_pos hu] at this; linear_combination this
      · intro h u hu; rw [if_pos hu]; linear_combination h u hu
    show (if P j σ then g σ else 0) = if P j' (shiftA A (j - j') σ) then g (shiftA A (j - j') σ) else 0
    by_cases hP : P j σ
    · rw [if_pos hP, if_pos (hiff.2 hP)]
      refine h2 _ _ (fun u hu => by simp [shiftA, hu]) ⟨j, (mem_filter.1 hj).2, hP⟩
        ⟨j', (mem_filter.1 hj').2, hiff.2 hP⟩
    · rw [if_neg hP, if_neg (fun h => hP (hiff.1 h))]
  by_cases hJ : J.Nonempty
  · obtain ⟨j1, hj1⟩ := hJ
    rw [sum_congr rfl fun j hj => heq j hj j1 hj1, sum_const, card_inLv hpK, nsmul_eq_mul,
      ZMod.natCast_self, zero_mul]
  · rw [not_nonempty_iff_eq_empty.1 hJ, sum_empty]

end Sym

/-! ## Blocks of `K` nodes and selections -/

section Lift

variable {N K : ℕ} [NeZero K]

/-- The selected level of block `w`. -/
def sel (σ : Fin N → ZMod K) (w : ℕ) : ZMod K := if h : w < N then σ ⟨w, h⟩ else 0

/-- The level of node `x` (relative to the selected node of its block). -/
def lev (σ : Fin N → ZMod K) (x : ℕ) : ZMod K := (x : ZMod K) - sel σ (x / K)

/-- The node of block `w` at level `z`. -/
def lift (σ : Fin N → ZMod K) (z : ZMod K) (w : ℕ) : ℕ := w * K + (z + sel σ w).val

theorem K_pos : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)

theorem lift_div (σ : Fin N → ZMod K) (z : ZMod K) (w : ℕ) : lift σ z w / K = w := by
  have := ZMod.val_lt (z + sel σ w)
  have hK := K_pos (K := K)
  rw [lift, Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt this, zero_add]

theorem lev_lift (σ : Fin N → ZMod K) (z : ZMod K) (w : ℕ) : lev σ (lift σ z w) = z := by
  rw [lev, lift_div, lift]
  push_cast
  rw [ZMod.natCast_self, mul_zero, zero_add, ZMod.natCast_zmod_val]
  ring

theorem eq_lift {σ : Fin N → ZMod K} {x w : ℕ} {z : ZMod K} (hw : x / K = w) (hz : lev σ x = z) :
    x = lift σ z w := by
  have hK := K_pos (K := K)
  have h1 : (x : ZMod K) = z + sel σ w := by rw [← hz, lev, hw]; ring
  have h2 : (z + sel σ w).val = x % K := by rw [← h1, ZMod.val_natCast]
  rw [lift, h2, ← hw, Nat.mul_comm]
  exact (Nat.div_add_mod x K).symm

theorem lift_inj {σ : Fin N → ZMod K} {z z' : ZMod K} {w w' : ℕ}
    (h : lift σ z w = lift σ z' w') : z = z' ∧ w = w' := by
  refine ⟨?_, ?_⟩
  · have := congrArg (lev σ) h; rwa [lev_lift, lev_lift] at this
  · have := congrArg (· / K) h; simpa only [lift_div] using this

theorem lift_lt {σ : Fin N → ZMod K} {z : ZMod K} {w : ℕ} (hw : w < N) : lift σ z w < K * N := by
  have := ZMod.val_lt (z + sel σ w)
  rw [lift]
  calc w * K + (z + sel σ w).val < w * K + K := by omega
    _ = (w + 1) * K := by ring
    _ ≤ N * K := Nat.mul_le_mul_right _ hw
    _ = K * N := Nat.mul_comm _ _

theorem div_lt_of_mem {x : ℕ} (hx : x < K * N) : x / K < N := by
  rw [Nat.div_lt_iff_lt_mul K_pos]; rwa [Nat.mul_comm]

omit [NeZero K] in
/-- Moving the selection inside one block. -/
theorem sel_eq {σ σ' : Fin N → ZMod K} {w : ℕ} (h : ∀ hw : w < N, σ ⟨w, hw⟩ = σ' ⟨w, hw⟩) :
    sel σ w = sel σ' w := by
  unfold sel; split_ifs with hw
  · exact h hw
  · rfl

end Lift

/-! ## Cross edges, inner edges and the pulled back designs -/

section Edges

variable {N K : ℕ} [NeZero K] (p : ℕ)

/-- A cross edge: one node in each of its blocks, all at a common level in `1, …, p`. -/
def cross (σ : Fin N → ZMod K) (e : Finset ℕ) : Prop :=
  (∀ x ∈ e, inLv p (lev σ x)) ∧ (∀ x ∈ e, ∀ y ∈ e, lev σ x = lev σ y) ∧
    ∀ x ∈ e, ∀ y ∈ e, x / K = y / K → x = y

/-- An inner edge: nodes of one block at levels outside `1, …, p`. -/
def inner (σ : Fin N → ZMod K) (e : Finset ℕ) : Prop :=
  ∀ x ∈ e, ∀ y ∈ e, x / K = y / K ∧ ¬ inLv p (lev σ x)

variable (K) in
/-- The blocks met by an edge. -/
def orb (e : Finset ℕ) : Finset ℕ := e.image (· / K)

/-- The selection maps `E` to a partial partition of the blocks. -/
def Good (σ : Fin N → ZMod K) (E : Finset (Finset ℕ)) : Prop :=
  (∀ e ∈ E, cross p σ e ∨ inner p σ e) ∧
    ∀ e ∈ E, ∀ f ∈ E, cross p σ e → cross p σ f → orb K e = orb K f ∨ Disjoint (orb K e) (orb K f)

/-- The image partition: orbits of the cross edges. -/
def VE (σ : Fin N → ZMod K) (E : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  (E.filter (cross p σ)).image (orb K)

/-- The pulled back design. -/
def sS {R : Type} [CommRing R] (s : Finset (Finset ℕ) → R) (σ : Fin N → ZMod K)
    (E : Finset (Finset ℕ)) : R :=
  if Good p σ E then s (VE p σ E) else 0

/-- Nodes of the given blocks at level `z`. -/
def liftSet (σ : Fin N → ZMod K) (z : ZMod K) (o : Finset ℕ) : Finset ℕ := o.image (lift σ z)

/-- The inner edge of block `w`. -/
def innerSet (σ : Fin N → ZMod K) (w : ℕ) : Finset ℕ :=
  (univ.filter fun z : ZMod K => ¬ inLv p z).image fun z => lift σ z w

variable {p}

theorem orb_liftSet (σ : Fin N → ZMod K) (z : ZMod K) (o : Finset ℕ) :
    orb K (liftSet σ z o) = o := by
  ext w; simp [orb, liftSet, lift_div]

theorem card_liftSet (σ : Fin N → ZMod K) (z : ZMod K) (o : Finset ℕ) :
    (liftSet σ z o).card = o.card :=
  card_image_of_injOn fun _ _ _ _ h => (lift_inj h).2

theorem mem_liftSet {σ : Fin N → ZMod K} {z : ZMod K} {o : Finset ℕ} {x : ℕ} :
    x ∈ liftSet σ z o ↔ x / K ∈ o ∧ lev σ x = z := by
  simp only [liftSet, mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact ⟨by rwa [lift_div], lev_lift _ _ _⟩
  · rintro ⟨h1, h2⟩; exact ⟨x / K, h1, (eq_lift rfl h2).symm⟩

theorem card_orb_cross {σ : Fin N → ZMod K} {e : Finset ℕ} (h : cross p σ e) :
    (orb K e).card = e.card :=
  card_image_of_injOn fun x hx y hy hxy => h.2.2 x hx y hy hxy

theorem cross_eq_liftSet {σ : Fin N → ZMod K} {e : Finset ℕ} (h : cross p σ e) {x : ℕ}
    (hx : x ∈ e) : e = liftSet σ (lev σ x) (orb K e) := by
  ext y
  rw [mem_liftSet]
  constructor
  · intro hy; exact ⟨mem_image_of_mem _ hy, h.2.1 y hy x hx⟩
  · rintro ⟨hy1, hy2⟩
    obtain ⟨y', hy', hyy'⟩ := mem_image.1 hy1
    have e1 : y' = lift σ (lev σ x) (y / K) := eq_lift hyy' (h.2.1 y' hy' x hx)
    have e2 : y = lift σ (lev σ x) (y / K) := eq_lift rfl hy2
    have : y = y' := e2.trans e1.symm
    rw [this]; exact hy'

theorem cross_liftSet {σ : Fin N → ZMod K} {z : ZMod K} (hz : inLv p z) (o : Finset ℕ) :
    cross p σ (liftSet σ z o) := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_, fun x hx y hy hxy => ?_⟩
  · rw [(mem_liftSet.1 hx).2]; exact hz
  · rw [(mem_liftSet.1 hx).2, (mem_liftSet.1 hy).2]
  · rw [eq_lift rfl (mem_liftSet.1 hx).2, eq_lift rfl (mem_liftSet.1 hy).2, hxy]

theorem not_cross_inner {σ : Fin N → ZMod K} {e : Finset ℕ} (hne : e.Nonempty)
    (h1 : cross p σ e) (h2 : inner p σ e) : False := by
  obtain ⟨x, hx⟩ := hne
  exact (h2 x hx x hx).2 (h1.1 x hx)

theorem card_innerSet (hpK : p < K) (σ : Fin N → ZMod K) (w : ℕ) :
    (innerSet p σ w).card = K - p := by
  rw [innerSet, card_image_of_injOn fun _ _ _ _ h => (lift_inj h).1, filter_not, card_sdiff,
    card_univ, ZMod.card, inter_univ, card_inLv hpK]

theorem mem_innerSet {σ : Fin N → ZMod K} {w x : ℕ} :
    x ∈ innerSet p σ w ↔ x / K = w ∧ ¬ inLv p (lev σ x) := by
  simp only [innerSet, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨lift_div _ _ _, by rwa [lev_lift]⟩
  · rintro ⟨h1, h2⟩; exact ⟨lev σ x, h2, (eq_lift h1 rfl).symm⟩

theorem inner_sub {σ : Fin N → ZMod K} {e : Finset ℕ} (h : inner p σ e) {x : ℕ} (hx : x ∈ e) :
    e ⊆ innerSet p σ (x / K) := fun y hy =>
  mem_innerSet.2 ⟨(h y hy x hx).1, (h y hy y hy).2⟩

theorem inner_innerSet (σ : Fin N → ZMod K) (w : ℕ) : inner p σ (innerSet p σ w) := by
  intro x hx y hy
  rw [mem_innerSet] at hx hy
  exact ⟨hx.1.trans hy.1.symm, hx.2⟩

theorem good_mono {σ : Fin N → ZMod K} {E F : Finset (Finset ℕ)} (h : Good p σ F) (hEF : E ⊆ F) :
    Good p σ E :=
  ⟨fun e he => h.1 e (hEF he), fun e he f hf => h.2 e (hEF he) f (hEF hf)⟩

theorem sS_insert_of_not {R : Type} [CommRing R] {s : Finset (Finset ℕ) → R}
    {σ : Fin N → ZMod K} {E : Finset (Finset ℕ)} (h : ¬ Good p σ E) (e : Finset ℕ) :
    sS p s σ (insert e E) = 0 :=
  if_neg fun hg => h (good_mono hg (subset_insert _ _))

end Edges

/-! ## The design identities for one selection -/

section OneSel

variable {N K p q : ℕ} [NeZero K]

theorem lt_KN_iff {x : ℕ} : x < K * N ↔ x / K < N := by
  rw [Nat.div_lt_iff_lt_mul K_pos, Nat.mul_comm]

theorem mem_orb {e : Finset ℕ} {u : ℕ} : u ∈ orb K e ↔ ∃ x ∈ e, x / K = u := by
  simp [orb]

theorem VE_pp {σ : Fin N → ZMod K} {E : Finset (Finset ℕ)} (hE : PP q E) (hG : Good p σ E) :
    PP q (VE p σ E) := by
  refine ⟨fun o ho => ?_, fun o ho o' ho' hne => ?_⟩
  · obtain ⟨f, hf, rfl⟩ := mem_image.1 ho
    obtain ⟨hfE, hfc⟩ := mem_filter.1 hf
    rw [card_orb_cross hfc]; exact hE.1 f hfE
  · obtain ⟨f, hf, rfl⟩ := mem_image.1 ho
    obtain ⟨f', hf', rfl⟩ := mem_image.1 ho'
    rcases hG.2 f (mem_filter.1 hf).1 f' (mem_filter.1 hf').1 (mem_filter.1 hf).2
      (mem_filter.1 hf').2 with h | h
    · exact absurd h hne
    · exact h

theorem VE_sub {σ : Fin N → ZMod K} {E : Finset (Finset ℕ)} (hES : ∀ e ∈ E, e ⊆ range (K * N)) :
    ∀ o ∈ VE p σ E, o ⊆ range N := by
  intro o ho u hu
  obtain ⟨f, hf, rfl⟩ := mem_image.1 ho
  obtain ⟨x, hx, rfl⟩ := mem_orb.1 hu
  exact mem_range.2 (lt_KN_iff.1 (mem_range.1 (hES f (mem_filter.1 hf).1 hx)))

theorem mem_cov_VE {σ : Fin N → ZMod K} {E : Finset (Finset ℕ)} {u : ℕ} :
    u ∈ cov (VE p σ E) ↔ ∃ f ∈ E, cross p σ f ∧ u ∈ orb K f := by
  rw [mem_cov]
  constructor
  · rintro ⟨o, ho, hu⟩
    obtain ⟨f, hf, rfl⟩ := mem_image.1 ho
    exact ⟨f, (mem_filter.1 hf).1, (mem_filter.1 hf).2, hu⟩
  · rintro ⟨f, hf, hc, hu⟩
    exact ⟨orb K f, mem_image.2 ⟨f, mem_filter.2 ⟨hf, hc⟩, rfl⟩, hu⟩

theorem VE_insert_cross {σ : Fin N → ZMod K} {E : Finset (Finset ℕ)} {e : Finset ℕ}
    (h : cross p σ e) : VE p σ (insert e E) = insert (orb K e) (VE p σ E) := by
  rw [VE, filter_insert, if_pos h, image_insert]; rfl

theorem VE_insert_not {σ : Fin N → ZMod K} {E : Finset (Finset ℕ)} {e : Finset ℕ}
    (h : ¬ cross p σ e) : VE p σ (insert e E) = VE p σ E := by
  rw [VE, filter_insert, if_neg h]; rfl

variable {R : Type} [CommRing R]

/-- A node at an inner level: only the inner edge of its block contributes. -/
theorem sum_inner (hKq : K = p + q) (hq : 1 ≤ q) {s : Finset (Finset ℕ) → R}
    {σ : Fin N → ZMod K} {E : Finset (Finset ℕ)} (hE : PP q E) {v : ℕ} (hv : v < K * N)
    (hvE : v ∉ cov E) (hG : Good p σ E) (hlv : ¬ inLv p (lev σ v)) :
    ∑ e ∈ blocks q (range (K * N) \ cov E) v, sS p s σ (insert e E) = s (VE p σ E) := by
  set ι := innerSet p σ (v / K)
  have hvι : v ∈ ι := mem_innerSet.2 ⟨rfl, hlv⟩
  have hιc : ι.card = q := by rw [card_innerSet (by omega)]; omega
  have hιne : ι.Nonempty := ⟨v, hvι⟩
  have hιE : Disjoint ι (cov E) := by
    refine disjoint_left.2 fun x hx hxE => ?_
    obtain ⟨f, hf, hxf⟩ := mem_cov.1 hxE
    rcases hG.1 f hf with hc | hi
    · exact (mem_innerSet.1 hx).2 (hc.1 x hxf)
    · have hsub : f ⊆ ι := by
        have := inner_sub hi hxf; rwa [(mem_innerSet.1 hx).1] at this
      have : f = ι := eq_of_subset_of_card_le hsub (by rw [hιc, hE.1 f hf])
      exact hvE (mem_cov.2 ⟨f, hf, this ▸ hvι⟩)
  have hιb : ι ∈ blocks q (range (K * N) \ cov E) v := by
    refine mem_blocks.2 ⟨fun x hx => mem_sdiff.2 ⟨mem_range.2 (lt_KN_iff.2 ?_),
      disjoint_left.1 hιE hx⟩, hιc, hvι⟩
    rw [(mem_innerSet.1 hx).1]; exact lt_KN_iff.1 hv
  have hιx : ¬ cross p σ ι := fun h => not_cross_inner hιne h (inner_innerSet σ _)
  rw [sum_eq_single ι]
  · rw [sS, if_pos, VE_insert_not hιx]
    refine ⟨fun e he => ?_, fun e he f hf hce hcf => ?_⟩
    · rcases mem_insert.1 he with rfl | he
      · exact Or.inr (inner_innerSet σ _)
      · exact hG.1 e he
    · rcases mem_insert.1 he with rfl | he
      · exact absurd hce hιx
      · rcases mem_insert.1 hf with rfl | hf
        · exact absurd hcf hιx
        · exact hG.2 e he f hf hce hcf
  · intro e he hne
    rw [sS, if_neg]
    intro hG'
    have hve := (mem_blocks.1 he).2.2
    rcases hG'.1 e (mem_insert_self _ _) with hc | hi
    · exact hlv (hc.1 v hve)
    · exact hne (eq_of_subset_of_card_le (inner_sub hi hve)
        (by rw [hιc, (mem_blocks.1 he).2.1]))
  · intro h; exact absurd hιb h

/-- A node at a cross level whose block is already an orbit: only the matching cross edge
contributes. -/
theorem sum_cross_cov {s : Finset (Finset ℕ) → R} {σ : Fin N → ZMod K} {E : Finset (Finset ℕ)}
    (hE : PP q E) (hES : ∀ e ∈ E, e ⊆ range (K * N)) {v : ℕ} (hvE : v ∉ cov E)
    (hG : Good p σ E) (hlv : inLv p (lev σ v)) (hw : v / K ∈ cov (VE p σ E)) :
    ∑ e ∈ blocks q (range (K * N) \ cov E) v, sS p s σ (insert e E) = s (VE p σ E) := by
  obtain ⟨f0, hf0, hc0, hw0⟩ := mem_cov_VE.1 hw
  set z := lev σ v
  set es := liftSet σ z (orb K f0)
  have hves : v ∈ es := mem_liftSet.2 ⟨hw0, rfl⟩
  have hesc : es.card = q := by rw [card_liftSet, card_orb_cross hc0, hE.1 f0 hf0]
  have hesx : cross p σ es := cross_liftSet hlv _
  have hesE : Disjoint es (cov E) := by
    refine disjoint_left.2 fun x hx hxE => ?_
    obtain ⟨hx1, hx2⟩ := mem_liftSet.1 hx
    obtain ⟨f, hf, hxf⟩ := mem_cov.1 hxE
    rcases hG.1 f hf with hc | hi
    · have hof : orb K f = orb K f0 := by
        rcases hG.2 f hf f0 hf0 hc hc0 with h | h
        · exact h
        · exact absurd hx1 (disjoint_left.1 h (mem_orb.2 ⟨x, hxf, rfl⟩))
      have : f = es := by rw [cross_eq_liftSet hc hxf, hx2, hof]
      exact hvE (mem_cov.2 ⟨f, hf, this ▸ hves⟩)
    · exact (hi x hxf x hxf).2 (hx2 ▸ hlv)
  have hesb : es ∈ blocks q (range (K * N) \ cov E) v := by
    refine mem_blocks.2 ⟨fun x hx => mem_sdiff.2 ⟨?_, disjoint_left.1 hesE hx⟩, hesc, hves⟩
    obtain ⟨y, hy, hyx⟩ := mem_orb.1 (mem_liftSet.1 hx).1
    exact mem_range.2 (lt_KN_iff.2 (hyx ▸ lt_KN_iff.1 (mem_range.1 (hES f0 hf0 hy))))
  have hoes : orb K es = orb K f0 := orb_liftSet _ _ _
  rw [sum_eq_single es]
  · rw [sS, if_pos, VE_insert_cross hesx, hoes,
      insert_eq_of_mem (show orb K f0 ∈ VE p σ E from mem_image.2 ⟨f0, mem_filter.2 ⟨hf0, hc0⟩, rfl⟩)]
    refine ⟨fun e he => ?_, fun e he f hf hce hcf => ?_⟩
    · rcases mem_insert.1 he with rfl | he
      · exact Or.inl hesx
      · exact hG.1 e he
    · rcases mem_insert.1 he with rfl | he <;> rcases mem_insert.1 hf with rfl | hf
      · exact Or.inl rfl
      · rw [hoes]; exact hG.2 f0 hf0 f hf hc0 hcf
      · rw [hoes]; exact hG.2 e he f0 hf0 hce hc0
      · exact hG.2 e he f hf hce hcf
  · intro e he hne
    rw [sS, if_neg]
    intro hG'
    have hve := (mem_blocks.1 he).2.2
    rcases hG'.1 e (mem_insert_self _ _) with hc | hi
    · have hoe : orb K e = orb K f0 := by
        rcases hG'.2 e (mem_insert_self _ _) f0 (mem_insert_of_mem hf0) hc hc0 with h | h
        · exact h
        · exact absurd hw0 (disjoint_left.1 h (mem_orb.2 ⟨v, hve, rfl⟩))
      exact hne (by rw [cross_eq_liftSet hc hve, hoe])
    · exact (hi v hve v hve).2 hlv
  · intro h; exact absurd hesb h

/-- A node at a cross level in a fresh block: the cross edges through it correspond to the
blocks through its block in the image. -/
theorem sum_cross_free {s : Finset (Finset ℕ) → R} {σ : Fin N → ZMod K} {E : Finset (Finset ℕ)}
    (hES : ∀ e ∈ E, e ⊆ range (K * N)) {v : ℕ} (hG : Good p σ E)
    (hlv : inLv p (lev σ v)) (hw : v / K ∉ cov (VE p σ E)) :
    ∑ e ∈ blocks q (range (K * N) \ cov E) v, sS p s σ (insert e E) =
      ∑ o ∈ blocks q (range N \ cov (VE p σ E)) (v / K), s (insert o (VE p σ E)) := by
  set z := lev σ v
  simp only [sS]
  rw [← sum_filter]
  have hcr : ∀ e ∈ (blocks q (range (K * N) \ cov E) v).filter fun e => Good p σ (insert e E),
      cross p σ e ∧ v ∈ e := by
    intro e he
    obtain ⟨he1, hG'⟩ := mem_filter.1 he
    have hve := (mem_blocks.1 he1).2.2
    rcases hG'.1 e (mem_insert_self _ _) with hc | hi
    · exact ⟨hc, hve⟩
    · exact absurd hlv (hi v hve v hve).2
  refine sum_nbij' (orb K) (liftSet σ z) (fun e he => ?_) (fun o ho => ?_) (fun e he => ?_)
    (fun o _ => orb_liftSet _ _ _) (fun e he => ?_)
  · obtain ⟨he1, hG'⟩ := mem_filter.1 he
    obtain ⟨hc, hve⟩ := hcr e he
    obtain ⟨hsub, hcard, -⟩ := mem_blocks.1 he1
    refine mem_blocks.2 ⟨fun u hu => ?_, by rw [card_orb_cross hc, hcard],
      mem_orb.2 ⟨v, hve, rfl⟩⟩
    obtain ⟨x, hx, rfl⟩ := mem_orb.1 hu
    refine mem_sdiff.2 ⟨mem_range.2 (lt_KN_iff.1 (mem_range.1 (mem_sdiff.1 (hsub hx)).1)),
      fun hcov => ?_⟩
    obtain ⟨f, hf, hfc, hxf⟩ := mem_cov_VE.1 hcov
    rcases hG'.2 e (mem_insert_self _ _) f (mem_insert_of_mem hf) hc hfc with h | h
    · exact hw (mem_cov_VE.2 ⟨f, hf, hfc, h ▸ mem_orb.2 ⟨v, hve, rfl⟩⟩)
    · exact disjoint_left.1 h hu hxf
  · obtain ⟨hsub, hcard, hwo⟩ := mem_blocks.1 ho
    have hdisj : ∀ x ∈ liftSet σ z o, x ∉ cov E := by
      intro x hx hxE
      obtain ⟨hx1, hx2⟩ := mem_liftSet.1 hx
      obtain ⟨f, hf, hxf⟩ := mem_cov.1 hxE
      rcases hG.1 f hf with hc | hi
      · exact (mem_sdiff.1 (hsub hx1)).2 (mem_cov_VE.2 ⟨f, hf, hc, mem_orb.2 ⟨x, hxf, rfl⟩⟩)
      · exact (hi x hxf x hxf).2 (hx2 ▸ hlv)
    refine mem_filter.2 ⟨mem_blocks.2 ⟨fun x hx => mem_sdiff.2 ⟨?_, hdisj x hx⟩,
      by rw [card_liftSet, hcard], mem_liftSet.2 ⟨hwo, rfl⟩⟩, ?_⟩
    · exact mem_range.2 (lt_KN_iff.2 (mem_range.1 (mem_sdiff.1 (hsub (mem_liftSet.1 hx).1)).1))
    · have hx := cross_liftSet (σ := σ) hlv o
      have hdo : ∀ f ∈ E, cross p σ f → Disjoint o (orb K f) := by
        intro f hf hfc
        refine disjoint_left.2 fun u hu huf => ?_
        exact (mem_sdiff.1 (hsub hu)).2 (mem_cov_VE.2 ⟨f, hf, hfc, huf⟩)
      refine ⟨fun e he => ?_, fun e he f hf hce hcf => ?_⟩
      · rcases mem_insert.1 he with rfl | he
        · exact Or.inl hx
        · exact hG.1 e he
      · rcases mem_insert.1 he with rfl | he <;> rcases mem_insert.1 hf with rfl | hf
        · exact Or.inl rfl
        · rw [orb_liftSet]; exact Or.inr (hdo f hf hcf)
        · rw [orb_liftSet]; exact Or.inr (hdo e he hce).symm
        · exact hG.2 e he f hf hce hcf
  · obtain ⟨hc, hve⟩ := hcr e he
    exact (cross_eq_liftSet hc hve).symm
  · rw [VE_insert_cross (hcr e he).1]

/-- The defect of the design condition for one selection: nonzero only for selections putting
`v` at a cross level in a fresh block while the image already has `d` blocks. -/
theorem defect {d : ℕ} (hKq : K = p + q) (hq : 1 ≤ q) (ds : Design q R (range N) d)
    (htr : ∀ F : Finset (Finset ℕ), d < F.card → ds.s F = 0) {σ : Fin N → ZMod K}
    {E : Finset (Finset ℕ)} (hE : PP q E) (hES : ∀ e ∈ E, e ⊆ range (K * N)) {v : ℕ}
    (hv : v < K * N) (hvE : v ∉ cov E) :
    sS p ds.s σ E - ∑ e ∈ blocks q (range (K * N) \ cov E) v, sS p ds.s σ (insert e E) =
      if Good p σ E ∧ inLv p (lev σ v) ∧ v / K ∉ cov (VE p σ E) ∧ (VE p σ E).card = d
      then ds.s (VE p σ E) else 0 := by
  by_cases hG : Good p σ E
  · rw [sS, if_pos hG]
    by_cases hlv : inLv p (lev σ v)
    · by_cases hw : v / K ∈ cov (VE p σ E)
      · rw [sum_cross_cov hE hES hvE hG hlv hw, sub_self, if_neg (fun h => h.2.2.1 hw)]
      · rw [sum_cross_free hES hG hlv hw]
        have hpp := VE_pp hE hG
        have hsub := VE_sub (p := p) (σ := σ) hES
        by_cases hlt : (VE p σ E).card < d
        · rw [← ds.ext _ hpp hsub hlt _ (mem_range.2 (lt_KN_iff.1 hv)) hw, sub_self,
            if_neg (fun h => by omega)]
        · rw [sum_eq_zero (fun o ho => htr _ ?_), sub_zero]
          · by_cases hd : (VE p σ E).card = d
            · rw [if_pos ⟨hG, hlv, hw, hd⟩]
            · rw [if_neg (fun h => hd h.2.2.2), htr _ (by omega)]
          · have : o ∉ VE p σ E := fun h => hw (sub_cov h (mem_blocks.1 ho).2.2)
            rw [card_insert_of_notMem this]; omega
    · rw [sum_inner hKq hq hE hv hvE hG hlv, sub_self, if_neg (fun h => hlv h.2.1)]
  · rw [sS, if_neg hG, sum_eq_zero (fun e _ => sS_insert_of_not hG e), sub_zero,
      if_neg (fun h => hG h.1)]

end OneSel

/-! ## Invariance under moving blocks -/

section Congr

variable {N K p : ℕ} [NeZero K]

theorem cross_congr {σ σ' : Fin N → ZMod K} {e : Finset ℕ} (h : ∀ x ∈ e, lev σ x = lev σ' x) :
    cross p σ e ↔ cross p σ' e := by
  unfold cross
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun x hx => h x hx ▸ h1 x hx, fun x hx y hy => h x hx ▸ h y hy ▸ h2 x hx y hy, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun x hx => (h x hx).symm ▸ h1 x hx,
      fun x hx y hy => (h x hx).symm ▸ (h y hy).symm ▸ h2 x hx y hy, h3⟩

theorem inner_congr {σ σ' : Fin N → ZMod K} {e : Finset ℕ} (h : ∀ x ∈ e, lev σ x = lev σ' x) :
    inner p σ e ↔ inner p σ' e := by
  unfold inner
  constructor
  · intro h1 x hx y hy; exact ⟨(h1 x hx y hy).1, h x hx ▸ (h1 x hx y hy).2⟩
  · intro h1 x hx y hy; exact ⟨(h1 x hx y hy).1, (h x hx).symm ▸ (h1 x hx y hy).2⟩

/-- `Good` and the image depend only on the levels of the covered nodes. -/
theorem good_congr {σ σ' : Fin N → ZMod K} {E : Finset (Finset ℕ)}
    (hc : ∀ e ∈ E, cross p σ e ↔ cross p σ' e) (hi : ∀ e ∈ E, inner p σ e ↔ inner p σ' e) :
    (Good p σ E ↔ Good p σ' E) ∧ VE p σ E = VE p σ' E := by
  refine ⟨?_, ?_⟩
  · unfold Good
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun e he => ?_, fun e he f hf hce hcf => h2 e he f hf ((hc e he).2 hce) ((hc f hf).2 hcf)⟩
      rcases h1 e he with h | h
      · exact Or.inl ((hc e he).1 h)
      · exact Or.inr ((hi e he).1 h)
    · rintro ⟨h1, h2⟩
      refine ⟨fun e he => ?_, fun e he f hf hce hcf => h2 e he f hf ((hc e he).1 hce) ((hc f hf).1 hcf)⟩
      rcases h1 e he with h | h
      · exact Or.inl ((hc e he).2 h)
      · exact Or.inr ((hi e he).2 h)
  · unfold VE; congr 1; exact filter_congr fun e he => hc e he

theorem lev_congr {σ σ' : Fin N → ZMod K} {x : ℕ} (h : sel σ (x / K) = sel σ' (x / K)) :
    lev σ x = lev σ' x := by
  rw [lev, lev, h]

end Congr

/-! ## Isolated cross edges -/

section Iso

variable {N K p q : ℕ} [NeZero K]

/-- Edges with one node per block whose blocks meet no other edge. -/
def Iso (E : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  E.filter fun e => (∀ x ∈ e, ∀ y ∈ e, x / K = y / K → x = y) ∧
    ∀ f ∈ E, f ≠ e → Disjoint (orb K f) (orb K e)

/-- If the block of `v` meets an edge, a bad selection forces an isolated edge (`|E| ≤ 2 d`). -/
theorem iso_nonempty {d : ℕ} (hq : 1 ≤ q) {σ : Fin N → ZMod K} {E : Finset (Finset ℕ)}
    (hE : PP q E) (hEc : E.card ≤ 2 * d) (hG : Good p σ E) {v : ℕ}
    (hw : v / K ∉ cov (VE p σ E)) (hd : (VE p σ E).card = d)
    (hA : ∃ x ∈ cov E, x / K = v / K) : (Iso (K := K) E).Nonempty := by
  obtain ⟨x0, hx0, hx0w⟩ := hA
  obtain ⟨fw, hfw, hx0f⟩ := mem_cov.1 hx0
  have hpp := VE_pp hE hG
  -- `fw` is an inner edge
  have hfwi : inner p σ fw := by
    rcases hG.1 fw hfw with h | h
    · exact absurd (mem_cov_VE.2 ⟨fw, hfw, h, mem_orb.2 ⟨x0, hx0f, hx0w⟩⟩) hw
    · exact h
  let Eo : Finset ℕ → Finset (Finset ℕ) := fun o => E.filter fun f => ¬ Disjoint (orb K f) o
  have hdisj : ∀ o ∈ VE p σ E, ∀ o' ∈ VE p σ E, o ≠ o' → Disjoint (Eo o) (Eo o') := by
    intro o ho o' ho' hne
    refine disjoint_left.2 fun f hf hf' => hne ?_
    obtain ⟨hfE, h1⟩ := mem_filter.1 hf
    obtain ⟨-, h2⟩ := mem_filter.1 hf'
    obtain ⟨u, hu1, hu2⟩ := not_disjoint_iff.1 h1
    obtain ⟨u', hu1', hu2'⟩ := not_disjoint_iff.1 h2
    rcases hG.1 f hfE with hc | hi
    · have hof : orb K f ∈ VE p σ E := mem_image.2 ⟨f, mem_filter.2 ⟨hfE, hc⟩, rfl⟩
      exact (pp_eq_of_mem hpp hof ho hu1 hu2).symm.trans (pp_eq_of_mem hpp hof ho' hu1' hu2')
    · obtain ⟨y, hy, rfl⟩ := mem_orb.1 hu1
      obtain ⟨y', hy', rfl⟩ := mem_orb.1 hu1'
      rw [(hi y hy y' hy').1] at hu2
      exact pp_eq_of_mem hpp ho ho' hu2 hu2'
  have hsub : (VE p σ E).biUnion Eo ⊆ E.erase fw := by
    intro f hf
    obtain ⟨o, ho, hfo⟩ := mem_biUnion.1 hf
    obtain ⟨hfE, h1⟩ := mem_filter.1 hfo
    refine mem_erase.2 ⟨fun hfw' => ?_, hfE⟩
    subst hfw'
    obtain ⟨u, hu1, hu2⟩ := not_disjoint_iff.1 h1
    obtain ⟨y, hy, rfl⟩ := mem_orb.1 hu1
    rw [(hfwi y hy x0 hx0f).1, hx0w] at hu2
    exact hw (sub_cov ho hu2)
  have hcard := card_le_card hsub
  rw [card_biUnion (fun o ho o' ho' hne => hdisj o ho o' ho' hne), card_erase_of_mem hfw] at hcard
  have hEpos : 1 ≤ E.card := card_pos.2 ⟨fw, hfw⟩
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hall : ∀ o ∈ VE p σ E, 2 ≤ (Eo o).card := by
    intro o ho
    by_contra hlt
    obtain ⟨f, hf, rfl⟩ := mem_image.1 ho
    obtain ⟨hfE, hfc⟩ := mem_filter.1 hf
    have hfo : f ∈ Eo (orb K f) := by
      refine mem_filter.2 ⟨hfE, fun h => ?_⟩
      have : (orb K f).Nonempty := by
        rw [← card_pos, card_orb_cross hfc, hE.1 f hfE]; omega
      obtain ⟨u, hu⟩ := this
      exact disjoint_left.1 h hu hu
    have hiso : f ∈ Iso (K := K) E := by
      refine mem_filter.2 ⟨hfE, hfc.2.2, fun g hg hgf => ?_⟩
      by_contra hd'
      have hg' : g ∈ Eo (orb K f) := mem_filter.2 ⟨hg, hd'⟩
      have : (Eo (orb K f)).card ≤ 1 := by omega
      exact hgf (card_le_one.1 this g hg' f hfo)
    rw [hne] at hiso; simp at hiso
  have : ∑ o ∈ VE p σ E, 2 ≤ ∑ o ∈ VE p σ E, (Eo o).card := sum_le_sum hall
  rw [sum_const, smul_eq_mul, hd] at this
  omega

end Iso

/-! ## Vanishing of the total defect -/

section Vanish

variable {N K p q : ℕ} [NeZero K]

/-- The defect of one selection. -/
def badG {R : Type} [CommRing R] (s : Finset (Finset ℕ) → R) (d : ℕ) (σ : Fin N → ZMod K)
    (E : Finset (Finset ℕ)) (v : ℕ) : R :=
  if Good p σ E ∧ inLv p (lev σ v) ∧ v / K ∉ cov (VE p σ E) ∧ (VE p σ E).card = d
  then s (VE p σ E) else 0

theorem badG_congr {R : Type} [CommRing R] {s : Finset (Finset ℕ) → R} {d : ℕ}
    {σ σ' : Fin N → ZMod K} {E : Finset (Finset ℕ)} {v : ℕ} (h1 : Good p σ E ↔ Good p σ' E)
    (h2 : VE p σ E = VE p σ' E) (h3 : inLv p (lev σ v) ↔ inLv p (lev σ' v)) :
    badG (p := p) s d σ E v = badG (p := p) s d σ' E v := by
  unfold badG
  rw [h2]
  exact if_congr (by rw [h1, h3]) rfl rfl

omit [NeZero K] in
theorem sel_fin (σ : Fin N → ZMod K) (u : Fin N) : sel σ u.val = σ u := by
  simp [sel, u.isLt]

omit [NeZero K] in
theorem sel_out {σ σ' : Fin N → ZMod K} {A : Finset (Fin N)} (h : ∀ u ∉ A, σ u = σ' u) {w : ℕ}
    (hw : ∀ hw : w < N, (⟨w, hw⟩ : Fin N) ∉ A) : sel σ w = sel σ' w :=
  sel_eq fun hw' => h _ (hw hw')

/-- **Vanishing**: for `|E| ≤ 2 d` the defects of all selections sum to zero mod `p`. -/
theorem vanish {d : ℕ} (hKq : K = p + q) (hq : 2 ≤ q) (s : Finset (Finset ℕ) → ZMod p)
    {E : Finset (Finset ℕ)} (hE : PP q E) (hEc : E.card ≤ 2 * d)
    (hES : ∀ e ∈ E, e ⊆ range (K * N)) {v : ℕ} (hv : v < K * N) :
    ∑ σ : Fin N → ZMod K, badG (p := p) s d σ E v = 0 := by
  have hpK : p < K := by omega
  set w0 := v / K
  have hw0 : w0 < N := lt_KN_iff.1 hv
  by_cases hA : ∃ x ∈ cov E, x / K = w0
  · by_cases hI : (Iso (K := K) E).Nonempty
    · obtain ⟨e0, he0⟩ := hI
      obtain ⟨he0E, hinj, hiso⟩ := mem_filter.1 he0
      have he0S := hES e0 he0E
      have he0c := hE.1 e0 he0E
      let A : Finset (Fin N) := univ.filter fun u => u.val ∈ orb K e0
      let pt : Fin N → ℕ := fun u => if h : ∃ x ∈ e0, x / K = u.val then Classical.choose h else 0
      have hpt : ∀ u ∈ A, pt u ∈ e0 ∧ pt u / K = u.val := by
        intro u hu
        have h : ∃ x ∈ e0, x / K = u.val := mem_orb.1 (mem_filter.1 hu).2
        simp only [pt, dif_pos h]
        exact Classical.choose_spec h
      have hinA : ∀ x (hx : x ∈ e0), (⟨x / K, lt_KN_iff.1 (mem_range.1 (he0S hx))⟩ : Fin N) ∈ A :=
        fun x hx => mem_filter.2 ⟨mem_univ _, mem_orb.2 ⟨x, hx, rfl⟩⟩
      have KF : ∀ σ : Fin N → ZMod K, (∃ j, inLv p j ∧ ∀ u ∈ A, (pt u : ZMod K) - σ u = j) ↔
          cross p σ e0 := by
        intro σ
        constructor
        · rintro ⟨j, hj, hall⟩
          have hlev : ∀ y ∈ e0, lev σ y = j := by
            intro y hy
            have hu := hinA y hy
            obtain ⟨hp1, hp2⟩ := hpt _ hu
            have : pt _ = y := hinj _ hp1 y hy hp2
            have h := hall _ hu
            rw [this] at h
            rw [lev, ← h]
            congr 1
            exact sel_fin σ ⟨y / K, lt_KN_iff.1 (mem_range.1 (he0S hy))⟩
          exact ⟨fun y hy => hlev y hy ▸ hj, fun x hx y hy => by rw [hlev x hx, hlev y hy], hinj⟩
        · intro hc
          have hne : e0.Nonempty := by rw [← card_pos]; omega
          obtain ⟨y0, hy0⟩ := hne
          refine ⟨lev σ y0, hc.1 y0 hy0, fun u hu => ?_⟩
          obtain ⟨hp1, hp2⟩ := hpt u hu
          rw [← hc.2.1 _ hp1 y0 hy0, lev, hp2, sel_fin]
      have hcrossG : ∀ σ : Fin N → ZMod K, Good p σ E → cross p σ e0 := by
        intro σ hG
        rcases hG.1 e0 he0E with h | h
        · exact h
        · exfalso
          obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.1 (show 1 < e0.card by omega)
          exact hxy (hinj x hx y hy (h x hx y hy).1)
      refine sym_zero hpK A (by
        obtain ⟨x, hx⟩ : e0.Nonempty := by rw [← card_pos]; omega
        exact ⟨_, hinA x hx⟩) (fun u => (pt u : ZMod K)) _ (fun σ hg => ?_)
        (fun σ σ' hout hc hc' => ?_)
      · unfold badG at hg
        by_cases hb : Good p σ E ∧ inLv p (lev σ v) ∧ v / K ∉ cov (VE p σ E) ∧
            (VE p σ E).card = d
        · exact (KF σ).2 (hcrossG σ hb.1)
        · exact absurd (if_neg hb) hg
      · have hc1 := (KF σ).1 hc
        have hc2 := (KF σ').1 hc'
        have hlevf : ∀ f ∈ E, f ≠ e0 → ∀ x ∈ f, lev σ x = lev σ' x := by
          intro f hf hne x hx
          refine lev_congr (sel_out hout fun hw hmem => ?_)
          exact disjoint_left.1 (hiso f hf hne) (mem_orb.2 ⟨x, hx, rfl⟩) (mem_filter.1 hmem).2
        have hne0 : e0.Nonempty := by rw [← card_pos]; omega
        obtain ⟨hgood, hVE⟩ := good_congr (p := p) (σ := σ) (σ' := σ') (E := E)
          (fun e he => by
            by_cases h : e = e0
            · subst h; exact ⟨fun _ => hc2, fun _ => hc1⟩
            · exact cross_congr (hlevf e he h))
          (fun e he => by
            by_cases h : e = e0
            · subst h
              exact ⟨fun hi => absurd hc1 (fun hx => not_cross_inner hne0 hx hi),
                fun hi => absurd hc2 (fun hx => not_cross_inner hne0 hx hi)⟩
            · exact inner_congr (hlevf e he h))
        by_cases hw : w0 ∈ orb K e0
        · have h1 : w0 ∈ cov (VE p σ E) := mem_cov_VE.2 ⟨e0, he0E, hc1, hw⟩
          have h2 : w0 ∈ cov (VE p σ' E) := mem_cov_VE.2 ⟨e0, he0E, hc2, hw⟩
          unfold badG
          rw [if_neg (fun h => h.2.2.1 h1), if_neg (fun h => h.2.2.1 h2)]
        · refine badG_congr hgood hVE ?_
          rw [lev_congr (sel_out hout fun hw' hmem => hw (mem_filter.1 hmem).2)]
    · refine sum_eq_zero fun σ _ => ?_
      unfold badG
      rw [if_neg]
      rintro ⟨hG, -, hw, hd⟩
      exact hI (iso_nonempty (by omega) hE hEc hG hw hd hA)
  · -- the block of `v` meets no edge
    let A : Finset (Fin N) := {⟨w0, hw0⟩}
    have KF : ∀ σ : Fin N → ZMod K, (∃ j, inLv p j ∧ ∀ u ∈ A, (v : ZMod K) - σ u = j) ↔
        inLv p (lev σ v) := by
      intro σ
      have hl : lev σ v = (v : ZMod K) - σ ⟨w0, hw0⟩ := by
        rw [lev, ← sel_fin σ ⟨w0, hw0⟩]
      constructor
      · rintro ⟨j, hj, hall⟩; rw [hl, hall _ (mem_singleton_self _)]; exact hj
      · intro h; exact ⟨_, h, fun u hu => by rw [mem_singleton.1 hu, ← hl]⟩
    refine sym_zero hpK A ⟨_, mem_singleton_self _⟩ (fun _ => (v : ZMod K)) _ (fun σ hg => ?_)
      (fun σ σ' hout hc hc' => ?_)
    · unfold badG at hg
      by_cases hb : Good p σ E ∧ inLv p (lev σ v) ∧ v / K ∉ cov (VE p σ E) ∧
          (VE p σ E).card = d
      · exact (KF σ).2 hb.2.1
      · exact absurd (if_neg hb) hg
    · have hlevE : ∀ e ∈ E, ∀ x ∈ e, lev σ x = lev σ' x := by
        intro e he x hx
        refine lev_congr (sel_out hout fun hw hmem => ?_)
        have : x / K = w0 := by
          have := mem_singleton.1 hmem; exact congrArg Fin.val this
        exact hA ⟨x, sub_cov he hx, this⟩
      obtain ⟨hgood, hVE⟩ := good_congr (p := p) (σ := σ) (σ' := σ') (E := E)
        (fun e he => cross_congr (hlevE e he)) (fun e he => inner_congr (hlevE e he))
      exact badG_congr hgood hVE ⟨fun _ => (KF σ').1 hc', fun _ => (KF σ).1 hc⟩

end Vanish

/-! ## The doubling step -/

section Step

variable {N K p q : ℕ} [NeZero K]

/-- Truncation of a design above its degree. -/
def truncD {R : Type} [CommRing R] {U : Finset ℕ} {D : ℕ} (ds : Design q R U D) :
    Design q R U D where
  s F := if F.card ≤ D then ds.s F else 0
  empty := by rw [if_pos (by simp), ds.empty]
  ext := by
    intro E hE hEU hEc v hv hvE
    rw [if_pos hEc.le, ds.ext E hE hEU hEc v hv hvE]
    refine sum_congr rfl fun e he => ?_
    have : e ∉ E := fun h => hvE (sub_cov h (mem_blocks.1 he).2.2)
    rw [if_pos (by rw [card_insert_of_notMem this]; omega)]

theorem truncD_zero {R : Type} [CommRing R] {U : Finset ℕ} {D : ℕ} (ds : Design q R U D)
    (F : Finset (Finset ℕ)) (h : D < F.card) : (truncD ds).s F = 0 := by
  show (if F.card ≤ D then ds.s F else 0) = 0
  rw [if_neg (by omega)]

/-- **BIKPPRS Lemma 4.3**: a degree `d` design on `N` nodes over `ZMod p` gives a degree
`2 d + 1` design on `(p + q) N` nodes, for a prime `p` not dividing `q ≥ 2`. -/
def stepD [Fact p.Prime] (hpq : ¬ p ∣ q) (hKq : K = p + q) (hq : 2 ≤ q) {d : ℕ}
    (ds : Design q (ZMod p) (range N) d) : Design q (ZMod p) (range (K * N)) (2 * d + 1) where
  s E := ((K : ZMod p) ^ N)⁻¹ * ∑ σ : Fin N → ZMod K, sS p (truncD ds).s σ E
  empty := by
    have hK0 : (K : ZMod p) ≠ 0 := by
      rw [hKq, Nat.cast_add, ZMod.natCast_self, zero_add]
      exact fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)
    have : ∀ σ : Fin N → ZMod K, sS p (truncD ds).s σ ∅ = 1 := by
      intro σ
      rw [sS, if_pos ⟨by simp, by simp⟩]
      have : VE p σ (∅ : Finset (Finset ℕ)) = ∅ := by simp [VE]
      rw [this, (truncD ds).empty]
    rw [sum_congr rfl fun σ _ => this σ, sum_const, card_univ, Fintype.card_fun, ZMod.card,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    exact inv_mul_cancel₀ (pow_ne_zero _ hK0)
  ext := by
    intro E hE hES hEc v hv hvE
    rw [← mul_sum, ← sub_eq_zero, ← mul_sub]
    refine mul_eq_zero_of_right _ ?_
    rw [sum_comm, ← sum_sub_distrib]
    have hv' : v < K * N := mem_range.1 hv
    rw [sum_congr rfl fun σ _ => defect hKq (by omega) (truncD ds) (truncD_zero ds) hE hES hv' hvE]
    exact vanish hKq hq _ hE (by omega) hES hv'

end Step

/-! ## Designs of degree `2^i - 1` on every large universe -/

section Exist

variable {p q : ℕ}

/-- The degree `0` design. -/
def baseD (R : Type) [CommRing R] (U : Finset ℕ) : Design q R U 0 where
  s E := if E = ∅ then 1 else 0
  empty := by simp
  ext _ _ _ h := absurd h (Nat.not_lt_zero _)

/-- **BIKPPRS Theorem 4.5** (iterated form): a degree `2^i - 1` design on `(p + q)^i N0` nodes. -/
theorem exists_iter [Fact p.Prime] (hpq : ¬ p ∣ q) (hq : 2 ≤ q) (N0 : ℕ) :
    ∀ i, Nonempty (Design q (ZMod p) (range ((p + q) ^ i * N0)) (2 ^ i - 1))
  | 0 => by rw [pow_zero, one_mul, pow_zero]; exact ⟨baseD _ _⟩
  | i + 1 => by
    haveI : NeZero (p + q) := ⟨by omega⟩
    obtain ⟨ds⟩ := exists_iter hpq hq N0 i
    have h1 : (p + q) ^ (i + 1) * N0 = (p + q) * ((p + q) ^ i * N0) := by ring
    have h2 : 2 ^ (i + 1) - 1 = 2 * (2 ^ i - 1) + 1 := by
      have := Nat.one_le_two_pow (n := i); rw [pow_succ]; omega
    rw [h1, h2]
    exact ⟨stepD (K := p + q) hpq rfl hq ds⟩

/-- Consecutive blocks of `q` nodes filling `[M, M + r q)`. -/
def fill (q M r : ℕ) : Finset (Finset ℕ) := (range r).image fun j => Ico (M + j * q) (M + j * q + q)

theorem div_of_mem_Ico {q M j x : ℕ} (hq : 1 ≤ q) (hx : x ∈ Ico (M + j * q) (M + j * q + q)) :
    (x - M) / q = j := by
  obtain ⟨h1, h2⟩ := mem_Ico.1 hx
  refine Nat.div_eq_of_lt_le ?_ ?_
  · omega
  · rw [Nat.add_mul, one_mul]; omega

theorem mem_cov_fill {q M r x : ℕ} (hq : 1 ≤ q) : x ∈ cov (fill q M r) ↔ M ≤ x ∧ x < M + r * q := by
  rw [mem_cov]
  constructor
  · rintro ⟨e, he, hx⟩
    obtain ⟨j, hj, rfl⟩ := mem_image.1 he
    obtain ⟨h1, h2⟩ := mem_Ico.1 hx
    have : (j + 1) * q ≤ r * q := Nat.mul_le_mul_right _ (mem_range.1 hj)
    rw [Nat.add_mul, one_mul] at this
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    set j := (x - M) / q
    have hj1 : j * q ≤ x - M := Nat.div_mul_le_self _ _
    have hj2 : x - M < j * q + q := by
      have := Nat.lt_div_mul_add (a := x - M) (show 0 < q by omega); rw [Nat.mul_comm] at this
      simpa [j, Nat.mul_comm] using this
    have hjr : j < r := by
      refine (Nat.div_lt_iff_lt_mul (by omega)).2 ?_; omega
    exact ⟨_, mem_image.2 ⟨j, mem_range.2 hjr, rfl⟩, mem_Ico.2 ⟨by omega, by omega⟩⟩

theorem fill_pp {q M r : ℕ} (hq : 1 ≤ q) : PP q (fill q M r) := by
  refine ⟨fun e he => ?_, fun e he f hf hef => ?_⟩
  · obtain ⟨j, -, rfl⟩ := mem_image.1 he; simp
  · obtain ⟨j, -, rfl⟩ := mem_image.1 he
    obtain ⟨j', -, rfl⟩ := mem_image.1 hf
    refine disjoint_left.2 fun x hx hx' => hef ?_
    rw [← div_of_mem_Ico hq hx, ← div_of_mem_Ico hq hx']

/-- **Designs on arbitrary universes**: for a prime `p ∤ q`, `q ≥ 2`, every universe of at least
`(p + q)^i q` nodes carries a degree `2^i - 1` design over `ZMod p`. -/
theorem exists_design [hp : Fact p.Prime] (hpq : ¬ p ∣ q) (hq : 2 ≤ q) (W : Finset ℕ) (i : ℕ)
    (hW : (p + q) ^ i * q ≤ W.card) : Nonempty (Design q (ZMod p) W (2 ^ i - 1)) := by
  haveI : NeZero q := ⟨by omega⟩
  have hcop : Nat.Coprime ((p + q) ^ i) q := by
    refine Nat.Coprime.pow_left _ ?_
    rw [Nat.coprime_add_self_left]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hpq
  set u := ZMod.unitOfCoprime ((p + q) ^ i) hcop
  set N0 := ((W.card : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)).val
  have hN0 : N0 < q := ZMod.val_lt _
  set M := (p + q) ^ i * N0
  have hMW : M ≤ W.card := le_trans (Nat.mul_le_mul_left _ hN0.le) hW
  have hmod : (M : ZMod q) = (W.card : ZMod q) := by
    simp only [M, N0, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id]
    rw [← ZMod.coe_unitOfCoprime _ hcop]
    rw [mul_comm (W.card : ZMod q), ← mul_assoc, Units.mul_inv, one_mul]
  have hdvd : q ∣ W.card - M := by
    apply (ZMod.natCast_eq_zero_iff _ _).1
    rw [Nat.cast_sub hMW, hmod, sub_self]
  obtain ⟨r, hr⟩ := hdvd
  obtain ⟨ds0⟩ := exists_iter hpq hq N0 i
  -- pad to `range |W|`
  have hpp := fill_pp (M := M) (r := r) (show 1 ≤ q by omega)
  have hsub : ∀ a ∈ fill q M r, a ⊆ range W.card := by
    intro a ha x hx
    have := (mem_cov_fill (show 1 ≤ q by omega)).1 (sub_cov ha hx)
    exact mem_range.2 (by rw [Nat.mul_comm] at hr; omega)
  have heq : range W.card \ cov (fill q M r) = range M := by
    ext x
    rw [mem_sdiff, mem_range, mem_range, mem_cov_fill (show 1 ≤ q by omega)]
    rw [Nat.mul_comm] at hr
    omega
  have ds1 : Design q (ZMod p) (range W.card) (2 ^ i - 1) := padD hpp hsub (heq ▸ ds0)
  -- transport to `W`
  let φ : ℕ → ℕ := fun j => if h : j < W.card then W.orderEmbOfFin rfl ⟨j, h⟩ else 0
  have hφ : Set.InjOn φ (range W.card) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    simp only [φ, dif_pos ha, dif_pos hb] at hab
    exact congrArg Fin.val ((W.orderEmbOfFin rfl).injective hab)
  have himg : (range W.card).image φ = W := by
    ext y
    simp only [mem_image, mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩
      simp only [φ, dif_pos hj]
      exact W.orderEmbOfFin_mem rfl _
    · intro hy
      have : y ∈ Set.range (W.orderEmbOfFin rfl) := by
        rw [range_orderEmbOfFin]; exact hy
      obtain ⟨⟨j, hj⟩, rfl⟩ := this
      exact ⟨j, hj, by simp only [φ, dif_pos hj]⟩
  rw [← himg]
  exact ⟨mapD ds1 φ hφ⟩

end Exist

end

end QP

end SATurday.ProofComplexity
