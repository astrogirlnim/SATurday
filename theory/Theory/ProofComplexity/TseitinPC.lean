import Theory.ProofComplexity.PolyCalc
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Theory.ProofComplexity.Tseitin

/-!
# Polynomial calculus degree lower bound for Tseitin mod q (Ladder Rung R4, 1C.2)

Binomial (Fourier) encoding of Tseitin mod `q` on a graph `G` (edges oriented from the smaller
to the larger endpoint): variables `y_e` (`edgeVar e`), axioms `y_e^q - 1` and, at every vertex
`v`, `∏_{e out of v} y_e - ω^{b v} ∏_{e into v} y_e`, over a field containing `ω` with
`ω^q = 1`. On a graph with inverse expansion `k` (`HasExpansionInv G k`), polynomial calculus
(without Boolean axioms) has no refutation of degree `d` when `6 k d < n` (`tseitin_pc_degree`).

Proof: Razborov's R-operator. Exponent vectors mod `q` live in `G → ZMod q`; two of them are
equivalent when they differ by a coboundary `∂c` (`bd`). Expansion makes small coboundaries come
from unique small potentials (`level`, `uniq`), so the phase `dlt` (the charge of the potential)
is additive on small vectors. `R` sends a monomial to its phase times the minimum degree
monomial of its class.

LOG: R4 TseitinPC module (Tseitin mod q degree lower bound)
-/

namespace SATurday.ProofComplexity

namespace TseitinPC

open Finset

noncomputable section

open Classical

section Comb

variable {n : ℕ} (G : FinGraph n) {q : ℕ} [NeZero q]

/-- Coboundary of a vertex potential: `∂c (e) = c(tail) - c(head)`. -/
def bd (c : Fin n → ZMod q) : G → ZMod q := fun e => c e.1.val.1 - c e.1.val.2

/-- Number of nonzero coordinates. -/
def wt {α : Type} [Fintype α] (x : α → ZMod q) : ℕ := (univ.filter fun e => x e ≠ 0).card

/-- Support of a potential. -/
def vsupp (c : Fin n → ZMod q) : Finset (Fin n) := univ.filter fun v => c v ≠ 0

variable {G}

theorem wt_bd_eq (c : Fin n → ZMod q) :
    wt (bd G c) = (G.filter fun e => c e.val.1 ≠ c e.val.2).card := by
  unfold wt bd
  rw [← card_map ⟨Subtype.val, Subtype.val_injective⟩]
  congr 1
  ext e
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk, sub_ne_zero]
  constructor
  · rintro ⟨⟨e, he⟩, h, rfl⟩; exact ⟨he, h⟩
  · rintro ⟨he, h⟩; exact ⟨⟨e, he⟩, h, rfl⟩

/-- Level sets: on an expander, a potential with a small coboundary is constant off a small
set. -/
theorem level {k : ℕ} (hG : HasExpansionInv G k) (c : Fin n → ZMod q)
    (h : 2 * k * wt (bd G c) < n) :
    ∃ l : ZMod q, (univ.filter fun v => c v ≠ l).card ≤ k * wt (bd G c) := by
  set w := wt (bd G c) with hw
  set Dif := G.filter fun e => c e.val.1 ≠ c e.val.2 with hDif
  have hwD : w = Dif.card := wt_bd_eq c
  set W : ZMod q → Finset (Fin n) := fun l => univ.filter fun v => c v = l
  have hcut : ∀ l, edgeBoundary G (W l) ⊆ Dif := by
    intro l e he
    simp only [edgeBoundary, mem_filter, W, mem_univ, true_and] at he
    refine mem_filter.2 ⟨he.1, ?_⟩
    rcases he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]; exact Ne.symm h2
    · rw [h2]; exact h1
  have hsum : ∑ l, (edgeBoundary G (W l)).card ≤ 2 * w := by
    have h1 : ∀ l, (edgeBoundary G (W l)).card =
        ∑ e ∈ Dif, if e ∈ edgeBoundary G (W l) then 1 else 0 := by
      intro l
      rw [sum_boole, Nat.cast_id, filter_mem_eq_inter, inter_eq_right.2 (hcut l)]
    simp_rw [h1]
    rw [sum_comm, hwD, mul_comm, ← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun e _ => ?_
    rw [sum_boole, Nat.cast_id]
    calc _ ≤ ({c e.val.1, c e.val.2} : Finset (ZMod q)).card := by
          refine card_le_card fun l hl => ?_
          simp only [mem_filter, mem_univ, true_and, edgeBoundary, W] at hl
          rcases hl.2 with ⟨h1, -⟩ | ⟨-, h2⟩
          · simp [h1]
          · simp [h2]
      _ ≤ 2 := card_le_two
  by_cases hbig : ∃ l, n < 2 * (W l).card
  · obtain ⟨l, hl⟩ := hbig
    refine ⟨l, ?_⟩
    set U := univ.filter fun v => c v ≠ l
    have hU : U.card + (W l).card = n := by
      have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) fun v => c v ≠ l
      have h2 : (univ.filter fun v => ¬ c v ≠ l) = W l := by ext v; simp [W]
      rw [h2, card_univ, Fintype.card_fin] at h; exact h
    rcases U.eq_empty_or_nonempty with hU0 | hUne
    · rw [hU0]; simp
    · have hexp := hG U hUne (by omega)
      have hsub : edgeBoundary G U ⊆ Dif := by
        intro e he
        simp only [edgeBoundary, mem_filter, U, mem_univ, true_and, not_not] at he
        refine mem_filter.2 ⟨he.1, ?_⟩
        rcases he.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h2]; exact h1
        · rw [h1]; exact Ne.symm h2
      calc U.card ≤ k * (edgeBoundary G U).card := hexp
        _ ≤ k * w := Nat.mul_le_mul_left _ (by rw [hwD]; exact card_le_card hsub)
  · push Not at hbig
    exfalso
    have hn : n = ∑ l, (W l).card := by
      rw [← card_eq_sum_card_fiberwise (f := c) (t := univ) (fun _ _ => mem_univ _)]
      simp
    have : n ≤ k * (2 * w) := by
      calc n = ∑ l, (W l).card := hn
        _ ≤ ∑ l, k * (edgeBoundary G (W l)).card := by
          refine sum_le_sum fun l _ => ?_
          rcases (W l).eq_empty_or_nonempty with h0 | hne
          · rw [h0]; simp
          · exact hG _ hne (hbig l)
        _ = k * ∑ l, (edgeBoundary G (W l)).card := by rw [mul_sum]
        _ ≤ k * (2 * w) := Nat.mul_le_mul_left _ hsum
    have : k * (2 * w) = 2 * k * w := by ring
    omega

theorem bd_sub (c c' : Fin n → ZMod q) : bd G (c - c') = bd G c - bd G c' := by
  funext e; simp only [bd, Pi.sub_apply]; ring

theorem bd_add (c c' : Fin n → ZMod q) : bd G (c + c') = bd G c + bd G c' := by
  funext e; simp only [bd, Pi.add_apply]; ring

/-- Uniqueness of small potentials. -/
theorem uniq {k : ℕ} (hG : HasExpansionInv G k) {c c' : Fin n → ZMod q}
    (hbd : bd G c = bd G c') (hsz : (vsupp c).card + (vsupp c').card < n) : c = c' := by
  have h0 : bd G (c - c') = 0 := by rw [bd_sub, hbd, sub_self]
  have hw : wt (bd G (c - c')) = 0 := by rw [h0]; simp [wt]
  obtain ⟨l, hl0⟩ := level hG (c - c') (by rw [hw]; omega)
  rw [hw, mul_zero, Nat.le_zero, card_eq_zero] at hl0
  have hl : ∀ v, c v - c' v = l := fun v => by
    by_contra hne
    have : v ∈ univ.filter fun v => (c - c') v ≠ l := mem_filter.2 ⟨mem_univ _, hne⟩
    rw [hl0] at this; simp at this
  by_cases hl0 : l = 0
  · funext v; have := hl v; rw [hl0, sub_eq_zero] at this; exact this
  · exfalso
    have : (univ : Finset (Fin n)) ⊆ vsupp c ∪ vsupp c' := by
      intro v _
      simp only [vsupp, mem_union, mem_filter, mem_univ, true_and]
      by_contra hcon
      push Not at hcon
      have := hl v; rw [hcon.1, hcon.2, sub_self] at this; exact hl0 this.symm
    have := (card_le_card this).trans (card_union_le _ _)
    simp at this; omega

/-- The canonical small potential of a coboundary. -/
def pot (k : ℕ) (x : G → ZMod q) : Fin n → ZMod q :=
  if h : ∃ c, bd G c = x ∧ (vsupp c).card ≤ k * wt x then Classical.choose h else 0

theorem pot_spec {k : ℕ} (hG : HasExpansionInv G k) {x : G → ZMod q} (hx : ∃ c, bd G c = x)
    (h : 2 * k * wt x < n) : bd G (pot k x) = x ∧ (vsupp (pot k x)).card ≤ k * wt x := by
  have hex : ∃ c, bd G c = x ∧ (vsupp c).card ≤ k * wt x := by
    obtain ⟨c0, rfl⟩ := hx
    obtain ⟨l, hl⟩ := level hG c0 h
    refine ⟨c0 - fun _ => l, ?_, ?_⟩
    · rw [bd_sub]; funext e; simp [bd]
    · refine le_trans (card_le_card fun v hv => ?_) hl
      simp only [vsupp, mem_filter, mem_univ, true_and, Pi.sub_apply, sub_ne_zero] at hv ⊢
      exact hv
  unfold pot; rw [dif_pos hex]; exact Classical.choose_spec hex

theorem pot_eq {k : ℕ} (hG : HasExpansionInv G k) {x : G → ZMod q} {c : Fin n → ZMod q}
    (hc : bd G c = x) (h : 2 * k * wt x < n) (hs : (vsupp c).card + k * wt x < n) :
    pot k x = c := by
  have := pot_spec hG ⟨c, hc⟩ h
  exact uniq hG (this.1.trans hc.symm) (by omega)

/-- The phase of a coboundary: the charge of its canonical potential. -/
def dlt (k : ℕ) (b : Fin n → ZMod q) (x : G → ZMod q) : ZMod q := ∑ v, pot (G := G) k x v * b v

theorem wt_add_le {α : Type} [Fintype α] (x y : α → ZMod q) : wt (x + y) ≤ wt x + wt y := by
  unfold wt
  refine (card_le_card fun e he => ?_).trans (card_union_le _ _)
  simp only [mem_filter, mem_univ, true_and, mem_union, Pi.add_apply] at he ⊢
  by_contra h; push Not at h; rw [h.1, h.2, add_zero] at he; exact he rfl

theorem wt_neg {α : Type} [Fintype α] (x : α → ZMod q) : wt (-x) = wt x := by
  unfold wt; congr 1; ext e; simp

theorem dlt_add {k : ℕ} (hG : HasExpansionInv G k) (b : Fin n → ZMod q) {x y : G → ZMod q}
    (hx : ∃ c, bd G c = x) (hy : ∃ c, bd G c = y)
    (hs : k * (wt x + wt y) + k * (wt x + wt y) < n) :
    dlt k b (x + y) = dlt k b x + dlt k b y := by
  have h1 := pot_spec hG hx (by nlinarith)
  have h2 := pot_spec hG hy (by nlinarith)
  have hxy := wt_add_le x y
  have heq : pot k (x + y) = pot k x + pot k y := by
    refine pot_eq hG (by rw [bd_add, h1.1, h2.1]) (by nlinarith) ?_
    refine lt_of_le_of_lt (Nat.add_le_add_right ((card_le_card fun v hv => ?_).trans
      ((card_union_le _ _).trans (Nat.add_le_add h1.2 h2.2))) _) ?_
    · simp only [vsupp, mem_filter, mem_univ, true_and, mem_union, Pi.add_apply] at hv ⊢
      by_contra h; push Not at h; rw [h.1, h.2, add_zero] at hv; exact hv rfl
    · nlinarith
  unfold dlt; rw [heq]; simp only [Pi.add_apply, add_mul, sum_add_distrib]

theorem dlt_zero {k : ℕ} (hG : HasExpansionInv G k) (hn : 0 < n) (b : Fin n → ZMod q) :
    dlt (G := G) k b 0 = 0 := by
  have : pot (G := G) k (0 : G → ZMod q) = 0 :=
    pot_eq hG (c := (0 : Fin n → ZMod q)) (by funext e; simp [bd]) (by simp [wt]; omega)
      (by simp [vsupp, wt]; omega)
  unfold dlt; rw [this]; simp

end Comb

/-! ## Classes and minimum degree representatives -/

section Classes

variable {n : ℕ} {G : FinGraph n} {q : ℕ} [NeZero q]

/-- Degree of the monomial with exponents the representatives `0..q-1`. -/
def vdeg (x : G → ZMod q) : ℕ := ∑ e, (x e).val

/-- The class of `x` modulo coboundaries. -/
def cls (x : G → ZMod q) : Finset (G → ZMod q) := univ.filter fun y => ∃ c, bd G c = y - x

/-- A minimum degree element of a finite set. -/
def minOf (S : Finset (G → ZMod q)) : G → ZMod q :=
  if h : S.Nonempty then Classical.choose (S.exists_min_image vdeg h) else 0

/-- The minimum degree representative of the class of `x`. -/
def base (x : G → ZMod q) : G → ZMod q := minOf (cls x)

theorem self_mem_cls (x : G → ZMod q) : x ∈ cls x :=
  mem_filter.2 ⟨mem_univ _, 0, by funext e; simp [bd]⟩

theorem cls_eq {x y : G → ZMod q} (h : ∃ c, bd G c = x - y) : cls x = cls y := by
  obtain ⟨c0, hc0⟩ := h
  ext z
  simp only [cls, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨c, hc⟩; exact ⟨c + c0, by rw [bd_add, hc, hc0]; abel⟩
  · rintro ⟨c, hc⟩; exact ⟨c - c0, by rw [bd_sub, hc, hc0]; abel⟩

theorem base_spec (x : G → ZMod q) : base x ∈ cls x ∧ vdeg (base x) ≤ vdeg x := by
  have hne : (cls x).Nonempty := ⟨x, self_mem_cls x⟩
  have := Classical.choose_spec ((cls x).exists_min_image vdeg hne)
  unfold base minOf; rw [dif_pos hne]
  exact ⟨this.1, this.2 x (self_mem_cls x)⟩

theorem base_rel (x : G → ZMod q) : ∃ c, bd G c = base x - x := by
  have := (base_spec x).1; simp only [cls, mem_filter, mem_univ, true_and] at this; exact this

theorem base_eq {x y : G → ZMod q} (h : ∃ c, bd G c = x - y) : base x = base y := by
  unfold base; rw [cls_eq h]

theorem base_base (x : G → ZMod q) : base (base x) = base x := base_eq (base_rel x)

theorem wt_le_vdeg (x : G → ZMod q) : wt x ≤ vdeg x := by
  unfold wt vdeg
  calc (univ.filter fun e => x e ≠ 0).card = ∑ e ∈ univ.filter (fun e => x e ≠ 0), 1 := by simp
    _ ≤ ∑ e ∈ univ.filter (fun e => x e ≠ 0), (x e).val := by
        refine sum_le_sum fun e he => ?_
        have := (mem_filter.1 he).2
        rw [Nat.one_le_iff_ne_zero, Ne, ZMod.val_eq_zero]; exact this
    _ ≤ ∑ e, (x e).val := sum_le_sum_of_subset (filter_subset _ _)

theorem eq_zero_of_vdeg {x : G → ZMod q} (h : vdeg x = 0) : x = 0 := by
  funext e
  have := (sum_eq_zero_iff.1 h) e (mem_univ _)
  rw [ZMod.val_eq_zero] at this; exact this

theorem base_zero : base (0 : G → ZMod q) = 0 := by
  have := (base_spec (0 : G → ZMod q)).2
  have h0 : vdeg (0 : G → ZMod q) = 0 := by simp [vdeg]
  exact eq_zero_of_vdeg (by omega)

theorem wt_sub_le {α : Type} [Fintype α] (x y : α → ZMod q) : wt (x - y) ≤ wt x + wt y := by
  rw [sub_eq_add_neg]; exact (wt_add_le _ _).trans (by rw [wt_neg])

/-- The unit vector of an edge. -/
def unitE (e : G) : G → ZMod q := fun e' => if e' = e then 1 else 0

theorem vdeg_add_unit (x : G → ZMod q) (e : G) : vdeg (x + unitE (q := q) e) ≤ vdeg x + 1 := by
  unfold vdeg
  rw [← sum_erase_add _ _ (mem_univ e), ← sum_erase_add _ _ (mem_univ e)]
  have h1 : ∑ e' ∈ univ.erase e, ((x + unitE (q := q) e) e').val = ∑ e' ∈ univ.erase e, (x e').val :=
    sum_congr rfl fun e' he' => by simp [unitE, ne_of_mem_erase he']
  have h2 : ((x + unitE (q := q) e) e).val ≤ (x e).val + 1 := by
    simp only [Pi.add_apply, unitE, if_true]
    exact (ZMod.val_add_le _ _).trans (Nat.add_le_add_left (by rw [ZMod.val_one_eq_one_mod]; exact Nat.mod_le _ _) _)
  omega

end Classes

/-! ## Phases -/

section Phase

variable {K : Type} [Field K] {q : ℕ} [NeZero q]

/-- `ω` raised to a residue mod `q`. -/
def pw (ω : K) (x : ZMod q) : K := ω ^ x.val

theorem pw_add {ω : K} (hω : ω ^ q = 1) (x y : ZMod q) : pw ω (x + y) = pw ω x * pw ω y := by
  unfold pw
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (x.val + y.val) q, pow_add, pow_mul, hω, one_pow, one_mul]

theorem pw_zero (ω : K) : pw ω (0 : ZMod q) = 1 := by simp [pw]

end Phase

/-! ## Monomials over the edge variables -/

section Mono

variable {n : ℕ} {G : FinGraph n} {q : ℕ} [NeZero q]

/-- The edge variables. -/
def EV (G : FinGraph n) : Finset ℕ := G.image edgeVar

/-- Exponents of the edge variables mod `q`. -/
def piv (G : FinGraph n) (s : ℕ →₀ ℕ) : G → ZMod q := fun e => ((s (edgeVar e.1) : ℕ) : ZMod q)

/-- The part of an exponent vector off the edge variables. -/
def rest (G : FinGraph n) (s : ℕ →₀ ℕ) : ℕ →₀ ℕ := s.filter fun i => i ∉ EV G

/-- The monomial with exponents the representatives of `x`. -/
def lift (x : G → ZMod q) : ℕ →₀ ℕ := ∑ e : G, Finsupp.single (edgeVar e.1) (x e).val

theorem mem_EV {e : G} : edgeVar e.1 ∈ EV G := mem_image.2 ⟨e.1, e.2, rfl⟩

theorem lift_apply_edge (hn : 0 < n) (x : G → ZMod q) (e : G) :
    lift x (edgeVar e.1) = (x e).val := by
  unfold lift
  rw [Finsupp.finset_sum_apply, sum_eq_single e]
  · simp
  · intro e' _ hne
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hne (Subtype.ext (edgeVar_injective n hn h))
  · simp

theorem lift_apply_off (x : G → ZMod q) {i : ℕ} (hi : i ∉ EV G) : lift x i = 0 := by
  unfold lift
  rw [Finsupp.finset_sum_apply]
  refine sum_eq_zero fun e _ => ?_
  rw [Finsupp.single_apply, if_neg]
  intro h; exact hi (h ▸ mem_EV)

theorem piv_lift_add (hn : 0 < n) (x : G → ZMod q) {r : ℕ →₀ ℕ} (hr : ∀ i ∈ EV G, r i = 0) :
    piv G (lift x + r) = x := by
  funext e
  simp only [piv, Finsupp.add_apply, lift_apply_edge hn, hr _ mem_EV, add_zero,
    ZMod.natCast_zmod_val]

theorem rest_lift_add (x : G → ZMod q) {r : ℕ →₀ ℕ} (hr : ∀ i ∈ EV G, r i = 0) :
    rest G (lift x + r) = r := by
  ext i
  simp only [rest, Finsupp.filter_apply, Finsupp.add_apply]
  by_cases h : i ∈ EV G
  · simp [h, hr i h]
  · simp [h, lift_apply_off x h]

theorem rest_off (s : ℕ →₀ ℕ) : ∀ i ∈ EV G, rest G s i = 0 := by
  intro i hi; simp [rest, Finsupp.filter_apply, hi]

theorem degree_lift (x : G → ZMod q) : Finsupp.degree (lift x) = vdeg x := by
  unfold lift vdeg; rw [map_sum]; simp

theorem piv_add_edge (hn : 0 < n) (s : ℕ →₀ ℕ) (e : G) :
    piv (q := q) G (s + Finsupp.single (edgeVar e.1) 1) = piv G s + unitE e := by
  funext e'
  simp only [piv, Finsupp.add_apply, Finsupp.single_apply, Pi.add_apply, unitE, Nat.cast_add]
  by_cases h : e' = e
  · subst h; simp
  · rw [if_neg, if_neg h]
    · simp
    · intro h'; exact h (Subtype.ext (edgeVar_injective n hn h').symm)

theorem piv_add_off (s : ℕ →₀ ℕ) {i : ℕ} (hi : i ∉ EV G) :
    piv (q := q) G (s + Finsupp.single i 1) = piv G s := by
  funext e
  simp only [piv, Finsupp.add_apply, Finsupp.single_apply]
  rw [if_neg (fun h => hi (by rw [h]; exact mem_EV)), add_zero]

theorem rest_add_edge (s : ℕ →₀ ℕ) {i : ℕ} (hi : i ∈ EV G) :
    rest G (s + Finsupp.single i 1) = rest G s := by
  ext j
  simp only [rest, Finsupp.filter_apply, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs with h1 h2 <;> simp_all

theorem rest_add_off (s : ℕ →₀ ℕ) {i : ℕ} (hi : i ∉ EV G) :
    rest G (s + Finsupp.single i 1) = rest G s + Finsupp.single i 1 := by
  ext j
  simp only [rest, Finsupp.filter_apply, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs with h1 h2 <;> simp_all

theorem degree_split (hn : 0 < n) (s : ℕ →₀ ℕ) :
    vdeg (piv (q := q) G s) + Finsupp.degree (rest G s) ≤ Finsupp.degree s := by
  have hs : s = s.filter (fun i => i ∈ EV G) + rest G s := (Finsupp.filter_pos_add_filter_neg _ _).symm
  conv_rhs => rw [hs]
  rw [map_add]
  refine Nat.add_le_add_right ?_ _
  have h1 : Finsupp.degree (s.filter fun i => i ∈ EV G) = ∑ i ∈ EV G, s i := by
    rw [Finsupp.degree_apply]
    refine sum_subset (fun i hi => ?_) (fun i hi hni => ?_) |>.trans (sum_congr rfl fun i hi => ?_)
    · simp only [Finsupp.mem_support_iff, Finsupp.filter_apply] at hi
      by_contra h; exact hi (if_neg h)
    · simp only [Finsupp.mem_support_iff, Finsupp.filter_apply, not_not] at hni
      exact hni
    · simp [Finsupp.filter_apply, hi]
  rw [h1, EV, sum_image fun a _ b _ h => edgeVar_injective n hn h]
  unfold vdeg piv
  rw [← sum_coe_sort G]
  refine sum_le_sum fun e _ => ?_
  rw [ZMod.val_natCast]; exact Nat.mod_le _ _

theorem degree_add_single (s : ℕ →₀ ℕ) (i : ℕ) :
    Finsupp.degree (s + Finsupp.single i 1) = Finsupp.degree s + 1 := by
  rw [map_add, Finsupp.degree_single]

end Mono

/-! ## The binomial Tseitin system -/

section Sys

variable {n : ℕ} (G : FinGraph n) {q : ℕ} [NeZero q] {K : Type} [Field K]

/-- Out edges of `v` as an exponent vector. -/
def outV (v : Fin n) : G → ZMod q := fun e => if e.1.val.1 = v then 1 else 0

/-- In edges of `v` as an exponent vector. -/
def inV (v : Fin n) : G → ZMod q := fun e => if e.1.val.2 = v then 1 else 0

/-- Vertex axiom: `∏_{out} y_e - ω^{b v} ∏_{in} y_e`. -/
def vertexAx (ω : K) (b : Fin n → ZMod q) (v : Fin n) : MvPolynomial ℕ K :=
  MvPolynomial.monomial (lift (outV (q := q) G v)) 1 -
    MvPolynomial.C (pw ω (b v)) * MvPolynomial.monomial (lift (inV (q := q) G v)) 1

/-- The binomial Tseitin mod `q` system. -/
def BTAx (ω : K) (b : Fin n → ZMod q) : Set (MvPolynomial ℕ K) :=
  {f | (∃ e ∈ G, f = MvPolynomial.X (edgeVar e) ^ q - 1) ∨ ∃ v, f = vertexAx G ω b v}

end Sys

section ROp

open MvPolynomial

variable {n : ℕ} {G : FinGraph n} {q : ℕ} [NeZero q] {K : Type} [Field K]

/-- The R-operator on monomials. -/
def Rmon (G : FinGraph n) (ω : K) (k d : ℕ) (b : Fin n → ZMod q) (s : ℕ →₀ ℕ) :
    MvPolynomial ℕ K :=
  if Finsupp.degree s ≤ d then
    C (pw ω (dlt (G := G) k b (piv G s - base (piv G s)))) *
      monomial (lift (base (piv (q := q) G s)) + rest G s) 1
  else 0

/-- The R-operator, extended additively. -/
def Rop (G : FinGraph n) (ω : K) (k d : ℕ) (b : Fin n → ZMod q) :
    MvPolynomial ℕ K →+ MvPolynomial ℕ K :=
  Finsupp.liftAddHom fun s => (AddMonoidHom.mulRight (Rmon G ω k d b s)).comp
    (C : K →+* MvPolynomial ℕ K).toAddMonoidHom

variable {ω : K} {k d : ℕ} {b : Fin n → ZMod q}

theorem Rop_monomial (s : ℕ →₀ ℕ) (c : K) : Rop G ω k d b (monomial s c) = C c * Rmon G ω k d b s := by
  show Finsupp.liftAddHom _ (Finsupp.single s c) = _
  simp

theorem Rop_C_mul (a : K) (f : MvPolynomial ℕ K) :
    Rop G ω k d b (C a * f) = C a * Rop G ω k d b f := by
  induction f using MvPolynomial.induction_on' with
  | monomial s c => rw [C_mul_monomial, Rop_monomial, Rop_monomial, map_mul, mul_assoc]
  | add p r hp hr => rw [mul_add, map_add, map_add, hp, hr, mul_add]

theorem bd_neg (c : Fin n → ZMod q) : bd G (-c) = -bd G c := by
  funext e; simp only [bd, Pi.neg_apply]; ring

theorem neg_rel {x y : G → ZMod q} (h : ∃ c, bd G c = x - y) : ∃ c, bd G c = y - x := by
  obtain ⟨c, hc⟩ := h; exact ⟨-c, by rw [bd_neg, hc, neg_sub]⟩

theorem Rmon_of_le {s : ℕ →₀ ℕ} (hs : Finsupp.degree s ≤ d) :
    Rmon G ω k d b s = C (pw ω (dlt (G := G) k b (piv G s - base (piv G s)))) *
      monomial (lift (base (piv (q := q) G s)) + rest G s) 1 := by
  unfold Rmon; rw [if_pos hs]

theorem X_mul_C_monomial (i : ℕ) (a : K) (t : ℕ →₀ ℕ) :
    X i * (C a * monomial t 1) = monomial (t + Finsupp.single i 1) a := by
  rw [C_mul_monomial, X, monomial_mul, add_comm, one_mul, mul_one]

/-- The key identity of the R-operator on monomials. -/
theorem Rmon_mul (hn : 0 < n) {k : ℕ} (hG : HasExpansionInv G k) (hω : ω ^ q = 1)
    (h8 : 8 * k * d < n) (s : ℕ →₀ ℕ) (i : ℕ) (hs : Finsupp.degree s + 1 ≤ d) :
    Rmon G ω k d b (s + Finsupp.single i 1) = Rop G ω k d b (X i * Rmon G ω k d b s) := by
  have hs' : Finsupp.degree s ≤ d := by omega
  have hsplit := degree_split (q := q) (G := G) hn s
  set β := base (piv (q := q) G s) with hβ
  have hβdeg : vdeg β ≤ vdeg (piv (q := q) G s) := (base_spec _).2
  have hβrel : ∃ c, bd G c = β - piv G s := base_rel _
  rw [Rmon_of_le hs', X_mul_C_monomial, Rop_monomial]
  have hroff := rest_off (G := G) s
  by_cases hi : i ∈ EV G
  · obtain ⟨e0, he0, rfl⟩ := mem_image.1 hi
    set e : G := ⟨e0, he0⟩
    have hdeg1 : Finsupp.degree (s + Finsupp.single (edgeVar e.1) 1) ≤ d := by
      rw [degree_add_single]; omega
    have hpivS := piv_add_edge (q := q) hn s e
    have hrestS := rest_add_edge (G := G) s hi
    -- the reduced monomial
    have hroff2 : ∀ j ∈ EV G, rest G s j = 0 := hroff
    have ht1 : piv (q := q) G (lift β + rest G s + Finsupp.single (edgeVar e.1) 1) =
        β + unitE e := by
      rw [piv_add_edge hn, piv_lift_add hn β hroff2]
    have ht2 : rest G (lift β + rest G s + Finsupp.single (edgeVar e.1) 1) = rest G s := by
      rw [rest_add_edge _ hi, rest_lift_add β hroff2]
    have ht3 : Finsupp.degree (lift β + rest G s + Finsupp.single (edgeVar e.1) 1) ≤ d := by
      rw [degree_add_single, map_add, degree_lift]; omega
    rw [Rmon_of_le hdeg1, Rmon_of_le ht3, ht1, ht2, hpivS, hrestS]
    have hbeq : base (β + unitE e) = base (piv G s + unitE (q := q) e) := by
      apply base_eq
      obtain ⟨c, hc⟩ := hβrel
      exact ⟨c, by rw [hc]; abel⟩
    rw [hbeq]
    set β' := base (piv G s + unitE (q := q) e)
    rw [← mul_assoc, ← map_mul, ← pw_add hω]
    congr 3
    -- the phase is additive
    have hx : ∃ c, bd G c = piv G s - β := neg_rel hβrel
    have hy : ∃ c, bd G c = β + unitE e - β' := by
      have := base_rel (β + unitE (q := q) e); rw [hbeq] at this; exact neg_rel this
    have hw1 : wt (piv (q := q) G s - β) ≤ 2 * (d - 1) := by
      have := wt_sub_le (piv (q := q) G s) β
      have := wt_le_vdeg (piv (q := q) G s); have := wt_le_vdeg β; omega
    have hw2 : wt (β + unitE e - β') ≤ 2 * d := by
      have := wt_sub_le (β + unitE (q := q) e) β'
      have h1 := wt_le_vdeg (β + unitE (q := q) e); have h2 := wt_le_vdeg β'
      have h3 := vdeg_add_unit β e
      have h4 : vdeg β' ≤ vdeg (β + unitE (q := q) e) := by rw [← hbeq]; exact (base_spec _).2
      omega
    have hkd : k * (wt (piv (q := q) G s - β) + wt (β + unitE e - β')) ≤ 4 * (k * d) := by
      calc _ ≤ k * (4 * d) := Nat.mul_le_mul_left _ (by omega)
        _ = 4 * (k * d) := by ring
    have h8' : 8 * k * d = 8 * (k * d) := by ring
    rw [← dlt_add hG b hx hy (by omega)]
    congr 1; abel
  · have hdeg1 : Finsupp.degree (s + Finsupp.single i 1) ≤ d := by
      rw [degree_add_single]; omega
    have hoff : ∀ j ∈ EV G, (rest G s + Finsupp.single i 1 : ℕ →₀ ℕ) j = 0 := by
      intro j hj
      rw [show ((rest G s + Finsupp.single i 1 : ℕ →₀ ℕ)) j = rest G s j + Finsupp.single i 1 j
        from Finsupp.add_apply _ _ _, hroff j hj, Finsupp.single_apply, if_neg (fun h => hi (by rw [h]; exact hj)), add_zero]
    have ht1 : piv (q := q) G (lift β + rest G s + Finsupp.single i 1) = β := by
      rw [add_assoc, piv_lift_add hn β hoff]
    have ht2 : rest G (lift β + rest G s + Finsupp.single i 1) = rest G s + Finsupp.single i 1 := by
      rw [add_assoc, rest_lift_add β hoff]
    have ht3 : Finsupp.degree (lift β + rest G s + Finsupp.single i 1) ≤ d := by
      rw [degree_add_single, map_add, degree_lift]; omega
    rw [Rmon_of_le hdeg1, Rmon_of_le ht3, ht1, ht2, piv_add_off s hi, rest_add_off s hi,
      base_base, sub_self, dlt_zero hG hn, pw_zero]
    simp [add_assoc]

/-- The R-operator commutes with multiplication by a variable on low degree polynomials. -/
theorem Rop_mul (hn : 0 < n) {k : ℕ} (hG : HasExpansionInv G k) (hω : ω ^ q = 1)
    (h8 : 8 * k * d < n) (g : MvPolynomial ℕ K) (i : ℕ) (hg : g.totalDegree + 1 ≤ d) :
    Rop G ω k d b (X i * g) = Rop G ω k d b (X i * Rop G ω k d b g) := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  simp only [mul_sum, map_sum]
  refine sum_congr rfl fun s hs => ?_
  rw [Rop_monomial, X, monomial_mul, one_mul, Rop_monomial, mul_left_comm, ← X, Rop_C_mul,
    add_comm, Rmon_mul hn hG hω h8 s i]
  have := le_totalDegree hs
  exact le_trans (Nat.add_le_add_right this 1) hg

end ROp

/-! ## The axioms vanish under `R`, and the lower bound -/

section Main

open MvPolynomial

variable {n : ℕ} {G : FinGraph n} {q : ℕ} [NeZero q] {K : Type} [Field K]
  {ω : K} {k d : ℕ} {b : Fin n → ZMod q}

theorem Rmon_trivial (hn : 0 < n) (hG : HasExpansionInv G k) {s : ℕ →₀ ℕ}
    (hs : Finsupp.degree s ≤ d) (hp : piv (q := q) G s = 0) (hr : rest G s = 0) :
    Rmon G ω k d b s = 1 := by
  have hl : lift (0 : G → ZMod q) = 0 := by simp [lift]
  rw [Rmon_of_le hs, hp, hr, base_zero, sub_self, dlt_zero hG hn, pw_zero, hl, add_zero, map_one,
    one_mul, monomial_zero', C_1]

theorem Rop_one (hn : 0 < n) (hG : HasExpansionInv G k) : Rop G ω k d b 1 = 1 := by
  rw [← C_1, ← monomial_zero', Rop_monomial, C_1, one_mul]
  exact Rmon_trivial hn hG (by simp) (by funext e; simp [piv]) (by ext j; simp [rest, Finsupp.filter_apply])

theorem Rop_edge (hn : 0 < n) (hG : HasExpansionInv G k) {e : FinEdge n} (he : e ∈ G)
    (hqd : q ≤ d) : Rop G ω k d b (X (edgeVar e) ^ q - 1) = 0 := by
  have hi : edgeVar e ∈ EV G := mem_image.2 ⟨e, he, rfl⟩
  rw [map_sub, Rop_one hn hG, X_pow_eq_monomial, Rop_monomial, C_1, one_mul,
    Rmon_trivial hn hG (by simpa using hqd), sub_self]
  · funext e'
    simp only [piv, Finsupp.single_apply, Pi.zero_apply]
    split_ifs <;> simp
  · ext j
    simp only [rest, Finsupp.filter_apply, Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply]
    split_ifs with h1 h2 <;> simp_all

/-- Vectors supported on edges at `v`, with representatives at most `1`, have small degree. -/
theorem vdeg_le_degree {v : Fin n} {x : G → ZMod q} (hx : ∀ e, x e ≠ 0 → e.1 ∈ incident G v)
    (hx1 : ∀ e, (x e).val ≤ 1) : vdeg x ≤ degree G v := by
  unfold vdeg degree
  calc ∑ e : G, (x e).val ≤ ∑ e : G, (if e.1 ∈ incident G v then 1 else 0) := by
        refine sum_le_sum fun e _ => ?_
        split_ifs with h
        · exact hx1 e
        · have : x e = 0 := by by_contra h'; exact h (hx e h')
          simp [this]
    _ = (univ.filter fun e : G => e.1 ∈ incident G v).card := by rw [sum_boole, Nat.cast_id]
    _ ≤ (incident G v).card :=
        card_le_card_of_injOn Subtype.val (fun e he => (mem_filter.1 he).2)
          (fun a _ b _ h => Subtype.ext h)

theorem val_ite_le (p : Prop) [Decidable p] : ((if p then (1 : ZMod q) else 0)).val ≤ 1 := by
  split_ifs
  · rw [ZMod.val_one_eq_one_mod]; exact Nat.mod_le _ _
  · simp

theorem Rop_vertex (hn : 0 < n) (hG : HasExpansionInv G k) (hω : ω ^ q = 1)
    (h8 : 8 * k * d + 2 ≤ n) (v : Fin n) (hdeg : degree G v ≤ d) :
    Rop G ω k d b (vertexAx G ω b v) = 0 := by
  set o := outV (q := q) G v
  set i' := inV (q := q) G v
  have hinc : ∀ e : G, (e.1.val.1 = v ∨ e.1.val.2 = v) → e.1 ∈ incident G v :=
    fun e h => mem_incident_iff.2 ⟨e.2, h⟩
  have hvo : vdeg o ≤ degree G v := vdeg_le_degree
    (fun e h => hinc e (Or.inl (by by_contra h'; exact h (by simp [o, outV, h']))))
    (fun e => val_ite_le _)
  have hvi : vdeg i' ≤ degree G v := vdeg_le_degree
    (fun e h => hinc e (Or.inr (by by_contra h'; exact h (by simp [i', inV, h']))))
    (fun e => val_ite_le _)
  have hp0 : ∀ x : G → ZMod q, piv (q := q) G (lift x) = x := fun x => by
    have := piv_lift_add hn x (r := 0) (by simp); rwa [add_zero] at this
  have hr0 : ∀ x : G → ZMod q, rest G (lift x) = 0 := fun x => by
    have := rest_lift_add x (r := 0) (by simp); rwa [add_zero] at this
  have hdo : Finsupp.degree (lift o) ≤ d := by rw [degree_lift]; omega
  have hdi : Finsupp.degree (lift i') ≤ d := by rw [degree_lift]; omega
  set ind : Fin n → ZMod q := fun w => if w = v then 1 else 0
  have hbd : bd G ind = o - i' := by
    funext e; simp only [bd, ind, o, i', outV, inV, Pi.sub_apply]
  have hbase : base o = base i' := base_eq ⟨ind, hbd⟩
  set β := base i'
  have hβi : vdeg β ≤ vdeg i' := (base_spec i').2
  have hwoi : wt (o - i') ≤ 2 * d := by
    have := wt_sub_le o i'; have := wt_le_vdeg o; have := wt_le_vdeg i'; omega
  have hkd : ∀ m, m ≤ 4 * d → k * m ≤ 4 * (k * d) := fun m hm => by
    calc k * m ≤ k * (4 * d) := Nat.mul_le_mul_left _ hm
      _ = 4 * (k * d) := by ring
  have h8' : 8 * k * d = 8 * (k * d) := by ring
  have hpot : dlt (G := G) k b (o - i') = b v := by
    have hk2 := hkd (wt (o - i')) (by omega)
    have := pot_eq hG hbd (by
      have : 2 * k * wt (o - i') = 2 * (k * wt (o - i')) := by ring
      omega) (by
      have : (vsupp ind).card ≤ 1 := by
        refine (card_le_card fun w hw => ?_).trans (card_singleton v).le
        simp only [vsupp, ind, mem_filter, mem_univ, true_and, ne_eq, ite_eq_right_iff,
          not_forall] at hw
        simp [hw.1]
      omega)
    unfold dlt; rw [this]; simp [ind]
  have hphase : dlt (G := G) k b (o - β) = b v + dlt (G := G) k b (i' - β) := by
    have hy : ∃ c, bd G c = i' - β := neg_rel (base_rel i')
    have hw2 : wt (i' - β) ≤ 2 * d := by
      have := wt_sub_le i' β; have := wt_le_vdeg i'; have := wt_le_vdeg β; omega
    have hk3 := hkd (wt (o - i') + wt (i' - β)) (by omega)
    rw [← hpot, ← dlt_add hG b ⟨ind, hbd⟩ hy (by omega)]
    congr 1; abel
  unfold vertexAx
  rw [map_sub, Rop_C_mul, Rop_monomial, Rop_monomial, C_1, one_mul, one_mul,
    Rmon_of_le hdo, Rmon_of_le hdi, hp0, hp0, hr0, hr0, hbase, hphase, pw_add hω, map_mul,
    mul_assoc, sub_self]

theorem le_totalDegree_X_pow_sub_one (i : ℕ) :
    q ≤ (X i ^ q - 1 : MvPolynomial ℕ K).totalDegree := by
  have hq : q ≠ 0 := NeZero.ne q
  have hmem : Finsupp.single i q ∈ (X i ^ q - 1 : MvPolynomial ℕ K).support := by
    rw [mem_support_iff, coeff_sub, coeff_X_pow, coeff_one, if_pos rfl, if_neg]
    · simp
    · intro h; exact hq (by simpa using congrArg (fun f => f i) h.symm)
  have := le_totalDegree hmem
  simpa using this

/-- **Tseitin mod `q` degree lower bound** (binomial encoding, BGIP style). On a graph with
inverse expansion `k`, maximum degree at most `d` and `8 k d + 2 ≤ n`, polynomial calculus over any
field containing `ω` with `ω^q = 1` has no degree `d` refutation of the binomial Tseitin system. -/
theorem tseitin_pc_degree (hn : 0 < n) (hG : HasExpansionInv G k) (hω : ω ^ q = 1)
    (h8 : 8 * k * d + 2 ≤ n) (hdeg : ∀ v, degree G v ≤ d) : ¬ PCD₀ (BTAx G ω b) d 1 := by
  have h8l : 8 * k * d < n := by omega
  intro h
  have key : ∀ f, PCD₀ (BTAx G ω b) d f → Rop G ω k d b f = 0 := by
    intro f hf
    induction hf with
    | ax hf hdf =>
      rcases hf with ⟨e, he, rfl⟩ | ⟨v, rfl⟩
      · exact Rop_edge hn hG he ((le_totalDegree_X_pow_sub_one _).trans hdf)
      · exact Rop_vertex hn hG hω h8 v (hdeg v)
    | lin a c _ _ ihf ihg => rw [map_add, Rop_C_mul, Rop_C_mul, ihf, ihg]; simp
    | mul i hg hdg ih =>
      rename_i g
      by_cases hg0 : g = 0
      · rw [hg0, mul_zero, map_zero]
      · have hdeg' : g.totalDegree + 1 ≤ d := by
          rw [totalDegree_mul_of_isDomain (X_ne_zero i) hg0, totalDegree_X] at hdg; omega
        rw [Rop_mul hn hG hω h8l g i hdeg', ih, mul_zero, map_zero]
  have := key 1 h
  rw [Rop_one hn hG] at this
  exact one_ne_zero this

end Main

/-! ## Non vacuity and the expander family -/

section Final

open MvPolynomial

variable {n : ℕ} {G : FinGraph n} {q : ℕ} [NeZero q] {K : Type} [Field K]

theorem eval_lift (y : ℕ → K) (x : G → ZMod q) :
    eval y (monomial (lift x) 1) = ∏ e : G, y (edgeVar e.1) ^ (x e).val := by
  unfold lift
  rw [monomial_sum_one, map_prod]
  refine prod_congr rfl fun e _ => ?_
  rw [← X_pow_eq_monomial, map_pow, eval_X]

/-- With a primitive `q`-th root of unity and total charge nonzero, the binomial Tseitin system
has no common root (the lower bound is about an unsatisfiable system). -/
theorem bt_no_root (hq : 2 ≤ q) {ω : K} (hω : IsPrimitiveRoot ω q) {b : Fin n → ZMod q}
    (hb : ∑ v, b v ≠ 0) (y : ℕ → K) : ¬ ∀ f ∈ BTAx G ω b, eval y f = 0 := by
  intro hy
  have hv1 : ((1 : ZMod q)).val = 1 := by
    haveI : Fact (1 < q) := ⟨hq⟩; exact ZMod.val_one q
  have hpow : ∀ (x : G → ZMod q) (v : Fin n),
      (∀ e, x e = if (e : FinEdge n).val.1 = v then 1 else 0) →
      ∏ e : G, y (edgeVar e.1) ^ (x e).val = ∏ e ∈ univ.filter (fun e : G => e.1.val.1 = v),
        y (edgeVar e.1) := by
    intro x v hx
    rw [prod_filter]
    refine prod_congr rfl fun e _ => ?_
    rw [hx e]; split_ifs <;> simp [hv1]
  have hpowi : ∀ (x : G → ZMod q) (v : Fin n),
      (∀ e, x e = if (e : FinEdge n).val.2 = v then 1 else 0) →
      ∏ e : G, y (edgeVar e.1) ^ (x e).val = ∏ e ∈ univ.filter (fun e : G => e.1.val.2 = v),
        y (edgeVar e.1) := by
    intro x v hx
    rw [prod_filter]
    refine prod_congr rfl fun e _ => ?_
    rw [hx e]; split_ifs <;> simp [hv1]
  have hvert : ∀ v, ∏ e ∈ univ.filter (fun e : G => e.1.val.1 = v), y (edgeVar e.1) =
      pw ω (b v) * ∏ e ∈ univ.filter (fun e : G => e.1.val.2 = v), y (edgeVar e.1) := by
    intro v
    have := hy _ (Or.inr ⟨v, rfl⟩)
    unfold vertexAx at this
    rw [map_sub, map_mul, eval_C, eval_lift, eval_lift, sub_eq_zero,
      hpow (outV G v) v (fun e => rfl), hpowi (inV G v) v (fun e => rfl)] at this
    exact this
  have htot : ∏ v, ∏ e ∈ univ.filter (fun e : G => e.1.val.1 = v), y (edgeVar e.1) =
      ∏ v, ∏ e ∈ univ.filter (fun e : G => e.1.val.2 = v), y (edgeVar e.1) := by
    rw [prod_fiberwise univ (fun e : G => e.1.val.1) (fun e => y (edgeVar e.1)),
      prod_fiberwise univ (fun e : G => e.1.val.2) (fun e => y (edgeVar e.1))]
  have hne : ∏ v, ∏ e ∈ univ.filter (fun e : G => e.1.val.2 = v), y (edgeVar e.1) ≠ 0 := by
    rw [prod_fiberwise univ (fun e : G => e.1.val.2) (fun e => y (edgeVar e.1))]
    refine prod_ne_zero_iff.2 fun e _ => ?_
    intro h0
    have := hy _ (Or.inl ⟨e.1, e.2, rfl⟩)
    rw [map_sub, map_pow, eval_X, h0, zero_pow (NeZero.ne q), map_one] at this
    simp at this
  simp_rw [hvert] at htot
  rw [prod_mul_distrib] at htot
  have h1 : ∏ v, pw ω (b v) = 1 := by
    exact mul_right_cancel₀ hne (htot.trans (one_mul _).symm)
  -- `∏ ω^{(b v).val} = ω^{(∑ b v).val}`
  have hω1 : ω ^ q = 1 := hω.pow_eq_one
  have hsum : ∀ (s : Finset (Fin n)), ∏ v ∈ s, pw ω (b v) = pw ω (∑ v ∈ s, b v) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [pw]
    | insert a s ha ih => rw [prod_insert ha, sum_insert ha, ih, pw_add hω1]
  rw [hsum] at h1
  unfold pw at h1
  have := hω.dvd_of_pow_eq_one _ h1
  have hlt := ZMod.val_lt (∑ v, b v)
  have : (∑ v, b v).val = 0 := by
    rcases this with ⟨c, hc⟩
    rcases c with _ | c
    · simpa using hc
    · nlinarith
  exact hb ((ZMod.val_eq_zero _).1 this)

/-- **Linear degree on cubic expanders**: for every `N` there is a connected cubic graph on
`n ≥ N` vertices on which, for every charge, field and `ω` with `ω^q = 1`, the binomial Tseitin
mod `q` system has no polynomial calculus refutation of degree `(n - 2) / 1312`. -/
theorem tseitin_pc_degree_cubic (q : ℕ) [NeZero q] (N : ℕ) :
    ∃ (n : ℕ) (G : FinGraph n), N ≤ n ∧ IsRegular G 3 ∧
      ∀ (K : Type) [Field K] (ω : K) (b : Fin n → ZMod q), ω ^ q = 1 →
        ¬ PCD₀ (BTAx G ω b) ((n - 2) / 1312) 1 := by
  obtain ⟨n, G, hN, hreg, -, hexp⟩ := exists_mggF2Cub_hasExpansionInv_family (max N 4000)
  refine ⟨n, G, le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN), hreg, ?_⟩
  intro K _ ω b hω
  have hn : 4000 ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hk : mggF2CubK = 164 := rfl
  refine tseitin_pc_degree (by omega) hexp hω ?_ (fun v => ?_)
  · rw [hk]
    have := Nat.div_mul_le_self (n - 2) 1312
    omega
  · rw [hreg v]
    have : 3 ≤ (n - 2) / 1312 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
    exact this

end Final

end

end TseitinPC

end SATurday.ProofComplexity
