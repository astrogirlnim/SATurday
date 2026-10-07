import Theory.ProofComplexity.Sunflower
import Theory.ProofComplexity.CuttingPlanes

/-!
# Clique lower bound for monotone Boolean circuits: approximators (Ladder Rung R3)

Razborov's approximation method in the Boppana–Sipser form. Positive tests are single
`k` cliques, negative tests are colorings `c : Fin n → Fin K` (edges join different
colors). Approximators are families of vertex sets of size at most `ℓ`, read as an
`OR` of clique indicators.

This file: graphs, clique indicators, normalized families and plucking (sunflower
replacement), with the plucking error bound on negative tests.

LOG: R3 MonotoneClique module (approximators, plucking)
-/

namespace SATurday.ProofComplexity

open Finset

noncomputable section

open Classical

variable {n : ℕ}

/-- A graph on `Fin n`. -/
abbrev Gr (n : ℕ) := Fin n → Fin n → Prop

/-- `X` is a clique of `G`. -/
def IsCl (G : Gr n) (X : Finset (Fin n)) : Prop := ∀ u ∈ X, ∀ v ∈ X, u ≠ v → G u v

/-- A family accepts `G` when one of its sets is a clique of `G`. -/
def Acc (G : Gr n) (F : Finset (Finset (Fin n))) : Prop := ∃ X ∈ F, IsCl G X

theorem IsCl.mono {G : Gr n} {X Y : Finset (Fin n)} (h : IsCl G X) (hY : Y ⊆ X) : IsCl G Y :=
  fun u hu v hv huv => h u (hY hu) v (hY hv) huv

theorem isCl_of_card_le_one {G : Gr n} {X : Finset (Fin n)} (h : X.card ≤ 1) : IsCl G X := by
  intro u hu v hv huv
  exact absurd (Finset.card_le_one.1 h u hu v hv) huv

/-- Positive test: the single clique on `K`. -/
def posG (K : Finset (Fin n)) : Gr n := fun u v => u ∈ K ∧ v ∈ K

/-- Negative test: the complete multipartite graph of a coloring. -/
def negG {K : ℕ} (c : Fin n → Fin K) : Gr n := fun u v => c u ≠ c v

theorem isCl_posG {K X : Finset (Fin n)} (hX : X.card ≠ 1) : IsCl (posG K) X ↔ X ⊆ K := by
  constructor
  · intro h u hu
    have h2 : 2 ≤ X.card := by
      rcases Nat.lt_or_ge X.card 2 with h' | h'
      · have : X.card = 0 := by
          have := Finset.card_pos.2 ⟨u, hu⟩; omega
        rw [Finset.card_eq_zero] at this; subst this; simp at hu
      · exact h'
    obtain ⟨v, hv, hvu⟩ : ∃ v ∈ X, v ≠ u := by
      by_contra hno
      push_neg at hno
      have : X ⊆ {u} := fun w hw => Finset.mem_singleton.2 (hno w hw)
      have := Finset.card_le_card this
      simp at this; omega
    exact (h u hu v hv (Ne.symm hvu)).1
  · intro h u hu v hv _
    exact ⟨h hu, h hv⟩

theorem isCl_negG {K : ℕ} {c : Fin n → Fin K} {X : Finset (Fin n)} :
    IsCl (negG c) X ↔ Set.InjOn c X := by
  constructor
  · intro h u hu v hv huv
    by_contra hne
    exact h u hu v hv hne huv
  · intro h u hu v hv huv hc
    exact huv (h hu hv hc)

/-! ## Normalized families -/

/-- Replace singletons by `∅` (both are cliques of every graph). -/
def normSet (X : Finset (Fin n)) : Finset (Fin n) := if X.card ≤ 1 then ∅ else X

def normF (F : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) := F.image normSet

theorem normSet_subset (X : Finset (Fin n)) : normSet X ⊆ X := by
  unfold normSet; split_ifs <;> simp

theorem normSet_card_ne_one (X : Finset (Fin n)) : (normSet X).card ≠ 1 := by
  unfold normSet; split_ifs with h <;> simp <;> omega

theorem isCl_normSet {G : Gr n} {X : Finset (Fin n)} : IsCl G (normSet X) ↔ IsCl G X := by
  unfold normSet
  split_ifs with h
  · exact ⟨fun _ => isCl_of_card_le_one h, fun _ => isCl_of_card_le_one (by simp)⟩
  · exact Iff.rfl

theorem acc_normF {G : Gr n} {F : Finset (Finset (Fin n))} : Acc G (normF F) ↔ Acc G F := by
  constructor
  · rintro ⟨Y, hY, hc⟩
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 hY
    exact ⟨X, hX, isCl_normSet.1 hc⟩
  · rintro ⟨X, hX, hc⟩
    exact ⟨normSet X, Finset.mem_image_of_mem _ hX, isCl_normSet.2 hc⟩

theorem normF_card_le (F : Finset (Finset (Fin n))) : (normF F).card ≤ F.card :=
  Finset.card_image_le

/-- Well formed approximators: small sets, no singletons. -/
def SmallF (ℓ : ℕ) (F : Finset (Finset (Fin n))) : Prop := ∀ X ∈ F, X.card ≤ ℓ ∧ X.card ≠ 1

theorem smallF_normF {ℓ : ℕ} {F : Finset (Finset (Fin n))} (h : ∀ X ∈ F, X.card ≤ ℓ) :
    SmallF ℓ (normF F) := by
  intro Y hY
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 hY
  exact ⟨(Finset.card_le_card (normSet_subset X)).trans (h X hX), normSet_card_ne_one X⟩

/-! ## Plucking -/

/-- One plucking step: replace a `p` petal sunflower by its core. -/
def pluckStep (p ℓ : ℕ) (F : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  if h : 2 ≤ p ∧ (∀ X ∈ F, X.card ≤ ℓ) ∧ sfBound p ℓ < F.card ∧ Nonempty (Fin n) then
    haveI := h.2.2.2
    let hs := exists_sunflower p ℓ F h.2.1 h.2.2.1
    normF ((F \ hs.choose) ∪ {hs.choose_spec.2.2.choose})
  else F

theorem pluckStep_card_lt {p ℓ : ℕ} {F : Finset (Finset (Fin n))} (hp : 2 ≤ p)
    (hF : ∀ X ∈ F, X.card ≤ ℓ) (hc : sfBound p ℓ < F.card) (hn : Nonempty (Fin n)) :
    (pluckStep p ℓ F).card < F.card := by
  unfold pluckStep
  rw [dif_pos ⟨hp, hF, hc, hn⟩]
  haveI := hn
  set hs := exists_sunflower p ℓ F hF hc
  have hsub := hs.choose_spec.1
  have hcard := hs.choose_spec.2.1
  refine lt_of_le_of_lt (normF_card_le _) ?_
  calc ((F \ hs.choose) ∪ {hs.choose_spec.2.2.choose}).card
      ≤ (F \ hs.choose).card + 1 := by
        have := Finset.card_union_le (F \ hs.choose) {hs.choose_spec.2.2.choose}; simpa using this
    _ = F.card - p + 1 := by rw [Finset.card_sdiff_of_subset hsub, hcard]
    _ < F.card := by
        have : p ≤ F.card := hcard ▸ Finset.card_le_card hsub
        omega

/-- Repeated plucking until at most `sfBound p ℓ` sets remain. -/
def pluck (p ℓ : ℕ) (F : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  if h : 2 ≤ p ∧ (∀ X ∈ F, X.card ≤ ℓ) ∧ sfBound p ℓ < F.card ∧ Nonempty (Fin n) then
    pluck p ℓ (pluckStep p ℓ F)
  else F
termination_by F.card
decreasing_by exact pluckStep_card_lt h.1 h.2.1 h.2.2.1 h.2.2.2

/-- The sunflower chosen by a plucking step, with its core. -/
theorem pluckStep_spec {p ℓ : ℕ} {F : Finset (Finset (Fin n))} (hp : 2 ≤ p)
    (hF : ∀ X ∈ F, X.card ≤ ℓ) (hc : sfBound p ℓ < F.card) (hn : Nonempty (Fin n)) :
    ∃ S Z, S ⊆ F ∧ S.card = p ∧ IsSunflower S Z ∧ (∀ X ∈ S, Z ⊆ X) ∧
      pluckStep p ℓ F = normF ((F \ S) ∪ {Z}) := by
  unfold pluckStep
  rw [dif_pos ⟨hp, hF, hc, hn⟩]
  haveI := hn
  set hs := exists_sunflower p ℓ F hF hc
  refine ⟨hs.choose, hs.choose_spec.2.2.choose, hs.choose_spec.1, hs.choose_spec.2.1,
    hs.choose_spec.2.2.choose_spec, ?_, rfl⟩
  intro X hX
  -- a second petal exists since `p ≥ 2`
  have h2 : 1 < hs.choose.card := by rw [hs.choose_spec.2.1]; omega
  obtain ⟨Y, hY, hXY⟩ := Finset.exists_mem_ne h2 X
  rw [← hs.choose_spec.2.2.choose_spec X hX Y hY (Ne.symm hXY)]
  exact Finset.inter_subset_left

theorem pluck_eq {p ℓ : ℕ} (F : Finset (Finset (Fin n))) :
    pluck p ℓ F = if 2 ≤ p ∧ (∀ X ∈ F, X.card ≤ ℓ) ∧ sfBound p ℓ < F.card ∧ Nonempty (Fin n)
      then pluck p ℓ (pluckStep p ℓ F) else F := by
  rw [pluck]; split_ifs <;> rfl

/-- Plucking keeps small sets and the no singleton shape. -/
theorem pluck_small {p ℓ : ℕ} : ∀ (F : Finset (Finset (Fin n))), SmallF ℓ F →
    SmallF ℓ (pluck p ℓ F) := by
  intro F
  induction h : F.card using Nat.strong_induction_on generalizing F with
  | _ N ih =>
  intro hF
  rw [pluck_eq]
  split_ifs with hc
  · obtain ⟨S, Z, hSF, hScard, hsun, hZ, heq⟩ := pluckStep_spec hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    refine ih _ (h ▸ pluckStep_card_lt hc.1 hc.2.1 hc.2.2.1 hc.2.2.2) _ rfl ?_
    rw [heq]
    apply smallF_normF
    intro X hX
    rcases Finset.mem_union.1 hX with hX | hX
    · exact (hF X (Finset.mem_sdiff.1 hX).1).1
    · rw [Finset.mem_singleton.1 hX]
      have : 0 < S.card := by omega
      obtain ⟨Y, hY⟩ := Finset.card_pos.1 this
      exact (Finset.card_le_card (hZ Y hY)).trans (hF Y (hSF hY)).1
  · exact hF

/-- Plucking stops at `sfBound p ℓ` sets. -/
theorem pluck_card {p ℓ : ℕ} (hp : 2 ≤ p) (hn : Nonempty (Fin n)) :
    ∀ (F : Finset (Finset (Fin n))), (∀ X ∈ F, X.card ≤ ℓ) → (pluck p ℓ F).card ≤ sfBound p ℓ := by
  intro F
  induction h : F.card using Nat.strong_induction_on generalizing F with
  | _ N ih =>
  intro hF
  rw [pluck_eq]
  split_ifs with hc
  · obtain ⟨S, Z, hSF, hScard, hsun, hZ, heq⟩ := pluckStep_spec hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    refine ih _ (h ▸ pluckStep_card_lt hc.1 hc.2.1 hc.2.2.1 hc.2.2.2) _ rfl ?_
    rw [heq]
    intro Y hY
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 hY
    refine (Finset.card_le_card (normSet_subset X)).trans ?_
    rcases Finset.mem_union.1 hX with hX | hX
    · exact hF X (Finset.mem_sdiff.1 hX).1
    · rw [Finset.mem_singleton.1 hX]
      have : 0 < S.card := by omega
      obtain ⟨Y, hY⟩ := Finset.card_pos.1 this
      exact (Finset.card_le_card (hZ Y hY)).trans (hF Y (hSF hY))
  · push_neg at hc
    by_contra hlt
    exact absurd (hc hp hF) (by push_neg; exact ⟨by omega, hn⟩)

/-- Every set of the input contains a set of the plucked family. -/
theorem pluck_sub {p ℓ : ℕ} : ∀ (F : Finset (Finset (Fin n))), ∀ X ∈ F,
    ∃ Y ∈ pluck p ℓ F, Y ⊆ X := by
  intro F
  induction h : F.card using Nat.strong_induction_on generalizing F with
  | _ N ih =>
  intro X hX
  rw [pluck_eq]
  split_ifs with hc
  · obtain ⟨S, Z, hSF, hScard, hsun, hZ, heq⟩ := pluckStep_spec hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    have hstep : ∃ X' ∈ pluckStep p ℓ F, X' ⊆ X := by
      rw [heq]
      by_cases hXS : X ∈ S
      · exact ⟨normSet Z, Finset.mem_image_of_mem _ (Finset.mem_union_right _
          (Finset.mem_singleton_self Z)), (normSet_subset Z).trans (hZ X hXS)⟩
      · exact ⟨normSet X, Finset.mem_image_of_mem _ (Finset.mem_union_left _
          (Finset.mem_sdiff.2 ⟨hX, hXS⟩)), normSet_subset X⟩
    obtain ⟨X', hX', hsub⟩ := hstep
    obtain ⟨Y, hY, hYX⟩ := ih _ (h ▸ pluckStep_card_lt hc.1 hc.2.1 hc.2.2.1 hc.2.2.2) _ rfl X' hX'
    exact ⟨Y, hY, hYX.trans hsub⟩
  · exact ⟨X, hX, Finset.Subset.refl X⟩

theorem pluck_acc {p ℓ : ℕ} {G : Gr n} {F : Finset (Finset (Fin n))} (h : Acc G F) :
    Acc G (pluck p ℓ F) := by
  obtain ⟨X, hX, hc⟩ := h
  obtain ⟨Y, hY, hYX⟩ := pluck_sub F X hX
  exact ⟨Y, hY, hc.mono hYX⟩

/-- Plucking error on negative tests: colorings accepted after plucking but not before. -/
theorem pluck_err {K p ℓ E : ℕ}
    (hE : ∀ (S : Finset (Finset (Fin n))) (Z : Finset (Fin n)), S.card = p → IsSunflower S Z →
      (∀ X ∈ S, Z ⊆ X) → (∀ X ∈ S, X.card ≤ ℓ) →
      (Finset.univ.filter fun c : Fin n → Fin K =>
        IsCl (negG c) Z ∧ ∀ X ∈ S, ¬ IsCl (negG c) X).card ≤ E) :
    ∀ (F : Finset (Finset (Fin n))),
      (Finset.univ.filter fun c : Fin n → Fin K =>
        Acc (negG c) (pluck p ℓ F) ∧ ¬ Acc (negG c) F).card ≤ F.card * E := by
  intro F
  induction h : F.card using Nat.strong_induction_on generalizing F with
  | _ N ih =>
  rw [pluck_eq]
  split_ifs with hc
  · obtain ⟨S, Z, hSF, hScard, hsun, hZ, heq⟩ := pluckStep_spec hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    have hlt := pluckStep_card_lt hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    have hrec := ih _ (h ▸ hlt) (pluckStep p ℓ F) rfl
    have hstepE := hE S Z hScard hsun hZ (fun X hX => hc.2.1 X (hSF hX))
    have hsub : (Finset.univ.filter fun c : Fin n → Fin K =>
          Acc (negG c) (pluck p ℓ (pluckStep p ℓ F)) ∧ ¬ Acc (negG c) F) ⊆
        (Finset.univ.filter fun c : Fin n → Fin K =>
          IsCl (negG c) Z ∧ ∀ X ∈ S, ¬ IsCl (negG c) X) ∪
        (Finset.univ.filter fun c : Fin n → Fin K =>
          Acc (negG c) (pluck p ℓ (pluckStep p ℓ F)) ∧ ¬ Acc (negG c) (pluckStep p ℓ F)) := by
      intro c hc'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc'
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hstep : Acc (negG c) (pluckStep p ℓ F)
      · left
        rw [heq, acc_normF] at hstep
        obtain ⟨Y, hY, hYc⟩ := hstep
        rcases Finset.mem_union.1 hY with hY | hY
        · exact absurd ⟨Y, (Finset.mem_sdiff.1 hY).1, hYc⟩ hc'.2
        · rw [Finset.mem_singleton.1 hY] at hYc
          exact ⟨hYc, fun X hX hXc => hc'.2 ⟨X, hSF hX, hXc⟩⟩
      · right; exact ⟨hc'.1, hstep⟩
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ E + (pluckStep p ℓ F).card * E := Nat.add_le_add hstepE hrec
      _ ≤ N * E := by
          have : (pluckStep p ℓ F).card + 1 ≤ N := h ▸ hlt
          nlinarith
  · simp

/-! ## Counting colorings that defeat a sunflower -/

/-- Colorings with prescribed equalities `c u = c v` along disjoint `u`s. -/
theorem card_compat_le {K : ℕ} (U : Finset (Fin n)) (pr : Fin n → Fin n)
    (hpr : ∀ u ∈ U, pr u ∉ U) :
    (Finset.univ.filter fun c : Fin n → Fin K => ∀ u ∈ U, c u = c (pr u)).card * K ^ U.card ≤
      K ^ n := by
  set T := Finset.univ.filter fun c : Fin n → Fin K => ∀ u ∈ U, c u = c (pr u)
  let φ : (Fin n → Fin K) → ({w // w ∉ U} → Fin K) := fun c w => c w.1
  have hinj : Set.InjOn φ (T : Set (Fin n → Fin K)) := by
    intro c1 h1 c2 h2 h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, T] at h1 h2
    funext w
    by_cases hw : w ∈ U
    · rw [h1 w hw, h2 w hw]
      exact congrFun h ⟨pr w, hpr w hw⟩
    · exact congrFun h ⟨w, hw⟩
  have h1 : T.card ≤ K ^ (n - U.card) := by
    calc T.card ≤ (Finset.univ : Finset ({w // w ∉ U} → Fin K)).card :=
          Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_univ _) hinj
      _ = K ^ (n - U.card) := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype_compl,
            Fintype.card_fin, Fintype.card_coe]
  have hU : U.card ≤ n := by
    have := Finset.card_le_univ U; simpa using this
  calc T.card * K ^ U.card ≤ K ^ (n - U.card) * K ^ U.card := Nat.mul_le_mul_right _ h1
    _ = K ^ n := by rw [← pow_add, Nat.sub_add_cancel hU]

/-- A random coloring defeats a sunflower with `p` petals with probability at most
`(ℓ²/K)^p`. -/
theorem sunflower_err {K ℓ p : ℕ} (S : Finset (Finset (Fin n))) (Z : Finset (Fin n))
    (hS : S.card = p) (hsun : IsSunflower S Z) (hZ : ∀ X ∈ S, Z ⊆ X)
    (hℓ : ∀ X ∈ S, X.card ≤ ℓ) :
    (Finset.univ.filter fun c : Fin n → Fin K =>
      IsCl (negG c) Z ∧ ∀ X ∈ S, ¬ IsCl (negG c) X).card * K ^ p ≤ (ℓ * ℓ) ^ p * K ^ n := by
  set T := S.pi fun X => (X \ Z) ×ˢ X
  let Comp : ((X : Finset (Fin n)) → X ∈ S → Fin n × Fin n) → Finset (Fin n → Fin K) :=
    fun σ => Finset.univ.filter fun c =>
      ∀ X (hX : X ∈ S), (σ X hX).1 ≠ (σ X hX).2 ∧ c (σ X hX).1 = c (σ X hX).2
  -- the event is covered by the compatible sets
  have hcover : (Finset.univ.filter fun c : Fin n → Fin K =>
      IsCl (negG c) Z ∧ ∀ X ∈ S, ¬ IsCl (negG c) X) ⊆ T.biUnion Comp := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨hcZ, hcS⟩ := hc
    have hex : ∀ X ∈ S, ∃ pr : Fin n × Fin n,
        pr ∈ (X \ Z) ×ˢ X ∧ pr.1 ≠ pr.2 ∧ c pr.1 = c pr.2 := by
      intro X hX
      have hni := hcS X hX
      rw [isCl_negG] at hni hcZ
      simp only [Set.InjOn, not_forall] at hni
      obtain ⟨u, hu, v, hv, huv, hne⟩ := hni
      by_cases huZ : u ∈ Z
      · have hvZ : v ∉ Z := by
          intro hvZ; exact hne (hcZ huZ hvZ huv)
        exact ⟨(v, u), Finset.mem_product.2 ⟨Finset.mem_sdiff.2 ⟨hv, hvZ⟩, hu⟩,
          fun h => hne h.symm, huv.symm⟩
      · exact ⟨(u, v), Finset.mem_product.2 ⟨Finset.mem_sdiff.2 ⟨hu, huZ⟩, hv⟩, hne, huv⟩
    let σ : (X : Finset (Fin n)) → X ∈ S → Fin n × Fin n := fun X hX => (hex X hX).choose
    refine Finset.mem_biUnion.2 ⟨σ, Finset.mem_pi.2 fun X hX => (hex X hX).choose_spec.1, ?_⟩
    simp only [Comp, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun X hX => (hex X hX).choose_spec.2
  -- each compatible set is small
  have hcomp : ∀ σ ∈ T, (Comp σ).card * K ^ p ≤ K ^ n := by
    intro σ hσ
    by_cases hbad : ∃ X, ∃ hX : X ∈ S, (σ X hX).1 = (σ X hX).2
    · obtain ⟨X, hX, he⟩ := hbad
      have : Comp σ = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro c hc
        simp only [Comp, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        exact (hc X hX).1 he
      rw [this]; simp
    · push_neg at hbad
      have hmem : ∀ X (hX : X ∈ S), (σ X hX).1 ∈ X \ Z ∧ (σ X hX).2 ∈ X := by
        intro X hX
        exact Finset.mem_product.1 (Finset.mem_pi.1 hσ X hX)
      let uOf : S → Fin n := fun X => (σ X.1 X.2).1
      have huinj : Function.Injective uOf := by
        intro X Y h
        by_contra hXY
        have hXY' : X.1 ≠ Y.1 := fun e => hXY (Subtype.ext e)
        have h1 := hmem X.1 X.2
        have h2 := hmem Y.1 Y.2
        have hu : uOf X ∈ X.1 ∩ Y.1 := Finset.mem_inter.2
          ⟨(Finset.mem_sdiff.1 h1.1).1, h ▸ (Finset.mem_sdiff.1 h2.1).1⟩
        rw [hsun X.1 X.2 Y.1 Y.2 hXY'] at hu
        exact (Finset.mem_sdiff.1 h1.1).2 hu
      set U := Finset.univ.image uOf with hU
      have hUcard : U.card = p := by
        rw [Finset.card_image_of_injective _ huinj, Finset.card_univ, Fintype.card_coe, hS]
      -- partner map: `u_X ↦ v_X`
      let pr : Fin n → Fin n := fun w =>
        if h : ∃ X : S, uOf X = w then (σ h.choose.1 h.choose.2).2 else w
      have hpr : ∀ w ∈ U, pr w ∉ U := by
        intro w hw
        obtain ⟨X, _, rfl⟩ := Finset.mem_image.1 hw
        have hex : ∃ Y : S, uOf Y = uOf X := ⟨X, rfl⟩
        have hY : hex.choose = X := huinj hex.choose_spec
        simp only [pr, dif_pos hex, hY]
        intro hv
        obtain ⟨Y, _, hYv⟩ := Finset.mem_image.1 hv
        by_cases hXY : X = Y
        · subst hXY
          exact hbad X.1 X.2 hYv
        · have hXY' : X.1 ≠ Y.1 := fun e => hXY (Subtype.ext e)
          have h1 := hmem Y.1 Y.2
          have hin : uOf Y ∈ X.1 ∩ Y.1 :=
            Finset.mem_inter.2 ⟨hYv ▸ (hmem X.1 X.2).2, (Finset.mem_sdiff.1 h1.1).1⟩
          rw [hsun X.1 X.2 Y.1 Y.2 hXY'] at hin
          exact (Finset.mem_sdiff.1 h1.1).2 hin
      have hsub : Comp σ ⊆ Finset.univ.filter fun c : Fin n → Fin K => ∀ u ∈ U, c u = c (pr u) := by
        intro c hc
        simp only [Comp, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        intro w hw
        obtain ⟨X, _, rfl⟩ := Finset.mem_image.1 hw
        have hex : ∃ Y : S, uOf Y = uOf X := ⟨X, rfl⟩
        have hY : hex.choose = X := huinj hex.choose_spec
        simp only [pr, dif_pos hex, hY]
        exact (hc X.1 X.2).2
      have := card_compat_le (K := K) U pr hpr
      rw [hUcard] at this
      exact (Nat.mul_le_mul_right _ (Finset.card_le_card hsub)).trans this
  -- the number of choices
  have hT : T.card ≤ (ℓ * ℓ) ^ p := by
    rw [Finset.card_pi]
    calc ∏ X ∈ S, ((X \ Z) ×ˢ X).card ≤ ∏ _X ∈ S, ℓ * ℓ := by
          apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
          intro X hX
          rw [Finset.card_product]
          exact Nat.mul_le_mul ((Finset.card_le_card Finset.sdiff_subset).trans (hℓ X hX))
            (hℓ X hX)
      _ = (ℓ * ℓ) ^ p := by rw [Finset.prod_const, hS]
  calc _ ≤ (T.biUnion Comp).card * K ^ p := Nat.mul_le_mul_right _ (Finset.card_le_card hcover)
    _ ≤ (∑ σ ∈ T, (Comp σ).card) * K ^ p := Nat.mul_le_mul_right _ Finset.card_biUnion_le
    _ = ∑ σ ∈ T, (Comp σ).card * K ^ p := Finset.sum_mul _ _ _
    _ ≤ ∑ _σ ∈ T, K ^ n := Finset.sum_le_sum hcomp
    _ = T.card * K ^ n := by simp
    _ ≤ (ℓ * ℓ) ^ p * K ^ n := Nat.mul_le_mul_right _ hT

end

end SATurday.ProofComplexity
