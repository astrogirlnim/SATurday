import Mathlib

/-!
# Safe sets and closure of linear forms (EGI, ECCC TR23-187 sections 3 and 4)

Forms are finitely supported vectors `ι →₀ K`; each variable `w : ι` lies in a block `b w : β`.
`proj S` kills the variables of the blocks in `S`. A finite set of independent forms is dangerous
when it has more elements than blocks in its support; a subspace is safe if it contains no
dangerous set. The closure `cl W` of a subspace is the least set of blocks `S` such that
`W.map (proj S)` is safe. This file proves existence of the least such set, monotonicity, and the
size bound `|cl W| + dim (W.map (proj (cl W))) ≤ dim W`.

LOG: R4 Closure module (closure of linear forms, EGI section 4)
-/

namespace SATurday.ProofComplexity

namespace Closure

noncomputable section

open Module Finset

variable {K ι β : Type*} [Field K] [DecidableEq β] (b : ι → β)

/-- Restriction killing the variables whose block is in `S`. -/
def proj [DecidableEq ι] (S : Finset β) : (ι →₀ K) →ₗ[K] (ι →₀ K) where
  toFun f := f.filter (fun w => b w ∉ S)
  map_add' f g := Finsupp.filter_add
  map_smul' c f := by
    ext w
    by_cases h : b w ∈ S <;> simp [Finsupp.filter_apply, h]

variable [DecidableEq ι]

theorem proj_apply (S : Finset β) (f : ι →₀ K) (w : ι) :
    proj b S f w = if b w ∈ S then 0 else f w := by
  simp [proj, Finsupp.filter_apply]

/-- Blocks in the support of a form. -/
def supp (f : ι →₀ K) : Finset β := f.support.image b

/-- Blocks in the support of a finite set of forms. -/
def suppF (H : Finset (ι →₀ K)) : Finset β := H.biUnion (supp b)

theorem mem_supp {f : ι →₀ K} {c : β} : c ∈ supp b f ↔ ∃ w, f w ≠ 0 ∧ b w = c := by
  simp [supp]

theorem proj_proj (S T : Finset β) (f : ι →₀ K) : proj b S (proj b T f) = proj b (S ∪ T) f := by
  ext w; simp only [proj_apply, mem_union]; by_cases h : b w ∈ S <;> by_cases h' : b w ∈ T <;> simp [h, h']

theorem proj_proj_of_subset {S T : Finset β} (h : S ⊆ T) (f : ι →₀ K) :
    proj b T (proj b S f) = proj b T f := by
  rw [proj_proj, union_eq_left.2 h]

theorem supp_proj_subset (S : Finset β) (f : ι →₀ K) : supp b (proj b S f) ⊆ supp b f \ S := by
  intro c hc
  obtain ⟨w, hw, rfl⟩ := (mem_supp b).1 hc
  rw [proj_apply] at hw
  by_cases h : b w ∈ S
  · simp [h] at hw
  · exact mem_sdiff.2 ⟨(mem_supp b).2 ⟨w, by simpa [h] using hw, rfl⟩, h⟩

theorem proj_eq_zero_iff (T : Finset β) (f : ι →₀ K) : proj b T f = 0 ↔ supp b f ⊆ T := by
  constructor
  · intro h c hc
    obtain ⟨w, hw, rfl⟩ := (mem_supp b).1 hc
    by_contra hn
    have := congrArg (fun g => g w) h
    simp [proj_apply, hn] at this
    exact hw this
  · intro h
    ext w
    rw [proj_apply]
    by_cases hw : b w ∈ T
    · simp [hw]
    · by_contra hne
      have : b w ∈ supp b f := (mem_supp b).2 ⟨w, by simpa [hw] using hne, rfl⟩
      exact hw (h this)

/-- Forms supported in `T`. -/
def U (T : Finset β) : Submodule K (ι →₀ K) := LinearMap.ker (proj b T)

theorem mem_U {T : Finset β} {f : ι →₀ K} : f ∈ U (K := K) b T ↔ supp b f ⊆ T := by
  simp [U, proj_eq_zero_iff]

/-- Dimension formula (EGI Lemma 4.2). -/
theorem finrank_eq_map_add (W : Submodule K (ι →₀ K)) [FiniteDimensional K W] (T : Finset β) :
    finrank K W = finrank K (W.map (proj b T)) + finrank K ↥(W ⊓ U b T) := by
  have h := LinearMap.finrank_range_add_finrank_ker ((proj b T).domRestrict W)
  rw [LinearMap.range_domRestrict] at h
  have hk : finrank K ↥(LinearMap.ker ((proj b T).domRestrict W)) = finrank K ↥(W ⊓ U b T) := by
    rw [LinearMap.ker_domRestrict]
    have e : Submodule.comap W.subtype (LinearMap.ker (proj b T)) = Submodule.comap W.subtype (W ⊓ U b T) := by
      ext x; simp [U, x.2]
    rw [e]
    exact (Submodule.comapSubtypeEquivOfLe (inf_le_left : W ⊓ U b T ≤ W)).finrank_eq
  omega

/-! ## Dangerous sets and safety -/

/-- A finite independent set of forms with more elements than blocks in its support. -/
def Dang (H : Finset (ι →₀ K)) : Prop :=
  LinearIndepOn K id (H : Set (ι →₀ K)) ∧ (suppF b H).card < H.card

/-- A subspace is safe if it contains no dangerous set. -/
def Safe (W : Submodule K (ι →₀ K)) : Prop :=
  ∀ H : Finset (ι →₀ K), (H : Set (ι →₀ K)) ⊆ W → ¬ Dang b H

theorem Safe.mono {W W' : Submodule K (ι →₀ K)} (h : Safe b W) (hle : W' ≤ W) : Safe b W' :=
  fun H hH => h H (hH.trans hle)

theorem supp_le_of_mem_U {T : Finset β} {f : ι →₀ K} (h : f ∈ U (K := K) b T) :
    supp b f ⊆ T := (mem_U b).1 h

theorem subset_suppF {H : Finset (ι →₀ K)} {f : ι →₀ K} (hf : f ∈ H) : supp b f ⊆ suppF b H :=
  subset_biUnion_of_mem (supp b) hf

theorem span_le_U (H : Finset (ι →₀ K)) :
    Submodule.span K (H : Set (ι →₀ K)) ≤ U b (suppF b H) := by
  apply Submodule.span_le.2
  intro f hf
  exact (mem_U b).2 (subset_suppF b hf)

/-- A subspace of forms supported in `S` of dimension more than `|S|` contains a dangerous set. -/
theorem exists_dang (W' : Submodule K (ι →₀ K)) [FiniteDimensional K W'] (S : Finset β)
    (hW : W' ≤ U b S) (h : S.card < finrank K W') :
    ∃ H : Finset (ι →₀ K), (H : Set (ι →₀ K)) ⊆ W' ∧ Dang b H := by
  classical
  let bs := Module.finBasis K W'
  let v : Fin (finrank K W') → (ι →₀ K) := fun i => (bs i : ι →₀ K)
  have hv : LinearIndependent K v := bs.linearIndependent.map' W'.subtype (Submodule.ker_subtype _)
  have hinj : Function.Injective v := hv.injective
  refine ⟨Finset.univ.image v, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨i, _, rfl⟩ := mem_image.1 (mem_coe.1 hf)
    exact (bs i).2
  · have : ((Finset.univ.image v : Finset _) : Set (ι →₀ K)) = Set.range v := by
      ext x; simp
    rw [this]
    exact hv.linearIndepOn_id
  · rw [card_image_of_injective _ hinj]
    simp only [card_univ, Fintype.card_fin]
    refine lt_of_le_of_lt (card_le_card ?_) h
    intro c hc
    obtain ⟨f, hf, hcf⟩ := mem_biUnion.1 hc
    obtain ⟨i, _, rfl⟩ := mem_image.1 hf
    exact supp_le_of_mem_U b (hW (bs i).2) hcf

/-- Minimally dangerous sets inside `W'` (minimal support size). -/
def MinDang (W' : Submodule K (ι →₀ K)) (H : Finset (ι →₀ K)) : Prop :=
  (H : Set (ι →₀ K)) ⊆ W' ∧ Dang b H ∧
    ∀ H' : Finset (ι →₀ K), (H' : Set (ι →₀ K)) ⊆ W' → Dang b H' → (suppF b H).card ≤ (suppF b H').card

theorem exists_minDang {W' : Submodule K (ι →₀ K)} (h : ¬ Safe b W') : ∃ H, MinDang b W' H := by
  classical
  unfold Safe at h
  push Not at h
  have hex : ∃ n, ∃ H : Finset (ι →₀ K), (H : Set (ι →₀ K)) ⊆ W' ∧ Dang b H ∧ (suppF b H).card = n := by
    obtain ⟨H, h1, h2⟩ := h
    exact ⟨_, H, h1, h2, rfl⟩
  obtain ⟨H, h1, h2, h3⟩ := Nat.find_spec hex
  refine ⟨H, h1, h2, fun H' h1' h2' => ?_⟩
  rw [h3]
  exact Nat.find_min' hex ⟨H', h1', h2', rfl⟩

/-- EGI Lemma 4.3: restricting a minimally dangerous set along a proper subset of its support
leaves a non safe space. -/
theorem not_safe_restrict {W' : Submodule K (ι →₀ K)} {H : Finset (ι →₀ K)} (hm : MinDang b W' H)
    {S : Finset β} (hS : S ⊆ suppF b H) (hne : S ≠ suppF b H) :
    ¬ Safe b ((Submodule.span K (H : Set (ι →₀ K))).map (proj b S)) := by
  classical
  obtain ⟨hHW, ⟨hli, hlt⟩, hmin⟩ := hm
  set Wh := Submodule.span K (H : Set (ι →₀ K)) with hWh
  have hrk : finrank K Wh = H.card := finrank_span_finset_eq_card hli
  have hWhW : Wh ≤ W' := Submodule.span_le.2 hHW
  have hdim : finrank K ↥(Wh ⊓ U b S) ≤ S.card := by
    by_contra hc
    push Not at hc
    obtain ⟨H', hH'1, hH'2⟩ := exists_dang b (Wh ⊓ U b S) S inf_le_right hc
    have := hmin H' (fun f hf => hWhW (hH'1 hf).1) hH'2
    have hsub : suppF b H' ⊆ S := by
      intro c hc'
      obtain ⟨f, hf, hcf⟩ := mem_biUnion.1 hc'
      exact supp_le_of_mem_U b (hH'1 hf).2 hcf
    have h1 := card_le_card hsub
    have h2 : S.card < (suppF b H).card := card_lt_card ⟨hS, fun h => hne (Subset.antisymm hS h)⟩
    omega
  have hfr := finrank_eq_map_add b Wh S
  have hcard : (suppF b H \ S).card = (suppF b H).card - S.card := card_sdiff_of_subset hS
  intro hsafe
  have hSc : S.card ≤ (suppF b H).card := card_le_card hS
  have hbig : (suppF b H \ S).card < finrank K ↥(Wh.map (proj b S)) := by
    generalize finrank K ↥(Wh.map (proj b S)) = a at *
    generalize finrank K ↥(Wh ⊓ U b S) = c at *
    generalize finrank K Wh = d at *
    omega
  have hle : Wh.map (proj b S) ≤ U b (suppF b H \ S) := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hg
    rw [mem_U]
    intro c hc
    have h1 := supp_proj_subset b S f hc
    have h2 : supp b f ⊆ suppF b H := (mem_U b).1 (span_le_U b H hf)
    exact mem_sdiff.2 ⟨h2 (mem_sdiff.1 h1).1, (mem_sdiff.1 h1).2⟩
  obtain ⟨H'', h1, h2⟩ := exists_dang b _ _ hle hbig
  exact hsafe H'' h1 h2

/-! ## The closure -/

theorem proj_inter {S T : Finset β} {f : ι →₀ K} (h : supp b f ⊆ T) :
    proj b (S ∩ T) f = proj b S f := by
  ext w
  rw [proj_apply, proj_apply]
  by_cases hw : f w = 0
  · simp [hw]
  · have : b w ∈ T := h ((mem_supp b).2 ⟨w, hw, rfl⟩)
    simp [this]

/-- Block sets reached by Algorithm 4.1 of EGI. -/
inductive Reach (W : Submodule K (ι →₀ K)) : Finset β → Prop
  | zero : Reach W ∅
  | step {S : Finset β} {H : Finset (ι →₀ K)} :
      Reach W S → MinDang b (W.map (proj b S)) H → Reach W (suppF b H ∪ S)

/-- Every reached set lies inside every set that makes the restriction safe. -/
theorem reach_le {W : Submodule K (ι →₀ K)} {S : Finset β} (hR : Reach b W S)
    {S' : Finset β} (hS' : Safe b (W.map (proj b S'))) : S ⊆ S' := by
  induction hR with
  | zero => exact empty_subset _
  | @step S H hR hm ih =>
    refine union_subset ?_ ih
    by_contra hnot
    have hS0 : S' ∩ suppF b H ⊆ suppF b H := inter_subset_right
    have hne : S' ∩ suppF b H ≠ suppF b H := fun h =>
      hnot (fun c hc => by rw [← h] at hc; exact (mem_inter.1 hc).1)
    apply not_safe_restrict b hm hS0 hne
    have key : (Submodule.span K (H : Set (ι →₀ K))).map (proj b (S' ∩ suppF b H)) ≤
        W.map (proj b S') := by
      intro g hg
      obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hg
      have hfW : f ∈ W.map (proj b S) :=
        (Submodule.span_le.2 hm.1 : Submodule.span K (H : Set (ι →₀ K)) ≤ _) hf
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hfW
      have hsupp : supp b (proj b S w) ⊆ suppF b H := (mem_U b).1 (span_le_U b H hf)
      refine Submodule.mem_map.2 ⟨w, hw, ?_⟩
      rw [proj_inter b hsupp, proj_proj_of_subset b ih]
    exact Safe.mono b hS' key

theorem reach_step_lt {W : Submodule K (ι →₀ K)} [FiniteDimensional K W] {S : Finset β}
    {H : Finset (ι →₀ K)} (hm : MinDang b (W.map (proj b S)) H) :
    (suppF b H ∪ S).card + finrank K ↥(W.map (proj b (suppF b H ∪ S))) <
      S.card + finrank K ↥(W.map (proj b S)) := by
  classical
  obtain ⟨hHW, ⟨hli, hlt⟩, _⟩ := hm.1, hm.2.1, hm.2.2
  set T := suppF b H with hT
  have hdisj : Disjoint T S := by
    rw [Finset.disjoint_left]
    intro c hcT hcS
    obtain ⟨f, hf, hcf⟩ := mem_biUnion.1 hcT
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 (hHW hf)
    exact (mem_sdiff.1 (supp_proj_subset b S w hcf)).2 hcS
  have hcu : (T ∪ S).card = T.card + S.card := card_union_of_disjoint hdisj
  set WS := W.map (proj b S) with hWS
  have hfr := finrank_eq_map_add b WS T
  have hmap : WS.map (proj b T) = W.map (proj b (T ∪ S)) := by
    rw [hWS, ← Submodule.map_comp]
    have : (proj (K := K) b T).comp (proj (K := K) b S) = proj (K := K) b (T ∪ S) := by
      exact LinearMap.ext fun f => proj_proj b T S f
    rw [this]
  have hlow : H.card ≤ finrank K ↥(WS ⊓ U b T) := by
    have hle : Submodule.span K (H : Set (ι →₀ K)) ≤ WS ⊓ U b T :=
      le_inf (Submodule.span_le.2 hHW) (span_le_U b H)
    rw [← finrank_span_finset_eq_card hli]
    exact Submodule.finrank_mono hle
  rw [hmap] at hfr
  clear_value WS T
  generalize finrank K ↥(W.map (proj b (T ∪ S))) = a at *
  generalize finrank K ↥(WS ⊓ U b T) = c at *
  generalize finrank K WS = d at *
  omega

theorem reach_size {W : Submodule K (ι →₀ K)} [FiniteDimensional K W] {S : Finset β}
    (hR : Reach b W S) : S.card + finrank K ↥(W.map (proj b S)) ≤ finrank K W := by
  induction hR with
  | zero =>
    have h0 : W.map (proj (K := K) b ∅) = W := by
      have : proj (K := K) b (∅ : Finset β) = LinearMap.id := by ext f : 1; ext w; simp [proj_apply]
      rw [this]; exact Submodule.map_id W
    rw [h0]; simp
  | step hR hm ih =>
    exact (reach_step_lt b hm).le.trans ih

theorem exists_reach_safe (W : Submodule K (ι →₀ K)) [FiniteDimensional K W] :
    ∀ n : ℕ, ∀ S : Finset β, Reach b W S → S.card + finrank K ↥(W.map (proj b S)) ≤ n →
      ∃ S', Reach b W S' ∧ Safe b (W.map (proj b S')) := by
  intro n
  induction n with
  | zero =>
    intro S hR hn
    by_cases hs : Safe b (W.map (proj b S))
    · exact ⟨S, hR, hs⟩
    · obtain ⟨H, hm⟩ := exists_minDang b hs
      have := reach_step_lt b (W := W) hm
      omega
  | succ n ih =>
    intro S hR hn
    by_cases hs : Safe b (W.map (proj b S))
    · exact ⟨S, hR, hs⟩
    · obtain ⟨H, hm⟩ := exists_minDang b hs
      have := reach_step_lt b (W := W) hm
      exact ih _ (Reach.step hR hm) (by omega)

/-- **Closure** (EGI Lemmas 4.4, 4.7): there is a least set of blocks whose removal makes the
restricted space safe, and it satisfies the size bound. -/
theorem exists_closure (W : Submodule K (ι →₀ K)) [FiniteDimensional K W] :
    ∃ S : Finset β, Safe b (W.map (proj b S)) ∧ (∀ S', Safe b (W.map (proj b S')) → S ⊆ S') ∧
      S.card + finrank K ↥(W.map (proj b S)) ≤ finrank K W := by
  obtain ⟨S, hR, hs⟩ := exists_reach_safe b W _ ∅ Reach.zero le_rfl
  exact ⟨S, hs, fun S' h => reach_le b hR h, reach_size b hR⟩

/-- The closure of a subspace of forms. -/
def cl (W : Submodule K (ι →₀ K)) [FiniteDimensional K W] : Finset β :=
  Classical.choose (exists_closure b W)

theorem cl_safe (W : Submodule K (ι →₀ K)) [FiniteDimensional K W] :
    Safe b (W.map (proj b (cl b W))) := (Classical.choose_spec (exists_closure b W)).1

theorem cl_min (W : Submodule K (ι →₀ K)) [FiniteDimensional K W] {S' : Finset β}
    (h : Safe b (W.map (proj b S'))) : cl b W ⊆ S' :=
  (Classical.choose_spec (exists_closure b W)).2.1 S' h

theorem cl_size (W : Submodule K (ι →₀ K)) [FiniteDimensional K W] :
    (cl b W).card + finrank K ↥(W.map (proj b (cl b W))) ≤ finrank K W :=
  (Classical.choose_spec (exists_closure b W)).2.2

theorem cl_card_le (W : Submodule K (ι →₀ K)) [FiniteDimensional K W] :
    (cl b W).card ≤ finrank K W := by
  have := cl_size b W; omega

/-- Monotonicity of the closure. -/
theorem cl_mono {W W' : Submodule K (ι →₀ K)} [FiniteDimensional K W] [FiniteDimensional K W']
    (h : W ≤ W') : cl b W ⊆ cl b W' := by
  have h1 : W.map (proj b (cl b W')) ≤ W'.map (proj b (cl b W')) := Submodule.map_mono h
  exact cl_min b W (Safe.mono b (cl_safe b W') h1)

end

end Closure

end SATurday.ProofComplexity
