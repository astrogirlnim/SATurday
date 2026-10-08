import Theory.ProofComplexity.KEvalBuild
import Theory.ProofComplexity.PHPKEval

/-!
# Bounded depth Frege lower bound for PHP (Ladder Rung R4, 1B.5)

Mod free depth `d` refutations (in the AC0[p] Frege sequent calculus of `AC0pFrege.lean`) of
the pigeonhole CNF `phpCNF n` need super polynomial size (`php_bdfrege_superpoly`).

Proof: from a small refutation build, level by level, random matching restrictions and
`k`-evaluations of all subformulas of all line formulas (PHP switching lemma plus a union
bound, `exists_shallow_ext`, `levels`), ending with enough free holes; `keval_no_refutation`
then forbids the empty sequent.

LOG: R4 PHPFrege module (bounded depth Frege PHP lower bound)
-/

namespace SATurday.ProofComplexity

open Finset

noncomputable section

open Classical

/-! ## Extensions of restrictions -/

theorem exists_ext {P H : Finset ℕ} (hPH : H.card ≤ P.card) {ρ0 : Mt} (hρ0 : IsMatch ρ0)
    (hU0 : InU P H ρ0) {m : ℕ} (hm1 : ρ0.card ≤ m) (hm2 : m ≤ H.card) :
    ∃ ρ ∈ Rm P H ρ0 m, True := by
  have hfH := fH_card hρ0 (hols_sub hU0)
  have hfP := fP_card hρ0 (pigs_sub hU0)
  obtain ⟨A, hA, hAc⟩ := exists_subset_card_eq (s := fH H ρ0) (n := m - ρ0.card) (by omega)
  obtain ⟨f, hf, hfi⟩ := exists_inj (fP P ρ0) A (by omega)
  set N : Mt := A.image fun j => (f j, j)
  have hNf : N ⊆ freeE P H ρ0 := by
    intro e he; obtain ⟨j, hj, rfl⟩ := mem_image.1 he
    exact mem_freeE.2 ⟨mem_sdiff.1 (hf j hj), mem_sdiff.1 (hA hj)⟩
  have hNm : IsMatch N := by
    intro e he e' he' h
    obtain ⟨j, hj, rfl⟩ := mem_image.1 he; obtain ⟨j', hj', rfl⟩ := mem_image.1 he'
    rcases h with h | h
    · simp only at h; rw [hfi hj hj' h]
    · simp only at h; rw [h]
  have hNc : N.card = m - ρ0.card := by
    rw [card_image_of_injOn fun j _ j' _ h => by simpa using congrArg Prod.snd h, hAc]
  have hdisj : Disjoint ρ0 N := disjoint_left.2 fun e he he' =>
    (disj_free hNf e he' e he).1 rfl
  refine ⟨ρ0 ∪ N, ?_, trivial⟩
  simp only [Rm, mem_filter, mem_powerset]
  refine ⟨union_subset hU0 (hNf.trans freeE_sub), ?_, subset_union_left, ?_⟩
  · have := compat_free hρ0 hNm hNf; unfold Compat at this; rwa [union_comm]
  · rw [card_union_of_disjoint hdisj, hNc]; omega

theorem bad_card {P H : Finset ℕ} {ρ0 : Mt} {m s w C : ℕ} (Ds : List MDNF)
    (hDs : ∀ D ∈ Ds, (∀ t ∈ D, InU P H t) ∧ ∀ t ∈ D, t.card ≤ w)
    (hC1 : w + (P.card - (m + (s + 1))) ≤ C) (hC2 : w + (H.card - (m + (s + 1))) ≤ C) :
    ((Rm P H ρ0 m).filter fun ρ => ∃ D ∈ Ds, s + 1 ≤ mdepth P H D ρ).card *
        (m + 1 - ρ0.card) ^ (s + 1) ≤
      Ds.length * ((Rm P H ρ0 m).card *
        ((P.card - m) * (H.card - m) * (2 * (w * (C * C)))) ^ (s + 1)) := by
  induction Ds with
  | nil => simp
  | cons D Ds ih =>
    have hD := hDs D (by simp)
    have h1 := mswitching_ratio hD.1 hD.2 ρ0 m (s + 1) C hC1 hC2
    have h2 := ih fun D' hD' => hDs D' (by simp [hD'])
    have hsub : ((Rm P H ρ0 m).filter fun ρ => ∃ D' ∈ D :: Ds, s + 1 ≤ mdepth P H D' ρ) ⊆
        ((Rm P H ρ0 m).filter fun ρ => s + 1 ≤ mdepth P H D ρ) ∪
          ((Rm P H ρ0 m).filter fun ρ => ∃ D' ∈ Ds, s + 1 ≤ mdepth P H D' ρ) := by
      intro ρ hρ
      simp only [mem_filter, mem_union, List.mem_cons] at hρ ⊢
      obtain ⟨hρ, D', hD', hd⟩ := hρ
      rcases hD' with rfl | hD'
      · exact Or.inl ⟨hρ, hd⟩
      · exact Or.inr ⟨hρ, D', hD', hd⟩
    calc _ ≤ (((Rm P H ρ0 m).filter fun ρ => s + 1 ≤ mdepth P H D ρ).card +
            ((Rm P H ρ0 m).filter fun ρ => ∃ D' ∈ Ds, s + 1 ≤ mdepth P H D' ρ).card) *
            (m + 1 - ρ0.card) ^ (s + 1) :=
          Nat.mul_le_mul_right _ ((card_le_card hsub).trans (card_union_le _ _))
      _ = _ := by rw [add_mul]
      _ ≤ _ := Nat.add_le_add h1 h2
      _ = _ := by simp only [List.length_cons]; ring

/-- **Union bound**: some extension makes every DNF in the list shallow. -/
theorem exists_shallow_ext {P H : Finset ℕ} (hPH : H.card ≤ P.card) {ρ0 : Mt}
    (hρ0 : IsMatch ρ0) (hU0 : InU P H ρ0) {m s w C : ℕ} (Ds : List MDNF)
    (hDs : ∀ D ∈ Ds, (∀ t ∈ D, InU P H t) ∧ ∀ t ∈ D, t.card ≤ w)
    (hm1 : ρ0.card ≤ m) (hm2 : m ≤ H.card)
    (hC1 : w + (P.card - (m + (s + 1))) ≤ C) (hC2 : w + (H.card - (m + (s + 1))) ≤ C)
    (hineq : Ds.length * ((P.card - m) * (H.card - m) * (2 * (w * (C * C)))) ^ (s + 1) <
      (m + 1 - ρ0.card) ^ (s + 1)) :
    ∃ ρ ∈ Rm P H ρ0 m, ∀ D ∈ Ds, mdepth P H D ρ ≤ s := by
  obtain ⟨ρ1, hρ1, -⟩ := exists_ext hPH hρ0 hU0 hm1 hm2
  have hpos : 0 < (Rm P H ρ0 m).card := card_pos.2 ⟨ρ1, hρ1⟩
  have hb := bad_card (ρ0 := ρ0) (m := m) Ds hDs hC1 hC2
  set B := (Rm P H ρ0 m).filter fun ρ => ∃ D ∈ Ds, s + 1 ≤ mdepth P H D ρ
  have hlt : B.card < (Rm P H ρ0 m).card := by
    by_contra hge
    push Not at hge
    have : (Rm P H ρ0 m).card * (m + 1 - ρ0.card) ^ (s + 1) ≤
        (Rm P H ρ0 m).card * (Ds.length *
          ((P.card - m) * (H.card - m) * (2 * (w * (C * C)))) ^ (s + 1)) :=
      calc _ ≤ B.card * (m + 1 - ρ0.card) ^ (s + 1) := Nat.mul_le_mul_right _ hge
        _ ≤ _ := hb
        _ = _ := by ring
    have := Nat.le_of_mul_le_mul_left this hpos
    omega
  obtain ⟨ρ, hρ, hρB⟩ := exists_mem_notMem_of_card_lt_card hlt
  refine ⟨ρ, hρ, fun D hD => ?_⟩
  by_contra h
  exact hρB (mem_filter.2 ⟨hρ, D, hD, by omega⟩)

/-! ## Iterating the levels -/

/-- Disjuncts of an `OR` of depth `t + 1`. -/
def orArgsAt (t : ℕ) : Fm → List Fm
  | .or l => if (Fm.or l).depth = t + 1 then l else []
  | _ => []

/-- Conjuncts of an `AND` of depth `t + 1`. -/
def andArgsAt (t : ℕ) : Fm → List Fm
  | .and l => if (Fm.and l).depth = t + 1 then l else []
  | _ => []

theorem mem_orArgsAt {t : ℕ} {φ ψ : Fm} (h : ψ ∈ orArgsAt t φ) :
    ∃ l, φ = .or l ∧ (Fm.or l).depth = t + 1 ∧ ψ ∈ l := by
  cases φ with
  | or l =>
    simp only [orArgsAt] at h
    split_ifs at h with hd
    · exact ⟨l, rfl, hd, h⟩
    · simp at h
  | _ => simp [orArgsAt] at h

theorem mem_andArgsAt {t : ℕ} {φ ψ : Fm} (h : ψ ∈ andArgsAt t φ) :
    ∃ l, φ = .and l ∧ (Fm.and l).depth = t + 1 ∧ ψ ∈ l := by
  cases φ with
  | and l =>
    simp only [andArgsAt] at h
    split_ifs at h with hd
    · exact ⟨l, rfl, hd, h⟩
    · simp at h
  | _ => simp [andArgsAt] at h

/-- **Levels**: under the counting inequalities, for every level `t ≤ T` there are a matching
restriction leaving `ℓ t` free holes and a `k`-evaluation of the formulas of depth `≤ t`. -/
theorem levels {Φ : List Fm} {vx : ℕ → ℕ × ℕ}
    (hcl : ∀ φ ∈ Φ, (∀ ψ, φ = .neg ψ → ψ ∈ Φ) ∧ (∀ l, φ = .or l → ∀ ψ ∈ l, ψ ∈ Φ) ∧
      (∀ l, φ = .and l → ∀ ψ ∈ l, ψ ∈ Φ))
    (hmod : ∀ φ ∈ Φ, isMod φ = false) {n k s T : ℕ} (ℓ : ℕ → ℕ) (hℓ0 : ℓ 0 = n)
    (hℓ : ∀ t < T, ℓ (t + 1) ≤ ℓ t) (hℓn : ∀ t ≤ T, ℓ t ≤ n) (hk : 1 ≤ k) (h2s : 2 * s ≤ k)
    (hineq : ∀ t < T, (2 * Φ.length) * ((ℓ (t + 1) + 1) * ℓ (t + 1) *
      (2 * (k * ((k + ℓ (t + 1) + 1) * (k + ℓ (t + 1) + 1))))) ^ (s + 1) <
        (ℓ t - ℓ (t + 1) + 1) ^ (s + 1)) :
    ∀ t ≤ T, ∃ ρ E, IsMatch ρ ∧ InU (range (n + 1)) (range n) ρ ∧ ρ.card = n - ℓ t ∧
      ∀ φ ∈ Φ, φ.depth ≤ t → Good (range (n + 1)) (range n) vx ρ k E φ := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨∅, E0 (range (n + 1)) (range n) vx, isMatch_empty, empty_subset _,
      by simp [hℓ0], fun φ _ hd => good_E0 hk φ (by omega)⟩
  | succ t ih =>
    intro ht
    obtain ⟨ρ, E, hρ, hρU, hρc, hG⟩ := ih (by omega)
    have hPH : (range n).card ≤ (range (n + 1)).card := by simp
    set Ds : List MDNF := Φ.map (fun φ => Dor E (orArgsAt t φ)) ++
      Φ.map (fun φ => Dand E (andArgsAt t φ)) with hDsdef
    have hDs : ∀ D ∈ Ds, (∀ x ∈ D, InU (range (n + 1)) (range n) x) ∧ ∀ x ∈ D, x.card ≤ k := by
      have key : ∀ ψ ∈ Φ, ψ.depth ≤ t → ∀ x ∈ (E ψ).1 ∪ (E ψ).2,
          InU (range (n + 1)) (range n) x ∧ x.card ≤ k := fun ψ hψ hd x hx =>
        ⟨((hG ψ hψ hd).mem x hx).1.trans freeE_sub, ((hG ψ hψ hd).mem x hx).2.2⟩
      intro D hD
      rcases List.mem_append.1 hD with hD | hD
      · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hD
        have : ∀ x ∈ Dor E (orArgsAt t φ), InU (range (n + 1)) (range n) x ∧ x.card ≤ k := by
          intro x hx
          obtain ⟨ψ, hψ, hxψ⟩ := mem_Dor.1 hx
          obtain ⟨l, rfl, hd, hψl⟩ := mem_orArgsAt hψ
          exact key ψ ((hcl _ hφ).2.1 l rfl ψ hψl) (by have := depth_child_or hψl; omega) x
            (mem_union.2 (Or.inl hxψ))
        exact ⟨fun x hx => (this x hx).1, fun x hx => (this x hx).2⟩
      · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hD
        have : ∀ x ∈ Dand E (andArgsAt t φ), InU (range (n + 1)) (range n) x ∧ x.card ≤ k := by
          intro x hx
          obtain ⟨ψ, hψ, hxψ⟩ := mem_Dand.1 hx
          obtain ⟨l, rfl, hd, hψl⟩ := mem_andArgsAt hψ
          exact key ψ ((hcl _ hφ).2.2 l rfl ψ hψl) (by have := depth_child_and hψl; omega) x
            (mem_union.2 (Or.inr hxψ))
        exact ⟨fun x hx => (this x hx).1, fun x hx => (this x hx).2⟩
    have hlen : Ds.length = 2 * Φ.length := by simp [hDsdef]; ring
    have hℓt := hℓ t (by omega)
    have hℓn1 := hℓn (t + 1) ht
    have hℓn0 := hℓn t (by omega)
    obtain ⟨ρ', hρ', hsh⟩ := exists_shallow_ext (C := k + ℓ (t + 1) + 1) (s := s) hPH hρ hρU Ds
      hDs (m := n - ℓ (t + 1)) (by omega) (by simp)
      (by simp; omega) (by simp; omega) (by
        rw [hlen, card_range, card_range, hρc,
          show n + 1 - (n - ℓ (t + 1)) = ℓ (t + 1) + 1 by omega,
          show n - (n - ℓ (t + 1)) = ℓ (t + 1) by omega,
          show n - ℓ (t + 1) + 1 - (n - ℓ t) = ℓ t - ℓ (t + 1) + 1 by omega]
        exact hineq t (by omega))
    simp only [Rm, mem_filter, mem_powerset] at hρ'
    obtain ⟨hU', hm', hsub, hc'⟩ := hρ'
    refine ⟨ρ', nextE (range (n + 1)) (range n) ρ' k t E, hm', hU', hc', ?_⟩
    refine level_step hcl hmod hG hρ hsub hm' hU' hPH h2s (fun l hφ hd => ?_) (fun l hφ hd => ?_)
    · refine hsh _ (List.mem_append_left _ (List.mem_map.2 ⟨.or l, hφ, ?_⟩))
      simp [orArgsAt, hd]
    · refine hsh _ (List.mem_append_right _ (List.mem_map.2 ⟨.and l, hφ, ?_⟩))
      simp [andArgsAt, hd]

/-! ## The formulas of a proof -/

theorem size_pos (φ : Fm) : 1 ≤ φ.size := by
  cases φ <;> simp [Fm.size]

theorem size_or (l : List Fm) : (Fm.or l).size = (l.map Fm.size).sum + 1 := by
  rw [Fm.size]; have := Fm.attach_map l Fm.size; simp only at this; rw [this]

theorem size_and (l : List Fm) : (Fm.and l).size = (l.map Fm.size).sum + 1 := by
  rw [Fm.size]; have := Fm.attach_map l Fm.size; simp only at this; rw [this]

theorem size_mod (r : ℕ) (l : List Fm) : (Fm.mod r l).size = (l.map Fm.size).sum + 1 := by
  rw [Fm.size]; have := Fm.attach_map l Fm.size; simp only at this; rw [this]

theorem flatten_length_le {l : List Fm} (f : Fm → List Fm) (h : ∀ ψ ∈ l, (f ψ).length ≤ ψ.size) :
    ((l.map f).flatten).length ≤ (l.map Fm.size).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.sum_cons]
    have := h a (by simp)
    have := ih fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)
    omega

theorem subs_length : ∀ φ : Fm, (subs φ).length ≤ φ.size
  | .var i => by simp [subs, Fm.size]
  | .neg ψ => by
      have := subs_length ψ; simp only [subs, List.length_cons, Fm.size]; omega
  | .and l => by
      rw [subs_and, size_and, List.length_cons]
      have := flatten_length_le (l := l) subs fun ψ hψ => by
        have : sizeOf ψ < sizeOf (Fm.and l) := by
          have := List.sizeOf_lt_of_mem hψ; simp only [Fm.and.sizeOf_spec]; omega
        exact subs_length ψ
      omega
  | .or l => by
      rw [subs_or, size_or, List.length_cons]
      have := flatten_length_le (l := l) subs fun ψ hψ => by
        have : sizeOf ψ < sizeOf (Fm.or l) := by
          have := List.sizeOf_lt_of_mem hψ; simp only [Fm.or.sizeOf_spec]; omega
        exact subs_length ψ
      omega
  | .mod r l => by
      rw [subs_mod, size_mod, List.length_cons]
      have := flatten_length_le (l := l) subs fun ψ hψ => by
        have : sizeOf ψ < sizeOf (Fm.mod r l) := by
          have := List.sizeOf_lt_of_mem hψ; simp only [Fm.mod.sizeOf_spec]; omega
        exact subs_length ψ
      omega

/-- Total size of the formulas of a sequent. -/
def seqSize (S : Seq) : ℕ := ((S.1 ++ S.2).map Fm.size).sum

theorem size_lineF_le (S : Seq) : (lineF S).size ≤ 2 * seqSize S + 1 := by
  rw [lineF, size_or, dsOf, seqSize, List.map_append, List.map_append, List.sum_append,
    List.sum_append, List.map_map]
  have h1 : (S.1.map (Fm.size ∘ Fm.neg)).sum = (S.1.map Fm.size).sum + S.1.length := by
    induction S.1 with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, Function.comp, Fm.size,
        List.length_cons] at ih ⊢; omega
  have h2 : S.1.length ≤ (S.1.map Fm.size).sum := by
    induction S.1 with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; have := size_pos a; omega
  omega

theorem seqSize_pos {S : Seq} (h : S ≠ ([], [])) : 1 ≤ seqSize S := by
  obtain ⟨Γ, Δ⟩ := S
  unfold seqSize
  by_cases hΓ : Γ = []
  · subst hΓ
    cases Δ with
    | nil => exact absurd rfl h
    | cons a l => simp only [List.nil_append, List.map_cons, List.sum_cons]; have := size_pos a; omega
  · obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hΓ
    simp only [List.cons_append, List.map_cons, List.sum_cons]; have := size_pos a; omega

/-- The subformulas of all line formulas of a proof. -/
def phiOf (L : List Seq) : List Fm :=
  ((L.filter fun S => S ≠ ([], [])).flatMap fun S => subs (lineF S)) ++ [Fm.or []]

theorem lineF_empty : lineF ([], []) = Fm.or [] := rfl

theorem subs_or_nil : subs (Fm.or []) = [Fm.or []] := by rw [subs_or]; simp

theorem mem_phiOf {L : List Seq} {S : Seq} (hS : S ∈ L) {φ : Fm} (hφ : φ ∈ subs (lineF S)) :
    φ ∈ phiOf L := by
  by_cases h : S = ([], [])
  · subst h; rw [lineF_empty, subs_or_nil] at hφ
    simp only [List.mem_singleton] at hφ; subst hφ
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · exact List.mem_append_left _ (List.mem_flatMap.2 ⟨S, List.mem_filter.2 ⟨hS, by simpa using h⟩, hφ⟩)

theorem phiOf_cases {L : List Seq} {φ : Fm} (h : φ ∈ phiOf L) :
    φ = Fm.or [] ∨ ∃ S ∈ L, φ ∈ subs (lineF S) := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨S, hS, hφ⟩ := List.mem_flatMap.1 h
    exact Or.inr ⟨S, (List.mem_filter.1 hS).1, hφ⟩
  · simp at h; exact Or.inl h

theorem phiOf_closed (L : List Seq) : ∀ φ ∈ phiOf L, (∀ ψ, φ = .neg ψ → ψ ∈ phiOf L) ∧
    (∀ l, φ = .or l → ∀ ψ ∈ l, ψ ∈ phiOf L) ∧ (∀ l, φ = .and l → ∀ ψ ∈ l, ψ ∈ phiOf L) := by
  intro φ hφ
  rcases phiOf_cases hφ with rfl | ⟨S, hS, hφS⟩
  · refine ⟨fun ψ h => by simp at h, fun l h ψ hψ => ?_, fun l h ψ _ => by simp at h⟩
    injection h with h; subst h; simp at hψ
  · refine ⟨fun ψ h => ?_, fun l h ψ hψ => ?_, fun l h ψ hψ => ?_⟩
    · subst h; exact mem_phiOf hS (sub_neg hφS)
    · subst h; exact mem_phiOf hS (sub_or hφS hψ)
    · subst h; exact mem_phiOf hS (sub_and hφS hψ)

theorem phiOf_length (L : List Seq) : (phiOf L).length ≤ 3 * fSize L + 1 := by
  unfold phiOf fSize
  rw [List.length_append, List.length_flatMap, List.length_singleton]
  have key : ∀ L' : List Seq, ((L'.filter fun S => S ≠ ([], [])).map
      fun S => (subs (lineF S)).length).sum ≤ 3 * (L'.map fun S => ((S.1 ++ S.2).map Fm.size).sum).sum := by
    intro L'
    induction L' with
    | nil => simp
    | cons S L' ih =>
      by_cases hS : S = ([], [])
      · subst hS
        rw [List.filter_cons_of_neg (by simp)]
        simp only [List.map_cons, List.sum_cons]
        omega
      · rw [List.filter_cons_of_pos (by simpa using hS)]
        simp only [List.map_cons, List.sum_cons]
        have h1 := subs_length (lineF S)
        have h2 := size_lineF_le S
        have h3 := seqSize_pos hS
        unfold seqSize at h2 h3
        omega
  have := key L
  omega

theorem phiOf_modfree {L : List Seq} (hmf : ModFree L) : ∀ φ ∈ phiOf L, isMod φ = false := by
  intro φ hφ
  rcases phiOf_cases hφ with rfl | ⟨S, hS, hφS⟩
  · rfl
  · rw [lineF, subs_or, List.mem_cons] at hφS
    rcases hφS with rfl | hφS
    · rfl
    · obtain ⟨_, ⟨χ, hχ, rfl⟩, hφχ⟩ :=
        List.mem_flatten.1 hφS |>.imp fun _ => And.imp_left List.mem_map.1
      rcases mem_dsOf.1 hχ with ⟨ψ, hψ, rfl⟩ | hχ
      · rw [subs, List.mem_cons] at hφχ
        rcases hφχ with rfl | hφχ
        · rfl
        · exact hmf S hS ψ (List.mem_append_left _ hψ) φ hφχ
      · exact hmf S hS χ (List.mem_append_right _ hχ) φ hφχ

theorem phiOf_depth {L : List Seq} {d : ℕ} (hd : FDepthLe d L) :
    ∀ φ ∈ phiOf L, φ.depth ≤ d + 1 := by
  intro φ hφ
  rcases phiOf_cases hφ with rfl | ⟨S, hS, hφS⟩
  · rw [depth_or]; simp
  · exact (depth_subs _ hφS).trans (depth_lineF (hd S hS))

/-! ## Parameters -/

theorem arith_step {ℓ k s Q R : ℕ} (hk : 1 ≤ k) (h36 : 36 * k ≤ ℓ) (hR : ℓ ^ 7 ≤ R)
    (hQ : Q < ℓ ^ (s + 1)) :
    Q * ((ℓ + 1) * ℓ * (2 * (k * ((k + ℓ + 1) * (k + ℓ + 1))))) ^ (s + 1) <
      (R - ℓ + 1) ^ (s + 1) := by
  have hX : (ℓ + 1) * ℓ * (2 * (k * ((k + ℓ + 1) * (k + ℓ + 1)))) ≤ ℓ ^ 5 := by
    have h1 : ℓ + 1 ≤ 2 * ℓ := by omega
    have h2 : k + ℓ + 1 ≤ 2 * ℓ := by omega
    calc (ℓ + 1) * ℓ * (2 * (k * ((k + ℓ + 1) * (k + ℓ + 1))))
        ≤ (2 * ℓ) * ℓ * (2 * (k * ((2 * ℓ) * (2 * ℓ)))) := by gcongr
      _ = (16 * k) * ℓ ^ 4 := by ring
      _ ≤ ℓ * ℓ ^ 4 := by gcongr; omega
      _ = ℓ ^ 5 := by ring
  have h6 : ℓ ^ 6 ≤ R - ℓ + 1 := by
    have ha : 1 ≤ ℓ ^ 6 := Nat.one_le_pow _ _ (by omega)
    have : ℓ ^ 6 + ℓ ≤ ℓ ^ 6 * ℓ + 1 := by nlinarith
    rw [show ℓ ^ 7 = ℓ ^ 6 * ℓ by ring] at hR
    omega
  have hpos : 0 < (ℓ ^ 5) ^ (s + 1) := pow_pos (pow_pos (by omega) 5) _
  calc Q * ((ℓ + 1) * ℓ * (2 * (k * ((k + ℓ + 1) * (k + ℓ + 1))))) ^ (s + 1)
      ≤ Q * (ℓ ^ 5) ^ (s + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX _)
    _ < ℓ ^ (s + 1) * (ℓ ^ 5) ^ (s + 1) := Nat.mul_lt_mul_of_pos_right hQ hpos
    _ = (ℓ ^ 6) ^ (s + 1) := by ring
    _ ≤ (R - ℓ + 1) ^ (s + 1) := Nat.pow_le_pow_left h6 _

theorem arith_count {n M E c : ℕ} (hM : 2 < M) (hn : n < (M + 1) ^ E) :
    8 * n ^ c < M ^ (2 * E * c + 3) := by
  have h1 : n ≤ (2 * M) ^ E := by
    have : (M + 1) ^ E ≤ (2 * M) ^ E := Nat.pow_le_pow_left (by omega) _
    omega
  have h2 : n ^ c ≤ (2 * M) ^ (E * c) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left h1 _
  have h3 : 2 ^ (E * c + 3) < M ^ (E * c + 3) := Nat.pow_lt_pow_left (by omega) (by omega)
  calc 8 * n ^ c ≤ 8 * (2 * M) ^ (E * c) := Nat.mul_le_mul_left _ h2
    _ = 2 ^ (E * c + 3) * M ^ (E * c) := by rw [mul_pow, pow_add]; ring
    _ < M ^ (E * c + 3) * M ^ (E * c) :=
        Nat.mul_lt_mul_of_pos_right h3 (by positivity)
    _ = M ^ (2 * E * c + 3) := by rw [← pow_add]; congr 1; ring

/-! ## The lower bound -/

/-- **Bounded depth Frege lower bound for PHP** (1B.5). For every depth `d` and exponent `c`,
for all large `n`, every mod free depth `d` refutation of `phpCNF n` in the AC0[p] Frege sequent
calculus has size larger than `n ^ c`. -/
theorem php_bdfrege_superpoly (p d c : ℕ) :
    ∃ N, ∀ n ≥ N, ∀ L, FRefutes p d (phpCNF n) L → ModFree L → n ^ c < fSize L := by
  set T := d + 1 with hT
  set E := 7 ^ T with hEdef
  set s := 2 * E * c + 2 with hs
  set k := 2 * s with hkdef
  refine ⟨(36 * k + 2) ^ E, fun n hn L hR hmf => ?_⟩
  by_contra hsz
  push Not at hsz
  have hE1 : 1 ≤ E := Nat.one_le_pow _ _ (by norm_num)
  have hk : 1 ≤ k := by omega
  have hbig : 36 * k + 2 ≤ n := le_trans (Nat.le_self_pow (by omega) _) hn
  set M := Nat.findGreatest (fun M => M ^ E ≤ n) n with hMdef
  have hM1 : M ^ E ≤ n := Nat.findGreatest_spec (P := fun M => M ^ E ≤ n) (m := 0)
    (Nat.zero_le _) (by simp only; rw [zero_pow (by omega)]; exact Nat.zero_le _)
  have hM2 : 36 * k + 2 ≤ M := Nat.le_findGreatest (P := fun M => M ^ E ≤ n) (by omega) hn
  have hMn : M ≤ n := Nat.findGreatest_le n
  have hM3 : n < (M + 1) ^ E := by
    by_contra h
    push Not at h
    by_cases hMn' : M + 1 ≤ n
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self M) hMn' h
    · have : M + 1 ≤ (M + 1) ^ E := Nat.le_self_pow (by omega) _
      omega
  set ℓ : ℕ → ℕ := fun t => if t = 0 then n else M ^ (7 ^ (T - t)) with hℓdef
  have hMpow : ∀ j, M ≤ M ^ (7 ^ j) := fun j =>
    Nat.le_self_pow (Nat.pos_iff_ne_zero.1 (Nat.one_le_pow _ _ (by norm_num))) _
  have hpowle : ∀ j ≤ T, M ^ (7 ^ j) ≤ n := fun j hj =>
    le_trans (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by norm_num) hj)) hM1
  have hpow7 : ∀ j, (M ^ (7 ^ j)) ^ 7 = M ^ (7 ^ (j + 1)) := fun j => by
    rw [← pow_mul, pow_succ]
  set Φ := phiOf L
  have hΦlen : 2 * Φ.length ≤ 8 * n ^ c := by
    have : Φ.length ≤ 3 * fSize L + 1 := phiOf_length L
    have : 1 ≤ n ^ c := Nat.one_le_pow _ _ (by omega)
    omega
  have hcount := arith_count (E := E) (c := c) (by omega) hM3
  obtain ⟨ρ, Ev, hρ, hρU, hρc, hG⟩ := levels (vx := phpVx n) (phiOf_closed L)
    (phiOf_modfree hmf) (n := n) (k := k) (s := s) (T := T) ℓ (by simp [hℓdef])
    (fun t ht => by
      have h1 : ℓ (t + 1) = M ^ (7 ^ (T - (t + 1))) := by simp [hℓdef]
      rw [h1]
      by_cases h0 : t = 0
      · subst h0; simp only [hℓdef, if_pos rfl]; exact hpowle _ (by omega)
      · simp only [hℓdef, if_neg h0]
        exact Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by norm_num) (by omega)))
    (fun t ht => by
      by_cases h0 : t = 0
      · subst h0; simp only [hℓdef, if_pos rfl]; exact le_rfl
      · simp only [hℓdef, if_neg h0]; exact hpowle _ (by omega))
    hk (by omega)
    (fun t ht => by
      have hℓ1 : ℓ (t + 1) = M ^ (7 ^ (T - (t + 1))) := by simp [hℓdef]
      have hR : (ℓ (t + 1)) ^ 7 ≤ ℓ t := by
        rw [hℓ1, hpow7]
        by_cases h0 : t = 0
        · subst h0
          simp only [hℓdef, if_pos rfl]
          rw [show T - (0 + 1) + 1 = T by omega]; exact hM1
        · simp only [hℓdef, if_neg h0]
          rw [show T - (t + 1) + 1 = T - t by omega]
      refine arith_step hk (le_trans (by omega) (hℓ1 ▸ hMpow _)) hR ?_
      calc 2 * Φ.length ≤ 8 * n ^ c := hΦlen
        _ < M ^ (s + 1) := by rw [hs]; exact hcount
        _ ≤ (ℓ (t + 1)) ^ (s + 1) := Nat.pow_le_pow_left (hℓ1 ▸ hMpow _) _)
    T le_rfl
  have hℓT : ℓ T = M := by simp [hℓdef, hT]
  have hfree : (fH (range n) ρ).card = M := by
    rw [fH_card hρ (hols_sub hρU), card_range, hρc, hℓT]; omega
  have hroom : 5 * k ≤ (fH (range n) ρ).card := by rw [hfree]; omega
  have hdepth := phiOf_depth hR.2.1
  refine keval_no_refutation hR.1 hmf (fun S hS φ hφ => hG φ (mem_phiOf hS hφ)
    (by have := hdepth φ (mem_phiOf hS hφ); omega))
    (php_clauseHit rfl rfl rfl hρ hρU hk hroom) hroom hR.2.2

end

end SATurday.ProofComplexity
