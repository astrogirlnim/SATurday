import Theory.ProofComplexity.QSwitch

/-!
# Canonical q-decision trees, restriction and coverage (Ladder Rung R4, 1D.2)

* `cdt`: the canonical q-decision tree of a DNF of partial q-partitions below a restriction `ρ`:
  query (point by point) the free points of the first term compatible with the current branch,
  then continue. Its `1`-branches contain a restricted term, its `0`-branches are incompatible
  with every restricted term (`cdt_one`, `cdt_zero`), and its height is at most `q` times the
  canonical depth (`ht_cdt`).
* `restrictT`: restriction of a tree by a partial partition, with the branch correspondence
  `br_restrict` / `restrict_br`.
* `exists_branch`: every partial partition leaving room is compatible with a branch.

LOG: R4 QTree module (canonical q-trees)
-/

namespace SATurday.ProofComplexity

namespace QP

open Finset

noncomputable section

open Classical

variable {q : ℕ} {α : Type}

open QT

/-! ## Querying a list of points -/

/-- Query the listed points that are still free, then continue with `k`. -/
def roundT (q : ℕ) (k : Finset ℕ → Finset (Finset ℕ) → QT α) :
    List ℕ → Finset ℕ → Finset (Finset ℕ) → QT α
  | [], W, σ => k W σ
  | v :: l, W, σ => if v ∈ W then node v (fun e => roundT q k l (W \ e) (insert e σ))
      else roundT q k l W σ

/-- Answers to a round: blocks of free points through the listed points, covering them. -/
def CovL (q : ℕ) (l : List ℕ) (W : Finset ℕ) (c : Finset (Finset ℕ)) : Prop :=
  (∀ e ∈ c, e ⊆ W) ∧ PP q c ∧ (∀ v ∈ l, v ∈ W → v ∈ cov c) ∧ ∀ e ∈ c, ∃ v ∈ l, v ∈ e

theorem covL_nil {W : Finset ℕ} {c : Finset (Finset ℕ)} (h : CovL q [] W c) : c = ∅ := by
  by_contra hne
  obtain ⟨e, he⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨v, hv, -⟩ := h.2.2.2 e he
  simp at hv

theorem covL_cons_out {l : List ℕ} {v : ℕ} {W : Finset ℕ} {c : Finset (Finset ℕ)} (hv : v ∉ W)
    (h : CovL q (v :: l) W c) : CovL q l W c := by
  refine ⟨h.1, h.2.1, fun u hu huW => h.2.2.1 u (List.mem_cons_of_mem _ hu) huW, fun e he => ?_⟩
  obtain ⟨u, hu, hue⟩ := h.2.2.2 e he
  rcases List.mem_cons.1 hu with rfl | hu
  · exact absurd (h.1 e he hue) hv
  · exact ⟨u, hu, hue⟩

theorem covL_cons_in {l : List ℕ} {v : ℕ} {W : Finset ℕ} {c : Finset (Finset ℕ)} (hq : 1 ≤ q)
    (hvW : v ∈ W) (h : CovL q (v :: l) W c) :
    ∃ e ∈ c, e ∈ blocks q W v ∧ CovL q l (W \ e) (c.erase e) := by
  obtain ⟨e, he, hve⟩ := mem_cov.1 (h.2.2.1 v (List.mem_cons_self) hvW)
  refine ⟨e, he, mem_blocks.2 ⟨h.1 e he, h.2.1.1 e he, hve⟩, fun f hf => ?_,
    pp_mono h.2.1 (erase_subset _ _), fun u hu huW => ?_, fun f hf => ?_⟩
  · obtain ⟨hfe, hfc⟩ := mem_erase.1 hf
    exact fun x hx => mem_sdiff.2 ⟨h.1 f hfc hx, fun hxe =>
      disjoint_left.1 (h.2.1.2 f hfc e he hfe) hx hxe⟩
  · obtain ⟨huW', hue⟩ := mem_sdiff.1 huW
    obtain ⟨f, hf, huf⟩ := mem_cov.1 (h.2.2.1 u (List.mem_cons_of_mem _ hu) huW')
    exact mem_cov.2 ⟨f, mem_erase.2 ⟨fun hfe => hue (hfe ▸ huf), hf⟩, huf⟩
  · obtain ⟨hfe, hfc⟩ := mem_erase.1 hf
    obtain ⟨u, hu, huf⟩ := h.2.2.2 f hfc
    rcases List.mem_cons.1 hu with rfl | hu
    · exact absurd (pp_eq_of_mem h.2.1 hfc he huf hve) hfe
    · exact ⟨u, hu, huf⟩

theorem covL_insert {l : List ℕ} {v : ℕ} {W : Finset ℕ} {e : Finset ℕ} {c : Finset (Finset ℕ)}
    (he : e ∈ blocks q W v) (h : CovL q l (W \ e) c) : CovL q (v :: l) W (insert e c) := by
  obtain ⟨heW, hec, hve⟩ := mem_blocks.1 he
  have hdisj : Disjoint e (cov c) := disjoint_left.2 fun x hxe hxc => by
    obtain ⟨f, hf, hxf⟩ := mem_cov.1 hxc
    exact (mem_sdiff.1 (h.1 f hf hxf)).2 hxe
  refine ⟨fun f hf => ?_, pp_insert h.2.1 hec hdisj, fun u hu huW => ?_, fun f hf => ?_⟩
  · rcases mem_insert.1 hf with rfl | hf
    · exact heW
    · exact (h.1 f hf).trans sdiff_subset
  · rw [cov_insert]
    by_cases hue : u ∈ e
    · exact mem_union.2 (Or.inl hue)
    · rcases List.mem_cons.1 hu with rfl | hu
      · exact absurd hve hue
      · exact mem_union.2 (Or.inr (h.2.2.1 u hu (mem_sdiff.2 ⟨huW, hue⟩)))
  · rcases mem_insert.1 hf with rfl | hf
    · exact ⟨v, List.mem_cons_self, hve⟩
    · obtain ⟨u, hu, huf⟩ := h.2.2.2 f hf
      exact ⟨u, List.mem_cons_of_mem _ hu, huf⟩

theorem sdiff_cov_insert (W : Finset ℕ) (e : Finset ℕ) (c : Finset (Finset ℕ)) :
    W \ cov (insert e c) = (W \ e) \ cov c := by
  rw [cov_insert, sdiff_sdiff_left]; rfl

theorem union_insert_comm (σ c : Finset (Finset ℕ)) (e : Finset ℕ) :
    σ ∪ insert e c = insert e σ ∪ c := by
  ext x; simp only [mem_union, mem_insert]; tauto

/-- Branches of a round: an answer cover followed by a branch of the continuation. -/
theorem br_roundT (hq : 1 ≤ q) (k : Finset ℕ → Finset (Finset ℕ) → QT α) :
    ∀ (l : List ℕ) (W : Finset ℕ) (σ : Finset (Finset ℕ)) (B : Finset (Finset ℕ) × α),
    B ∈ br q (roundT q k l W σ) W → ∃ c, CovL q l W c ∧
      ∃ B' ∈ br q (k (W \ cov c) (σ ∪ c)) (W \ cov c), B = (c ∪ B'.1, B'.2)
  | [], W, σ, B, h => ⟨∅, ⟨by simp, ⟨by simp, by simp⟩, by simp, by simp⟩, B,
      by simpa [roundT, cov] using h, by simp⟩
  | v :: l, W, σ, B, h => by
    by_cases hv : v ∈ W
    · simp only [roundT, if_pos hv] at h
      obtain ⟨e, he, B1, hB1, rfl⟩ := mem_br_node.1 h
      obtain ⟨c, hc, B', hB', hB1eq⟩ := br_roundT hq k l (W \ e) (insert e σ) B1 hB1
      refine ⟨insert e c, covL_insert he hc, B', ?_, ?_⟩
      · rw [sdiff_cov_insert, union_insert_comm]; exact hB'
      · rw [hB1eq]; ext1
        · simp only; ext x; simp only [mem_insert, mem_union]; tauto
        · rfl
    · simp only [roundT, if_neg hv] at h
      obtain ⟨c, hc, B', hB', hB⟩ := br_roundT hq k l W σ B h
      refine ⟨c, ⟨hc.1, hc.2.1, fun u hu huW => ?_, fun e he => ?_⟩, B', hB', hB⟩
      · rcases List.mem_cons.1 hu with rfl | hu
        · exact absurd huW hv
        · exact hc.2.2.1 u hu huW
      · obtain ⟨u, hu, hue⟩ := hc.2.2.2 e he
        exact ⟨u, List.mem_cons_of_mem _ hu, hue⟩

theorem wf_roundT (k : Finset ℕ → Finset (Finset ℕ) → QT α) (hk : ∀ W σ, WF q (k W σ) W) :
    ∀ (l : List ℕ) (W : Finset ℕ) (σ : Finset (Finset ℕ)), WF q (roundT q k l W σ) W
  | [], W, σ => hk W σ
  | v :: l, W, σ => by
    by_cases hv : v ∈ W
    · simp only [roundT, if_pos hv]
      exact ⟨hv, fun e _ => wf_roundT k hk l (W \ e) (insert e σ)⟩
    · simp only [roundT, if_neg hv]; exact wf_roundT k hk l W σ

theorem ht_roundT (hq : 1 ≤ q) (k : Finset ℕ → Finset (Finset ℕ) → QT α) {h : ℕ} :
    ∀ (l : List ℕ) (W : Finset ℕ) (σ : Finset (Finset ℕ)),
    (∀ c, CovL q l W c → ht q (k (W \ cov c) (σ ∪ c)) (W \ cov c) ≤ h) →
    ht q (roundT q k l W σ) W ≤ l.length + h
  | [], W, σ, hk => by
    have := hk ∅ ⟨by simp, ⟨by simp, by simp⟩, by simp, by simp⟩
    simpa [roundT, cov] using this
  | v :: l, W, σ, hk => by
    by_cases hv : v ∈ W
    · simp only [roundT, if_pos hv, ht, List.length_cons]
      have : ((blocks q W v).sup fun e => ht q (roundT q k l (W \ e) (insert e σ)) (W \ e)) ≤
          l.length + h := by
        refine Finset.sup_le fun e he => ht_roundT hq k l (W \ e) (insert e σ) fun c hc => ?_
        have := hk (insert e c) (covL_insert he hc)
        rwa [sdiff_cov_insert, union_insert_comm] at this
      omega
    · simp only [roundT, if_neg hv, List.length_cons]
      have := ht_roundT hq k l W σ fun c hc => hk c ⟨hc.1, hc.2.1,
        fun u hu huW => by
          rcases List.mem_cons.1 hu with rfl | hu
          · exact absurd huW hv
          · exact hc.2.2.1 u hu huW,
        fun e he => by
          obtain ⟨u, hu, hue⟩ := hc.2.2.2 e he
          exact ⟨u, List.mem_cons_of_mem _ hu, hue⟩⟩
      omega

theorem card_covL {l : List ℕ} {W : Finset ℕ} {c : Finset (Finset ℕ)} (h : CovL q l W c) :
    c.card ≤ l.length := by
  have : ∀ e ∈ c, ∃ v ∈ l, v ∈ e := h.2.2.2
  choose f hf1 hf2 using this
  refine (card_le_card_of_injOn (fun e => if he : e ∈ c then f e he else 0) (s := c)
    (t := l.toFinset) (fun e he => ?_) (fun e he e' he' hee => ?_)).trans (List.toFinset_card_le l)
  · simp only [dif_pos (mem_coe.1 he)]; exact List.mem_toFinset.2 (hf1 e he)
  · simp only [dif_pos (mem_coe.1 he), dif_pos (mem_coe.1 he')] at hee
    exact pp_eq_of_mem h.2.1 he he' (hf2 e he) (hee ▸ hf2 e' he')

/-! ## The canonical tree -/

/-- Points of a partial partition, in increasing order. -/
def ptsL (τ : Finset (Finset ℕ)) : List ℕ := (cov τ).sort (· ≤ ·)

/-- The canonical tree with fuel, current free points `W` and current branch `σ`. -/
def cdt (q : ℕ) (D : List (Finset (Finset ℕ))) (ρ : Finset (Finset ℕ)) :
    ℕ → Finset ℕ → Finset (Finset ℕ) → QT Bool
  | 0, _, _ => leaf false
  | n + 1, W, σ => match qfirst q (ρ ∪ σ) D with
    | none => leaf false
    | some t => if t ⊆ ρ ∪ σ then leaf true
        else roundT q (cdt q D ρ n) (ptsL (t \ (ρ ∪ σ))) W σ

/-- The canonical tree of `D` below `ρ`. -/
def canonT (q : ℕ) (U : Finset ℕ) (D : List (Finset (Finset ℕ))) (ρ : Finset (Finset ℕ)) :
    QT Bool :=
  cdt q D ρ (U.card + 1) (free U ρ) ∅

theorem wf_cdt (D : List (Finset (Finset ℕ))) (ρ : Finset (Finset ℕ)) :
    ∀ n W σ, WF q (cdt q D ρ n W σ) W
  | 0, W, σ => trivial
  | n + 1, W, σ => by
    simp only [cdt]
    split
    · trivial
    · split_ifs
      · trivial
      · exact wf_roundT _ (fun W σ => wf_cdt D ρ n W σ) _ W σ

/-- The invariant of the canonical recursion. -/
structure CInv (q : ℕ) (U : Finset ℕ) (ρ σ : Finset (Finset ℕ)) (W : Finset ℕ) : Prop where
  pp : PP q (ρ ∪ σ)
  inU : InU U (ρ ∪ σ)
  free : W = free U (ρ ∪ σ)

theorem cinv_step {U : Finset ℕ} {ρ σ c : Finset (Finset ℕ)} {W : Finset ℕ} {l : List ℕ}
    (h : CInv q U ρ σ W) (hc : CovL q l W c) : CInv q U ρ (σ ∪ c) (W \ cov c) := by
  have hcf : ∀ e ∈ c, e ⊆ free U (ρ ∪ σ) := fun e he => h.free ▸ hc.1 e he
  refine ⟨?_, ?_, ?_⟩
  · rw [← union_assoc]
    exact pp_union h.pp hc.2.1 fun e he f hf _ => (disj_free_blocks (hcf f hf) e he).symm
  · intro e he
    rw [← union_assoc] at he
    rcases mem_union.1 he with he | he
    · exact h.inU e he
    · exact (hcf e he).trans sdiff_subset
  · rw [h.free]; ext x; simp only [free, cov_union, mem_sdiff, mem_union]; tauto

/-- A round of the canonical tree answers a cover of the first term's free blocks. -/
theorem covL_qcovers (hq : 1 ≤ q) {U : Finset ℕ} {ρ σ t : Finset (Finset ℕ)} {W : Finset ℕ}
    (h : CInv q U ρ σ W) (hct : Compat q (ρ ∪ σ) t) (htU : InU U t) (hts : ¬ t ⊆ ρ ∪ σ)
    {c : Finset (Finset ℕ)} (hc : CovL q (ptsL (t \ (ρ ∪ σ))) W c) :
    c ∈ qcovers q U (ρ ∪ σ) (t \ (ρ ∪ σ)) := by
  have hτf := blocks_free_of_compat hct htU
  have hcovW : cov (t \ (ρ ∪ σ)) ⊆ W := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := mem_cov.1 hx
    rw [h.free]; exact hτf b hb hxb
  have hcov : cov (t \ (ρ ∪ σ)) ⊆ cov c := fun x hx =>
    hc.2.2.1 x ((mem_sort _).2 hx) (hcovW hx)
  refine mem_qcovers.2 ⟨fun e he => h.free ▸ hc.1 e he, ?_, hc.2.1, hcov, fun e he => ?_⟩
  · obtain ⟨b, hb⟩ := not_subset.1 hts
    have hbτ : b ∈ t \ (ρ ∪ σ) := mem_sdiff.2 hb
    have hbne : b.Nonempty := by
      rw [← card_pos, hct.1 b (mem_union.2 (Or.inr hb.1))]; omega
    obtain ⟨x, hx⟩ := hbne
    obtain ⟨e, he, -⟩ := mem_cov.1 (hcov (sub_cov hbτ hx))
    exact ⟨e, he⟩
  · obtain ⟨v, hv, hve⟩ := hc.2.2.2 e he
    exact not_disjoint_iff.2 ⟨v, hve, (mem_sort _).1 hv⟩

theorem ht_cdt (hq : 1 ≤ q) {U : Finset ℕ} {D : List (Finset (Finset ℕ))} (hU : ∀ t ∈ D, InU U t)
    (ρ : Finset (Finset ℕ)) :
    ∀ n W σ, CInv q U ρ σ W → ht q (cdt q D ρ n W σ) W ≤ q * cdepth q U D (ρ ∪ σ)
  | 0, W, σ, _ => by simp [cdt, ht]
  | n + 1, W, σ, hinv => by
    simp only [cdt]
    split
    · simp [ht]
    · rename_i t hF
      split_ifs with hts
      · simp [ht]
      · have hct := qfirst_compat hF
        have htU := hU t (qfirst_mem hF)
        have hdep := cdepth_some (U := U) hF
        rw [if_neg hts] at hdep
        set τ := t \ (ρ ∪ σ)
        have hτp : PP q τ := pp_mono hct (sdiff_subset.trans subset_union_right)
        have hle : τ.card ≤ cdepth q U D (ρ ∪ σ) := by rw [hdep]; omega
        have hlen : (ptsL τ).length = q * τ.card := by rw [ptsL, length_sort, card_cov hτp]
        have := ht_roundT (h := q * (cdepth q U D (ρ ∪ σ) - τ.card)) hq (cdt q D ρ n) (ptsL τ) W σ
          (fun c hc => by
            have h1 := ht_cdt hq hU ρ n (W \ cov c) (σ ∪ c) (cinv_step hinv hc)
            have h2 := le_cdepth_cover hF hts (covL_qcovers hq hinv hct htU hts hc)
            have h3 : (t \ (ρ ∪ σ)).card = τ.card := rfl
            rw [← union_assoc] at h1
            calc _ ≤ q * cdepth q U D (ρ ∪ σ ∪ c) := h1
              _ ≤ _ := Nat.mul_le_mul_left _ (by omega))
        rw [hlen] at this
        calc _ ≤ q * τ.card + q * (cdepth q U D (ρ ∪ σ) - τ.card) := this
          _ = _ := by rw [← mul_add]; congr 1; omega

theorem cdt_one {D : List (Finset (Finset ℕ))} (hq : 1 ≤ q) (ρ : Finset (Finset ℕ)) :
    ∀ n W σ B, B ∈ br q (cdt q D ρ n W σ) W → B.2 = true →
      ∃ t ∈ D, Compat q (ρ ∪ σ) t ∧ t ⊆ ρ ∪ σ ∪ B.1
  | 0, W, σ, B, h, h2 => by simp [cdt, br] at h; rw [h] at h2; simp at h2
  | n + 1, W, σ, B, h, h2 => by
    simp only [cdt] at h
    split at h
    · simp [br] at h; rw [h] at h2; simp at h2
    · rename_i t hF
      split_ifs at h with hts
      · simp [br] at h
        exact ⟨t, qfirst_mem hF, qfirst_compat hF, by rw [h]; simpa using hts⟩
      · obtain ⟨c, hc, B', hB', rfl⟩ := br_roundT hq _ _ W σ B h
        obtain ⟨t', ht', hc', hsub⟩ := cdt_one hq ρ n _ _ B' hB' h2
        refine ⟨t', ht', compat_mono hc' (by rw [← union_assoc]; exact subset_union_left) subset_rfl,
          hsub.trans ?_⟩
        intro x hx; simp only [mem_union] at hx ⊢; tauto

theorem cdt_zero {U : Finset ℕ} {D : List (Finset (Finset ℕ))} (hq : 1 ≤ q)
    (hU : ∀ t ∈ D, InU U t) (ρ : Finset (Finset ℕ)) :
    ∀ n W σ B, CInv q U ρ σ W → W.card < n → B ∈ br q (cdt q D ρ n W σ) W → B.2 = false →
      ∀ t ∈ D, ¬ Compat q (ρ ∪ σ ∪ B.1) t
  | 0, W, σ, B, _, hn, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, W, σ, B, hinv, hn, h, h2 => by
    simp only [cdt] at h
    split at h
    · rename_i hF
      simp [br] at h; rw [h]; simpa using qfirst_none hF
    · rename_i t hF
      split_ifs at h with hts
      · simp [br] at h; rw [h] at h2; simp at h2
      · have hct := qfirst_compat hF
        have htU := hU t (qfirst_mem hF)
        obtain ⟨c, hc, B', hB', rfl⟩ := br_roundT hq _ _ W σ B h
        have hcq := covL_qcovers hq hinv hct htU hts hc
        have hlt : (W \ cov c).card < n := by
          obtain ⟨-, ⟨e, he⟩, -, hcov, htouch⟩ := mem_qcovers.1 hcq
          obtain ⟨x, hxe, hxτ⟩ := not_disjoint_iff.1 (htouch e he)
          have hxW : x ∈ W := by
            obtain ⟨b, hb, hxb⟩ := mem_cov.1 hxτ
            rw [hinv.free]; exact blocks_free_of_compat hct htU b hb hxb
          have : (W \ cov c).card < W.card := card_lt_card ⟨sdiff_subset, fun h' =>
            (mem_sdiff.1 (h' hxW)).2 (sub_cov he hxe)⟩
          omega
        intro t' ht'
        have := cdt_zero hq hU ρ n _ _ B' (cinv_step hinv hc) hlt hB' h2 t' ht'
        convert this using 2
        ext x; simp only [mem_union]; tauto

/-! ## Properties of the canonical tree -/

theorem cinv_top {U : Finset ℕ} {ρ : Finset (Finset ℕ)} (hρ : PP q ρ) (hρU : InU U ρ) :
    CInv q U ρ ∅ (free U ρ) := ⟨by simpa using hρ, by simpa using hρU, by simp⟩

theorem wf_canonT (U : Finset ℕ) (D : List (Finset (Finset ℕ))) (ρ : Finset (Finset ℕ)) :
    WF q (canonT q U D ρ) (free U ρ) := wf_cdt D ρ _ _ _

theorem ht_canonT (hq : 1 ≤ q) {U : Finset ℕ} {D : List (Finset (Finset ℕ))}
    (hU : ∀ t ∈ D, InU U t) {ρ : Finset (Finset ℕ)} (hρ : PP q ρ) (hρU : InU U ρ) :
    ht q (canonT q U D ρ) (free U ρ) ≤ q * cdepth q U D ρ := by
  have := ht_cdt hq hU ρ (U.card + 1) (free U ρ) ∅ (cinv_top hρ hρU)
  simpa using this

theorem canonT_one (hq : 1 ≤ q) {U : Finset ℕ} {D : List (Finset (Finset ℕ))}
    {ρ : Finset (Finset ℕ)} {B : Finset (Finset ℕ) × Bool} (h : B ∈ br q (canonT q U D ρ) (free U ρ))
    (h2 : B.2 = true) : ∃ t ∈ D, Compat q ρ t ∧ t \ ρ ⊆ B.1 := by
  obtain ⟨t, ht, hc, hsub⟩ := cdt_one hq ρ _ _ _ B h h2
  refine ⟨t, ht, by simpa using hc, fun e he => ?_⟩
  obtain ⟨he1, he2⟩ := mem_sdiff.1 he
  have := hsub he1
  simp only [union_empty, mem_union] at this
  exact this.resolve_left he2

theorem canonT_zero (hq : 1 ≤ q) {U : Finset ℕ} {D : List (Finset (Finset ℕ))}
    (hU : ∀ t ∈ D, InU U t) {ρ : Finset (Finset ℕ)} (hρ : PP q ρ) (hρU : InU U ρ)
    {B : Finset (Finset ℕ) × Bool} (h : B ∈ br q (canonT q U D ρ) (free U ρ)) (h2 : B.2 = false) :
    ∀ t ∈ D, Compat q ρ t → ¬ Compat q B.1 (t \ ρ) := by
  intro t ht hct hc
  have hz := cdt_zero hq hU ρ _ _ _ B (cinv_top hρ hρU)
    (lt_of_le_of_lt (card_le_card sdiff_subset) (Nat.lt_succ_self _)) h h2 t ht
  apply hz
  obtain ⟨hBp, hBf, -⟩ := br_props _ _ _ h
  have hρB : PP q (ρ ∪ B.1) := pp_union hρ hBp fun e he f hf _ =>
    (disj_free_blocks (hBf f hf) e he).symm
  have hall : PP q (ρ ∪ B.1 ∪ (t \ ρ)) := by
    refine pp_union hρB (pp_mono hct (sdiff_subset.trans subset_union_right)) fun e he f hf hef => ?_
    rcases mem_union.1 he with he | he
    · exact hct.2 e (mem_union.2 (Or.inl he)) f (mem_union.2 (Or.inr (mem_sdiff.1 hf).1)) hef
    · exact hc.2 e (mem_union.2 (Or.inl he)) f (mem_union.2 (Or.inr hf)) hef
  refine pp_mono hall fun e he => ?_
  simp only [union_empty, mem_union, mem_sdiff] at he ⊢
  by_cases heρ : e ∈ ρ
  · exact Or.inl (Or.inl heρ)
  · rcases he with (he | he) | he
    · exact absurd he heρ
    · exact Or.inl (Or.inr he)
    · exact Or.inr ⟨he, heρ⟩

/-! ## Restriction of trees -/

/-- Restriction by a partial partition: queried points covered by it follow its block. -/
def restrictT (τ : Finset (Finset ℕ)) : QT α → QT α
  | leaf a => leaf a
  | node v ch => if v ∈ cov τ then restrictT τ (ch (blockOf τ v))
      else node v fun e => restrictT τ (ch e)

/-- Blocks of `τ` lie inside or outside the free set. -/
def Sep (τ : Finset (Finset ℕ)) (W : Finset ℕ) : Prop := ∀ f ∈ τ, f ⊆ W ∨ Disjoint f W

theorem sep_sdiff {τ : Finset (Finset ℕ)} (hτ : PP q τ) {W : Finset ℕ} (h : Sep τ W)
    {e : Finset ℕ} (he : e ∈ τ ∨ Disjoint e (cov τ)) : Sep τ (W \ e) := by
  intro f hf
  rcases h f hf with h1 | h1
  · rcases he with he | he
    · by_cases hfe : f = e
      · subst hfe; exact Or.inr disjoint_sdiff
      · exact Or.inl fun x hx => mem_sdiff.2 ⟨h1 hx, fun hxe =>
          disjoint_left.1 (hτ.2 f hf e he hfe) hx hxe⟩
    · exact Or.inl fun x hx => mem_sdiff.2 ⟨h1 hx, fun hxe =>
        disjoint_left.1 he hxe (sub_cov hf hx)⟩
  · exact Or.inr (h1.mono_right sdiff_subset)

theorem restrict_props (hq : 1 ≤ q) {τ : Finset (Finset ℕ)} (hτ : PP q τ) :
    ∀ (T : QT α) (W : Finset ℕ), WF q T W → Sep τ W →
    WF q (restrictT τ T) (W \ cov τ) ∧ ht q (restrictT τ T) (W \ cov τ) ≤ ht q T W ∧
    (∀ B' ∈ br q (restrictT τ T) (W \ cov τ),
      ∃ B ∈ br q T W, Compat q τ B.1 ∧ B.1 \ τ = B'.1 ∧ B.2 = B'.2) ∧
    (∀ B ∈ br q T W, Compat q τ B.1 → (B.1 \ τ, B.2) ∈ br q (restrictT τ T) (W \ cov τ))
  | leaf a, W, _, _ => by
    refine ⟨trivial, le_rfl, fun B' hB' => ?_, fun B hB _ => ?_⟩
    · simp [restrictT, br] at hB'
      exact ⟨(∅, a), by simp [br], by simpa [Compat] using hτ, by simp [hB'], by simp [hB']⟩
    · simp [br] at hB; simp [restrictT, br, hB]
  | node v ch, W, hwf, hsep => by
    obtain ⟨hvW, hch⟩ := hwf
    by_cases hvτ : v ∈ cov τ
    · obtain ⟨hf, hvf⟩ := blockOf_spec hvτ
      set f := blockOf τ v
      have hfW : f ⊆ W := by
        rcases hsep f hf with h | h
        · exact h
        · exact absurd hvW (disjoint_left.1 h hvf)
      have hfb : f ∈ blocks q W v := mem_blocks.2 ⟨hfW, hτ.1 f hf, hvf⟩
      have heqW : (W \ f) \ cov τ = W \ cov τ := by
        ext x; simp only [mem_sdiff]
        constructor
        · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, fun h => h2 (sub_cov hf h)⟩, h2⟩
      obtain ⟨i1, i2, i3, i4⟩ := restrict_props hq hτ (ch f) (W \ f) (hch f hfb)
        (sep_sdiff hτ hsep (Or.inl hf))
      rw [heqW] at i1 i2 i3 i4
      simp only [restrictT, if_pos hvτ]
      refine ⟨i1, i2.trans (by have := ht_child (ch := ch) hfb; omega), fun B' hB' => ?_,
        fun B hB hc => ?_⟩
      · obtain ⟨B1, hB1, hc, he, hl⟩ := i3 B' hB'
        refine ⟨(insert f B1.1, B1.2), mem_br_node.2 ⟨f, hfb, B1, hB1, rfl⟩, ?_, ?_, hl⟩
        · simp only
          unfold Compat
          rw [show τ ∪ insert f B1.1 = τ ∪ B1.1 by
            ext x; simp only [mem_union, mem_insert]; constructor
            · rintro (h | rfl | h)
              · exact Or.inl h
              · exact Or.inl hf
              · exact Or.inr h
            · rintro (h | h)
              · exact Or.inl h
              · exact Or.inr (Or.inr h)]
          exact hc
        · simp only; rw [← he, insert_sdiff_of_mem _ hf]
      · obtain ⟨e, he, B1, hB1, rfl⟩ := mem_br_node.1 hB
        have hef : e = f := pp_eq_of_mem hc (mem_union.2 (Or.inr (mem_insert_self _ _)))
          (mem_union.2 (Or.inl hf)) (mem_blocks.1 he).2.2 hvf
        subst hef
        have := i4 B1 hB1 (compat_mono hc subset_rfl (subset_insert _ _))
        simpa [insert_sdiff_of_mem _ hf] using this
    · simp only [restrictT, if_neg hvτ]
      have hvW' : v ∈ W \ cov τ := mem_sdiff.2 ⟨hvW, hvτ⟩
      have hblk : ∀ e ∈ blocks q (W \ cov τ) v, e ∈ blocks q W v ∧ Disjoint e (cov τ) := by
        intro e he
        obtain ⟨hsub, hc, hve⟩ := mem_blocks.1 he
        exact ⟨mem_blocks.2 ⟨hsub.trans sdiff_subset, hc, hve⟩,
          disjoint_left.2 fun x hx => (mem_sdiff.1 (hsub hx)).2⟩
      have heqW : ∀ e : Finset ℕ, (W \ e) \ cov τ = (W \ cov τ) \ e := fun e => by
        ext x; simp only [mem_sdiff]; tauto
      have IH := fun e (he : e ∈ blocks q (W \ cov τ) v) =>
        restrict_props hq hτ (ch e) (W \ e) (hch e (hblk e he).1)
          (sep_sdiff hτ hsep (Or.inr (hblk e he).2))
      refine ⟨⟨hvW', fun e he => ?_⟩, ?_, fun B' hB' => ?_, fun B hB hc => ?_⟩
      · have := (IH e he).1; rwa [heqW] at this
      · simp only [ht]
        refine Nat.add_le_add_right (Finset.sup_le fun e he => ?_) 1
        have := (IH e he).2.1
        rw [heqW] at this
        exact this.trans (le_sup (f := fun e => ht q (ch e) (W \ e)) (hblk e he).1)
      · obtain ⟨e, he, B1', hB1', rfl⟩ := mem_br_node.1 hB'
        have i3 := (IH e he).2.2.1
        rw [heqW] at i3
        obtain ⟨B1, hB1, hc, heq, hl⟩ := i3 B1' hB1'
        have heτ : e ∉ τ := by
          intro h; obtain ⟨-, -, hve⟩ := mem_blocks.1 he; exact hvτ (sub_cov h hve)
        refine ⟨(insert e B1.1, B1.2), mem_br_node.2 ⟨e, (hblk e he).1, B1, hB1, rfl⟩, ?_, ?_, hl⟩
        · simp only
          have hB1W := br_blocks hB1
          unfold Compat
          rw [show τ ∪ insert e B1.1 = insert e (τ ∪ B1.1) by
            ext x; simp only [mem_union, mem_insert]; tauto]
          refine pp_insert hc (mem_blocks.1 he).2.1 ?_
          rw [cov_union]
          refine disjoint_union_right.2 ⟨(hblk e he).2, ?_⟩
          refine disjoint_left.2 fun x hxe hxB => ?_
          obtain ⟨g, hg, hxg⟩ := mem_cov.1 hxB
          exact (mem_sdiff.1 (hB1W g hg hxg)).2 hxe
        · simp only; rw [insert_sdiff_of_notMem _ heτ, heq]
      · obtain ⟨e, he, B1, hB1, rfl⟩ := mem_br_node.1 hB
        obtain ⟨heW, hec, hve⟩ := mem_blocks.1 he
        have heτ : e ∉ τ := fun h => hvτ (sub_cov h hve)
        have hed : Disjoint e (cov τ) := by
          refine disjoint_left.2 fun x hxe hxτ => ?_
          obtain ⟨g, hg, hxg⟩ := mem_cov.1 hxτ
          have := pp_eq_of_mem hc (mem_union.2 (Or.inr (mem_insert_self _ _)))
            (mem_union.2 (Or.inl hg)) hxe hxg
          exact heτ (this ▸ hg)
        have he' : e ∈ blocks q (W \ cov τ) v :=
          mem_blocks.2 ⟨fun x hx => mem_sdiff.2 ⟨heW hx, disjoint_left.1 hed hx⟩, hec, hve⟩
        have i4 := (IH e he').2.2.2 B1 hB1 (compat_mono hc subset_rfl (subset_insert _ _))
        rw [heqW] at i4
        simp only
        rw [insert_sdiff_of_notMem _ heτ]
        exact mem_br_node.2 ⟨e, he', (B1.1 \ τ, B1.2), i4, rfl⟩

/-! ## Flipping labels -/

def flipT : QT Bool → QT Bool
  | leaf b => leaf (!b)
  | node v ch => node v fun e => flipT (ch e)

theorem flip_props : ∀ (T : QT Bool) (W : Finset ℕ),
    (WF q (flipT T) W ↔ WF q T W) ∧ ht q (flipT T) W = ht q T W ∧
    br q (flipT T) W = (br q T W).image fun B => (B.1, !B.2)
  | leaf b, W => by simp [flipT, WF, ht, br]
  | node v ch, W => by
    have IH := fun e => flip_props (ch e) (W \ e)
    refine ⟨?_, ?_, ?_⟩
    · simp only [flipT, WF]
      exact and_congr_right fun _ => forall₂_congr fun e _ => (IH e).1
    · simp only [flipT, ht]; congr 1
      exact sup_congr rfl fun e _ => (IH e).2.1
    · ext B
      constructor
      · intro hB
        rw [flipT] at hB
        obtain ⟨e, he, B', hB', rfl⟩ := mem_br_node.1 hB
        rw [(IH e).2.2] at hB'
        obtain ⟨B1, hB1, rfl⟩ := mem_image.1 hB'
        exact mem_image.2 ⟨(insert e B1.1, B1.2), mem_br_node.2 ⟨e, he, B1, hB1, rfl⟩, rfl⟩
      · intro hB
        obtain ⟨B0, hB0, rfl⟩ := mem_image.1 hB
        obtain ⟨e, he, B1, hB1, rfl⟩ := mem_br_node.1 hB0
        rw [flipT]
        refine mem_br_node.2 ⟨e, he, (B1.1, !B1.2), ?_, rfl⟩
        rw [(IH e).2.2]; exact mem_image.2 ⟨B1, hB1, rfl⟩

/-! ## Coverage -/

/-- Every partial partition of free points leaving room is compatible with a branch. -/
theorem exists_branch (hq : 1 ≤ q) : ∀ (T : QT α) (W : Finset ℕ) (π : Finset (Finset ℕ)),
    WF q T W → PP q π → (∀ f ∈ π, f ⊆ W) → q * (π.card + ht q T W) ≤ W.card →
    ∃ B ∈ br q T W, Compat q π B.1
  | leaf a, W, π, _, hπ, _, _ => ⟨(∅, a), by simp [br], by simpa [Compat] using hπ⟩
  | node v ch, W, π, hwf, hπ, hπW, hroom => by
    obtain ⟨hvW, hch⟩ := hwf
    have hht : 1 ≤ ht q (node v ch) W := by simp [ht]
    by_cases hvπ : v ∈ cov π
    · obtain ⟨f, hf, hvf⟩ := mem_cov.1 hvπ
      have hfb : f ∈ blocks q W v := mem_blocks.2 ⟨hπW f hf, hπ.1 f hf, hvf⟩
      have hhc := ht_child (ch := ch) hfb
      have hπ1 : 1 ≤ π.card := card_pos.2 ⟨f, hf⟩
      have hWf : (W \ f).card = W.card - q := by
        rw [card_sdiff_of_subset (hπW f hf), hπ.1 f hf]
      obtain ⟨B1, hB1, hc⟩ := exists_branch hq (ch f) (W \ f) (π.erase f) (hch f hfb)
        (pp_mono hπ (erase_subset _ _))
        (fun g hg => by
          obtain ⟨hgf, hgπ⟩ := mem_erase.1 hg
          exact fun x hx => mem_sdiff.2 ⟨hπW g hgπ hx,
            fun hxf => disjoint_left.1 (hπ.2 g hgπ f hf hgf) hx hxf⟩)
        (by
          rw [card_erase_of_mem hf, hWf]
          have : q * (π.card - 1 + ht q (ch f) (W \ f)) + q ≤ q * (π.card + ht q (node v ch) W) := by
            have h1 : π.card - 1 + ht q (ch f) (W \ f) + 1 ≤ π.card + ht q (node v ch) W := by omega
            calc q * (π.card - 1 + ht q (ch f) (W \ f)) + q
                = q * (π.card - 1 + ht q (ch f) (W \ f) + 1) := by ring
              _ ≤ _ := Nat.mul_le_mul_left _ h1
          omega)
      refine ⟨(insert f B1.1, B1.2), mem_br_node.2 ⟨f, hfb, B1, hB1, rfl⟩, ?_⟩
      unfold Compat
      rw [show π ∪ insert f B1.1 = insert f (π.erase f ∪ B1.1) by
        ext x; simp only [mem_union, mem_insert, mem_erase]
        constructor
        · rintro (h | rfl | h)
          · by_cases hx : x = f
            · exact Or.inl hx
            · exact Or.inr (Or.inl ⟨hx, h⟩)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr h)
        · rintro (rfl | ⟨-, h⟩ | h)
          · exact Or.inl hf
          · exact Or.inl h
          · exact Or.inr (Or.inr h)]
      refine pp_insert hc (hπ.1 f hf) ?_
      rw [cov_union]
      refine disjoint_union_right.2 ⟨disjoint_left.2 fun x hxf hx => ?_,
        disjoint_left.2 fun x hxf hx => ?_⟩
      · obtain ⟨g, hg, hxg⟩ := mem_cov.1 hx
        obtain ⟨hgf, hgπ⟩ := mem_erase.1 hg
        exact disjoint_left.1 (hπ.2 g hgπ f hf hgf) hxg hxf
      · obtain ⟨g, hg, hxg⟩ := mem_cov.1 hx
        exact (mem_sdiff.1 (br_blocks hB1 g hg hxg)).2 hxf
    · -- a fresh block through `v`
      have hfreeW : W.card - q * π.card ≤ (W \ cov π).card := by
        have := card_sdiff_ge W (cov π); rwa [card_cov hπ] at this
      have hroom' : q * π.card + q * ht q (node v ch) W ≤ W.card := by rw [← mul_add]; exact hroom
      have hqht : q ≤ q * ht q (node v ch) W := by
        have := Nat.mul_le_mul_left q hht; rwa [mul_one] at this
      have hvfree : v ∈ W \ cov π := mem_sdiff.2 ⟨hvW, hvπ⟩
      have hcard : q - 1 ≤ ((W \ cov π).erase v).card := by
        rw [card_erase_of_mem hvfree]; omega
      obtain ⟨S, hS, hSc⟩ := exists_subset_card_eq hcard
      have hvS : v ∉ S := fun h => (mem_erase.1 (hS h)).1 rfl
      set e := insert v S
      have hesub : e ⊆ W \ cov π := insert_subset hvfree (hS.trans (erase_subset _ _))
      have hec : e.card = q := by rw [card_insert_of_notMem hvS, hSc]; omega
      have heb : e ∈ blocks q W v :=
        mem_blocks.2 ⟨hesub.trans sdiff_subset, hec, mem_insert_self _ _⟩
      have hed : Disjoint e (cov π) := disjoint_left.2 fun x hx => (mem_sdiff.1 (hesub hx)).2
      have hhc := ht_child (ch := ch) heb
      obtain ⟨B1, hB1, hc⟩ := exists_branch hq (ch e) (W \ e) π (hch e heb) hπ
        (fun g hg x hx => mem_sdiff.2 ⟨hπW g hg hx, fun hxe =>
          disjoint_left.1 hed hxe (sub_cov hg hx)⟩)
        (by
          rw [card_sdiff_of_subset (hesub.trans sdiff_subset), hec]
          have : q * (π.card + ht q (ch e) (W \ e)) + q ≤ q * (π.card + ht q (node v ch) W) := by
            have h1 : π.card + ht q (ch e) (W \ e) + 1 ≤ π.card + ht q (node v ch) W := by omega
            calc q * (π.card + ht q (ch e) (W \ e)) + q
                = q * (π.card + ht q (ch e) (W \ e) + 1) := by ring
              _ ≤ _ := Nat.mul_le_mul_left _ h1
          omega)
      refine ⟨(insert e B1.1, B1.2), mem_br_node.2 ⟨e, heb, B1, hB1, rfl⟩, ?_⟩
      unfold Compat
      rw [show π ∪ insert e B1.1 = insert e (π ∪ B1.1) by
        ext x; simp only [mem_union, mem_insert]; tauto]
      refine pp_insert hc hec ?_
      rw [cov_union]
      refine disjoint_union_right.2 ⟨hed, disjoint_left.2 fun x hxe hx => ?_⟩
      obtain ⟨g, hg, hxg⟩ := mem_cov.1 hx
      exact (mem_sdiff.1 (br_blocks hB1 g hg hxg)).2 hxe

end

end QP

end SATurday.ProofComplexity
