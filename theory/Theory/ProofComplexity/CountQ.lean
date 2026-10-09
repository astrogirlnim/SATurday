import Theory.ProofComplexity.QLevel
import Theory.ProofComplexity.Designs
import Theory.ProofComplexity.PHPFrege
import Mathlib.Combinatorics.Colex

/-!
# Count_q is hard for bounded depth Frege with Count_p axioms (Ladder Rung R4, 1D.2)

Beame–Impagliazzo–Krajíček–Pitassi–Pudlák 1994 and Buss–Impagliazzo–Krajíček–Pudlák–Razborov–Sgall
1997, via designs. `countqCNF q N` says that the `q`-subsets of `[N]` chosen by the variables
form a partition of `[N]` (cover clauses and conflict clauses); it is unsatisfiable for
`q ∤ N` (`countq_unsat`). The Count_p instances used as axioms are valid (`countSeq_valid`).

* `countq_clauseHit`: at any q-partition restriction with room, the clauses of `countqCNF` are
  hit by the variable trees.
* `countp_lines`: below a restriction whose free part carries a large design, no Count_p
  instance line of the proof has a false branch (`count_mass_false`).

LOG: R4 CountQ module (Count_q lower bound with Count_p axioms)
-/

namespace SATurday.ProofComplexity

namespace QP

open Finset

noncomputable section

open Classical

/-! ## The counting principle -/

/-- The variable of a block. -/
def qv (e : Finset ℕ) : ℕ := Finset.equivBitIndices.symm e

/-- The block of a variable. -/
def vxq : ℕ → Finset ℕ := Finset.equivBitIndices

theorem vxq_qv (e : Finset ℕ) : vxq (qv e) = e := Finset.equivBitIndices.apply_symm_apply e

theorem qv_inj {e f : Finset ℕ} (h : qv e = qv f) : e = f := by
  rw [← vxq_qv e, h, vxq_qv]

/-- Point `i` is covered by a chosen block. -/
def coverClause (q N i : ℕ) : Clause := (blocks q (range N) i).image fun e => ⟨qv e, true⟩

/-- Two overlapping blocks are not both chosen. -/
def confClause (e e' : Finset ℕ) : Clause := {⟨qv e, false⟩, ⟨qv e', false⟩}

def confBlocks (q N : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((range N).powersetCard q ×ˢ (range N).powersetCard q).filter fun ee =>
    ee.1 ≠ ee.2 ∧ ¬ Disjoint ee.1 ee.2

/-- `Count_q^N`: the chosen `q`-subsets of `[N]` partition `[N]`. -/
def countqCNF (q N : ℕ) : CNF :=
  (range N).image (coverClause q N) ∪ (confBlocks q N).image fun ee => confClause ee.1 ee.2

theorem countq_unsat {q N : ℕ} (hN : ¬ q ∣ N) : ¬ Satisfiable (countqCNF q N) := by
  rintro ⟨a, ha⟩
  set P := ((range N).powersetCard q).filter fun e => a (qv e) = true
  have hcov : ∀ i < N, ∃ e ∈ P, i ∈ e := by
    intro i hi
    obtain ⟨l, hl, hsat⟩ := ha (coverClause q N i)
      (mem_union.2 (Or.inl (mem_image.2 ⟨i, mem_range.2 hi, rfl⟩)))
    obtain ⟨e, he, rfl⟩ := mem_image.1 hl
    obtain ⟨hsub, hc, hie⟩ := mem_blocks.1 he
    exact ⟨e, mem_filter.2 ⟨mem_powersetCard.2 ⟨hsub, hc⟩, hsat⟩, hie⟩
  have hdisj : ∀ e ∈ P, ∀ f ∈ P, e ≠ f → Disjoint e f := by
    intro e he f hf hef
    by_contra hd
    obtain ⟨he1, he2⟩ := mem_filter.1 he
    obtain ⟨hf1, hf2⟩ := mem_filter.1 hf
    obtain ⟨l, hl, hsat⟩ := ha (confClause e f)
      (mem_union.2 (Or.inr (mem_image.2 ⟨(e, f), mem_filter.2 ⟨mem_product.2 ⟨he1, hf1⟩,
        hef, hd⟩, rfl⟩)))
    simp only [confClause, mem_insert, mem_singleton] at hl
    rcases hl with rfl | rfl
    · simp [litSat, he2] at hsat
    · simp [litSat, hf2] at hsat
  have hU : range N = P.biUnion id := by
    ext i
    simp only [mem_biUnion, id]
    constructor
    · intro hi; exact hcov i (mem_range.1 hi)
    · rintro ⟨e, he, hie⟩
      exact (mem_powersetCard.1 (mem_filter.1 he).1).1 hie
  have hcard : N = q * P.card := by
    have := congrArg card hU
    rw [card_range, card_biUnion (fun e he f hf hef => by simpa using hdisj e he f hf hef)] at this
    rw [this]; simp only [id]
    rw [sum_congr rfl fun e he => (mem_powersetCard.1 (mem_filter.1 he).1).2, sum_const,
      smul_eq_mul, Nat.mul_comm]
  exact hN ⟨_, hcard⟩

/-! ## Validity of the Count_p axioms -/

theorem countSeq_valid {p M : ℕ} (hM : ¬ p ∣ M) (ψ : Finset ℕ → Fm) (r : ℕ)
    (a : Assignment) : SeqSat r a (countSeq p M ψ) := by
  intro hall
  exfalso
  set P := (cntG p M).filter fun g => (ψ g).eval r a = true
  have hcov : ∀ i < M, ∃ g ∈ P, i ∈ g := by
    intro i hi
    have h := hall (covF p M ψ i)
      (List.mem_append_left _ (List.mem_map.2 ⟨i, by simpa using hi, rfl⟩))
    rw [covF, Fm.eval_or] at h
    obtain ⟨χ, hχ, hχt⟩ := h
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hχ
    obtain ⟨hgG, hig⟩ := mem_filter.1 (mem_toList.1 hg)
    exact ⟨g, mem_filter.2 ⟨hgG, hχt⟩, hig⟩
  have hdisj : ∀ g ∈ P, ∀ g' ∈ P, g ≠ g' → Disjoint g g' := by
    intro g hg g' hg' hne
    by_contra hd
    obtain ⟨hg1, hg2⟩ := mem_filter.1 hg
    obtain ⟨hg1', hg2'⟩ := mem_filter.1 hg'
    have h := hall (confF ψ g g') (List.mem_append_right _ (List.mem_map.2
      ⟨(g, g'), mem_toList.2 (mem_filter.2 ⟨mem_product.2 ⟨hg1, hg1'⟩, hne, hd⟩), rfl⟩))
    rw [confF, Fm.eval_or] at h
    obtain ⟨χ, hχ, hχt⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
    rcases hχ with rfl | rfl
    · rw [Fm.eval_neg] at hχt; rw [hχt] at hg2; exact Bool.noConfusion hg2
    · rw [Fm.eval_neg] at hχt; rw [hχt] at hg2'; exact Bool.noConfusion hg2'
  have hU : range M = P.biUnion id := by
    ext i
    simp only [mem_biUnion, id]
    constructor
    · intro hi; exact hcov i (mem_range.1 hi)
    · rintro ⟨g, hg, hig⟩
      exact (mem_powersetCard.1 (mem_filter.1 hg).1).1 hig
  have hcard : M = p * P.card := by
    have := congrArg card hU
    rw [card_range, card_biUnion (fun g hg g' hg' hne => by simpa using hdisj g hg g' hg' hne)]
      at this
    rw [this]
    calc ∑ u ∈ P, (id u).card = ∑ u ∈ P, p :=
          sum_congr rfl fun g hg => (mem_powersetCard.1 (mem_filter.1 hg).1).2
      _ = p * P.card := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
  exact hM ⟨_, hcard⟩

/-! ## Hitting the clauses of Count_q -/

section Hit

variable {q : ℕ} {U : Finset ℕ} {vx : ℕ → Finset ℕ} {ρ : Finset (Finset ℕ)} {k : ℕ} {E : QSet}

theorem pp_free_union {α : Finset (Finset ℕ)} (hρ : PP q ρ) (hα : PP q α)
    (hαf : ∀ f ∈ α, f ⊆ free U ρ) : PP q (α ∪ ρ) :=
  pp_union hα hρ fun f hf g hg _ => disj_free_blocks (hαf f hf) g hg

theorem var_one {v : ℕ} (hG : SGood q U vx ρ k E (.var v)) (he : vx v ∈ U.powersetCard q)
    (hρ : PP q ρ) (hroom : q * (3 * k) ≤ (free U ρ).card) {π : Finset (Finset ℕ)}
    (hπf : ∀ f ∈ π, f ⊆ free U ρ) (hπp : PP q π) (hπk : π.card ≤ 2 * k)
    (hin : vx v ∈ π ∨ vx v ∈ ρ) : ∃ γ ∈ (E (.var v)).1, Compat q γ π := by
  obtain ⟨α, hα, hc⟩ := qcov2 hG hroom hπf hπp hπk
  rcases mem_union.1 hα with h1 | h0
  · exact ⟨α, h1, hc⟩
  · exfalso
    have hl := hG.loc; simp only [QLoc] at hl
    obtain ⟨-, hz⟩ := hl he
    obtain ⟨hαf, -, -⟩ := hG.mem α hα
    refine hz α h0 (pp_mono (pp_free_union (U := U) hρ hc (fun f hf => ?_)) ?_)
    · rcases mem_union.1 hf with hf | hf
      · exact hαf f hf
      · exact hπf f hf
    · intro f hf
      simp only [mem_insert, mem_union] at hf ⊢
      rcases hf with rfl | hf | hf
      · rcases hin with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · exact Or.inl (Or.inl hf)
      · exact Or.inr hf

theorem var_zero {v : ℕ} (hG : SGood q U vx ρ k E (.var v)) (he : vx v ∈ U.powersetCard q)
    (hroom : q * (3 * k) ≤ (free U ρ).card) {π : Finset (Finset ℕ)}
    (hπf : ∀ f ∈ π, f ⊆ free U ρ) (hπp : PP q π) (hπk : π.card ≤ 2 * k) (heρ : vx v ∉ ρ)
    (hbad : ∀ α, (∀ f ∈ α, f ⊆ free U ρ) → Compat q α π → vx v ∈ α → False) :
    ∃ γ ∈ (E (.var v)).2, Compat q γ π := by
  obtain ⟨α, hα, hc⟩ := qcov2 hG hroom hπf hπp hπk
  rcases mem_union.1 hα with h1 | h0
  · exfalso
    have hl := hG.loc; simp only [QLoc] at hl
    obtain ⟨ho, -⟩ := hl he
    have := ho α h1
    rcases mem_union.1 this with h | h
    · exact hbad α (hG.mem α hα).1 hc h
    · exact heρ h
  · exact ⟨α, h0, hc⟩

theorem lit_sub {C : Clause} {l : Literal} (hl : l ∈ C) : litFm l ∈ subs (clauseFm C) :=
  sub_or (self_mem_subs _) (List.mem_map.2 ⟨l, mem_toList.2 hl, rfl⟩)

theorem litFm_pos (x : ℕ) : litFm ⟨x, true⟩ = .var x := by simp [litFm]

theorem litFm_neg (x : ℕ) : litFm ⟨x, false⟩ = .neg (.var x) := by simp [litFm]

/-- **Clause hits for Count_q**: with room, every clause of `countqCNF` is hit. -/
theorem countq_clauseHit {N : ℕ} (hq : 1 ≤ q) (hρ : PP q ρ) (hρU : InU (range N) ρ) (hk : 1 ≤ k)
    (hroom : q * (3 * k) ≤ (free (range N) ρ).card) :
    SClauseHit q (range N) vxq ρ k E (countqCNF q N) := by
  intro C hC hgood β hβf hβp hβk
  have hβk2 : β.card ≤ 2 * k := by omega
  have hfreeU : free (range N) ρ ⊆ range N := sdiff_subset
  rcases mem_union.1 hC with hC | hC
  · obtain ⟨i, hi, rfl⟩ := mem_image.1 hC
    -- a block through `i` inside `ρ ∪ π` for a small `π ⊇ β`
    obtain ⟨e, heb, π, hβπ, hπf, hπp, hπk, hin⟩ : ∃ e ∈ blocks q (range N) i, ∃ π,
        β ⊆ π ∧ (∀ f ∈ π, f ⊆ free (range N) ρ) ∧ PP q π ∧ π.card ≤ 2 * k ∧ (e ∈ π ∨ e ∈ ρ) := by
      by_cases hiρ : i ∈ cov ρ
      · obtain ⟨f, hf, hif⟩ := mem_cov.1 hiρ
        exact ⟨f, mem_blocks.2 ⟨hρU f hf, hρ.1 f hf, hif⟩, β, subset_rfl, hβf, hβp, hβk2,
          Or.inr hf⟩
      · by_cases hiβ : i ∈ cov β
        · obtain ⟨f, hf, hif⟩ := mem_cov.1 hiβ
          exact ⟨f, mem_blocks.2 ⟨(hβf f hf).trans hfreeU, hβp.1 f hf, hif⟩, β, subset_rfl, hβf,
            hβp, hβk2, Or.inl hf⟩
        · have hifree : i ∈ free (range N) ρ \ cov β :=
            mem_sdiff.2 ⟨mem_sdiff.2 ⟨mem_range.2 (mem_range.1 hi), hiρ⟩, hiβ⟩
          have hcard : q - 1 ≤ ((free (range N) ρ \ cov β).erase i).card := by
            rw [card_erase_of_mem hifree]
            have h1 := card_sdiff_ge (free (range N) ρ) (cov β)
            rw [card_cov hβp] at h1
            have h2 : q * β.card ≤ q * k := Nat.mul_le_mul_left _ hβk
            have h3 : q * k ≤ q * (3 * k) - q * k := by
              rw [← Nat.mul_sub]; exact Nat.mul_le_mul_left _ (by omega)
            have h4 : q ≤ q * k := by have := Nat.mul_le_mul_left q hk; rwa [mul_one] at this
            omega
          obtain ⟨S, hS, hSc⟩ := exists_subset_card_eq hcard
          have hiS : i ∉ S := fun h => (mem_erase.1 (hS h)).1 rfl
          set e := insert i S
          have hesub : e ⊆ free (range N) ρ \ cov β :=
            insert_subset hifree (hS.trans (erase_subset _ _))
          have hec : e.card = q := by rw [card_insert_of_notMem hiS, hSc]; omega
          have hed : Disjoint e (cov β) := disjoint_left.2 fun x hx => (mem_sdiff.1 (hesub hx)).2
          have heβ : e ∉ β := fun h =>
            disjoint_left.1 hed (mem_insert_self _ _) (sub_cov h (mem_insert_self _ _))
          refine ⟨e, mem_blocks.2 ⟨fun x hx => hfreeU (mem_sdiff.1 (hesub hx)).1, hec,
            mem_insert_self _ _⟩, insert e β, subset_insert _ _, fun f hf => ?_,
            pp_insert hβp hec hed, by rw [card_insert_of_notMem heβ]; omega,
            Or.inl (mem_insert_self _ _)⟩
          rcases mem_insert.1 hf with rfl | hf
          · exact fun x hx => (mem_sdiff.1 (hesub hx)).1
          · exact hβf f hf
    have hl : (⟨qv e, true⟩ : Literal) ∈ coverClause q N i := mem_image.2 ⟨e, heb, rfl⟩
    have hG : SGood q (range N) vxq ρ k E (.var (qv e)) := by
      have := hgood _ (lit_sub hl); rwa [litFm_pos] at this
    have he : vxq (qv e) ∈ (range N).powersetCard q := by
      rw [vxq_qv]; exact mem_powersetCard.2 ⟨(mem_blocks.1 heb).1, (mem_blocks.1 heb).2.1⟩
    obtain ⟨γ, hγ, hc⟩ := var_one hG he hρ hroom hπf hπp hπk (by rw [vxq_qv]; exact hin)
    exact ⟨_, hl, γ, by rw [litFm_pos]; exact hγ, compat_mono hc subset_rfl hβπ⟩
  · obtain ⟨⟨e, e'⟩, hee, rfl⟩ := mem_image.1 hC
    obtain ⟨hp, hne, hov⟩ := mem_filter.1 hee
    obtain ⟨he1, he2⟩ := mem_product.1 hp
    simp only at hne hov he1 he2
    have hl1 : (⟨qv e, false⟩ : Literal) ∈ confClause e e' := by simp [confClause]
    have hl2 : (⟨qv e', false⟩ : Literal) ∈ confClause e e' := by simp [confClause]
    have hGn1 : SGood q (range N) vxq ρ k E (.neg (.var (qv e))) := by
      have := hgood _ (lit_sub hl1); rwa [litFm_neg] at this
    have hGn2 : SGood q (range N) vxq ρ k E (.neg (.var (qv e'))) := by
      have := hgood _ (lit_sub hl2); rwa [litFm_neg] at this
    have hG1 : SGood q (range N) vxq ρ k E (.var (qv e)) := by
      have := hgood _ (sub_neg (litFm_neg (qv e) ▸ lit_sub hl1)); exact this
    have hG2 : SGood q (range N) vxq ρ k E (.var (qv e')) := by
      have := hgood _ (sub_neg (litFm_neg (qv e') ▸ lit_sub hl2)); exact this
    have hu1 : vxq (qv e) ∈ (range N).powersetCard q := by rw [vxq_qv]; exact he1
    have hu2 : vxq (qv e') ∈ (range N).powersetCard q := by rw [vxq_qv]; exact he2
    have fin1 : ∀ γ ∈ (E (.var (qv e))).2, Compat q γ β →
        ∃ l ∈ confClause e e', ∃ γ ∈ (E (litFm l)).1, Compat q γ β := fun γ hγ hc =>
      ⟨_, hl1, γ, by rw [litFm_neg, (sgood_neg hGn1).1]; exact hγ, hc⟩
    have fin2 : ∀ γ ∈ (E (.var (qv e'))).2, Compat q γ β →
        ∃ l ∈ confClause e e', ∃ γ ∈ (E (litFm l)).1, Compat q γ β := fun γ hγ hc =>
      ⟨_, hl2, γ, by rw [litFm_neg, (sgood_neg hGn2).1]; exact hγ, hc⟩
    obtain ⟨x, hxe, hxe'⟩ := not_disjoint_iff.1 hov
    -- a block meeting the restriction outside it is false
    have notfree : ∀ f : Finset ℕ, (∃ y ∈ f, y ∈ cov ρ) → ∀ α : Finset (Finset ℕ),
        (∀ g ∈ α, g ⊆ free (range N) ρ) → f ∈ α → False := by
      rintro f ⟨y, hyf, hyρ⟩ α hαf hfα
      exact (mem_sdiff.1 (hαf f hfα hyf)).2 hyρ
    by_cases heρ : e ∈ ρ
    · have he'ρ : e' ∉ ρ := fun h => hne (pp_eq_of_mem hρ heρ h hxe hxe')
      obtain ⟨γ, hγ, hc⟩ := var_zero hG2 hu2 hroom hβf hβp hβk2 (by rwa [vxq_qv])
        (fun α hαf _ h => notfree e' ⟨x, hxe', sub_cov heρ hxe⟩ α hαf (by rwa [vxq_qv] at h))
      exact fin2 γ hγ hc
    · by_cases he'ρ : e' ∈ ρ
      · obtain ⟨γ, hγ, hc⟩ := var_zero hG1 hu1 hroom hβf hβp hβk2 (by rwa [vxq_qv])
          (fun α hαf _ h => notfree e ⟨x, hxe, sub_cov he'ρ hxe'⟩ α hαf (by rwa [vxq_qv] at h))
        exact fin1 γ hγ hc
      · by_cases hef : ∃ y ∈ e, y ∈ cov ρ
        · obtain ⟨γ, hγ, hc⟩ := var_zero hG1 hu1 hroom hβf hβp hβk2 (by rwa [vxq_qv])
            (fun α hαf _ h => notfree e hef α hαf (by rwa [vxq_qv] at h))
          exact fin1 γ hγ hc
        · by_cases he'f : ∃ y ∈ e', y ∈ cov ρ
          · obtain ⟨γ, hγ, hc⟩ := var_zero hG2 hu2 hroom hβf hβp hβk2 (by rwa [vxq_qv])
              (fun α hαf _ h => notfree e' he'f α hαf (by rwa [vxq_qv] at h))
            exact fin2 γ hγ hc
          · obtain ⟨α, hα, hc⟩ := qcov2 hG1 hroom hβf hβp hβk2
            rcases mem_union.1 hα with h1 | h0
            · have hl := hG1.loc; simp only [QLoc] at hl
              have heα : e ∈ α := by
                have := (hl hu1).1 α h1
                rw [vxq_qv] at this
                rcases mem_union.1 this with h | h
                · exact h
                · exact absurd h heρ
              obtain ⟨hαf, hαp, hαk⟩ := hG1.mem α hα
              obtain ⟨huf, hup, huk⟩ := qunion_small hαf hβf hc hαk hβk
              obtain ⟨γ, hγ, hcγ⟩ := var_zero hG2 hu2 hroom huf hup huk (by rwa [vxq_qv])
                (fun α' _ hc' h => by
                  rw [vxq_qv] at h
                  exact hne (pp_eq_of_mem hc' (mem_union.2 (Or.inr (mem_union.2 (Or.inl heα))))
                    (mem_union.2 (Or.inl h)) hxe hxe'))
              exact fin2 γ hγ (qcompat_right hcγ)
            · exact fin1 α h0 hc

end Hit

/-! ## Count_p instance lines have no false branch -/

open QT

theorem countp_lines {p : ℕ} [hp : Fact p.Prime] {q : ℕ} (hpq : ¬ p ∣ q) (hq : 2 ≤ q)
    {U : Finset ℕ} {vx : ℕ → Finset ℕ} {ρ : Finset (Finset ℕ)} {k : ℕ} {ET : Fm → QT Bool}
    {S : Seq} (hS : CountInst p S) (hG : ∀ φ ∈ subs (lineF S), TGood q U vx ρ k ET φ) {i : ℕ}
    (hi1 : 4 * k + 1 ≤ 2 ^ i) (hi2 : (p + q) ^ i * q + q * k ≤ (free U ρ).card) :
    zeros q (ET (lineF S)) (free U ρ) = ∅ := by
  obtain ⟨M, ψ, hM, rfl⟩ := hS
  set W := free U ρ
  set G := cntG p M
  by_contra hne
  obtain ⟨α, hα⟩ := nonempty_iff_ne_empty.2 hne
  have hGl := hG _ (self_mem_subs _)
  obtain ⟨hαp, hαW, hαk⟩ := br_props _ _ _ (mem_zeros.1 hα)
  simp only at hαp hαW hαk
  have hαk' : α.card ≤ k := hαk.trans hGl.ht
  have hlx : ∀ χ ∈ dsOf (countSeq p M ψ), ∀ γ ∈ ones q (ET χ) W, ¬ Compat q α γ := by
    have hl := hGl.loc; simp only [lineF, QLoc, setsOf] at hl; exact hl.2 α hα
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  -- subformulas
  have hneg : ∀ φ ∈ (countSeq p M ψ).1, Fm.neg φ ∈ subs (lineF (countSeq p M ψ)) := fun φ hφ =>
    sub_or (self_mem_subs _) (mem_dsOf.2 (Or.inl ⟨φ, hφ, rfl⟩))
  have hcovΓ : ∀ i < M, covF p M ψ i ∈ (countSeq p M ψ).1 := fun i hi =>
    List.mem_append_left _ (List.mem_map.2 ⟨i, by simpa using hi, rfl⟩)
  have hconfΓ : ∀ gg ∈ confPairs p M, confF ψ gg.1 gg.2 ∈ (countSeq p M ψ).1 := fun gg hgg =>
    List.mem_append_right _ (List.mem_map.2 ⟨gg, mem_toList.2 hgg, rfl⟩)
  have hψsub : ∀ g ∈ G, ψ g ∈ subs (lineF (countSeq p M ψ)) := by
    intro g hg
    obtain ⟨hgM, hgc⟩ := mem_powersetCard.1 hg
    obtain ⟨j, hj⟩ : g.Nonempty := by rw [← card_pos, hgc]; omega
    have hjM := mem_range.1 (hgM hj)
    exact sub_or (sub_neg (hneg _ (hcovΓ j hjM)))
      (List.mem_map.2 ⟨g, mem_toList.2 (mem_filter.2 ⟨hg, hj⟩), rfl⟩)
  -- `α` kills the false branches of the axiom antecedents
  have hAz : ∀ j < M, ∀ γ ∈ zeros q (ET (covF p M ψ j)) W, ¬ Compat q α γ := by
    intro j hj γ hγ
    have hGn := hG _ (hneg _ (hcovΓ j hj))
    have hln := hGn.loc; simp only [QLoc, setsOf] at hln
    refine hlx _ (mem_dsOf.2 (Or.inl ⟨_, hcovΓ j hj, rfl⟩)) γ ?_
    have := congrArg Prod.fst hln; simp only at this; rw [this]; exact hγ
  have hCz : ∀ gg ∈ confPairs p M, ∀ γ ∈ zeros q (ET (confF ψ gg.1 gg.2)) W, ¬ Compat q α γ := by
    intro gg hgg γ hγ
    have hGn := hG _ (hneg _ (hconfΓ gg hgg))
    have hln := hGn.loc; simp only [QLoc, setsOf] at hln
    refine hlx _ (mem_dsOf.2 (Or.inl ⟨_, hconfΓ gg hgg, rfl⟩)) γ ?_
    have := congrArg Prod.fst hln; simp only at this; rw [this]; exact hγ
  -- the design
  have hW' : (p + q) ^ i * q ≤ (W \ cov α).card := by
    have h1 := card_sdiff_ge W (cov α)
    rw [card_cov hαp] at h1
    have : q * α.card ≤ q * k := Nat.mul_le_mul_left _ hαk'
    omega
  obtain ⟨ds'⟩ := exists_design hpq hq (W \ cov α) i hW'
  let ds := padD hαp hαW ds'
  have hsa : ds.s α = 1 := by
    show pad α ds'.s α = 1
    rw [pad_self, ds'.empty]
  -- the trees
  let T : Finset ℕ → QT Bool := fun g => if g ∈ G then ET (ψ g) else QT.leaf false
  let A : ℕ → QT Bool := fun j => if j < M then ET (covF p M ψ j) else QT.leaf false
  let C : Finset ℕ → Finset ℕ → QT Bool := fun g g' =>
    if (g, g') ∈ confPairs p M then ET (confF ψ g g') else QT.leaf false
  have hleaf : WF q (QT.leaf false : QT Bool) W ∧ ht q (QT.leaf false : QT Bool) W ≤ k :=
    ⟨trivial, by simp [ht]⟩
  refine count_mass_false ds hαp hαW hsa (h := k) hM T A C (fun g => ?_) (fun j => ?_)
    (fun g g' => ?_) (fun j hj B hB hcB => ?_) (fun g hg g' hg' hne hov γ hγ hcγ => ?_)
    (by have : 4 * k ≤ 2 ^ i - 1 := by omega
        omega)
  · simp only [T]; split_ifs with h
    · exact ⟨(hG _ (hψsub g h)).wf, (hG _ (hψsub g h)).ht⟩
    · exact hleaf
  · simp only [A]; split_ifs with h
    · exact ⟨(hG _ (sub_neg (hneg _ (hcovΓ j h)))).wf, (hG _ (sub_neg (hneg _ (hcovΓ j h)))).ht⟩
    · exact hleaf
  · simp only [C]; split_ifs with h
    · exact ⟨(hG _ (sub_neg (hneg _ (hconfΓ _ h)))).wf, (hG _ (sub_neg (hneg _ (hconfΓ _ h)))).ht⟩
    · exact hleaf
  · simp only [A, if_pos hj] at hB
    cases hb : B.2
    · exfalso
      exact hAz j hj B.1 (mem_zeros.2 (by rw [← hb]; exact hB)) hcB
    · have hGc := hG _ (sub_neg (hneg _ (hcovΓ j hj)))
      have hlc := hGc.loc; simp only [covF, QLoc, setsOf] at hlc
      obtain ⟨χ, hχ, β, hβ, hβB⟩ := hlc.1 B.1 (mem_ones.2 (by rw [← hb]; exact hB))
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hχ
      obtain ⟨hgG, hjg⟩ := mem_filter.1 (mem_toList.1 hg)
      refine ⟨g, hgG, hjg, (β, true), ?_, rfl, hβB⟩
      simp only [T]; rw [if_pos hgG]; exact mem_ones.1 hβ
  · have hpair : (g, g') ∈ confPairs p M := mem_filter.2 ⟨mem_product.2 ⟨hg, hg'⟩, hne, hov⟩
    simp only [C, if_pos hpair] at hγ
    cases hb : γ.2
    · exfalso
      exact hCz _ hpair γ.1 (mem_zeros.2 (by rw [← hb]; exact hγ)) hcγ
    · have hGc := hG _ (sub_neg (hneg _ (hconfΓ _ hpair)))
      have hlc := hGc.loc; simp only [confF, QLoc, setsOf] at hlc
      obtain ⟨χ, hχ, δ, hδ, hδγ⟩ := hlc.1 γ.1 (mem_ones.2 (by rw [← hb]; exact hγ))
      have hsubc : confF ψ g g' ∈ subs (lineF (countSeq p M ψ)) := sub_neg (hneg _ (hconfΓ _ hpair))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hχ
      rcases hχ with rfl | rfl
      · have hGn := hG (Fm.neg (ψ g)) (sub_or hsubc (by simp))
        have hln := hGn.loc; simp only [QLoc, setsOf] at hln
        have : ones q (ET (Fm.neg (ψ g))) W = zeros q (ET (ψ g)) W := congrArg Prod.fst hln
        rw [this] at hδ
        refine ⟨(δ, false), Or.inl ?_, rfl, hδγ⟩
        simp only [T]; rw [if_pos (show g ∈ G from hg)]; exact mem_zeros.1 hδ
      · have hGn := hG (Fm.neg (ψ g')) (sub_or hsubc (by simp))
        have hln := hGn.loc; simp only [QLoc, setsOf] at hln
        have : ones q (ET (Fm.neg (ψ g'))) W = zeros q (ET (ψ g')) W := congrArg Prod.fst hln
        rw [this] at hδ
        refine ⟨(δ, false), Or.inr ?_, rfl, hδγ⟩
        simp only [T]; rw [if_pos (show g' ∈ G from hg')]; exact mem_zeros.1 hδ

/-! ## Shallow extensions of restrictions -/

theorem exists_ext_q {q : ℕ} (hq : 1 ≤ q) {U : Finset ℕ} {ρ0 : Finset (Finset ℕ)} (hρ0 : PP q ρ0)
    (hU0 : InU U ρ0) : ∀ j, q * (ρ0.card + j) ≤ U.card → ∃ ρ, ρ ∈ Rq q U ρ0 (ρ0.card + j)
  | 0, _ => ⟨ρ0, mem_Rq.2 ⟨hU0, hρ0, subset_rfl, rfl⟩⟩
  | j + 1, h => by
    obtain ⟨ρ, hρ⟩ := exists_ext_q hq hρ0 hU0 j (le_trans (Nat.mul_le_mul_left _ (by omega)) h)
    obtain ⟨hρU, hρp, h0, hc⟩ := mem_Rq.1 hρ
    have hfc := card_free hρp hρU
    have : q ≤ (free U ρ).card := by
      rw [hfc, hc]
      have : q * (ρ0.card + j) + q ≤ q * (ρ0.card + (j + 1)) := by ring_nf; omega
      omega
    obtain ⟨e, he, hec⟩ := exists_subset_card_eq this
    have hed : Disjoint e (cov ρ) := disjoint_left.2 fun x hx => (mem_sdiff.1 (he hx)).2
    have heρ : e ∉ ρ := by
      intro h
      obtain ⟨x, hx⟩ : e.Nonempty := by rw [← card_pos, hec]; omega
      exact disjoint_left.1 hed hx (sub_cov h hx)
    refine ⟨insert e ρ, mem_Rq.2 ⟨fun f hf => ?_, pp_insert hρp hec hed,
      h0.trans (subset_insert _ _), by rw [card_insert_of_notMem heρ, hc]; omega⟩⟩
    rcases mem_insert.1 hf with rfl | hf
    · exact he.trans sdiff_subset
    · exact hρU f hf

theorem bad_card_q {q : ℕ} (hq : 1 ≤ q) {U : Finset ℕ} {ρ0 : Finset (Finset ℕ)} {m s w C : ℕ}
    (Ds : List (List (Finset (Finset ℕ))))
    (hDs : ∀ D ∈ Ds, (∀ t ∈ D, InU U t) ∧ ∀ t ∈ D, t.card ≤ w)
    (hC : q * w + (U.card - q * (m + (s + 1))) ≤ C) :
    ((Rq q U ρ0 m).filter fun ρ => ∃ D ∈ Ds, s + 1 ≤ cdepth q U D ρ).card *
        (m + 1 - ρ0.card) ^ (s + 1) ≤
      Ds.length * ((Rq q U ρ0 m).card *
        ((U.card - q * m).choose q * (2 * (w * C ^ (q * q)))) ^ (s + 1)) := by
  induction Ds with
  | nil => simp
  | cons D Ds ih =>
    have hD := hDs D (by simp)
    have h1 := qswitching_ratio hD.1 hD.2 hq ρ0 m (s + 1) C hC
    have h2 := ih fun D' hD' => hDs D' (by simp [hD'])
    have hsub : ((Rq q U ρ0 m).filter fun ρ => ∃ D' ∈ D :: Ds, s + 1 ≤ cdepth q U D' ρ) ⊆
        ((Rq q U ρ0 m).filter fun ρ => s + 1 ≤ cdepth q U D ρ) ∪
          ((Rq q U ρ0 m).filter fun ρ => ∃ D' ∈ Ds, s + 1 ≤ cdepth q U D' ρ) := by
      intro ρ hρ
      simp only [mem_filter, mem_union, List.mem_cons] at hρ ⊢
      obtain ⟨hρ, D', hD', hd⟩ := hρ
      rcases hD' with rfl | hD'
      · exact Or.inl ⟨hρ, hd⟩
      · exact Or.inr ⟨hρ, D', hD', hd⟩
    calc _ ≤ (((Rq q U ρ0 m).filter fun ρ => s + 1 ≤ cdepth q U D ρ).card +
            ((Rq q U ρ0 m).filter fun ρ => ∃ D' ∈ Ds, s + 1 ≤ cdepth q U D' ρ).card) *
            (m + 1 - ρ0.card) ^ (s + 1) :=
          Nat.mul_le_mul_right _ ((card_le_card hsub).trans (card_union_le _ _))
      _ = _ := by rw [add_mul]
      _ ≤ _ := Nat.add_le_add h1 h2
      _ = _ := by simp only [List.length_cons]; ring

/-- **Union bound**: some extension makes every DNF in the list shallow. -/
theorem exists_shallow_ext_q {q : ℕ} (hq : 1 ≤ q) {U : Finset ℕ} {ρ0 : Finset (Finset ℕ)}
    (hρ0 : PP q ρ0) (hU0 : InU U ρ0) {m s w C : ℕ} (Ds : List (List (Finset (Finset ℕ))))
    (hDs : ∀ D ∈ Ds, (∀ t ∈ D, InU U t) ∧ ∀ t ∈ D, t.card ≤ w)
    (hm1 : ρ0.card ≤ m) (hm2 : q * m ≤ U.card)
    (hC : q * w + (U.card - q * (m + (s + 1))) ≤ C)
    (hineq : Ds.length * ((U.card - q * m).choose q * (2 * (w * C ^ (q * q)))) ^ (s + 1) <
      (m + 1 - ρ0.card) ^ (s + 1)) :
    ∃ ρ ∈ Rq q U ρ0 m, ∀ D ∈ Ds, cdepth q U D ρ ≤ s := by
  obtain ⟨ρ1, hρ1⟩ := exists_ext_q hq hρ0 hU0 (m - ρ0.card) (by rw [Nat.add_sub_cancel' hm1]; exact hm2)
  rw [Nat.add_sub_cancel' hm1] at hρ1
  have hpos : 0 < (Rq q U ρ0 m).card := card_pos.2 ⟨ρ1, hρ1⟩
  have hb := bad_card_q hq (ρ0 := ρ0) (m := m) Ds hDs hC
  set B := (Rq q U ρ0 m).filter fun ρ => ∃ D ∈ Ds, s + 1 ≤ cdepth q U D ρ
  have hlt : B.card < (Rq q U ρ0 m).card := by
    by_contra hge
    push Not at hge
    have : (Rq q U ρ0 m).card * (m + 1 - ρ0.card) ^ (s + 1) ≤
        (Rq q U ρ0 m).card * (Ds.length *
          ((U.card - q * m).choose q * (2 * (w * C ^ (q * q)))) ^ (s + 1)) :=
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

/-- **Levels**: under the counting inequalities, for every level `t ≤ T` there are a partial
q-partition with `m t` blocks and a tree evaluation of the formulas of depth `≤ t`. -/
theorem levels_q {q : ℕ} (hq : 1 ≤ q) {vx : ℕ → Finset ℕ} {Φ : List Fm}
    (hcl : ∀ φ ∈ Φ, (∀ ψ, φ = .neg ψ → ψ ∈ Φ) ∧ (∀ l, φ = .or l → ∀ ψ ∈ l, ψ ∈ Φ) ∧
      (∀ l, φ = .and l → ∀ ψ ∈ l, ψ ∈ Φ))
    (hmod : ∀ φ ∈ Φ, isMod φ = false) {N k s T : ℕ} (m : ℕ → ℕ) (hm0 : m 0 = 0)
    (hmono : ∀ t < T, m t ≤ m (t + 1)) (hmN : ∀ t ≤ T, q * m t ≤ N) (hk : 1 ≤ k)
    (hqs : q * s ≤ k)
    (hineq : ∀ t < T, (2 * Φ.length) * ((N - q * m (t + 1)).choose q *
      (2 * (k * (q * k + (N - q * m (t + 1))) ^ (q * q)))) ^ (s + 1) <
        (m (t + 1) + 1 - m t) ^ (s + 1)) :
    ∀ t ≤ T, ∃ ρ ET, PP q ρ ∧ InU (range N) ρ ∧ ρ.card = m t ∧
      ∀ φ ∈ Φ, φ.depth ≤ t → TGood q (range N) vx ρ k ET φ := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨∅, ET0 q (range N) vx, ⟨by simp, by simp⟩, by simp [InU], by simp [hm0],
      fun φ _ hd => tgood_ET0 hq hk φ (by omega)⟩
  | succ t ih =>
    intro ht
    obtain ⟨ρ, ET, hρ, hρU, hρc, hG⟩ := ih (by omega)
    set U := range N
    set Ds : List (List (Finset (Finset ℕ))) := Φ.map (fun φ => DorT q U ρ ET (orArgsAt t φ)) ++
      Φ.map (fun φ => DandT q U ρ ET (andArgsAt t φ)) with hDsdef
    have key : ∀ ψ ∈ Φ, ψ.depth ≤ t → ∀ x, x ∈ ones q (ET ψ) (free U ρ) ∨
        x ∈ zeros q (ET ψ) (free U ρ) → InU U x ∧ x.card ≤ k := by
      intro ψ hψ hd x hx
      have hB : ∃ b, (x, b) ∈ br q (ET ψ) (free U ρ) := by
        rcases hx with hx | hx
        · exact ⟨true, mem_ones.1 hx⟩
        · exact ⟨false, mem_zeros.1 hx⟩
      obtain ⟨b, hb⟩ := hB
      obtain ⟨-, hf, hc⟩ := br_props _ _ _ hb
      exact ⟨fun f hf' => (hf f hf').trans sdiff_subset, hc.trans (hG ψ hψ hd).ht⟩
    have hDs : ∀ D ∈ Ds, (∀ x ∈ D, InU U x) ∧ ∀ x ∈ D, x.card ≤ k := by
      intro D hD
      rcases List.mem_append.1 hD with hD | hD
      · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hD
        have : ∀ x ∈ DorT q U ρ ET (orArgsAt t φ), InU U x ∧ x.card ≤ k := by
          intro x hx
          obtain ⟨ψ, hψ, hxψ⟩ := mem_DorT.1 hx
          obtain ⟨l, rfl, hd, hψl⟩ := mem_orArgsAt hψ
          exact key ψ ((hcl _ hφ).2.1 l rfl ψ hψl) (by have := depth_child_or hψl; omega) x
            (Or.inl hxψ)
        exact ⟨fun x hx => (this x hx).1, fun x hx => (this x hx).2⟩
      · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hD
        have : ∀ x ∈ DandT q U ρ ET (andArgsAt t φ), InU U x ∧ x.card ≤ k := by
          intro x hx
          obtain ⟨ψ, hψ, hxψ⟩ := mem_DandT.1 hx
          obtain ⟨l, rfl, hd, hψl⟩ := mem_andArgsAt hψ
          exact key ψ ((hcl _ hφ).2.2 l rfl ψ hψl) (by have := depth_child_and hψl; omega) x
            (Or.inr hxψ)
        exact ⟨fun x hx => (this x hx).1, fun x hx => (this x hx).2⟩
    have hlen : Ds.length = 2 * Φ.length := by simp [hDsdef]; ring
    have hmt := hmono t (by omega)
    have hmN1 := hmN (t + 1) ht
    obtain ⟨ρ', hρ', hsh⟩ := exists_shallow_ext_q (C := q * k + (N - q * m (t + 1))) (s := s)
      (w := k) hq hρ hρU Ds hDs (m := m (t + 1)) (by omega) (by rw [card_range]; exact hmN1)
      (by
        rw [card_range]
        have : N - q * (m (t + 1) + (s + 1)) ≤ N - q * m (t + 1) :=
          Nat.sub_le_sub_left (Nat.mul_le_mul_left _ (by omega)) _
        omega)
      (by rw [hlen, card_range, hρc]; exact hineq t (by omega))
    obtain ⟨hU', hp', hsub, hc'⟩ := mem_Rq.1 hρ'
    have hρτ : ρ ∪ (ρ' \ ρ) = ρ' := union_sdiff_of_subset hsub
    have hd : Disjoint ρ (ρ' \ ρ) := disjoint_sdiff
    have := level_step_q hq hcl hmod (t := t) (k := k) (τ := ρ' \ ρ) hG (by rw [hρτ]; exact hp')
      (by rw [hρτ]; exact hU') hd
      (fun l hφ hd' => by
        have h := hsh _ (List.mem_append_left _ (List.mem_map.2 ⟨.or l, hφ, rfl⟩))
        simp only [orArgsAt, if_pos hd'] at h
        rw [hρτ]
        exact le_trans (Nat.mul_le_mul_left _ h) hqs)
      (fun l hφ hd' => by
        have h := hsh _ (List.mem_append_right _ (List.mem_map.2 ⟨.and l, hφ, rfl⟩))
        simp only [andArgsAt, if_pos hd'] at h
        rw [hρτ]
        exact le_trans (Nat.mul_le_mul_left _ h) hqs)
    rw [hρτ] at this
    exact ⟨ρ', _, hp', hU', hc', this⟩

/-! ## Arithmetic -/

theorem arith_q {q k ℓ s Q Δ : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k) (hqk : q * k ≤ ℓ)
    (hℓ : 2 ^ (q * q + 1) ≤ ℓ) (hQ : Q < ℓ ^ (s + 1)) (hΔ : ℓ ^ (q * q + q + 3) ≤ Δ) :
    Q * (ℓ.choose q * (2 * (k * (q * k + ℓ) ^ (q * q)))) ^ (s + 1) < Δ ^ (s + 1) := by
  have hℓ1 : 1 ≤ ℓ := le_trans (Nat.one_le_two_pow) hℓ
  have hkℓ : k ≤ ℓ := le_trans (Nat.le_mul_of_pos_left k (by omega)) hqk
  have hX : ℓ.choose q * (2 * (k * (q * k + ℓ) ^ (q * q))) ≤ ℓ ^ (q * q + q + 2) := by
    calc ℓ.choose q * (2 * (k * (q * k + ℓ) ^ (q * q)))
        ≤ ℓ ^ q * (2 * (ℓ * (2 * ℓ) ^ (q * q))) := by
          gcongr
          · exact Nat.choose_le_pow _ _
          · omega
      _ = 2 ^ (q * q + 1) * ℓ ^ (q * q + q + 1) := by ring
      _ ≤ ℓ * ℓ ^ (q * q + q + 1) := Nat.mul_le_mul_right _ hℓ
      _ = ℓ ^ (q * q + q + 2) := by ring
  have hpos : 0 < (ℓ ^ (q * q + q + 2)) ^ (s + 1) := by positivity
  calc Q * (ℓ.choose q * (2 * (k * (q * k + ℓ) ^ (q * q)))) ^ (s + 1)
      ≤ Q * (ℓ ^ (q * q + q + 2)) ^ (s + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX _)
    _ < ℓ ^ (s + 1) * (ℓ ^ (q * q + q + 2)) ^ (s + 1) := Nat.mul_lt_mul_of_pos_right hQ hpos
    _ = (ℓ ^ (q * q + q + 3)) ^ (s + 1) := by ring
    _ ≤ Δ ^ (s + 1) := Nat.pow_le_pow_left hΔ _

theorem arith_R {q R e : ℕ} (h1 : 2 ^ e ≤ R) (h2 : q + 1 ≤ R) :
    q * (2 * R) ^ e + R ≤ R ^ (e + 2) := by
  have hR1 : 1 ≤ R := by omega
  have ha : (2 * R) ^ e ≤ R ^ (e + 1) := by
    calc (2 * R) ^ e = 2 ^ e * R ^ e := by rw [mul_pow]
      _ ≤ R * R ^ e := Nat.mul_le_mul_right _ h1
      _ = R ^ (e + 1) := by ring
  have hb : R ≤ R ^ (e + 1) := Nat.le_self_pow (by omega) _
  calc q * (2 * R) ^ e + R ≤ q * R ^ (e + 1) + R ^ (e + 1) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ ha) hb
    _ = (q + 1) * R ^ (e + 1) := by ring
    _ ≤ R * R ^ (e + 1) := Nat.mul_le_mul_right _ h2
    _ = R ^ (e + 2) := by ring

theorem arith_design {p q K : ℕ} (hq : 1 ≤ q) (hK1 : q * (10 * q) ^ (p + q) ≤ K) (hK2 : q * q ≤ K)
    (hK3 : 2 ≤ K) : (10 * (q * K)) ^ (p + q) * q + q * (q * K) ≤ K ^ (p + q + 2) := by
  have h1 : (10 * (q * K)) ^ (p + q) * q ≤ K ^ (p + q + 1) := by
    calc (10 * (q * K)) ^ (p + q) * q = (q * (10 * q) ^ (p + q)) * K ^ (p + q) := by ring
      _ ≤ K * K ^ (p + q) := Nat.mul_le_mul_right _ hK1
      _ = K ^ (p + q + 1) := by ring
  have h2 : q * (q * K) ≤ K ^ (p + q + 1) := by
    calc q * (q * K) = (q * q) * K := by ring
      _ ≤ K * K := Nat.mul_le_mul_right _ hK2
      _ = K ^ 2 := by ring
      _ ≤ K ^ (p + q + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  calc _ ≤ K ^ (p + q + 1) + K ^ (p + q + 1) := Nat.add_le_add h1 h2
    _ = 2 * K ^ (p + q + 1) := by ring
    _ ≤ K * K ^ (p + q + 1) := Nat.mul_le_mul_right _ hK3
    _ = K ^ (p + q + 2) := by ring

theorem exists_design_exp {p q k : ℕ} (hk : 1 ≤ k) :
    ∃ i, 4 * k + 1 ≤ 2 ^ i ∧ (p + q) ^ i ≤ (10 * k) ^ (p + q) := by
  refine ⟨Nat.log 2 (4 * k + 1) + 1, (Nat.lt_pow_succ_log_self (by norm_num) _).le, ?_⟩
  have h1 : 2 ^ (Nat.log 2 (4 * k + 1) + 1) ≤ 10 * k := by
    have := Nat.pow_log_le_self 2 (show 4 * k + 1 ≠ 0 by omega)
    rw [pow_succ]; omega
  calc (p + q) ^ (Nat.log 2 (4 * k + 1) + 1)
      ≤ (2 ^ (p + q)) ^ (Nat.log 2 (4 * k + 1) + 1) :=
        Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
    _ = (2 ^ (Nat.log 2 (4 * k + 1) + 1)) ^ (p + q) := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (10 * k) ^ (p + q) := Nat.pow_le_pow_left h1 _

/-! ## The lower bound -/

/-- **Count_q requires exponential size bounded depth Frege proofs with Count_p axioms** (1D.2;
BIKPP 1994, BIKPPRS 1997). Let `p` be a prime not dividing `q ≥ 2`, `F = q² + q + 5`,
`M = ⌊N^{1/F^{d+1}}⌋` and `K = ⌊M^{1/(p+q+2)}⌋` (as `Nat.findGreatest`). For all large `N`,
every mod free depth `d` refutation of `countqCNF q N` in the sequent calculus with all
instances of the Count_p axiom schema has size at least `2^K / 8`. -/
theorem countq_bdfrege_exp {p q : ℕ} [hp : Fact p.Prime] (hpq : ¬ p ∣ q) (hq2 : 2 ≤ q) (d : ℕ) :
    ∃ N0, ∀ N ≥ N0, ∀ L, FRefutesC p d (countqCNF q N) L → ModFree L →
      2 ^ Nat.findGreatest (fun K => K ^ (p + q + 2) ≤
          Nat.findGreatest (fun M => M ^ ((q * q + q + 5) ^ (d + 1)) ≤ N) N)
        (Nat.findGreatest (fun M => M ^ ((q * q + q + 5) ^ (d + 1)) ≤ N) N) ≤ 8 * fSize L := by
  have hq : 1 ≤ q := by omega
  set e := q * q + q + 3 with he
  set F := q * q + q + 5 with hF
  set T := d + 1 with hT
  set H := F ^ T with hH
  set G := p + q + 2 with hG
  set K0 := 2 ^ e * (10 * q) ^ (p + q + 1) with hK0
  have hH1 : 1 ≤ H := Nat.one_le_pow _ _ (by omega)
  have hG1 : 1 ≤ G := by omega
  have hK0e : 2 ^ e ≤ K0 := Nat.le_mul_of_pos_right _ (by positivity)
  have hK0q : q * (10 * q) ^ (p + q) ≤ K0 := by
    calc q * (10 * q) ^ (p + q) ≤ (10 * q) * (10 * q) ^ (p + q) := Nat.mul_le_mul_right _ (by omega)
      _ = (10 * q) ^ (p + q + 1) := by ring
      _ ≤ K0 := Nat.le_mul_of_pos_left _ (by positivity)
  have hK0qq : 3 * (q * q) ≤ K0 := by
    calc 3 * (q * q) ≤ (10 * q) ^ 2 := by nlinarith
      _ ≤ (10 * q) ^ (p + q + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ K0 := Nat.le_mul_of_pos_left _ (by positivity)
  have he2 : 2 ^ (q * q + 1) ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hel : q + 1 ≤ 2 ^ e := by
    have := Nat.lt_two_pow_self (n := e); omega
  refine ⟨(K0 ^ G) ^ H, fun N hN L hR hmf => ?_⟩
  set M := Nat.findGreatest (fun M => M ^ H ≤ N) N with hMdef
  have hK0pos : 1 ≤ K0 := le_trans Nat.one_le_two_pow hK0e
  have hKG : K0 ^ G ≤ (K0 ^ G) ^ H := Nat.le_self_pow (by omega) _
  have hM1 : M ^ H ≤ N := Nat.findGreatest_spec (P := fun M => M ^ H ≤ N) (m := 0)
    (Nat.zero_le _) (by simp only; rw [zero_pow (by omega)]; exact Nat.zero_le _)
  have hM2 : K0 ^ G ≤ M := Nat.le_findGreatest (P := fun M => M ^ H ≤ N) (by omega) hN
  have hMN : M ≤ N := Nat.findGreatest_le N
  set K := Nat.findGreatest (fun K => K ^ G ≤ M) M with hKdef
  have hK1 : K ^ G ≤ M := Nat.findGreatest_spec (P := fun K => K ^ G ≤ M) (m := 0)
    (Nat.zero_le _) (by simp only; rw [zero_pow (by omega)]; exact Nat.zero_le _)
  have hK2 : K0 ≤ K := Nat.le_findGreatest (P := fun K => K ^ G ≤ M)
    (le_trans (Nat.le_self_pow (by omega) _) hM2) hM2
  show 2 ^ K ≤ 8 * fSize L
  by_contra hsz
  push Not at hsz
  have hKe : 2 ^ e ≤ K := le_trans hK0e hK2
  have h2e : 2 ≤ 2 ^ e := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ e by omega); simpa using this
  have hK2' : 2 ≤ K := le_trans h2e hKe
  have hKM : K * K ≤ M := by
    calc K * K = K ^ 2 := by ring
      _ ≤ K ^ G := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ M := hK1
  have hKleM : K ≤ M := le_trans (Nat.le_mul_of_pos_left K (by omega)) hKM
  set k := q * K with hkdef
  set s := K with hsdef
  have hk : 1 ≤ k := by have := Nat.mul_le_mul hq (show 1 ≤ K by omega); simpa using this
  -- target free sizes and block counts
  set R : ℕ → ℕ := fun t => if t = 0 then N else M ^ (F ^ (T - t)) with hRdef
  set m : ℕ → ℕ := fun t => (N - R t) / q with hmdef
  have hRpow : ∀ j, M ≤ M ^ (F ^ j) := fun j =>
    Nat.le_self_pow (Nat.pos_iff_ne_zero.1 (Nat.one_le_pow _ _ (by omega))) _
  have hRle : ∀ t ≤ T, R t ≤ N := by
    intro t ht
    by_cases h0 : t = 0
    · simp [hRdef, h0]
    · simp only [hRdef, if_neg h0]
      exact le_trans (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega)
        (show T - t ≤ T by omega))) hM1
  have hRM : ∀ t ≤ T, M ≤ R t := by
    intro t ht
    by_cases h0 : t = 0
    · simp only [hRdef, if_pos h0]; exact hMN
    · simp only [hRdef, if_neg h0]; exact hRpow _
  have hRstep : ∀ t < T, R (t + 1) ^ F ≤ R t := by
    intro t ht
    have h1 : R (t + 1) = M ^ (F ^ (T - (t + 1))) := by simp [hRdef]
    rw [h1, ← pow_mul, ← pow_succ, show T - (t + 1) + 1 = T - t by omega]
    by_cases h0 : t = 0
    · simp only [hRdef, if_pos h0]; rw [h0, Nat.sub_zero]; exact hM1
    · simp only [hRdef, if_neg h0]; exact le_rfl
  have hRmono : ∀ t < T, R (t + 1) ≤ R t := fun t ht =>
    le_trans (Nat.le_self_pow (by omega) _) (hRstep t ht)
  have hmq : ∀ t ≤ T, q * m t + (N - R t) % q = N - R t := fun t _ => Nat.div_add_mod _ _
  have hmod_lt : ∀ t, (N - R t) % q < q := fun t => Nat.mod_lt _ (by omega)
  have hℓ : ∀ t ≤ T, R t ≤ N - q * m t ∧ N - q * m t < R t + q := by
    intro t ht
    have := hmq t ht; have := hmod_lt t; have := hRle t ht
    omega
  have hm0 : m 0 = 0 := by simp [hmdef, hRdef]
  have hmono : ∀ t < T, m t ≤ m (t + 1) := fun t ht =>
    Nat.div_le_div_right (Nat.sub_le_sub_left (hRmono t ht) _)
  have hmN : ∀ t ≤ T, q * m t ≤ N := fun t ht => by have := hmq t ht; omega
  -- the formulas of the proof
  set Φ := phiOf L
  have hΦ : 2 * Φ.length < 2 ^ (s + 1) := by
    have h1 : Φ.length ≤ 3 * fSize L + 1 := phiOf_length L
    have h2s : 2 ≤ 2 ^ s := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ s by omega); simpa using this
    rw [pow_succ]; omega
  have hineq : ∀ t < T, (2 * Φ.length) * ((N - q * m (t + 1)).choose q *
      (2 * (k * (q * k + (N - q * m (t + 1))) ^ (q * q)))) ^ (s + 1) <
        (m (t + 1) + 1 - m t) ^ (s + 1) := by
    intro t ht
    obtain ⟨hℓ1, hℓ2⟩ := hℓ (t + 1) ht
    have hRM1 := hRM (t + 1) ht
    have hRℓ : M ≤ N - q * m (t + 1) := le_trans hRM1 hℓ1
    refine arith_q hq hk ?_ ?_ ?_ ?_
    · calc q * k = (q * q) * K := by rw [hkdef]; ring
        _ ≤ K * K := Nat.mul_le_mul_right _ (by omega)
        _ ≤ N - q * m (t + 1) := le_trans hKM hRℓ
    · exact le_trans he2 (le_trans hKe (le_trans hKleM hRℓ))
    · calc 2 * Φ.length < 2 ^ (s + 1) := hΦ
        _ ≤ (N - q * m (t + 1)) ^ (s + 1) := Nat.pow_le_pow_left (by omega) _
    · -- the shrinking step
      have hR'e : 2 ^ e ≤ R (t + 1) := le_trans hKe (le_trans hKleM hRM1)
      have hR'q : q + 1 ≤ R (t + 1) := le_trans hel hR'e
      have hAR := arith_R (q := q) hR'e hR'q
      have hℓ2R : N - q * m (t + 1) ≤ 2 * R (t + 1) := by omega
      have hpowℓ : q * (N - q * m (t + 1)) ^ e ≤ q * (2 * R (t + 1)) ^ e :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hℓ2R _)
      have hstep := hRstep t ht
      rw [show F = e + 2 by omega] at hstep
      have hmt := hmq t (by omega)
      have hmt1 := hmq (t + 1) ht
      have hr1 := hmod_lt (t + 1)
      have hr0 := hmod_lt t
      have hRt := hRle t (by omega)
      have hmle := hmono t ht
      have hΔeq : q * (m (t + 1) + 1 - m t) + q * m t = q * m (t + 1) + q := by
        rw [← mul_add, Nat.sub_add_cancel (by omega), mul_add, mul_one]
      have hlt : q * (N - q * m (t + 1)) ^ e < q * (m (t + 1) + 1 - m t) := by omega
      exact (Nat.lt_of_mul_lt_mul_left hlt).le
  obtain ⟨ρ, ET, hρ, hρU, hρc, hGood⟩ := levels_q (vx := vxq) hq (phiOf_closed L)
    (phiOf_modfree hmf) (N := N) (k := k) (s := s) (T := T) m hm0 hmono hmN hk le_rfl hineq T
    le_rfl
  -- the final free set
  have hfree : M ≤ (free (range N) ρ).card := by
    rw [card_free hρ hρU, card_range, hρc]
    have h1 := (hℓ T le_rfl).1
    have h2 : R T = M := by simp [hRdef, hT]
    omega
  have hroom : q * (3 * k) ≤ (free (range N) ρ).card := by
    refine le_trans ?_ (le_trans hKM hfree)
    calc q * (3 * k) = (3 * (q * q)) * K := by rw [hkdef]; ring
      _ ≤ K * K := Nat.mul_le_mul_right _ (le_trans hK0qq hK2)
  obtain ⟨i, hi1, hi2⟩ := exists_design_exp (p := p) (q := q) hk
  have hdes : (p + q) ^ i * q + q * k ≤ (free (range N) ρ).card := by
    refine le_trans ?_ (le_trans hK1 hfree)
    calc (p + q) ^ i * q + q * k ≤ (10 * k) ^ (p + q) * q + q * k :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ hi2) _
      _ ≤ _ := arith_design hq (le_trans hK0q hK2) (le_trans (by omega) (le_trans hK0qq hK2)) hK2'
  have hdepth := phiOf_depth hR.2.1
  have hTG : ∀ S ∈ L, ∀ φ ∈ subs (lineF S), TGood q (range N) vxq ρ k ET φ := fun S hS φ hφ =>
    hGood φ (mem_phiOf hS hφ) (by have := hdepth φ (mem_phiOf hS hφ); omega)
  have hsound := qkeval_sound (E := setsOf q (range N) ρ ET) hR.1 hmf
    (fun S hS φ hφ => tgood_sgood hq (hTG S hS φ hφ))
    (countq_clauseHit hq hρ hρU hk hroom) hroom
    (fun S hS hc => countp_lines hpq hq2 hc (hTG S hS) hi1 hdes)
  have h0 := hsound _ hR.2.2
  have hG0 := tgood_sgood hq (hTG _ hR.2.2 _ (self_mem_subs _))
  obtain ⟨α, hα, -⟩ := hG0.cov ∅ (by simp) (by simp [PP]) (by simp; omega)
  rw [h0, union_empty] at hα
  have hl := hG0.loc; simp only [lineF, QLoc] at hl
  obtain ⟨ψ, hψ, -⟩ := hl.1 α hα
  simp [dsOf] at hψ

/-- Non vacuity: for `q ∤ N`, `countqCNF q N` has refutations in the system with Count_p
axioms (already without them, by simulating resolution). -/
theorem countq_refutable (p : ℕ) {q N : ℕ} (hN : ¬ q ∣ N) :
    ∃ L, FRefutesC p 1 (countqCNF q N) L := by
  obtain ⟨L, hL, hd, he⟩ := frefutes_of_unsat (p := p) (countq_unsat hN)
  exact ⟨L, fun k hk => Or.inl (hL k hk), hd, he⟩

end

end QP

end SATurday.ProofComplexity
