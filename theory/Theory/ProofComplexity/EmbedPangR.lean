import Theory.ProofComplexity.FregeRankBridge
import Theory.ProofComplexity.EmbedPangLin

/-!
# `Pang.Refutation` embeds in the bounded rank calculus `R_ρ^p` (`C1.RRefutation`), `ρ ≥ 1`

Referee leftover (dossier Section 17, item 2): Pang's dag-like `Res(lin F_p)` (`Pang.Refutation`,
PangDag.lean) into the calculus `R_ρ^p` of `C1Rank.lean`.

A Pang line is a finite set of polynomials `h` of degree `≤ 1`, read as the disjunction of the
equations `h = 0`.  The translation sends `h` to the rank one term `{nrm (toF h)}`: `toF h` is the
affine form with `formPoly (toF h) = h`, and `nrm` scales a form with a variable so that the
coefficient of its least variable is `1` (this makes `1 - x` and `x - 1` the same term, so a CNF
clause is translated to exactly `C1.clauseRLine`).  Every Pang rule becomes one rule of `R_ρ^p`:
`init`, `bool` (`taut`), `weak` are the same rules, `falseConst` and `mul` are instances of `sem1`,
`comb` of `sem2`; the axiom `0 = 0` is derived once, in three nodes, at the start.

Main result: `PangR.pang_to_rref`: a `Pang.Refutation Φ V p` with `S` nodes, `V` nonempty, gives an
`RRefutation Φ V ρ p` with at most `S + 3` nodes, for every `ρ ≥ 1`.

The converse is not claimed (the rules `sem1`, `sem2` of `R_ρ^p` are semantic and its terms are
conjunctions of up to `ρ` equations).

This file does not relate `Pang.Refutation` to the AC0[p] Frege sequent calculus `FProof`: the
embedding is into `R_ρ^p`, which is not a Cook-Reckhow system and is not a depth-bounded Frege
system.
-/

open SATurday.ProofComplexity MvPolynomial C1 FBridge

namespace PangR

noncomputable section
open Classical

variable {p : ℕ} [Fact p.Prime] {Φ : CNF} {V : Finset ℕ} {ρ : ℕ}

/-! ## Forms of linear polynomials -/

theorem formPoly_eq_phi (l : AffForm p) : formPoly l = RLF.phi ((l.1, -l.2) : RLF.LEq (ZMod p)) := by
  simp only [formPoly, RLF.phi, RLF.lin, map_neg, sub_neg_eq_add]

theorem formPoly_injective : Function.Injective (formPoly (p := p)) := by
  intro l l' h
  rw [formPoly_eq_phi, formPoly_eq_phi] at h
  have := RLF.phi_injective h
  simp only [Prod.mk.injEq, neg_inj] at this
  exact Prod.ext this.1 this.2

/-- The affine form of a polynomial of degree `≤ 1` (zero otherwise). -/
def toF (h : Pang.Poly p) : AffForm p :=
  if hd : h.totalDegree ≤ 1 then
    ((Classical.choose (RLF.exists_phi h hd)).1, -(Classical.choose (RLF.exists_phi h hd)).2)
  else 0

theorem formPoly_toF {h : Pang.Poly p} (hd : h.totalDegree ≤ 1) : formPoly (toF h) = h := by
  have he := Classical.choose_spec (RLF.exists_phi h hd)
  rw [toF, dif_pos hd, formPoly_eq_phi]
  simpa using he

theorem toF_formPoly (l : AffForm p) : toF (formPoly l) = l :=
  formPoly_injective (formPoly_toF (totalDegree_formPoly l))

theorem ev_toF (a : ℕ → ZMod p) {h : Pang.Poly p} (hd : h.totalDegree ≤ 1) :
    ev a (toF h) = eval a h := by
  rw [← eval_formPoly, formPoly_toF hd]

theorem coeff_formPoly_single (l : AffForm p) (j : ℕ) :
    coeff (Finsupp.single j 1) (formPoly l) = l.1 j := by
  rw [formPoly_eq_phi]
  simp only [RLF.phi, coeff_sub, RLF.coeff_lin_single, coeff_C]
  have : (0 : ℕ →₀ ℕ) ≠ Finsupp.single j 1 := by
    intro h; have := congrArg (fun f => f j) h; simp at this
  simp [this]

theorem supp_toF (h : Pang.Poly p) : (toF h).1.support ⊆ h.vars := by
  intro j hj
  by_cases hd : h.totalDegree ≤ 1
  · have h1 : coeff (Finsupp.single j 1) h ≠ 0 := by
      rw [← formPoly_toF hd, coeff_formPoly_single]
      exact Finsupp.mem_support_iff.1 hj
    rw [mem_vars]
    exact ⟨Finsupp.single j 1, mem_support_iff.2 h1, by simp⟩
  · rw [toF, dif_neg hd] at hj
    simp at hj

/-- Normalisation: scale a form with a variable so that its least variable has coefficient `1`. -/
def nrm (l : AffForm p) : AffForm p :=
  if h : l.1.support.Nonempty then (l.1 (l.1.support.min' h))⁻¹ • l else l

theorem ev_nrm (a : ℕ → ZMod p) (l : AffForm p) : ev a (nrm l) = 0 ↔ ev a l = 0 := by
  unfold nrm
  split_ifs with h
  · have hne : l.1 (l.1.support.min' h) ≠ 0 :=
      Finsupp.mem_support_iff.1 (Finset.min'_mem _ h)
    rw [map_smul, smul_eq_mul]
    simp [hne]
  · rfl

theorem supp_nrm (l : AffForm p) : (nrm l).1.support ⊆ l.1.support := by
  unfold nrm
  split_ifs
  · rw [Prod.smul_fst]; exact Finsupp.support_smul
  · exact Finset.Subset.refl _

theorem nrm_single (i : ℕ) (c a : ZMod p) (hc : c ≠ 0) :
    nrm ((Finsupp.single i c, a) : AffForm p) = (Finsupp.single i 1, c⁻¹ * a) := by
  have hs : (Finsupp.single i c).support = {i} := Finsupp.support_single_ne_zero i hc
  have hn : (Finsupp.single i c).support.Nonempty := by rw [hs]; simp
  rw [nrm, dif_pos hn]
  have hm : (Finsupp.single i c).support.min' hn = i := by simp [hs]
  rw [hm]
  simp [Prod.smul_mk, Finsupp.smul_single, hc]

/-! ## The translation -/

/-- The rank one term of a polynomial. -/
def tr (h : Pang.Poly p) : Term p := {nrm (toF h)}

/-- The translation of a line. -/
def trL (L : Pang.Line p) : RLine p := L.image tr

theorem trueAt_tr (a : ℕ → ZMod p) {h : Pang.Poly p} (hd : h.totalDegree ≤ 1) :
    TrueAt a (tr h) ↔ eval a h = 0 := by
  simp [TrueAt, tr, ev_nrm, ev_toF a hd]

theorem formPoly_formVar (i : ℕ) : formPoly (formVar i : AffForm p) = X i := by
  simp [formPoly, formVar, Finsupp.sum_single_index]

theorem formPoly_formVarSub (i : ℕ) : formPoly (formVarSub i : AffForm p) = X i - 1 := by
  simp [formPoly, formVarSub, Finsupp.sum_single_index, sub_eq_add_neg]

theorem tr_X (i : ℕ) : tr (X i : Pang.Poly p) = {formVar i} := by
  rw [tr, ← formPoly_formVar, toF_formPoly]
  congr 1
  rw [formVar, nrm_single i 1 0 one_ne_zero]
  simp

theorem tr_Xsub (i : ℕ) : tr (X i - 1 : Pang.Poly p) = {formVarSub i} := by
  rw [tr, ← formPoly_formVarSub, toF_formPoly]
  congr 1
  rw [formVarSub, nrm_single i 1 (-1) one_ne_zero]
  simp

theorem tr_oneSub (i : ℕ) : tr (1 - X i : Pang.Poly p) = {formVarSub i} := by
  have e : formPoly ((Finsupp.single i (-1), 1) : AffForm p) = 1 - X i := by
    unfold formPoly
    rw [Finsupp.sum_single_index (by simp)]
    simp only [map_neg, map_one]
    ring
  rw [tr, ← e, toF_formPoly]
  congr 1
  rw [formVarSub, nrm_single i (-1) 1 (neg_ne_zero.2 one_ne_zero)]
  simp

theorem tr_litPoly (l : Literal) : tr (litPoly l : Pang.Poly p) = litTerm l := by
  unfold litPoly litTerm
  cases l.pos
  · simp [tr_X]
  · simp [tr_oneSub]

theorem trL_clauseLine (C : Clause) : trL (Pang.clauseLine C : Pang.Line p) = clauseRLine C := by
  unfold trL Pang.clauseLine clauseRLine
  rw [Finset.image_image]
  exact Finset.image_congr fun l _ => tr_litPoly l

theorem good_trL (hρ : 1 ≤ ρ) {L : Pang.Line p} (hL : Pang.WF V L) : GoodL V ρ (trL L) := by
  intro T hT
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hT
  refine goodT_singleton hρ ?_
  intro j hj
  exact (hL h hh).2 j (supp_toF h (supp_nrm _ hj))

theorem rank_tr_le (hρ : 1 ≤ ρ) (h : Pang.Poly p) : rank (tr h) ≤ ρ :=
  (FBridge.rank_le_card _).trans (by simpa [tr] using hρ)

theorem erase_sub {L L' : Pang.Line p} {f : Pang.Poly p} (h : L.erase f ⊆ L') :
    (trL L).erase (tr f) ⊆ trL L' := by
  intro T hT
  obtain ⟨hne, hT⟩ := Finset.mem_erase.1 hT
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hT
  refine Finset.mem_image_of_mem _ (h (Finset.mem_erase.2 ⟨?_, hg⟩))
  rintro rfl; exact hne rfl

/-- One Pang step is one step of `R_ρ^p` on the translated lines, except the axiom `0 = 0`. -/
theorem step_sim (hρ : 1 ≤ ρ) {Ls : List (Pang.Line p)} {L : Pang.Line p}
    (hi : Pang.Infer Φ V Ls L) (hL : Pang.WF V L) (hLs : ∀ M ∈ Ls, Pang.WF V M) :
    L = {0} ∨ ∃ prems : List (RLine p), (∀ M ∈ prems, ∃ M' ∈ Ls, M = trL M') ∧
      RInfer Φ ρ prems (trL L) := by
  cases hi with
  | init C hC =>
    right
    refine ⟨[], by simp, ?_⟩
    rw [trL_clauseLine]
    exact RInfer.init C hC
  | zero => left; rfl
  | bool i _ =>
    right
    refine ⟨[], by simp, ?_⟩
    have : trL ({X i, X i - 1} : Pang.Line p) = {{formVar i}, {formVarSub i}} := by
      simp [trL, Finset.image_insert, tr_X, tr_Xsub]
    rw [this]
    exact RInfer.taut i
  | @weak L₀ L' h =>
    right
    exact ⟨[trL L₀], by simp, RInfer.weak _ (Finset.image_subset_image h)⟩
  | @falseConst L₀ c hc hmem L' h =>
    right
    refine ⟨[trL L₀], by simp, ?_⟩
    refine RInfer.sem1 (T₁ := tr (C c)) (T₃ := none) (Finset.mem_image_of_mem _ hmem) ?_ _
      (erase_sub h) (by simp) (by simp)
    intro a ha _
    exfalso
    have := (trueAt_tr _ (by simp)).1 ha
    simp at this
    exact hc this
  | @comb L₁ L₂ f g hf hg α β L' h =>
    right
    refine ⟨[trL L₁, trL L₂], by simp, ?_⟩
    have hdf := (hLs L₁ (by simp) f hf).1
    have hdg := (hLs L₂ (by simp) g hg).1
    have hmem : C α * f + C β * g ∈ L := h (Finset.mem_insert_self _ _)
    have hd := (hL _ hmem).1
    refine RInfer.sem2 (T₁ := tr f) (T₂ := tr g) (T₃ := some (tr (C α * f + C β * g)))
      (Finset.mem_image_of_mem _ hf) (Finset.mem_image_of_mem _ hg) ?_ _
      (erase_sub (fun x hx => h (Finset.mem_insert_of_mem (Finset.mem_union_left _ hx))))
      (erase_sub (fun x hx => h (Finset.mem_insert_of_mem (Finset.mem_union_right _ hx))))
      (by intro T hT; cases hT; exact Finset.mem_image_of_mem _ hmem)
      (by intro T hT; cases hT; exact rank_tr_le hρ _)
    intro a h1 h2
    have e1 := (trueAt_tr _ hdf).1 h1
    have e2 := (trueAt_tr _ hdg).1 (h2 _ rfl)
    exact ⟨_, rfl, (trueAt_tr _ hd).2 (by simp [e1, e2])⟩
  | @mul L₀ f hf g hdeg hvars L' h =>
    right
    refine ⟨[trL L₀], by simp, ?_⟩
    have hdf := (hLs L₀ (by simp) f hf).1
    have hmem : f * g ∈ L := h (Finset.mem_insert_self _ _)
    refine RInfer.sem1 (T₁ := tr f) (T₃ := some (tr (f * g))) (Finset.mem_image_of_mem _ hf) ?_ _
      (erase_sub (fun x hx => h (Finset.mem_insert_of_mem hx)))
      (by intro T hT; cases hT; exact Finset.mem_image_of_mem _ hmem)
      (by intro T hT; cases hT; exact rank_tr_le hρ _)
    intro a h1 _
    have e1 := (trueAt_tr _ hdf).1 h1
    exact ⟨_, rfl, (trueAt_tr _ hdeg).2 (by simp [e1])⟩

/-- **Pang into `R_ρ^p`.**  A `Pang.Refutation Φ V p` with `S` nodes, `V` nonempty, gives an
`R_ρ^p` refutation of `Φ` over the same variables with at most `S + 3` nodes, for every `ρ ≥ 1`. -/
theorem pang_to_rref (R : Pang.Refutation Φ V p) (hV : V.Nonempty) (hρ : 1 ≤ ρ) :
    ∃ R' : RRefutation Φ V ρ p, R'.S ≤ R.S + 3 := by
  obtain ⟨v₀, hv⟩ := hV
  have hwf0 : Pang.WF V ({0} : Pang.Line p) := by
    intro h hh; rw [Finset.mem_singleton] at hh; subst hh; simp
  obtain ⟨L0, hE0, hm0⟩ := reach_true (Φ := Φ) hv hρ (Der.nil (p := p)) (T := tr 0)
    (fun a => (trueAt_tr _ (by simp)).2 (by simp)) (good_trL hρ hwf0)
    (by simp [trL])
  have key : ∀ k ≤ R.S, ∃ Ls : List (RLine p), Der Φ V ρ Ls ∧ trL ({0} : Pang.Line p) ∈ Ls ∧
      (∀ i < k, trL (R.line i) ∈ Ls) ∧ Ls.length ≤ k + 3 := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨L0, hE0.1, hm0, by simp, by simpa using hE0.2.2⟩
    | succ k ih =>
      intro hk
      obtain ⟨Ls, hD, hz, hall, hlen⟩ := ih (by omega)
      have hkS : k < R.S := by omega
      have hprem : ∀ M ∈ (R.prem k).map R.line, Pang.WF V M := by
        intro M hM
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hM
        exact R.wf j ((R.prem_lt k hkS j hj).trans hkS)
      rcases step_sim hρ (R.infer k hkS) (R.wf k hkS) hprem with he | ⟨prems, hp, hi⟩
      · refine ⟨Ls, hD, hz, fun i hi => ?_, by omega⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact hall i hi
        · rw [he]; exact hz
      · obtain ⟨Ls₂, hE, hm⟩ := reach_step hD (prems := prems)
          (fun M hM => by
            obtain ⟨M', hM', rfl⟩ := hp M hM
            obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hM'
            exact hall j (R.prem_lt k hkS j hj)) hi (good_trL hρ (R.wf k hkS))
        refine ⟨Ls₂, hE.1, hE.2.1 _ hz, fun i hi => ?_, by have := hE.2.2; omega⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact hE.2.1 _ (hall i hi)
        · exact hm
  obtain ⟨Ls, hD, _, hall, hlen⟩ := key R.S le_rfl
  have he : (∅ : RLine p) ∈ Ls := by
    have := hall (R.S - 1) (by have := R.S_pos; omega)
    rw [R.last] at this
    simpa [trL] using this
  obtain ⟨R', hR'⟩ := der_refutation hD he
  exact ⟨R', hR'.trans hlen⟩

end

end PangR
