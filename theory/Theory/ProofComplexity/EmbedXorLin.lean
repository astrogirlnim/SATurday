import Theory.ProofComplexity.EmbedPang
import Theory.ProofComplexity.ResLinDag

/-!
# `RLDag` over `F_2` (Part-Tzameret style) embeds in dag-like `Res(⊕)` (`RL.DagRefutes`)

`RLF.RLDag` over `ZMod 2` has syntactic weakening and the combination rule
`C ∨ f = a, D ∨ g = b ⊢ C ∨ D ∨ (αf + βg = αa + βb)`. `RL.DagRefutes` (ResLinDag.lean) is the
Itsykson-Sokolov system with semantic weakening and the resolution rule
`C ∨ f = a, D ∨ f = a + 1 ⊢ C ∨ D`. With the clause encoding `encCl` (a literal `l` becomes the
equation `x_{l.var} = bv l.pos`) we prove

* `rldag2_to_dagRefutes`: an `RLDag` refutation of the CNF `Phi` with `n` lines (from `Ax2 Phi`
  and the Boolean axioms) gives `RL.DagRefutes ↑Phi (n + 1)`.

The additive `+1` is the line used to derive the Boolean axiom clauses (tautologies) by semantic
weakening, which needs one existing line (any clause of `Phi`); it requires `Phi` to be nonempty.
The converse direction (semantic weakening into syntactic) is not claimed.
-/

open SATurday.ProofComplexity

namespace SATurday.ProofComplexity

namespace RLF

noncomputable section

open Classical

local instance instDecEqLEq2 : DecidableEq (LEq (ZMod 2)) := leqDec (ZMod 2)

/-- The `RL` form `(support, constant)` of an equation over `F_2`. -/
def toE (e : LEq (ZMod 2)) : Finset ℕ × ZMod 2 := (e.1.support, e.2)

/-- A linear clause over `F_2` as an `RL.LClause`. -/
def toL (L : Finset (LEq (ZMod 2))) : RL.LClause := L.image toE

theorem lf_support (c : ℕ →₀ ZMod 2) (x : ℕ → ZMod 2) : RL.lf c.support x = lval c x := by
  unfold RL.lf lval Finsupp.sum
  refine Finset.sum_congr rfl fun i hi => ?_
  have : c i = 1 := by
    have h : c i ≠ 0 := Finsupp.mem_support_iff.1 hi
    revert h; generalize c i = a; revert a; decide
  simp [this]

theorem lsatL_toL (x : ℕ → ZMod 2) (L : Finset (LEq (ZMod 2))) :
    RL.lsatL x (toL L) ↔ clSat x L := by
  unfold RL.lsatL clSat toL
  constructor
  · rintro ⟨e, he, hv⟩
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
    exact ⟨e', he', by simpa [eSat, toE, lf_support] using hv⟩
  · rintro ⟨e, he, hv⟩
    exact ⟨toE e, Finset.mem_image_of_mem _ he, by simpa [eSat, toE, lf_support] using hv⟩

theorem imp_toL {L L' : Finset (LEq (ZMod 2))} (h : ∀ x, clSat x L → clSat x L') :
    RL.Imp (toL L) (toL L') := fun x hx =>
  (lsatL_toL x L').2 (h x ((lsatL_toL x L).1 hx))

/-- A clause as a linear clause over `F_2`. -/
def encCl (C : Clause) : Finset (LEq (ZMod 2)) :=
  C.image fun l => (Finsupp.single l.var 1, RL.bv l.pos)

theorem toL_encCl (C : Clause) : toL (encCl C) = RL.ofClause C := by
  unfold toL encCl RL.ofClause
  rw [Finset.image_image]
  refine Finset.image_congr fun l _ => ?_
  simp [toE, Finsupp.support_single_ne_zero]

/-- The CNF as linear clauses over `F_2`. -/
def Ax2 (Φ : CNF) : Set (Finset (LEq (ZMod 2))) := {L | ∃ C ∈ Φ, L = encCl C}

theorem z2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem add_line {Φ : CNF} {D0 : Clause} {𝓛 : Finset (Finset (LEq (ZMod 2)))}
    {P : Finset RL.LClause} (hP : RL.Der (↑Φ : Set Clause) P) (hD0 : RL.ofClause D0 ∈ P)
    (hmem : ∀ L ∈ 𝓛, toL L ∈ P) (hc : P.card ≤ 𝓛.card + 1) (T : Finset (LEq (ZMod 2)))
    (hs : RL.Step (↑Φ : Set Clause) P (toL T)) :
    ∃ P', RL.Der (↑Φ : Set Clause) P' ∧ RL.ofClause D0 ∈ P' ∧
      (∀ L ∈ insert T 𝓛, toL L ∈ P') ∧ P'.card ≤ (insert T 𝓛).card + 1 := by
  by_cases hT : T ∈ 𝓛
  · refine ⟨P, hP, hD0, ?_, ?_⟩
    · intro L hL
      rcases Finset.mem_insert.1 hL with rfl | hL
      · exact hmem _ hT
      · exact hmem L hL
    · rw [Finset.insert_eq_of_mem hT]; exact hc
  · refine ⟨insert (toL T) P, RL.Der.add hP hs, Finset.mem_insert_of_mem hD0, ?_, ?_⟩
    · intro L hL
      rcases Finset.mem_insert.1 hL with rfl | hL
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hmem L hL)
    · have := Finset.card_insert_le (toL T) P
      rw [Finset.card_insert_of_notMem hT]; omega

theorem rldag2_to_der {Φ : CNF} {D0 : Clause} (hD0 : D0 ∈ Φ)
    {𝓛 : Finset (Finset (LEq (ZMod 2)))} (h : RLDag (Ax2 Φ ∪ boolAx) 𝓛) :
    ∃ P, RL.Der (↑Φ : Set Clause) P ∧ RL.ofClause D0 ∈ P ∧ (∀ L ∈ 𝓛, toL L ∈ P) ∧
      P.card ≤ 𝓛.card + 1 := by
  induction h with
  | empty =>
    refine ⟨{RL.ofClause D0}, ?_, by simp, by simp, by simp⟩
    simpa using RL.Der.add RL.Der.empty (RL.Step.ax (Ax := (↑Φ : Set Clause)) (by exact_mod_cast hD0))
  | @ax 𝓛 C _ hC ih =>
    obtain ⟨P, hP, hD, hmem, hc⟩ := ih
    refine add_line hP hD hmem hc C ?_
    rcases hC with ⟨D, hDΦ, rfl⟩ | ⟨i, rfl⟩
    · rw [toL_encCl]
      exact RL.Step.ax (by exact_mod_cast hDΦ)
    · exact RL.Step.weak hD (fun x _ => (lsatL_toL x _).2
        (boolAx_sat (fun i => z2_cases (x i)) _ (boolCl_mem_boolAx i)))
  | @weak 𝓛 L L' _ hL hsub ih =>
    obtain ⟨P, hP, hD, hmem, hc⟩ := ih
    refine add_line hP hD hmem hc L' (RL.Step.weak (hmem L hL) (imp_toL ?_))
    rintro x ⟨e, he, hv⟩
    exact ⟨e, hsub he, hv⟩
  | @comb 𝓛 A B e1 e2 α β _ hA hB h1 h2 ih =>
    obtain ⟨P, hP, hD, hmem, hc⟩ := ih
    set T := A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2} with hT
    have hcmb_zero : ∀ x, eSat x (cmb 0 0 e1 e2) := by
      intro x; simp [eSat, cmb, lval_zero]
    have hsubA : ∀ x, clSat x (A.erase e1 ∪ B.erase e2) → clSat x T := by
      rintro x ⟨e, he, hv⟩
      exact ⟨e, Finset.mem_union_left _ he, hv⟩
    rcases z2_cases α with rfl | rfl <;> rcases z2_cases β with rfl | rfl
    · refine add_line hP hD hmem hc T (RL.Step.weak (hmem A hA) (imp_toL ?_))
      intro x _
      exact ⟨cmb 0 0 e1 e2, Finset.mem_union_right _ (Finset.mem_singleton_self _),
        hcmb_zero x⟩
    · refine add_line hP hD hmem hc T (RL.Step.weak (hmem B hB) (imp_toL ?_))
      rintro x ⟨e, he, hv⟩
      by_cases hee : e = e2
      · subst hee
        refine ⟨cmb 0 1 e1 e, Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
        simp only [eSat, cmb, lval_add, lval_smul] at hv ⊢
        rw [hv]; simp
      · exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_erase.2 ⟨hee, he⟩)), hv⟩
    · refine add_line hP hD hmem hc T (RL.Step.weak (hmem A hA) (imp_toL ?_))
      rintro x ⟨e, he, hv⟩
      by_cases hee : e = e1
      · subst hee
        refine ⟨cmb 1 0 e e2, Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
        simp only [eSat, cmb, lval_add, lval_smul] at hv ⊢
        rw [hv]; simp
      · exact ⟨e, Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_erase.2 ⟨hee, he⟩)), hv⟩
    · -- resolution on the form of the first equation
      have hTeq : toL T = toL (A.erase e1) ∪ (toL (B.erase e2) ∪ {toE (cmb 1 1 e1 e2)}) := by
        simp only [hT, toL, Finset.image_union, Finset.image_singleton, Finset.union_assoc]
      have i1 : RL.Imp (toL A) (insert (e1.1.support, e1.2) (toL (A.erase e1))) := by
        rintro x ⟨e, he, hv⟩
        obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
        by_cases hee : e' = e1
        · subst hee; exact ⟨toE e', Finset.mem_insert_self _ _, hv⟩
        · exact ⟨toE e', Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
            (Finset.mem_erase.2 ⟨hee, he'⟩)), hv⟩
      have i2 : RL.Imp (toL B) (insert (e1.1.support, e1.2 + 1)
          (toL (B.erase e2) ∪ {toE (cmb 1 1 e1 e2)})) := by
        rintro x ⟨e, he, hv⟩
        obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
        by_cases hee : e' = e2
        · subst hee
          have hv' : lval e'.1 x = e'.2 := by simpa [toE, lf_support] using hv
          by_cases hx1 : lval e1.1 x = e1.2
          · refine ⟨toE (cmb 1 1 e1 e'), Finset.mem_insert_of_mem (Finset.mem_union_right _
              (Finset.mem_singleton_self _)), ?_⟩
            simp only [toE, lf_support, cmb, lval_add, lval_smul]
            rw [hx1, hv']
          · refine ⟨(e1.1.support, e1.2 + 1), Finset.mem_insert_self _ _, ?_⟩
            have hz : ∀ u v : ZMod 2, u ≠ v → u = v + 1 := by decide
            simp only [lf_support]
            exact hz _ _ hx1
        · exact ⟨toE e', Finset.mem_insert_of_mem (Finset.mem_union_left _
            (Finset.mem_image_of_mem _ (Finset.mem_erase.2 ⟨hee, he'⟩))), hv⟩
      have hres := RL.Step.res (Ax := (↑Φ : Set Clause)) (P := P) (hmem A hA) (hmem B hB) i1 i2
      refine add_line hP hD hmem hc T ?_
      rw [hTeq]; exact hres
  | @simp 𝓛 L c _ hc h0 ih =>
    obtain ⟨P, hP, hD, hmem, hc'⟩ := ih
    refine add_line hP hD hmem hc' L (RL.Step.weak (hmem _ h0) (imp_toL ?_))
    rintro x ⟨e, he, hv⟩
    rcases Finset.mem_insert.1 he with rfl | he
    · exfalso
      simp only [eSat, lval_zero] at hv
      exact hc hv.symm
    · exact ⟨e, he, hv⟩

/-- **`RLDag` over `F_2` embeds in dag-like `Res(⊕)`.** A refutation of the CNF `Φ` with `n` lines
of `RLDag` (from the encoded clauses and the Boolean axioms) gives `RL.DagRefutes ↑Φ (n + 1)`. -/
theorem rldag2_to_dagRefutes {Φ : CNF} (hne : Φ.Nonempty)
    {𝓛 : Finset (Finset (LEq (ZMod 2)))} (h : RLDag (Ax2 Φ ∪ boolAx) 𝓛)
    (h0 : (∅ : Finset (LEq (ZMod 2))) ∈ 𝓛) :
    RL.DagRefutes (↑Φ : Set Clause) (𝓛.card + 1) := by
  obtain ⟨D0, hD0⟩ := hne
  obtain ⟨P, hP, _, hmem, hc⟩ := rldag2_to_der hD0 h
  refine ⟨P, hP, ?_, hc⟩
  have := hmem _ h0
  simpa [toL] using this

end

end RLF

end SATurday.ProofComplexity
