import Theory.ProofComplexity.EmbedPangLin

/-!
# `RLDag` over `F_p` embeds in Pang's `Res(lin F_p)` (`Pang.Refutation`), size-preservingly

`RLF.RLDag` (dag-like `Res(lin F_p)` with syntactic weakening, ResLinFDag.lean) is the calculus of
Part and Tzameret. `Pang.Refutation` (PangDag.lean) has the rules of Pang (axioms, weakening,
false-constant deletion, linear combination, multiplication by a polynomial keeping degree `<= 1`),
with weakening fused into `comb`, `mul` and `falseConst`. This file proves

* `rldag_to_pang`: a refutation of the CNF `Phi` (encoded as linear clauses by `linAx Phi`)
  consisting of `n` lines of `RLDag` gives a `Pang.Refutation Phi V p` with at most `n + 1` nodes,
  for every variable set `V` containing the variables of `Phi`. No assumption is made on the
  variables occurring in the `RLDag` derivation: variables outside `V` are set to `0` (the
  restriction `rV`), which maps the Boolean axiom of such a variable to the weakening of Pang's
  axiom `0 = 0`; this is the reason for the extra node.

So the Lean `Pang.Refutation` system is at least as strong as `RLDag`, with no loss in size. The
encoding of the clause `l_1 v ... v l_k` as the linear clause is `litLE`: a positive literal `x = 1`
is encoded as `-x = -1` and a negative literal `x = 0` as `x = 0`, so that `phi (litLE l) = litPoly l`
exactly (Pang's `clauseLine`). This is a scalar multiple of the usual `x = 1`; relating the two
encodings costs one `RLDag` step per positive literal occurrence of an axiom clause and is not
proved here.
-/

open SATurday.ProofComplexity MvPolynomial

namespace SATurday.ProofComplexity

namespace RLF

noncomputable section

open Classical

variable {p : ℕ} [Fact p.Prime]

/-- The decidable equality on `LEq F` used in the definitions of `RLDag` (generic field, classical
equality on `F`). We install it on `LEq (ZMod p)` so that `insert`/`erase` in our statements are
the ones of `RLDag`. -/
@[reducible] def leqDec (F : Type) [Field F] : DecidableEq (LEq F) := by
  classical exact inferInstance

local instance instDecEqLEq : DecidableEq (LEq (ZMod p)) := leqDec (ZMod p)

/-- The encoding of a literal as a linear equation; `phi (litLE l) = litPoly l`. -/
def litLE (l : Literal) : LEq (ZMod p) :=
  if l.pos then (-(Finsupp.single l.var 1), -1) else (Finsupp.single l.var 1, 0)

theorem phi_litLE (l : Literal) : phi (litLE (p := p) l) = litPoly l := by
  unfold litLE litPoly
  cases hp : l.pos
  · simp [phi, lin_single]
  · simp only [if_true, phi]
    have : lin (-(Finsupp.single l.var (1 : ZMod p))) = - X l.var := by
      have h := lin_smul (-1 : ZMod p) (Finsupp.single l.var 1)
      rw [neg_one_smul] at h
      rw [h, lin_single]; simp
    rw [this]; simp; ring

/-- A clause as a linear clause. -/
def axClause (C : Clause) : Finset (LEq (ZMod p)) := C.image litLE

/-- The CNF `Φ` as a set of linear clauses. -/
def linAx (Φ : CNF) : Set (Finset (LEq (ZMod p))) := {L | ∃ C ∈ Φ, L = axClause C}

/-- Restriction to the variables in `V`: all other variables are set to `0`. -/
def rV (V : Finset ℕ) (e : LEq (ZMod p)) : LEq (ZMod p) :=
  (e.1.filter (fun i => i ∈ V), e.2)

theorem rV_cmb (V : Finset ℕ) (α β : ZMod p) (e1 e2 : LEq (ZMod p)) :
    rV V (cmb α β e1 e2) = cmb α β (rV V e1) (rV V e2) := by
  unfold rV cmb
  refine Prod.ext ?_ rfl
  ext i
  by_cases hi : i ∈ V <;> simp [Finsupp.filter_apply, hi]

theorem rV_eq_self (V : Finset ℕ) (e : LEq (ZMod p)) (h : ∀ i ∈ e.1.support, i ∈ V) :
    rV V e = e := by
  unfold rV
  refine Prod.ext ?_ rfl
  exact (Finsupp.filter_eq_self_iff _ _).2 fun i hi => h i (Finsupp.mem_support_iff.2 hi)

theorem support_rV (V : Finset ℕ) (e : LEq (ZMod p)) : (rV V e).1.support ⊆ V := by
  intro i hi
  unfold rV at hi
  rw [Finsupp.support_filter] at hi
  exact (Finset.mem_filter.1 hi).2

/-- The Pang line of a linear clause, after restriction to `V`. -/
def lineOf (V : Finset ℕ) (L : Finset (LEq (ZMod p))) : Pang.Line p := L.image fun e => phi (rV V e)

theorem lineOf_axClause {V : Finset ℕ} {C : Clause} (hC : ∀ l ∈ C, l.var ∈ V) :
    lineOf V (axClause (p := p) C) = Pang.clauseLine C := by
  unfold lineOf axClause Pang.clauseLine
  rw [Finset.image_image]
  refine Finset.image_congr fun l hl => ?_
  have : rV V (litLE (p := p) l) = litLE l := by
    have hv := hC l hl
    refine rV_eq_self V _ fun i hi => ?_
    unfold litLE at hi
    have hsingle : i = l.var := by
      split_ifs at hi
      · simp only [Finsupp.support_neg] at hi
        exact Finset.mem_singleton.1 (Finsupp.support_single_subset hi)
      · exact Finset.mem_singleton.1 (Finsupp.support_single_subset hi)
    rw [hsingle]; exact hv
  simp only [Function.comp, this]
  exact phi_litLE l

theorem lineOf_mono {V : Finset ℕ} {L L' : Finset (LEq (ZMod p))} (h : L ⊆ L') :
    lineOf V L ⊆ lineOf V L' :=
  Finset.image_subset_image h

theorem mem_lineOf {V : Finset ℕ} {L : Finset (LEq (ZMod p))} {h : Pang.Poly p} :
    h ∈ lineOf V L ↔ ∃ e ∈ L, phi (rV V e) = h := by
  unfold lineOf; simp

theorem phi_mem_lineOf {V : Finset ℕ} {L : Finset (LEq (ZMod p))} {e : LEq (ZMod p)}
    (h : e ∈ L) : phi (rV V e) ∈ lineOf V L :=
  mem_lineOf.2 ⟨e, h, rfl⟩

theorem lineOf_erase_subset (V : Finset ℕ) (L : Finset (LEq (ZMod p))) (e : LEq (ZMod p)) :
    (lineOf V L).erase (phi (rV V e)) ⊆ lineOf V (L.erase e) := by
  intro h hh
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hh
  obtain ⟨e', he', rfl⟩ := mem_lineOf.1 hmem
  exact mem_lineOf.2 ⟨e', Finset.mem_erase.2 ⟨fun h => hne (h ▸ rfl), he'⟩, rfl⟩

/-- Sequences of Pang lines, each inferred from earlier ones. -/
def PSeq (Φ : CNF) (V : Finset ℕ) (l : List (Pang.Line p)) : Prop :=
  ∀ i < l.length, ∃ prem : List ℕ, (∀ j ∈ prem, j < i) ∧
    Pang.Infer Φ V (prem.map fun j => l.getD j ∅) (l.getD i ∅) ∧ Pang.WF V (l.getD i ∅)

theorem PSeq.snoc {Φ : CNF} {V : Finset ℕ} {l : List (Pang.Line p)} {L : Pang.Line p}
    (hl : PSeq Φ V l) (prem : List ℕ) (hp : ∀ j ∈ prem, j < l.length)
    (hi : Pang.Infer Φ V (prem.map fun j => l.getD j ∅) L) (hw : Pang.WF V L) :
    PSeq Φ V (l ++ [L]) := by
  intro i hi'
  have hget : ∀ j, j < l.length → (l ++ [L]).getD j ∅ = l.getD j ∅ := fun j hj => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  rcases Nat.lt_or_ge i l.length with h | h
  · obtain ⟨pr, hpr, hinf, hwf⟩ := hl i h
    refine ⟨pr, hpr, ?_, ?_⟩
    · rw [hget i h]
      have : (pr.map fun j => (l ++ [L]).getD j ∅) = pr.map fun j => l.getD j ∅ :=
        List.map_congr_left fun j hj => hget j ((hpr j hj).trans h)
      rw [this]; exact hinf
    · rw [hget i h]; exact hwf
  · have hi_eq : i = l.length := by simp at hi'; omega
    have hL : (l ++ [L]).getD i ∅ = L := by
      subst hi_eq; simp [List.getD_eq_getElem?_getD]
    refine ⟨prem, fun j hj => hi_eq ▸ hp j hj, ?_, ?_⟩
    · rw [hL]
      have : (prem.map fun j => (l ++ [L]).getD j ∅) = prem.map fun j => l.getD j ∅ :=
        List.map_congr_left fun j hj => hget j (hp j hj)
      rw [this]; exact hi
    · rw [hL]; exact hw

theorem idx_of_mem {l : List (Pang.Line p)} {M : Pang.Line p} (h : M ∈ l) :
    ∃ i < l.length, l.getD i ∅ = M := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
  exact ⟨i, hi, by simp [List.getD_eq_getElem?_getD, hi]⟩

theorem wf_lineOf {V : Finset ℕ} (L : Finset (LEq (ZMod p))) : Pang.WF V (lineOf V L) := by
  intro h hh
  obtain ⟨e, he, rfl⟩ := mem_lineOf.1 hh
  exact ⟨phi_totalDegree _, fun v hv => support_rV V e (vars_phi _ v hv)⟩

/-- Extending the sequence by one line, unless it is already present. The invariant is that the
sequence consists of the line `{0}` and the images of the lines of `𝓛`. -/
theorem step_ext {Φ : CNF} {V : Finset ℕ} {𝓛 : Finset (Finset (LEq (ZMod p)))}
    {l : List (Pang.Line p)} (hl : PSeq Φ V l) (hnd : l.Nodup)
    (hts : l.toFinset = insert {0} (𝓛.image (lineOf V))) (L' : Finset (LEq (ZMod p)))
    (hinf : ∃ prem : List ℕ, (∀ j ∈ prem, j < l.length) ∧
      Pang.Infer Φ V (prem.map fun j => l.getD j ∅) (lineOf V L')) :
    ∃ l' : List (Pang.Line p), PSeq Φ V l' ∧ l'.Nodup ∧
      l'.toFinset = insert {0} ((insert L' 𝓛).image (lineOf V)) := by
  by_cases hm : lineOf V L' ∈ l
  · refine ⟨l, hl, hnd, ?_⟩
    rw [Finset.image_insert, hts]
    have : lineOf V L' ∈ insert {0} (𝓛.image (lineOf V)) := by rw [← hts]; exact List.mem_toFinset.2 hm
    rw [Finset.insert_comm, Finset.insert_eq_of_mem this]
  · obtain ⟨prem, hp, hinf⟩ := hinf
    refine ⟨l ++ [lineOf V L'], hl.snoc prem hp hinf (wf_lineOf L'), ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hnd, List.nodup_singleton _, ?_⟩
      intro x hx y hy hxy
      rw [List.mem_singleton] at hy
      subst hy; subst hxy
      exact hm hx
    · rw [Finset.image_insert, Finset.insert_comm, ← hts]
      ext x; simp [or_comm]

/-- **Embedding of `RLDag` into Pang's system (core).** -/
theorem rldag_to_pseq {Φ : CNF} {V : Finset ℕ} (hΦ : ∀ D ∈ Φ, ∀ l ∈ D, l.var ∈ V)
    {𝓛 : Finset (Finset (LEq (ZMod p)))} (h : RLDag (linAx Φ ∪ boolAx) 𝓛) :
    ∃ l : List (Pang.Line p), PSeq Φ V l ∧ l.Nodup ∧
      l.toFinset = insert {0} (𝓛.image (lineOf V)) := by
  induction h with
  | empty =>
    refine ⟨[({0} : Pang.Line p)], ?_, by simp, by simp⟩
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    refine ⟨[], by simp, ?_, ?_⟩
    · simpa using (Pang.Infer.zero (Φ := Φ) (V := V) (p := p))
    · intro h hh
      simp at hh; subst hh
      exact ⟨by simp, fun v hv => by simp at hv⟩
  | @ax 𝓛 C _ hC ih =>
    obtain ⟨l, hl, hnd, hts⟩ := ih
    refine step_ext hl hnd hts C ?_
    rcases hC with ⟨D, hD, rfl⟩ | ⟨i, rfl⟩
    · refine ⟨[], by simp, ?_⟩
      rw [lineOf_axClause (hΦ D hD)]; exact Pang.Infer.init D hD
    · by_cases hi : i ∈ V
      · refine ⟨[], by simp, ?_⟩
        have : lineOf V (boolCl (F := ZMod p) i) = {X i, X i - 1} := by
          have hr : ∀ a : ZMod p, rV V (Finsupp.single i (1 : ZMod p), a) = (Finsupp.single i 1, a) := by
            intro a
            exact rV_eq_self V _ fun j hj => by
              have := Finset.mem_singleton.1 (Finsupp.support_single_subset hj)
              rw [this]; exact hi
          simp [lineOf, boolCl, hr, phi, lin_single]
        rw [this]; exact Pang.Infer.bool i hi
      · have hz' : ({0} : Pang.Line p) ∈ l := List.mem_toFinset.1 (by rw [hts]; simp)
        obtain ⟨j, hj, hgj⟩ := idx_of_mem hz'
        refine ⟨[j], by simpa using hj, ?_⟩
        have : ([j].map fun k => l.getD k ∅) = [({0} : Pang.Line p)] := by
          simp only [List.map_cons, List.map_nil, hgj]
        rw [this]
        refine Pang.Infer.weak _ ?_
        intro q hq
        rw [Finset.mem_singleton] at hq; subst hq
        refine mem_lineOf.2 ⟨(Finsupp.single i 1, 0), by simp [boolCl], ?_⟩
        simp [rV, phi, lin, Finsupp.filter_single_of_neg (p := fun j => j ∈ V) hi]
  | @weak 𝓛 L0 L' _ hL0 hsub ih =>
    obtain ⟨l, hl, hnd, hts⟩ := ih
    have hmem : lineOf V L0 ∈ l := by
      rw [← List.mem_toFinset, hts]; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hL0)
    obtain ⟨i, hi, hgi⟩ := idx_of_mem hmem
    refine step_ext hl hnd hts L' ⟨[i], by simpa using hi, ?_⟩
    have : ([i].map fun j => l.getD j ∅) = [lineOf V L0] := by
      simp only [List.map_cons, List.map_nil, hgi]
    rw [this]
    exact Pang.Infer.weak _ (lineOf_mono hsub)
  | @comb 𝓛 A B e1 e2 α β _ hA hB h1 h2 ih =>
    obtain ⟨l, hl, hnd, hts⟩ := ih
    have hmA : lineOf V A ∈ l := by
      rw [← List.mem_toFinset, hts]; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hA)
    have hmB : lineOf V B ∈ l := by
      rw [← List.mem_toFinset, hts]; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hB)
    obtain ⟨i, hi, hgi⟩ := idx_of_mem hmA
    obtain ⟨j, hj, hgj⟩ := idx_of_mem hmB
    refine step_ext hl hnd hts _ ⟨[i, j], by simp [hi, hj], ?_⟩
    have : ([i, j].map fun j => l.getD j ∅) = [lineOf V A, lineOf V B] := by
      simp only [List.map_cons, List.map_nil, hgi, hgj]
    rw [this]
    refine Pang.Infer.comb (f := phi (rV V e1)) (g := phi (rV V e2)) (phi_mem_lineOf h1)
      (phi_mem_lineOf h2) α β _ ?_
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact mem_lineOf.2 ⟨cmb α β e1 e2, by simp, by rw [rV_cmb, phi_cmb]⟩
    · rcases Finset.mem_union.1 hx with hx | hx
      · have := lineOf_erase_subset V A e1 hx
        exact lineOf_mono (by intro y hy; simp [hy]) this
      · have := lineOf_erase_subset V B e2 hx
        exact lineOf_mono (by intro y hy; simp [hy]) this
  | @simp 𝓛 L c _ hc h0 ih =>
    obtain ⟨l, hl, hnd, hts⟩ := ih
    have hmem : lineOf V (insert ((0 : ℕ →₀ ZMod p), c) L) ∈ l := by
      rw [← List.mem_toFinset, hts]; exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ h0)
    obtain ⟨i, hi, hgi⟩ := idx_of_mem hmem
    refine step_ext hl hnd hts L ⟨[i], by simpa using hi, ?_⟩
    have : ([i].map fun j => l.getD j ∅) = [lineOf V (insert ((0 : ℕ →₀ ZMod p), c) L)] := by
      simp only [List.map_cons, List.map_nil, hgi]
    rw [this]
    have hphi : phi (rV V ((0 : ℕ →₀ ZMod p), c)) = C (-c) := by simp [phi, lin, rV, Finsupp.filter_zero]
    refine Pang.Infer.falseConst (-c) (neg_ne_zero.2 hc) ?_ _ ?_
    · rw [← hphi]; exact phi_mem_lineOf (Finset.mem_insert_self _ _)
    · intro x hx
      rw [← hphi] at hx
      have := lineOf_erase_subset V (insert ((0 : ℕ →₀ ZMod p), c) L) ((0 : ℕ →₀ ZMod p), c) hx
      refine lineOf_mono ?_ this
      intro y hy
      rcases Finset.mem_erase.1 hy with ⟨hne, hy⟩
      exact (Finset.mem_insert.1 hy).resolve_left hne

/-- **`RLDag` embeds in `Pang.Refutation` with one extra node.** If every variable of the clauses
of `Φ` lies in `V`, a refutation of `Φ` (encoded as the linear clauses `linAx Φ`, with the Boolean
axioms) with `n` lines of `RLDag` gives a `Pang.Refutation Φ V p` with at most `n + 1` nodes.
There is no assumption on the variables used inside the `RLDag` derivation. -/
theorem rldag_to_pang {Φ : CNF} {V : Finset ℕ} (hΦ : ∀ D ∈ Φ, ∀ l ∈ D, l.var ∈ V)
    {𝓛 : Finset (Finset (LEq (ZMod p)))}
    (h : RLDag (linAx Φ ∪ boolAx) 𝓛) (h0 : (∅ : Finset (LEq (ZMod p))) ∈ 𝓛) :
    ∃ R : Pang.Refutation Φ V p, R.S ≤ 𝓛.card + 1 := by
  obtain ⟨l, hl, hnd, hts⟩ := rldag_to_pseq hΦ h
  have hmem : (∅ : Pang.Line p) ∈ l := by
    rw [← List.mem_toFinset, hts]
    exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨∅, h0, by simp [lineOf]⟩)
  obtain ⟨k, hk, hgk⟩ := idx_of_mem hmem
  have hlen : l.length ≤ 𝓛.card + 1 := by
    rw [← List.toFinset_card_of_nodup hnd, hts]
    exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ Finset.card_image_le)
  refine ⟨{ S := k + 1
            line := fun i => l.getD i ∅
            prem := fun i => if hi : i < l.length then (hl i hi).choose else []
            S_pos := Nat.succ_pos _
            prem_lt := ?_
            infer := ?_
            wf := ?_
            last := by simpa using hgk }, ?_⟩
  · intro i hi j hj
    have hil : i < l.length := by omega
    rw [dif_pos hil] at hj
    exact (hl i hil).choose_spec.1 j hj
  · intro i hi
    have hil : i < l.length := by omega
    rw [dif_pos hil]
    exact (hl i hil).choose_spec.2.1
  · intro i hi
    have hil : i < l.length := by omega
    exact (hl i hil).choose_spec.2.2
  · show k + 1 ≤ 𝓛.card + 1
    omega

end

end RLF

end SATurday.ProofComplexity
