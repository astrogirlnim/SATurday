import Theory.ProofComplexity.EmbedPangLin

/-!
# `RLDag` over `F_p` embeds in Pang's `Res(lin F_p)` (`Pang.Refutation`), size-preservingly

`RLF.RLDag` (dag-like `Res(lin F_p)` with syntactic weakening, ResLinFDag.lean) is the calculus of
Part and Tzameret. `Pang.Refutation` (PangDag.lean) has the rules of Pang (axioms, weakening,
false-constant deletion, linear combination, multiplication by a polynomial keeping degree `<= 1`),
with weakening fused into `comb`, `mul` and `falseConst`. This file proves

* `rldag_to_pang`: a refutation of the CNF `Phi` (encoded as linear clauses by `linAx Phi`)
  consisting of `n` lines of `RLDag` gives a `Pang.Refutation Phi V p` with at most `n` nodes
  (the variable set `V` only has to contain the variables occurring in the derivation).

So the Lean `Pang.Refutation` system is at least as strong as `RLDag`, with no loss in size. The
encoding of the clause `l_1 v ... v l_k` as the linear clause is `litEq`: a positive literal `x = 1`
is encoded as `-x = -1` and a negative literal `x = 0` as `x = 0`, so that `phi (litEq l) = litPoly l`
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

/-- The encoding of a literal as a linear equation; `phi (litEq l) = litPoly l`. -/
def litEq (l : Literal) : LEq (ZMod p) :=
  if l.pos then (-(Finsupp.single l.var 1), -1) else (Finsupp.single l.var 1, 0)

theorem phi_litEq (l : Literal) : phi (litEq (p := p) l) = litPoly l := by
  unfold litEq litPoly
  cases hp : l.pos
  · simp [phi, lin_single]
  · simp only [if_true, phi]
    have : lin (-(Finsupp.single l.var (1 : ZMod p))) = - X l.var := by
      have h := lin_smul (-1 : ZMod p) (Finsupp.single l.var 1)
      rw [neg_one_smul] at h
      rw [h, lin_single]; simp
    rw [this]; simp; ring

/-- A clause as a linear clause. -/
def axClause (C : Clause) : Finset (LEq (ZMod p)) := C.image litEq

/-- The CNF `Φ` as a set of linear clauses. -/
def linAx (Φ : CNF) : Set (Finset (LEq (ZMod p))) := {L | ∃ C ∈ Φ, L = axClause C}

/-- The Pang line of a linear clause. -/
def lineOf (L : Finset (LEq (ZMod p))) : Pang.Line p := L.image phi

theorem lineOf_axClause (C : Clause) : lineOf (axClause (p := p) C) = Pang.clauseLine C := by
  unfold lineOf axClause Pang.clauseLine
  rw [Finset.image_image]
  refine Finset.image_congr fun l _ => ?_
  exact phi_litEq l

theorem lineOf_mono {L L' : Finset (LEq (ZMod p))} (h : L ⊆ L') : lineOf L ⊆ lineOf L' :=
  Finset.image_subset_image h

theorem mem_lineOf {L : Finset (LEq (ZMod p))} {h : Pang.Poly p} :
    h ∈ lineOf L ↔ ∃ e ∈ L, phi e = h := by
  unfold lineOf; simp

theorem phi_mem_lineOf {L : Finset (LEq (ZMod p))} {e : LEq (ZMod p)} :
    phi e ∈ lineOf L ↔ e ∈ L := by
  rw [mem_lineOf]
  constructor
  · rintro ⟨e', he', h⟩; rw [← phi_injective h]; exact he'
  · intro h; exact ⟨e, h, rfl⟩

theorem lineOf_erase_subset (L : Finset (LEq (ZMod p))) (e : LEq (ZMod p)) :
    (lineOf L).erase (phi e) ⊆ lineOf (L.erase e) := by
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

theorem wf_lineOf {V : Finset ℕ} {L : Finset (LEq (ZMod p))} (hV : ∀ e ∈ L, e.1.support ⊆ V) :
    Pang.WF V (lineOf L) := by
  intro h hh
  obtain ⟨e, he, rfl⟩ := mem_lineOf.1 hh
  exact ⟨phi_totalDegree e, fun v hv => hV e he (vars_phi e v hv)⟩

/-- Extending the sequence by one line, unless it is already present. -/
theorem step_ext {Φ : CNF} {V : Finset ℕ} {𝓛 : Finset (Finset (LEq (ZMod p)))}
    {l : List (Pang.Line p)} (hl : PSeq Φ V l) (hnd : l.Nodup)
    (hts : l.toFinset = 𝓛.image lineOf) (L' : Finset (LEq (ZMod p)))
    (hw : Pang.WF V (lineOf L'))
    (hinf : ∃ prem : List ℕ, (∀ j ∈ prem, j < l.length) ∧
      Pang.Infer Φ V (prem.map fun j => l.getD j ∅) (lineOf L')) :
    ∃ l' : List (Pang.Line p), PSeq Φ V l' ∧ l'.Nodup ∧
      l'.toFinset = (insert L' 𝓛).image lineOf := by
  by_cases hm : lineOf L' ∈ l
  · refine ⟨l, hl, hnd, ?_⟩
    rw [Finset.image_insert, hts]
    exact (Finset.insert_eq_of_mem (by rw [← hts]; exact List.mem_toFinset.2 hm)).symm
  · obtain ⟨prem, hp, hinf⟩ := hinf
    refine ⟨l ++ [lineOf L'], hl.snoc prem hp hinf hw, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hnd, List.nodup_singleton _, ?_⟩
      intro x hx y hy hxy
      rw [List.mem_singleton] at hy
      subst hy; subst hxy
      exact hm hx
    · rw [Finset.image_insert, ← hts]
      ext x; simp [or_comm]

/-- **Embedding of `RLDag` into Pang's system (core).** Every derivation of `RLDag` from the
CNF encoding gives a Pang sequence containing exactly the images of its lines. -/
theorem rldag_to_pseq {Φ : CNF} {V : Finset ℕ} {Ax : Set (Finset (LEq (ZMod p)))}
    (hax : ∀ C ∈ Ax, (∃ D ∈ Φ, lineOf C = Pang.clauseLine D) ∨ lineOf C = {0})
    {𝓛 : Finset (Finset (LEq (ZMod p)))} (h : RLDag (Ax ∪ boolAx) 𝓛) :
    (∀ L ∈ 𝓛, ∀ e ∈ L, e.1.support ⊆ V) →
    ∃ l : List (Pang.Line p), PSeq Φ V l ∧ l.Nodup ∧ l.toFinset = 𝓛.image lineOf := by
  induction h with
  | empty => intro _; exact ⟨[], fun i hi => by simp at hi, List.nodup_nil, by simp⟩
  | @ax 𝓛 C _ hC ih =>
    intro hV
    obtain ⟨l, hl, hnd, hts⟩ := ih fun L hL => hV L (Finset.mem_insert_of_mem hL)
    have hVC : ∀ e ∈ C, e.1.support ⊆ V := hV C (Finset.mem_insert_self _ _)
    refine step_ext hl hnd hts C (wf_lineOf hVC) ⟨[], by simp, ?_⟩
    rcases hC with hC | ⟨i, rfl⟩
    · rcases hax C hC with ⟨D, hD, h⟩ | h
      · rw [h]; exact Pang.Infer.init D hD
      · rw [h]; exact Pang.Infer.zero
    · have hi : i ∈ V := by
        have := hVC (Finsupp.single i 1, 0) (by simp [boolCl])
        exact this (by simp)
      have : lineOf (boolCl (F := ZMod p) i) = {X i, X i - 1} := by
        simp [lineOf, boolCl, phi, lin_single]
      rw [this]; exact Pang.Infer.bool i hi
  | @weak 𝓛 L0 L' _ hL0 hsub ih =>
    intro hV
    obtain ⟨l, hl, hnd, hts⟩ := ih fun L hL => hV L (Finset.mem_insert_of_mem hL)
    have hVC : ∀ e ∈ L', e.1.support ⊆ V := hV L' (Finset.mem_insert_self _ _)
    have hmem : lineOf L0 ∈ l := by
      rw [← List.mem_toFinset, hts]; exact Finset.mem_image_of_mem _ hL0
    obtain ⟨i, hi, hgi⟩ := idx_of_mem hmem
    refine step_ext hl hnd hts L' (wf_lineOf hVC) ⟨[i], by simpa using hi, ?_⟩
    have : ([i].map fun j => l.getD j ∅) = [lineOf L0] := by simp only [List.map_cons, List.map_nil, hgi]
    rw [this]
    exact Pang.Infer.weak _ (lineOf_mono hsub)
  | @comb 𝓛 A B e1 e2 α β _ hA hB h1 h2 ih =>
    intro hV
    obtain ⟨l, hl, hnd, hts⟩ := ih fun L hL => hV L (Finset.mem_insert_of_mem hL)
    have hVC : ∀ e ∈ A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2}, e.1.support ⊆ V :=
      hV _ (Finset.mem_insert_self _ _)
    have hmA : lineOf A ∈ l := by
      rw [← List.mem_toFinset, hts]; exact Finset.mem_image_of_mem _ hA
    have hmB : lineOf B ∈ l := by
      rw [← List.mem_toFinset, hts]; exact Finset.mem_image_of_mem _ hB
    obtain ⟨i, hi, hgi⟩ := idx_of_mem hmA
    obtain ⟨j, hj, hgj⟩ := idx_of_mem hmB
    refine step_ext hl hnd hts _ (wf_lineOf hVC) ⟨[i, j], by simp [hi, hj], ?_⟩
    have : ([i, j].map fun j => l.getD j ∅) = [lineOf A, lineOf B] := by simp only [List.map_cons, List.map_nil, hgi, hgj]
    rw [this]
    refine Pang.Infer.comb (f := phi e1) (g := phi e2) (phi_mem_lineOf.2 h1)
      (phi_mem_lineOf.2 h2) α β _ ?_
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact mem_lineOf.2 ⟨cmb α β e1 e2, by simp, phi_cmb α β e1 e2⟩
    · rcases Finset.mem_union.1 hx with hx | hx
      · have := lineOf_erase_subset A e1 hx
        exact lineOf_mono (by intro y hy; simp [hy]) this
      · have := lineOf_erase_subset B e2 hx
        exact lineOf_mono (by intro y hy; simp [hy]) this
  | @simp 𝓛 L c _ hc h0 ih =>
    intro hV
    obtain ⟨l, hl, hnd, hts⟩ := ih fun L' hL => hV L' (Finset.mem_insert_of_mem hL)
    have hVC : ∀ e ∈ L, e.1.support ⊆ V := hV L (Finset.mem_insert_self _ _)
    have hmem : lineOf (insert ((0 : ℕ →₀ ZMod p), c) L) ∈ l := by
      rw [← List.mem_toFinset, hts]; exact Finset.mem_image_of_mem _ h0
    obtain ⟨i, hi, hgi⟩ := idx_of_mem hmem
    refine step_ext hl hnd hts L (wf_lineOf hVC) ⟨[i], by simpa using hi, ?_⟩
    have : ([i].map fun j => l.getD j ∅) = [lineOf (insert ((0 : ℕ →₀ ZMod p), c) L)] := by
      simp only [List.map_cons, List.map_nil, hgi]
    rw [this]
    have hphi : phi ((0 : ℕ →₀ ZMod p), c) = C (-c) := by simp [phi, lin]
    refine Pang.Infer.falseConst (-c) (neg_ne_zero.2 hc) ?_ _ ?_
    · rw [← hphi]; exact phi_mem_lineOf.2 (Finset.mem_insert_self _ _)
    · intro x hx
      rw [← hphi] at hx
      have := lineOf_erase_subset (insert ((0 : ℕ →₀ ZMod p), c) L) ((0 : ℕ →₀ ZMod p), c) hx
      refine lineOf_mono ?_ this
      intro y hy
      rcases Finset.mem_erase.1 hy with ⟨hne, hy⟩
      exact (Finset.mem_insert.1 hy).resolve_left hne

/-- **`RLDag` embeds in `Pang.Refutation` without loss of size.** A refutation of `Phi`
(encoded as the linear clauses `linAx Phi`, together with the Boolean axioms and possibly a
set of extra axiom clauses each of which is the image of a Pang initial line) with `n` lines of
`RLDag` gives a `Pang.Refutation Phi V p` with at most `n` nodes. -/
theorem rldag_to_pang {Φ : CNF} {V : Finset ℕ} {𝓛 : Finset (Finset (LEq (ZMod p)))}
    (h : RLDag (linAx Φ ∪ boolAx) 𝓛) (h0 : (∅ : Finset (LEq (ZMod p))) ∈ 𝓛)
    (hV : ∀ L ∈ 𝓛, ∀ e ∈ L, e.1.support ⊆ V) :
    ∃ R : Pang.Refutation Φ V p, R.S ≤ 𝓛.card := by
  have hax : ∀ C ∈ linAx (p := p) Φ,
      (∃ D ∈ Φ, lineOf C = Pang.clauseLine D) ∨ lineOf C = {0} := by
    rintro C ⟨D, hD, rfl⟩
    exact Or.inl ⟨D, hD, lineOf_axClause D⟩
  obtain ⟨l, hl, hnd, hts⟩ := rldag_to_pseq hax h hV
  have hmem : (∅ : Pang.Line p) ∈ l := by
    rw [← List.mem_toFinset, hts]
    exact Finset.mem_image.2 ⟨∅, h0, by simp [lineOf]⟩
  obtain ⟨k, hk, hgk⟩ := idx_of_mem hmem
  have hlen : l.length ≤ 𝓛.card := by
    rw [← List.toFinset_card_of_nodup hnd, hts]; exact Finset.card_image_le
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
  · show k + 1 ≤ 𝓛.card
    omega

end

end RLF

end SATurday.ProofComplexity
