import Theory.ProofComplexity.EmbedPang
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Pang's `Res(lin F_p)` embeds in `RLDag` over `F_p` (converse of `EmbedPang`)

`pang_to_rldag`: a `Pang.Refutation Phi V p` with `S` nodes gives an `RLDag` refutation with at most
`2 S` lines, from the linear clauses `linAx Phi`, the Boolean axioms and the single trivial clause
`zeroCl = {0 = 0}` (Pang has `0 = 0` as an axiom; `RLDag` does not). The factor 2: Pang's
`comb`, `mul` and `falseConst` have weakening fused into the step, `RLDag` needs a separate
weakening line. The restricted `mul` (`(f * g).totalDegree <= 1`) is a scalar multiplication
(`g` constant) or acts on a constant `f`, which is a false constant (deleted) or `0`
(replaced by `0 = 0`); each is one `comb` or one `simp` step of `RLDag`.

Together with `rldag_to_pang` (`n` lines of `RLDag` give at most `n + 1` Pang nodes) this shows
the two dag-like systems p-simulate each other with line counts within a factor 2, for the clause
encoding `litLE` (see EmbedPang.lean for the encoding caveat) and with the extra axiom `zeroCl`.
-/

open SATurday.ProofComplexity MvPolynomial

namespace SATurday.ProofComplexity

namespace RLF

noncomputable section

open Classical

variable {p : ℕ} [Fact p.Prime]

/-- Same instance as in `EmbedPang` (see there). -/
local instance instDecEqLEq' : DecidableEq (LEq (ZMod p)) := leqDec (ZMod p)

/-- A chosen equation with `phi e = h`, if there is one. -/
def psi (h : Pang.Poly p) : LEq (ZMod p) :=
  if hh : ∃ e, phi e = h then hh.choose else (0, 0)

theorem phi_psi {h : Pang.Poly p} (hh : ∃ e, phi e = h) : phi (psi h) = h := by
  unfold psi; rw [dif_pos hh]; exact hh.choose_spec

theorem psi_phi (e : LEq (ZMod p)) : psi (phi e) = e := by
  have := phi_psi (h := phi e) ⟨e, rfl⟩
  exact phi_injective this

theorem psi_injOn {h h' : Pang.Poly p} (hh : ∃ e, phi e = h) (hh' : ∃ e, phi e = h')
    (he : psi h = psi h') : h = h' := by
  rw [← phi_psi hh, ← phi_psi hh', he]

/-- The linear clause of a Pang line. -/
def lineBack (M : Pang.Line p) : Finset (LEq (ZMod p)) := M.image psi

/-- Every polynomial of the line has degree at most one. -/
def Lin (M : Pang.Line p) : Prop := ∀ h ∈ M, ∃ e, phi e = h

theorem lin_of_wf {V : Finset ℕ} {M : Pang.Line p} (h : Pang.WF V M) : Lin M :=
  fun q hq => exists_phi q (h q hq).1

theorem lineBack_mono {M M' : Pang.Line p} (h : M ⊆ M') : lineBack M ⊆ lineBack M' :=
  Finset.image_subset_image h

theorem psi_mem {M : Pang.Line p} {q : Pang.Poly p} (h : q ∈ M) : psi q ∈ lineBack M :=
  Finset.mem_image_of_mem _ h

theorem lineBack_erase {M : Pang.Line p} {f : Pang.Poly p} :
    (lineBack M).erase (psi f) ⊆ lineBack (M.erase f) := by
  intro y hy
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hy
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hmem
  exact Finset.mem_image.2 ⟨q, Finset.mem_erase.2 ⟨fun h => hne (h ▸ rfl), hq⟩, rfl⟩

theorem cmb_psi {f g : Pang.Poly p} (hf : ∃ e, phi e = f) (hg : ∃ e, phi e = g) (a b : ZMod p) :
    cmb a b (psi f) (psi g) = psi (C a * f + C b * g) := by
  rw [← psi_phi (cmb a b (psi f) (psi g)), phi_cmb, phi_psi hf, phi_psi hg]

/-- The trivial clause `0 = 0`. -/
def zeroCl : Finset (LEq (ZMod p)) := {((0 : ℕ →₀ ZMod p), 0)}

section Steps

variable {Ax : Set (Finset (LEq (ZMod p)))}

theorem ext_ax {𝓛 : Finset (Finset (LEq (ZMod p)))} (hD : RLDag Ax 𝓛) {C : Finset (LEq (ZMod p))}
    (hC : C ∈ Ax) :
    ∃ 𝓛', RLDag Ax 𝓛' ∧ 𝓛 ⊆ 𝓛' ∧ C ∈ 𝓛' ∧ 𝓛'.card ≤ 𝓛.card + 2 :=
  ⟨insert C 𝓛, RLDag.ax C hD hC, Finset.subset_insert _ _, Finset.mem_insert_self _ _,
    by have := Finset.card_insert_le C 𝓛; omega⟩

theorem ext_weak {𝓛 : Finset (Finset (LEq (ZMod p)))} (hD : RLDag Ax 𝓛)
    {L T : Finset (LEq (ZMod p))} (hL : L ∈ 𝓛) (hT : L ⊆ T) :
    ∃ 𝓛', RLDag Ax 𝓛' ∧ 𝓛 ⊆ 𝓛' ∧ T ∈ 𝓛' ∧ 𝓛'.card ≤ 𝓛.card + 2 :=
  ⟨insert T 𝓛, RLDag.weak L T hD hL hT, Finset.subset_insert _ _, Finset.mem_insert_self _ _,
    by have := Finset.card_insert_le T 𝓛; omega⟩

theorem ext_comb {𝓛 : Finset (Finset (LEq (ZMod p)))} (hD : RLDag Ax 𝓛)
    {A B T : Finset (LEq (ZMod p))} {e1 e2 : LEq (ZMod p)} (hA : A ∈ 𝓛) (hB : B ∈ 𝓛)
    (h1 : e1 ∈ A) (h2 : e2 ∈ B) (α β : ZMod p)
    (hT : A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2} ⊆ T) :
    ∃ 𝓛', RLDag Ax 𝓛' ∧ 𝓛 ⊆ 𝓛' ∧ T ∈ 𝓛' ∧ 𝓛'.card ≤ 𝓛.card + 2 := by
  have h := RLDag.comb A B e1 e2 α β hD hA hB h1 h2
  refine ⟨insert T (insert (A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2}) 𝓛),
    RLDag.weak _ T h (Finset.mem_insert_self _ _) hT,
    fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),
    Finset.mem_insert_self _ _, ?_⟩
  have := Finset.card_insert_le T (insert (A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2}) 𝓛)
  have := Finset.card_insert_le (A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2}) 𝓛
  omega

theorem ext_simp {𝓛 : Finset (Finset (LEq (ZMod p)))} (hD : RLDag Ax 𝓛)
    {L T : Finset (LEq (ZMod p))} (c : ZMod p) (hc : c ≠ 0)
    (h0 : insert ((0 : ℕ →₀ ZMod p), c) L ∈ 𝓛) (hT : L ⊆ T) :
    ∃ 𝓛', RLDag Ax 𝓛' ∧ 𝓛 ⊆ 𝓛' ∧ T ∈ 𝓛' ∧ 𝓛'.card ≤ 𝓛.card + 2 := by
  have h := RLDag.simp L c hD hc h0
  refine ⟨insert T (insert L 𝓛), RLDag.weak _ T h (Finset.mem_insert_self _ _) hT,
    fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),
    Finset.mem_insert_self _ _, ?_⟩
  have := Finset.card_insert_le T (insert L 𝓛)
  have := Finset.card_insert_le L 𝓛
  omega

theorem ext_comb_pang {𝓛 : Finset (Finset (LEq (ZMod p)))} (hD : RLDag Ax 𝓛)
    {L₁ L₂ L' : Pang.Line p} {f g : Pang.Poly p} (hA : lineBack L₁ ∈ 𝓛) (hB : lineBack L₂ ∈ 𝓛)
    (hl1 : Lin L₁) (hl2 : Lin L₂) (hf : f ∈ L₁) (hg : g ∈ L₂) (a b : ZMod p)
    (h : insert (C a * f + C b * g) (L₁.erase f ∪ L₂.erase g) ⊆ L') :
    ∃ 𝓛', RLDag Ax 𝓛' ∧ 𝓛 ⊆ 𝓛' ∧ lineBack L' ∈ 𝓛' ∧ 𝓛'.card ≤ 𝓛.card + 2 := by
  refine ext_comb hD hA hB (psi_mem hf) (psi_mem hg) a b ?_
  intro x hx
  simp only [Finset.mem_union, Finset.mem_singleton] at hx
  rcases hx with (hx | hx) | rfl
  · exact lineBack_mono (fun y hy => h (Finset.mem_insert_of_mem (Finset.mem_union_left _ hy)))
      (lineBack_erase hx)
  · exact lineBack_mono (fun y hy => h (Finset.mem_insert_of_mem (Finset.mem_union_right _ hy)))
      (lineBack_erase hx)
  · rw [cmb_psi (hl1 f hf) (hl2 g hg)]
    exact psi_mem (h (Finset.mem_insert_self _ _))

theorem ext_drop {𝓛 : Finset (Finset (LEq (ZMod p)))} (hD : RLDag Ax 𝓛)
    {L L' : Pang.Line p} {f : Pang.Poly p} (hA : lineBack L ∈ 𝓛) (hf : f ∈ L) (c : ZMod p)
    (hc : c ≠ 0) (hfc : f = C c) (h : L.erase f ⊆ L') :
    ∃ 𝓛', RLDag Ax 𝓛' ∧ 𝓛 ⊆ 𝓛' ∧ lineBack L' ∈ 𝓛' ∧ 𝓛'.card ≤ 𝓛.card + 2 := by
  have hpsi : psi f = ((0 : ℕ →₀ ZMod p), -c) := by
    have : phi ((0 : ℕ →₀ ZMod p), -c) = f := by simp [phi, lin, hfc]
    rw [← this, psi_phi]
  refine ext_simp hD (L := lineBack (L.erase f)) (-c) (neg_ne_zero.2 hc) ?_ (lineBack_mono h)
  have : insert ((0 : ℕ →₀ ZMod p), -c) (lineBack (L.erase f)) = lineBack L := by
    rw [← hpsi]
    unfold lineBack
    rw [← Finset.image_insert, Finset.insert_erase hf]
  rw [this]; exact hA

end Steps

theorem lineBack_clauseLine (C : Clause) :
    lineBack (Pang.clauseLine C : Pang.Line p) = axClause C := by
  unfold lineBack Pang.clauseLine axClause
  rw [Finset.image_image]
  refine Finset.image_congr fun l _ => ?_
  simp only [Function.comp]
  rw [← phi_litLE, psi_phi]

/-- Adding the line of node `k` of a Pang refutation, given the earlier ones. -/
theorem node_step {Φ : CNF} {V : Finset ℕ} (R : Pang.Refutation Φ V p) {k : ℕ} (hk : k < R.S)
    {𝓛 : Finset (Finset (LEq (ZMod p)))}
    (hD : RLDag (linAx Φ ∪ {zeroCl} ∪ boolAx) 𝓛)
    (hprev : ∀ j < k, lineBack (R.line j) ∈ 𝓛) :
    ∃ 𝓛', RLDag (linAx Φ ∪ {zeroCl} ∪ boolAx) 𝓛' ∧ 𝓛 ⊆ 𝓛' ∧
      lineBack (R.line k) ∈ 𝓛' ∧ 𝓛'.card ≤ 𝓛.card + 2 := by
  have hinf := R.infer k hk
  have hwf := R.wf k hk
  have hmemP : ∀ L ∈ (R.prem k).map R.line, lineBack L ∈ 𝓛 ∧ Lin L := by
    intro L hL
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hL
    have hjk := R.prem_lt k hk j hj
    exact ⟨hprev j hjk, lin_of_wf (R.wf j (hjk.trans hk))⟩
  generalize (R.prem k).map R.line = Ls at hinf hmemP
  generalize R.line k = Lk at hinf hwf ⊢
  cases hinf with
  | init C hC =>
    exact ext_ax hD (C := lineBack (Pang.clauseLine C))
      (Or.inl (Or.inl ⟨C, hC, lineBack_clauseLine C⟩))
  | zero =>
    have : lineBack ({0} : Pang.Line p) = zeroCl := by
      have : psi (0 : Pang.Poly p) = ((0 : ℕ →₀ ZMod p), 0) := by
        have h : phi ((0 : ℕ →₀ ZMod p), (0 : ZMod p)) = 0 := by simp [phi, lin]
        rw [← h, psi_phi]
      simp [lineBack, zeroCl, this]
    rw [this]
    exact ext_ax hD (C := zeroCl) (Or.inl (Or.inr rfl))
  | bool i hi =>
    have : lineBack ({X i, X i - 1} : Pang.Line p) = boolCl i := by
      have h0 : psi (X i : Pang.Poly p) = (Finsupp.single i 1, 0) := by
        have h : phi (Finsupp.single i (1 : ZMod p), (0 : ZMod p)) = X i := by
          simp [phi, lin_single]
        rw [← h, psi_phi]
      have h1 : psi (X i - 1 : Pang.Poly p) = (Finsupp.single i 1, 1) := by
        have h : phi (Finsupp.single i (1 : ZMod p), (1 : ZMod p)) = X i - 1 := by
          simp [phi, lin_single]
        rw [← h, psi_phi]
      simp [lineBack, boolCl, h0, h1]
    rw [this]
    exact ext_ax hD (C := boolCl i) (Or.inr ⟨i, rfl⟩)
  | weak L' h =>
    exact ext_weak hD (hmemP _ (List.mem_singleton_self _)).1 (lineBack_mono h)
  | falseConst c hc hmem L' h =>
    exact ext_drop hD (hmemP _ (List.mem_singleton_self _)).1 hmem c hc rfl h
  | comb hf hg a b L' h =>
    exact ext_comb_pang hD (hmemP _ (by simp)).1 (hmemP _ (by simp)).1 (hmemP _ (by simp)).2
      (hmemP _ (by simp)).2 hf hg a b h
  | @mul L f hf g hdeg hvars _ h =>
    obtain ⟨hA, hlin⟩ := hmemP L (List.mem_singleton_self _)
    have hsub : L.erase f ⊆ Lk := fun x hx => h (Finset.mem_insert_of_mem hx)
    have hfg : f * g ∈ Lk := h (Finset.mem_insert_self _ _)
    by_cases hf0 : f = 0
    · refine ext_comb_pang hD hA hA hlin hlin hf hf 0 0 ?_
      have : C (0 : ZMod p) * f + C 0 * f = f * g := by simp [hf0]
      rw [this]
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hfg
      · exact hsub (by simpa using hx)
    by_cases hg0 : g.totalDegree = 0
    · obtain ⟨c, hc⟩ : ∃ c, g = C c := ⟨_, totalDegree_eq_zero_iff_eq_C.mp hg0⟩
      refine ext_comb_pang hD hA hA hlin hlin hf hf c 0 ?_
      have : C c * f + C (0 : ZMod p) * f = f * g := by rw [hc]; simp [mul_comm]
      rw [this]
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hfg
      · exact hsub (by simpa using hx)
    · have hg' : g ≠ 0 := fun h0 => hg0 (by simp [h0])
      have hdm := totalDegree_mul_of_isDomain hf0 hg'
      have hfd : f.totalDegree = 0 := by omega
      obtain ⟨c, hc⟩ : ∃ c, f = C c := ⟨_, totalDegree_eq_zero_iff_eq_C.mp hfd⟩
      have hc0 : c ≠ 0 := fun h0 => hf0 (by simp [hc, h0])
      exact ext_drop hD hA hf c hc0 hc hsub
