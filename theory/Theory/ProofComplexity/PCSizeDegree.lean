import Theory.ProofComplexity.TseitinBool

/-!
# Size–degree tradeoff for polynomial calculus (Ladder Rung R4, 1C.3)

Multilinear polynomial calculus over a field `F`, with polynomials stored as finitely supported
functions on variable sets (`ML F = Finset ℕ →₀ F`, the set `S` standing for `∏_{i ∈ S} x_i`).
Multiplication by a variable is `S ↦ insert x S`; the restrictions `x := 0` and `x := 1` are
`filter (x ∉ ·)` and `S ↦ S.erase x`.

The Impagliazzo–Pudlák–Sgall argument: a refutation (as a list of lines) with few monomials of
more than `d₀` variables ("fat") is turned, by restricting a variable that occurs in many fat
monomials, into a low degree refutation (`ips`).

LOG: R4 PCSizeDegree module (size–degree tradeoff)
-/

namespace SATurday.ProofComplexity

namespace MLPC

open Finset

noncomputable section

open Classical

variable {F : Type} [Field F]

/-- Multilinear polynomials: coefficients on variable sets. -/
abbrev ML (F : Type) [Field F] := Finset ℕ →₀ F

/-- The constant `1`. -/
def one : ML F := Finsupp.single ∅ 1

/-- Multiplication by the variable `x`. -/
def mulX (x : ℕ) (f : ML F) : ML F := f.mapDomain (insert x)

/-- Restriction `x := 0`. -/
def res0 (x : ℕ) (f : ML F) : ML F := f.filter fun S => x ∉ S

/-- Restriction `x := 1`. -/
def res1 (x : ℕ) (f : ML F) : ML F := f.mapDomain fun S => S.erase x

/-- Killing every monomial with a variable outside `V`. -/
def resV (V : Finset ℕ) (f : ML F) : ML F := f.filter fun S => S ⊆ V

/-- Degree: the largest monomial. -/
def mdeg (f : ML F) : ℕ := f.support.sup Finset.card

/-- Monomials with more than `d₀` variables. -/
def fatS (d₀ : ℕ) (f : ML F) : Finset (Finset ℕ) := f.support.filter fun S => d₀ < S.card

theorem mulX_add (x : ℕ) (f g : ML F) : mulX x (f + g) = mulX x f + mulX x g := Finsupp.mapDomain_add
theorem mulX_smul (x : ℕ) (a : F) (f : ML F) : mulX x (a • f) = a • mulX x f := Finsupp.mapDomain_smul _ _
theorem res1_add (x : ℕ) (f g : ML F) : res1 x (f + g) = res1 x f + res1 x g := Finsupp.mapDomain_add
theorem res1_smul (x : ℕ) (a : F) (f : ML F) : res1 x (a • f) = a • res1 x f := Finsupp.mapDomain_smul _ _
theorem res0_add (x : ℕ) (f g : ML F) : res0 x (f + g) = res0 x f + res0 x g := Finsupp.filter_add
theorem res0_smul (x : ℕ) (a : F) (f : ML F) : res0 x (a • f) = a • res0 x f := Finsupp.filter_smul
theorem resV_add (V : Finset ℕ) (f g : ML F) : resV V (f + g) = resV V f + resV V g := Finsupp.filter_add
theorem resV_smul (V : Finset ℕ) (a : F) (f : ML F) : resV V (a • f) = a • resV V f := Finsupp.filter_smul

theorem mulX_single (x : ℕ) (S : Finset ℕ) (c : F) :
    mulX x (Finsupp.single S c) = Finsupp.single (insert x S) c := Finsupp.mapDomain_single

theorem fsp {p : Finset ℕ → Prop} [DecidablePred p] {S : Finset ℕ} {c : F} (h : p S) :
    (Finsupp.single S c).filter p = Finsupp.single S c := Finsupp.filter_single_of_pos p h

theorem fsn {p : Finset ℕ → Prop} [DecidablePred p] {S : Finset ℕ} {c : F} (h : ¬ p S) :
    (Finsupp.single S c).filter p = 0 := Finsupp.filter_single_of_neg p h

/-- Additive induction for statements about `ML`. -/
theorem ml_induction {P : ML F → Prop} (f : ML F) (h0 : P 0)
    (hadd : ∀ f g, P f → P g → P (f + g)) (hs : ∀ S c, P (Finsupp.single S c)) : P f :=
  Finsupp.induction_linear f h0 hadd hs

theorem res0_mulX_ne {x y : ℕ} (h : y ≠ x) (f : ML F) : res0 x (mulX y f) = mulX y (res0 x f) := by
  induction f using ml_induction with
  | h0 => simp [res0, mulX, Finsupp.filter_zero]
  | hadd f g hf hg => rw [mulX_add, res0_add, hf, hg, res0_add, mulX_add]
  | hs S c =>
    rw [mulX_single]
    unfold res0
    by_cases hx : x ∈ S
    · rw [fsn (by simp [hx]), fsn (by simp [hx])]
      simp [mulX]
    · rw [fsp (by simp [hx, Ne.symm h]),
        fsp hx, mulX_single]

theorem res0_mulX_self (x : ℕ) (f : ML F) : res0 x (mulX x f) = 0 := by
  induction f using ml_induction with
  | h0 => simp [res0, mulX, Finsupp.filter_zero]
  | hadd f g hf hg => rw [mulX_add, res0_add, hf, hg, add_zero]
  | hs S c =>
    rw [mulX_single]; unfold res0
    exact fsn (by simp)

theorem res1_mulX_ne {x y : ℕ} (h : y ≠ x) (f : ML F) : res1 x (mulX y f) = mulX y (res1 x f) := by
  unfold res1 mulX
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1
  funext S
  simp only [Function.comp]
  exact Finset.erase_insert_of_ne h

theorem res1_mulX_self (x : ℕ) (f : ML F) : res1 x (mulX x f) = res1 x f := by
  unfold res1 mulX
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext S
  simp only [Function.comp]
  exact Finset.erase_insert_eq_erase _ _

theorem resV_mulX_mem {V : Finset ℕ} {y : ℕ} (hy : y ∈ V) (f : ML F) :
    resV V (mulX y f) = mulX y (resV V f) := by
  induction f using ml_induction with
  | h0 => simp [resV, mulX, Finsupp.filter_zero]
  | hadd f g hf hg => rw [mulX_add, resV_add, hf, hg, resV_add, mulX_add]
  | hs S c =>
    rw [mulX_single]; unfold resV
    by_cases hS : S ⊆ V
    · rw [fsp (p := fun S => S ⊆ V) (insert_subset hy hS), fsp (p := fun S => S ⊆ V) hS,
        mulX_single]
    · rw [fsn (p := fun S => S ⊆ V) (fun h => hS ((subset_insert _ _).trans h)),
        fsn (p := fun S => S ⊆ V) hS]
      simp [mulX]

theorem resV_mulX_nmem {V : Finset ℕ} {y : ℕ} (hy : y ∉ V) (f : ML F) : resV V (mulX y f) = 0 := by
  induction f using ml_induction with
  | h0 => simp [resV, mulX, Finsupp.filter_zero]
  | hadd f g hf hg => rw [mulX_add, resV_add, hf, hg, add_zero]
  | hs S c =>
    rw [mulX_single]; unfold resV
    exact fsn (fun h => hy (h (mem_insert_self _ _)))

theorem res0_one (x : ℕ) : res0 x (one : ML F) = one :=
  fsp (by simp)

theorem res1_one (x : ℕ) : res1 x (one : ML F) = one := by
  unfold res1 one; rw [Finsupp.mapDomain_single]; simp

theorem resV_one (V : Finset ℕ) : resV V (one : ML F) = one :=
  fsp (empty_subset _)

/-! ## Supports and fat monomials -/

theorem support_res1 (x : ℕ) (f : ML F) : (res1 x f).support ⊆ f.support.image fun S => S.erase x :=
  Finsupp.mapDomain_support

theorem support_mulX (x : ℕ) (f : ML F) : (mulX x f).support ⊆ f.support.image (insert x) :=
  Finsupp.mapDomain_support

theorem fat_res0 (d₀ x : ℕ) (f : ML F) :
    (fatS d₀ (res0 x f)).card + (f.support.filter fun S => d₀ < S.card ∧ x ∈ S).card =
      (fatS d₀ f).card := by
  unfold fatS res0
  rw [Finsupp.support_filter, filter_filter]
  have := card_filter_add_card_filter_not (s := fatS d₀ f) fun S => x ∉ S
  unfold fatS at this
  rw [filter_filter, filter_filter] at this
  rw [← this]
  congr 2
  · ext S; simp [and_comm]
  · ext S; simp

theorem fat_res1 (d₀ x : ℕ) (f : ML F) : (fatS d₀ (res1 x f)).card ≤ (fatS d₀ f).card := by
  have hsub : fatS d₀ (res1 x f) ⊆ (fatS d₀ f).image fun S => S.erase x := by
    intro T hT
    obtain ⟨hT1, hT2⟩ := mem_filter.1 hT
    obtain ⟨S, hS, rfl⟩ := mem_image.1 (support_res1 x f hT1)
    refine mem_image.2 ⟨S, mem_filter.2 ⟨hS, lt_of_lt_of_le hT2 (card_erase_le)⟩, rfl⟩
  exact (card_le_card hsub).trans card_image_le

theorem fat_resV (d₀ : ℕ) (V : Finset ℕ) (f : ML F) : (fatS d₀ (resV V f)).card ≤ (fatS d₀ f).card := by
  refine card_le_card fun S hS => ?_
  obtain ⟨h1, h2⟩ := mem_filter.1 hS
  unfold resV at h1; rw [Finsupp.support_filter] at h1
  exact mem_filter.2 ⟨(mem_filter.1 h1).1, h2⟩

/-! ## Derivations and proofs -/

/-- Degree `d` multilinear derivations. -/
inductive MLD (Ax : Set (ML F)) (d : ℕ) : ML F → Prop
  | ax {f} : f ∈ Ax → mdeg f ≤ d → MLD Ax d f
  | lin {f g} (a b : F) : MLD Ax d f → MLD Ax d g → MLD Ax d (a • f + b • g)
  | mul {f} (x : ℕ) : MLD Ax d f → mdeg (mulX x f) ≤ d → MLD Ax d (mulX x f)

/-- One step of a proof given as a list of lines. -/
def MLStep (Ax : Set (ML F)) (prev : List (ML F)) (f : ML F) : Prop :=
  f ∈ Ax ∨ (∃ g ∈ prev, ∃ h ∈ prev, ∃ a b : F, f = a • g + b • h) ∨ (∃ g ∈ prev, ∃ x, f = mulX x g)

/-- A proof: every line follows from earlier lines. -/
def MLProof (Ax : Set (ML F)) (L : List (ML F)) : Prop :=
  ∀ k (hk : k < L.length), MLStep Ax (L.take k) (L.get ⟨k, hk⟩)

/-- Number of fat monomial occurrences. -/
def fatL (d₀ : ℕ) (L : List (ML F)) : ℕ := (L.map fun f => (fatS d₀ f).card).sum

/-- Size: number of monomial occurrences. -/
def sizeL (L : List (ML F)) : ℕ := (L.map fun f => f.support.card).sum

theorem fatL_le_sizeL (d₀ : ℕ) (L : List (ML F)) : fatL d₀ L ≤ sizeL L := by
  unfold fatL sizeL
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (card_filter_le _ _) ih

theorem mdeg_le {f : ML F} {d : ℕ} : mdeg f ≤ d ↔ ∀ S ∈ f.support, S.card ≤ d := Finset.sup_le_iff

theorem mld_mdeg {Ax : Set (ML F)} {d : ℕ} {f : ML F} (h : MLD Ax d f) : mdeg f ≤ d := by
  induction h with
  | ax _ hd => exact hd
  | lin a b _ _ ihf ihg =>
    rw [mdeg_le] at ihf ihg ⊢
    intro S hS
    have := Finsupp.support_add hS
    rcases mem_union.1 this with h | h
    · exact ihf S (Finsupp.support_smul h)
    · exact ihg S (Finsupp.support_smul h)
  | mul _ _ hd => exact hd

theorem mld_mono {Ax : Set (ML F)} {d d' : ℕ} (hdd : d ≤ d') {f : ML F} (h : MLD Ax d f) :
    MLD Ax d' f := by
  induction h with
  | ax hf hd => exact MLD.ax hf (hd.trans hdd)
  | lin a b _ _ ihf ihg => exact MLD.lin a b ihf ihg
  | mul x _ hd ih => exact MLD.mul x ih (hd.trans hdd)

theorem mld_zero {Ax : Set (ML F)} {d : ℕ} {g : ML F} (hg : MLD Ax d g) : MLD Ax d 0 := by
  have := MLD.lin 0 0 hg hg; simpa using this

theorem fatS_card_zero {d₀ : ℕ} {f : ML F} (h : (fatS d₀ f).card = 0) : mdeg f ≤ d₀ := by
  rw [mdeg_le]
  intro S hS
  by_contra hlt
  have : S ∈ fatS d₀ f := mem_filter.2 ⟨hS, by omega⟩
  rw [card_eq_zero.1 h] at this; simp at this

/-- **Base case**: a proof without fat monomials is a degree `d₀` derivation. -/
theorem mld_of_proof {Ax : Set (ML F)} {L : List (ML F)} {d₀ : ℕ} (hL : MLProof Ax L)
    (hfat : fatL d₀ L = 0) : ∀ g ∈ L, MLD Ax d₀ g := by
  have hdeg : ∀ g ∈ L, mdeg g ≤ d₀ := by
    intro g hg
    apply fatS_card_zero
    unfold fatL at hfat
    exact List.sum_eq_zero_iff.1 hfat _ (List.mem_map.2 ⟨g, hg, rfl⟩)
  have key : ∀ j (hj : j < L.length), MLD Ax d₀ (L.get ⟨j, hj⟩) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    intro hj
    have hmem : L.get ⟨j, hj⟩ ∈ L := List.get_mem _ _
    have hprev : ∀ g ∈ L.take j, MLD Ax d₀ g := by
      intro g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
      have hij : i < j := by simp at hi; omega
      have := ih i hij (by simp at hi; omega)
      simp only [List.getElem_take]
      simpa using this
    rcases hL j hj with hax | ⟨g, hg, h, hh, a, b, he⟩ | ⟨g, hg, x, he⟩
    · exact MLD.ax hax (hdeg _ hmem)
    · rw [he]; exact MLD.lin a b (hprev g hg) (hprev h hh)
    · rw [he]; exact MLD.mul x (hprev g hg) (he ▸ hdeg _ hmem)
  intro g hg
  obtain ⟨⟨j, hj⟩, rfl⟩ := List.mem_iff_get.1 hg
  exact key j hj

/-- A linear map compatible with multiplication by variables maps proofs to proofs. -/
theorem proof_map {Ax : Set (ML F)} {L : List (ML F)} (hL : MLProof Ax L) (ρ : ML F → ML F)
    (hadd : ∀ f g, ρ (f + g) = ρ f + ρ g) (hsmul : ∀ (a : F) f, ρ (a • f) = a • ρ f)
    (hmul : ∀ x g, ρ (mulX x g) = mulX x (ρ g) ∨ ∃ c : F, ρ (mulX x g) = c • ρ g) :
    MLProof (ρ '' Ax) (L.map ρ) := by
  intro k hk
  have hk' : k < L.length := by simpa using hk
  simp only [List.get_eq_getElem, List.getElem_map]
  rw [← List.map_take]
  rcases hL k hk' with hax | ⟨g, hg, h, hh, a, b, he⟩ | ⟨g, hg, x, he⟩
  · exact Or.inl ⟨_, hax, rfl⟩
  · refine Or.inr (Or.inl ⟨ρ g, List.mem_map_of_mem hg, ρ h, List.mem_map_of_mem hh, a, b, ?_⟩)
    simp only [List.get_eq_getElem] at he
    rw [he, hadd, hsmul, hsmul]
  · simp only [List.get_eq_getElem] at he
    rw [he]
    rcases hmul x g with h1 | ⟨c, h1⟩
    · exact Or.inr (Or.inr ⟨ρ g, List.mem_map_of_mem hg, x, h1⟩)
    · refine Or.inr (Or.inl ⟨ρ g, List.mem_map_of_mem hg, ρ g, List.mem_map_of_mem hg, c, 0, ?_⟩)
      rw [h1, zero_smul, add_zero]

/-! ## Combining the two restrictions -/

theorem mulX_sub (x : ℕ) (f g : ML F) : mulX x (f - g) = mulX x f - mulX x g := Finsupp.mapDomain_sub
theorem res1_sub (x : ℕ) (f g : ML F) : res1 x (f - g) = res1 x f - res1 x g := Finsupp.mapDomain_sub

theorem mulX_comm (x y : ℕ) (f : ML F) : mulX x (mulX y f) = mulX y (mulX x f) := by
  unfold mulX
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1; funext S; exact Finset.insert_comm x y S

theorem mdeg_mulX_le (x : ℕ) (f : ML F) : mdeg (mulX x f) ≤ mdeg f + 1 := by
  rw [mdeg_le]
  intro T hT
  obtain ⟨S, hS, rfl⟩ := mem_image.1 (support_mulX x f hT)
  exact (card_insert_le _ _).trans (Nat.add_le_add_right (le_sup (f := Finset.card) hS) 1)

theorem mdeg_sub_le (f g : ML F) : mdeg (f - g) ≤ max (mdeg f) (mdeg g) := by
  rw [mdeg_le]
  intro S hS
  rcases mem_union.1 (Finsupp.support_sub hS) with h | h
  · exact le_max_of_le_left (le_sup (f := Finset.card) h)
  · exact le_max_of_le_right (le_sup (f := Finset.card) h)

theorem res0_identity (x : ℕ) (f : ML F) : res0 x f - mulX x (res0 x f) = f - mulX x f := by
  induction f using ml_induction with
  | h0 => simp [res0, mulX, Finsupp.filter_zero]
  | hadd f g hf hg =>
    rw [res0_add, mulX_add, mulX_add]
    have : res0 x f + res0 x g - (mulX x (res0 x f) + mulX x (res0 x g)) =
        (res0 x f - mulX x (res0 x f)) + (res0 x g - mulX x (res0 x g)) := by abel
    rw [this, hf, hg]; abel
  | hs S c =>
    unfold res0
    by_cases hx : x ∈ S
    · rw [fsn (p := fun S => x ∉ S) (by simpa using hx), mulX_single, insert_eq_of_mem hx]
      simp [mulX]
    · rw [fsp (p := fun S => x ∉ S) hx]

/-- From a refutation after `x := 0`, derive `1 - x` (two more degrees). -/
theorem stepA {Ax : Set (ML F)} {w D₀ x : ℕ} (hw : ∀ a ∈ Ax, mdeg a ≤ w) {g : ML F}
    (h : MLD (res0 x '' Ax) D₀ g) : MLD Ax (max (D₀ + 2) (w + 1)) (g - mulX x g) := by
  induction h with
  | ax hf _ =>
    obtain ⟨f, hf, rfl⟩ := hf
    rw [res0_identity]
    have h1 : MLD Ax (max (D₀ + 2) (w + 1)) f := MLD.ax hf ((hw f hf).trans (by omega))
    have h2 := MLD.mul x h1 ((mdeg_mulX_le x f).trans (by have := hw f hf; omega))
    have := MLD.lin 1 (-1) h1 h2
    simpa [sub_eq_add_neg] using this
  | lin a b _ _ ihf ihg =>
    rename_i f g _ _
    have := MLD.lin a b ihf ihg
    convert this using 1
    rw [mulX_add, mulX_smul, mulX_smul, smul_sub, smul_sub]; abel
  | mul y hf hd ih =>
    rename_i f
    have hdeg := mld_mdeg hf
    have h1 : mdeg (f - mulX x f) ≤ mdeg f + 1 :=
      (mdeg_sub_le _ _).trans (max_le (Nat.le_succ _) (mdeg_mulX_le x f))
    have := MLD.mul y ih ((mdeg_mulX_le y _).trans (by omega))
    convert this using 1
    rw [mulX_sub, mulX_comm]

/-- Multiplication by the monomial of `T`. -/
def mulSet (T : Finset ℕ) (h : ML F) : ML F := h.mapDomain (T ∪ ·)

theorem mulSet_empty (h : ML F) : mulSet ∅ h = h := by
  unfold mulSet; simp only [empty_union]; exact Finsupp.mapDomain_id

theorem mulSet_insert (a : ℕ) (T : Finset ℕ) (h : ML F) : mulSet (insert a T) h = mulX a (mulSet T h) := by
  unfold mulSet mulX
  rw [← Finsupp.mapDomain_comp]
  congr 1; funext S; simp only [Function.comp]; exact insert_union _ _ _

/-- `1 - x`. -/
def uX (x : ℕ) : ML F := one - mulX x one

theorem mulSet_uX (x : ℕ) (T : Finset ℕ) :
    mulSet T (uX x : ML F) = Finsupp.single T 1 - Finsupp.single (insert x T) 1 := by
  unfold mulSet uX one mulX
  rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single]
  simp

theorem mdeg_mulSet_uX (x : ℕ) (T : Finset ℕ) : mdeg (mulSet T (uX x : ML F)) ≤ T.card + 1 := by
  rw [mulSet_uX]
  refine (mdeg_sub_le _ _).trans (max_le ?_ ?_)
  · unfold mdeg; refine (sup_mono Finsupp.support_single_subset).trans ?_; simp
  · unfold mdeg; refine (sup_mono Finsupp.support_single_subset).trans ?_
    simp only [sup_singleton]; exact card_insert_le _ _

theorem mld_mulSet {Ax : Set (ML F)} {E x : ℕ} (hu : MLD Ax E (uX x)) :
    ∀ T : Finset ℕ, T.card + 1 ≤ E → MLD Ax E (mulSet T (uX x)) := by
  intro T
  induction T using Finset.induction_on with
  | empty => intro _; rw [mulSet_empty]; exact hu
  | insert a T ha ih =>
    intro hT
    rw [card_insert_of_notMem ha] at hT
    have hd : mdeg (mulSet (insert a T) (uX x : ML F)) ≤ E := by
      have := mdeg_mulSet_uX (F := F) x (insert a T)
      rw [card_insert_of_notMem ha] at this; omega
    rw [mulSet_insert] at hd ⊢
    exact MLD.mul a (ih (by omega)) hd

theorem mld_sum {Ax : Set (ML F)} {E : ℕ} {ι : Type} (s : Finset ι) (f : ι → ML F)
    (h0 : MLD Ax E 0) (hf : ∀ i ∈ s, MLD Ax E (f i)) : MLD Ax E (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    rw [sum_insert ha]
    have := MLD.lin 1 1 (hf a (mem_insert_self _ _)) (ih fun i hi => hf i (mem_insert_of_mem hi))
    simpa using this

theorem res1_sum {ι : Type} (x : ℕ) (s : Finset ι) (g : ι → ML F) :
    res1 x (∑ i ∈ s, g i) = ∑ i ∈ s, res1 x (g i) := by
  induction s using Finset.induction_on with
  | empty => simp [res1]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, res1_add, ih]

theorem stepB_ax {Ax : Set (ML F)} {E w x : ℕ} (hu : MLD Ax E (uX x)) {f : ML F} (hf : f ∈ Ax)
    (hfw : mdeg f ≤ w) (hwE : w ≤ E) : MLD Ax E (res1 x f) := by
  have h0 := mld_zero hu
  have hf' : f = ∑ S ∈ f.support, Finsupp.single S (f S) := (Finsupp.sum_single f).symm
  have hd : ∑ S ∈ f.support, (res1 x (Finsupp.single S (f S)) - Finsupp.single S (f S)) =
      res1 x f - f := by
    rw [sum_sub_distrib, ← res1_sum, ← hf']
  have hS : MLD Ax E (∑ S ∈ f.support, (res1 x (Finsupp.single S (f S)) - Finsupp.single S (f S))) := by
    refine mld_sum _ _ h0 fun S hS => ?_
    by_cases hx : x ∈ S
    · have hSw : S.card ≤ w := (le_sup (f := Finset.card) hS).trans hfw
      have heq : res1 x (Finsupp.single S (f S)) - Finsupp.single S (f S) =
          f S • mulSet (S.erase x) (uX x) := by
        rw [mulSet_uX, insert_erase hx, smul_sub, Finsupp.smul_single, Finsupp.smul_single]
        unfold res1; rw [Finsupp.mapDomain_single]; simp
      rw [heq]
      have hc := card_erase_of_mem hx
      have hpos : 0 < S.card := card_pos.2 ⟨x, hx⟩
      have := MLD.lin (f S) 0 (mld_mulSet hu (S.erase x) (by omega)) h0
      simpa using this
    · have : res1 x (Finsupp.single S (f S)) = Finsupp.single S (f S) := by
        unfold res1; rw [Finsupp.mapDomain_single, erase_eq_of_notMem hx]
      rw [this, sub_self]; exact h0
  rw [hd] at hS
  have := MLD.lin 1 1 (MLD.ax hf (hfw.trans hwE)) hS
  simpa using this

theorem stepB {Ax : Set (ML F)} {E w x D₁ : ℕ} (hu : MLD Ax E (uX x)) (hw : ∀ a ∈ Ax, mdeg a ≤ w)
    (hwE : w ≤ E) {g : ML F} (h : MLD (res1 x '' Ax) D₁ g) : MLD Ax (max D₁ E) g := by
  induction h with
  | ax hf _ =>
    obtain ⟨f, hf, rfl⟩ := hf
    exact mld_mono (le_max_right _ _) (stepB_ax hu hf (hw f hf) hwE)
  | lin a b _ _ ihf ihg => exact MLD.lin a b ihf ihg
  | mul y _ hd ih => exact MLD.mul y ih (hd.trans (le_max_left _ _))

/-- **Combining**: refutations after `x := 0` and `x := 1` give one of `F`. -/
theorem combine {Ax : Set (ML F)} {w x D₀ D₁ : ℕ} (hw : ∀ a ∈ Ax, mdeg a ≤ w)
    (h0 : MLD (res0 x '' Ax) D₀ one) (h1 : MLD (res1 x '' Ax) D₁ one) :
    MLD Ax (max D₁ (max (D₀ + 2) (w + 1))) one :=
  stepB (stepA hw h0) hw (by omega) h1

/-! ## The Impagliazzo–Pudlák–Sgall induction -/

/-- Fat monomial occurrences containing `x`. -/
def cntL (d₀ x : ℕ) (L : List (ML F)) : ℕ :=
  (L.map fun g => (g.support.filter fun S => d₀ < S.card ∧ x ∈ S).card).sum

theorem fatL_res0 (d₀ x : ℕ) (L : List (ML F)) :
    fatL d₀ (L.map (res0 x)) + cntL d₀ x L = fatL d₀ L := by
  unfold fatL cntL
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    have := fat_res0 d₀ x a
    simp only [List.map_map, Function.comp] at ih ⊢
    omega

theorem fatL_res1 (d₀ x : ℕ) (L : List (ML F)) : fatL d₀ (L.map (res1 x)) ≤ fatL d₀ L := by
  unfold fatL
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp] at ih ⊢
    exact Nat.add_le_add (fat_res1 d₀ x a) ih

theorem mdeg_res0_le (x : ℕ) (f : ML F) : mdeg (res0 x f) ≤ mdeg f := by
  unfold mdeg res0; rw [Finsupp.support_filter]; exact sup_mono (filter_subset _ _)

theorem mdeg_res1_le (x : ℕ) (f : ML F) : mdeg (res1 x f) ≤ mdeg f := by
  rw [mdeg_le]
  intro T hT
  obtain ⟨S, hS, rfl⟩ := mem_image.1 (support_res1 x f hT)
  exact card_erase_le.trans (le_sup (f := Finset.card) hS)

theorem averaging {d₀ : ℕ} {V : Finset ℕ} {L : List (ML F)}
    (hsub : ∀ g ∈ L, ∀ S ∈ g.support, S ⊆ V) :
    (d₀ + 1) * fatL d₀ L ≤ ∑ x ∈ V, cntL d₀ x L := by
  unfold fatL cntL
  induction L with
  | nil => simp
  | cons g L ih =>
    simp only [List.map_cons, List.sum_cons, sum_add_distrib, mul_add]
    refine Nat.add_le_add ?_ (ih fun g' hg' => hsub g' (List.mem_cons_of_mem _ hg'))
    have hg := hsub g (List.mem_cons_self)
    calc (d₀ + 1) * (fatS d₀ g).card = ∑ S ∈ fatS d₀ g, (d₀ + 1) := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ S ∈ fatS d₀ g, S.card := sum_le_sum fun S hS => (mem_filter.1 hS).2
      _ = ∑ S ∈ fatS d₀ g, ∑ x ∈ V, if x ∈ S then 1 else 0 := by
          refine sum_congr rfl fun S hS => ?_
          rw [sum_boole, Nat.cast_id, filter_mem_eq_inter, inter_eq_right.2 (hg S (mem_filter.1 hS).1)]
      _ = ∑ x ∈ V, ∑ S ∈ fatS d₀ g, if x ∈ S then 1 else 0 := sum_comm
      _ = ∑ x ∈ V, (g.support.filter fun S => d₀ < S.card ∧ x ∈ S).card := by
          refine sum_congr rfl fun x _ => ?_
          rw [sum_boole, Nat.cast_id]
          unfold fatS; rw [filter_filter]

theorem ratio_pow (N a k : ℕ) : (N - 1 - a) ^ k * N ^ k ≤ (N - a) ^ k * (N - 1) ^ k := by
  rw [← mul_pow, ← mul_pow]
  refine Nat.pow_le_pow_left ?_ _
  by_cases h : a + 1 ≤ N
  · obtain ⟨m, rfl⟩ : ∃ m, N = a + 1 + m := ⟨N - (a + 1), by omega⟩
    rw [show a + 1 + m - 1 - a = m by omega, show a + 1 + m - a = m + 1 by omega,
      show a + 1 + m - 1 = a + m by omega]
    nlinarith
  · rw [show N - 1 - a = 0 by omega]; simp

theorem fat_pos_card {d₀ : ℕ} {V : Finset ℕ} {L : List (ML F)}
    (hsub : ∀ g ∈ L, ∀ S ∈ g.support, S ⊆ V) (h : fatL d₀ L ≠ 0) : d₀ < V.card := by
  unfold fatL at h
  obtain ⟨n, hn, hn0⟩ : ∃ n ∈ L.map (fun f => (fatS d₀ f).card), n ≠ 0 := by
    by_contra hc; push Not at hc; exact h (List.sum_eq_zero hc)
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hn
  obtain ⟨S, hS⟩ := card_pos.1 (Nat.pos_of_ne_zero hn0)
  obtain ⟨hS1, hS2⟩ := mem_filter.1 hS
  exact lt_of_lt_of_le hS2 (card_le_card (hsub g hg S hS1))

theorem one_mem_map {L : List (ML F)} (h : one ∈ L) (ρ : ML F → ML F) (hρ : ρ one = one) :
    (one : ML F) ∈ L.map ρ := by
  rw [← hρ]; exact List.mem_map_of_mem h

theorem res0_proof {Ax : Set (ML F)} {L : List (ML F)} (hL : MLProof Ax L) (x : ℕ) :
    MLProof (res0 x '' Ax) (L.map (res0 x)) := by
  refine proof_map hL _ (res0_add x) (res0_smul x) fun y g => ?_
  by_cases hy : y = x
  · subst hy; exact Or.inr ⟨0, by rw [res0_mulX_self, zero_smul]⟩
  · exact Or.inl (res0_mulX_ne hy g)

theorem res1_proof {Ax : Set (ML F)} {L : List (ML F)} (hL : MLProof Ax L) (x : ℕ) :
    MLProof (res1 x '' Ax) (L.map (res1 x)) := by
  refine proof_map hL _ (res1_add x) (res1_smul x) fun y g => ?_
  by_cases hy : y = x
  · subst hy; exact Or.inr ⟨1, by rw [res1_mulX_self, one_smul]⟩
  · exact Or.inl (res1_mulX_ne hy g)

theorem resV_proof {Ax : Set (ML F)} {L : List (ML F)} (hL : MLProof Ax L) (V : Finset ℕ) :
    MLProof (resV V '' Ax) (L.map (resV V)) := by
  refine proof_map hL _ (resV_add V) (resV_smul V) fun y g => ?_
  by_cases hy : y ∈ V
  · exact Or.inl (resV_mulX_mem hy g)
  · exact Or.inr ⟨0, by rw [resV_mulX_nmem hy, zero_smul]⟩

/-- **IPS**: a refutation with at most `f` fat (more than `d₀` variables) monomial occurrences
over `N` variables, with `f (N - d₀ - 1)^k < N^k`, yields a refutation of degree
`max d₀ (w + 1) + 2 k`, where `w` bounds the axiom degrees. -/
theorem ips (d₀ w : ℕ) : ∀ N k (V : Finset ℕ) (Ax : Set (ML F)) (L : List (ML F)) (f : ℕ),
    V.card = N → (∀ a ∈ Ax, mdeg a ≤ w) → MLProof Ax L → one ∈ L →
    (∀ g ∈ L, ∀ S ∈ g.support, S ⊆ V) → fatL d₀ L ≤ f → f * (N - (d₀ + 1)) ^ k < N ^ k →
    MLD Ax (max d₀ (w + 1) + 2 * k) one := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro k V Ax L f hV hw hL h1 hsub hfat hineq
  set B := max d₀ (w + 1)
  have base : ∀ {Ax' : Set (ML F)} {L' : List (ML F)}, MLProof Ax' L' → one ∈ L' →
      fatL d₀ L' = 0 → ∀ D, d₀ ≤ D → MLD Ax' D one := fun hL' h1' h0 D hD =>
    mld_mono hD (mld_of_proof hL' h0 _ h1')
  by_cases h0 : fatL d₀ L = 0
  · exact base hL h1 h0 _ (by omega)
  cases k with
  | zero => simp at hineq; omega
  | succ k =>
  have hNd := fat_pos_card hsub h0
  obtain ⟨x, hxV, hx⟩ : ∃ x ∈ V, (d₀ + 1) * fatL d₀ L ≤ N * cntL d₀ x L := by
    by_contra hc
    push Not at hc
    have h2 := averaging (d₀ := d₀) hsub
    have h3 : ∑ x ∈ V, N * cntL d₀ x L < ∑ x ∈ V, (d₀ + 1) * fatL d₀ L :=
      sum_lt_sum_of_nonempty (card_pos.1 (by omega)) hc
    rw [← mul_sum, sum_const, smul_eq_mul, hV] at h3
    nlinarith
  have hV' : (V.erase x).card = N - 1 := by rw [card_erase_of_mem hxV, hV]
  have hN1 : N - 1 < N := by omega
  have hwr0 : ∀ a ∈ res0 x '' Ax, mdeg a ≤ w := by
    rintro _ ⟨a, ha, rfl⟩; exact (mdeg_res0_le x a).trans (hw a ha)
  have hwr1 : ∀ a ∈ res1 x '' Ax, mdeg a ≤ w := by
    rintro _ ⟨a, ha, rfl⟩; exact (mdeg_res1_le x a).trans (hw a ha)
  have hsub0 : ∀ g ∈ L.map (res0 x), ∀ S ∈ g.support, S ⊆ V.erase x := by
    intro g' hg' S hS
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
    unfold res0 at hS; rw [Finsupp.support_filter] at hS
    obtain ⟨hS1, hS2⟩ := mem_filter.1 hS
    exact fun y hy => mem_erase.2 ⟨fun h => hS2 (h ▸ hy), hsub g hg S hS1 hy⟩
  have hsub1 : ∀ g ∈ L.map (res1 x), ∀ S ∈ g.support, S ⊆ V.erase x := by
    intro g' hg' T hT
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
    obtain ⟨S, hS, rfl⟩ := mem_image.1 (support_res1 x g hT)
    exact erase_subset_erase x (hsub g hg S hS)
  have hratio := ratio_pow N (d₀ + 1)
  -- branch `x := 0`
  have hb0 : MLD (res0 x '' Ax) (B + 2 * k) one := by
    set f0 := fatL d₀ (L.map (res0 x))
    by_cases hf0 : f0 = 0
    · exact base (res0_proof hL x) (one_mem_map h1 _ (res0_one x)) hf0 _ (by omega)
    have hN' := fat_pos_card hsub0 hf0
    rw [hV'] at hN'
    refine ih (N - 1) hN1 k (V.erase x) _ _ f0 hV' hwr0 (res0_proof hL x)
      (one_mem_map h1 _ (res0_one x)) hsub0 le_rfl ?_
    have hsplit := fatL_res0 d₀ x L
    have hNf0 : N * f0 ≤ (N - (d₀ + 1)) * f := by
      have : N * f0 + N * cntL d₀ x L = N * fatL d₀ L := by rw [← mul_add, hsplit]
      have h4 : (N - (d₀ + 1)) * fatL d₀ L + (d₀ + 1) * fatL d₀ L = N * fatL d₀ L := by
        rw [← add_mul, Nat.sub_add_cancel (by omega)]
      have h5 : (N - (d₀ + 1)) * fatL d₀ L ≤ (N - (d₀ + 1)) * f := Nat.mul_le_mul_left _ hfat
      omega
    have hA : f0 * (N - (d₀ + 1)) ^ k < N ^ k := by
      have : N * (f0 * (N - (d₀ + 1)) ^ k) < N * N ^ k := by
        calc N * (f0 * (N - (d₀ + 1)) ^ k) = (N * f0) * (N - (d₀ + 1)) ^ k := by ring
          _ ≤ ((N - (d₀ + 1)) * f) * (N - (d₀ + 1)) ^ k := Nat.mul_le_mul_right _ hNf0
          _ = f * (N - (d₀ + 1)) ^ (k + 1) := by ring
          _ < N ^ (k + 1) := hineq
          _ = N * N ^ k := by ring
      exact Nat.lt_of_mul_lt_mul_left this
    have hpos : 0 < N ^ k := Nat.pow_pos (by omega)
    have hpos1 : 0 < (N - 1) ^ k := Nat.pow_pos (by omega)
    have h6 := hratio k
    have : f0 * (N - 1 - (d₀ + 1)) ^ k * N ^ k < (N - 1) ^ k * N ^ k := by
      calc f0 * (N - 1 - (d₀ + 1)) ^ k * N ^ k = f0 * ((N - 1 - (d₀ + 1)) ^ k * N ^ k) := by ring
        _ ≤ f0 * ((N - (d₀ + 1)) ^ k * (N - 1) ^ k) := Nat.mul_le_mul_left _ h6
        _ = (f0 * (N - (d₀ + 1)) ^ k) * (N - 1) ^ k := by ring
        _ < N ^ k * (N - 1) ^ k := Nat.mul_lt_mul_of_pos_right hA hpos1
        _ = (N - 1) ^ k * N ^ k := by ring
    exact Nat.lt_of_mul_lt_mul_right this
  -- branch `x := 1`
  have hb1 : MLD (res1 x '' Ax) (B + 2 * (k + 1)) one := by
    set f1 := fatL d₀ (L.map (res1 x))
    by_cases hf1 : f1 = 0
    · exact base (res1_proof hL x) (one_mem_map h1 _ (res1_one x)) hf1 _ (by omega)
    have hN' := fat_pos_card hsub1 hf1
    rw [hV'] at hN'
    refine ih (N - 1) hN1 (k + 1) (V.erase x) _ _ f hV' hwr1 (res1_proof hL x)
      (one_mem_map h1 _ (res1_one x)) hsub1 ((fatL_res1 d₀ x L).trans hfat) ?_
    have hpos1 : 0 < (N - 1) ^ (k + 1) := Nat.pow_pos (by omega)
    have h6 := hratio (k + 1)
    have : f * (N - 1 - (d₀ + 1)) ^ (k + 1) * N ^ (k + 1) < (N - 1) ^ (k + 1) * N ^ (k + 1) := by
      calc f * (N - 1 - (d₀ + 1)) ^ (k + 1) * N ^ (k + 1)
          = f * ((N - 1 - (d₀ + 1)) ^ (k + 1) * N ^ (k + 1)) := by ring
        _ ≤ f * ((N - (d₀ + 1)) ^ (k + 1) * (N - 1) ^ (k + 1)) := Nat.mul_le_mul_left _ h6
        _ = (f * (N - (d₀ + 1)) ^ (k + 1)) * (N - 1) ^ (k + 1) := by ring
        _ < N ^ (k + 1) * (N - 1) ^ (k + 1) := Nat.mul_lt_mul_of_pos_right hineq hpos1
        _ = (N - 1) ^ (k + 1) * N ^ (k + 1) := by ring
    exact Nat.lt_of_mul_lt_mul_right this
  exact mld_mono (by omega) (combine hw hb0 hb1)

theorem fatL_resV (d₀ : ℕ) (V : Finset ℕ) (L : List (ML F)) :
    fatL d₀ (L.map (resV V)) ≤ fatL d₀ L := by
  unfold fatL
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp] at ih ⊢
    exact Nat.add_le_add (fat_resV d₀ V a) ih

/-! ## Explicit parameters -/

theorem bern (u t : ℕ) : ∀ r, u ^ r * (u + r * t) ≤ (u + t) ^ r * u := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 : u ^ (r + 1) * (u + (r + 1) * t) ≤ (u + t) * (u ^ r * (u + r * t)) := by
      rw [pow_succ]; nlinarith [Nat.zero_le (u ^ r * r * t * t), Nat.zero_le (u ^ r)]
    calc u ^ (r + 1) * (u + (r + 1) * t) ≤ (u + t) * (u ^ r * (u + r * t)) := h1
      _ ≤ (u + t) * ((u + t) ^ r * u) := Nat.mul_le_mul_left _ ih
      _ = (u + t) ^ (r + 1) * u := by ring

theorem two_pow_le {N t r : ℕ} (hr1 : 1 ≤ r) (ht : t ≤ N) (hr : N ≤ r * t + t) :
    2 * (N - t) ^ r ≤ N ^ r := by
  set u := N - t
  have hN : N = u + t := by omega
  have hb := bern u t r
  rw [← hN] at hb
  rcases Nat.eq_zero_or_pos u with hu | hu
  · rw [hu, zero_pow (by omega), mul_zero]; exact Nat.zero_le _
  · have : 2 * u ^ r * u ≤ N ^ r * u := by
      calc 2 * u ^ r * u = u ^ r * (u + u) := by ring
        _ ≤ u ^ r * (u + r * t) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ N ^ r * u := hb
    exact Nat.le_of_mul_le_mul_right this hu

/-- **Size–degree tradeoff** (explicit form). A refutation of size below `2^m` over the
variables `V` (axioms of degree at most `w`, monomials of axioms inside `V`) yields a
refutation of degree `max (t - 1) (w + 1) + 2 r m` whenever `1 ≤ t ≤ |V| ≤ r t + t`. -/
theorem size_degree {Ax : Set (ML F)} {L : List (ML F)} {V : Finset ℕ} {w m t r : ℕ}
    (hw : ∀ a ∈ Ax, mdeg a ≤ w) (hAxV : ∀ a ∈ Ax, ∀ S ∈ a.support, S ⊆ V)
    (hL : MLProof Ax L) (h1 : one ∈ L) (hsize : sizeL L < 2 ^ m) (ht : 1 ≤ t) (hr1 : 1 ≤ r)
    (htV : t ≤ V.card) (hr : V.card ≤ r * t + t) :
    MLD Ax (max (t - 1) (w + 1) + 2 * (r * m)) one := by
  have hAx : resV V '' Ax = Ax := by
    ext a; constructor
    · rintro ⟨b, hb, rfl⟩
      have : resV V b = b := by
        unfold resV; rw [Finsupp.filter_eq_self_iff]; intro S hS; exact hAxV b hb S
          (Finsupp.mem_support_iff.2 hS)
      rw [this]; exact hb
    · intro ha
      refine ⟨a, ha, ?_⟩
      unfold resV; rw [Finsupp.filter_eq_self_iff]; intro S hS
      exact hAxV a ha S (Finsupp.mem_support_iff.2 hS)
  have hL' := resV_proof hL V
  rw [hAx] at hL'
  have hsub : ∀ g ∈ L.map (resV V), ∀ S ∈ g.support, S ⊆ V := by
    intro g' hg' S hS
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hg'
    unfold resV at hS; rw [Finsupp.support_filter] at hS
    exact (mem_filter.1 hS).2
  have hfat : fatL (t - 1) (L.map (resV V)) ≤ sizeL L :=
    (fatL_resV (t - 1) V L).trans (fatL_le_sizeL (t - 1) L)
  refine ips (t - 1) w V.card (r * m) V Ax _ (sizeL L) rfl hw hL'
    (one_mem_map h1 _ (resV_one V)) hsub hfat ?_
  rw [show t - 1 + 1 = t by omega]
  have h2 := two_pow_le hr1 htV hr
  have h3 : 2 ^ m * (V.card - t) ^ (r * m) ≤ V.card ^ (r * m) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    calc (2 * (V.card - t) ^ r) ^ m ≤ (V.card ^ r) ^ m := Nat.pow_le_pow_left h2 _
      _ = _ := rfl
  rcases Nat.eq_zero_or_pos ((V.card - t) ^ (r * m)) with h0 | hpos
  · rw [h0, mul_zero]; exact Nat.pow_pos (by omega)
  · calc sizeL L * (V.card - t) ^ (r * m) < 2 ^ m * (V.card - t) ^ (r * m) :=
          Nat.mul_lt_mul_of_pos_right hsize hpos
      _ ≤ _ := h3

/-! ## Back to polynomial calculus -/

open MvPolynomial in
/-- The polynomial of a multilinear polynomial. -/
def toPoly (f : ML F) : MvPolynomial ℕ F := f.sum fun S c => C c * ∏ i ∈ S, X i

open MvPolynomial in
/-- Boolean correction term for multiplication by `x`. -/
def corr (x : ℕ) (f : ML F) : MvPolynomial ℕ F :=
  f.sum fun S c => if x ∈ S then C c * (∏ i ∈ S.erase x, X i) * (X x ^ 2 - X x) else 0

open MvPolynomial in
theorem toPoly_add (f g : ML F) : toPoly (f + g) = toPoly f + toPoly g :=
  Finsupp.sum_add_index' (by simp) (by intros; rw [C_add, add_mul])

open MvPolynomial in
theorem toPoly_smul (a : F) (f : ML F) : toPoly (a • f) = C a * toPoly f := by
  unfold toPoly
  rw [Finsupp.sum_smul_index' (by simp), Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [smul_eq_mul, C_mul, mul_assoc]

open MvPolynomial in
theorem toPoly_single (S : Finset ℕ) (c : F) : toPoly (Finsupp.single S c) = C c * ∏ i ∈ S, X i :=
  Finsupp.sum_single_index (by simp)

open MvPolynomial in
theorem corr_add (x : ℕ) (f g : ML F) : corr x (f + g) = corr x f + corr x g := by
  unfold corr
  refine Finsupp.sum_add_index' (fun S => by split_ifs <;> simp) (fun S a b => ?_)
  split_ifs <;> simp [C_add, add_mul]

open MvPolynomial in
theorem toPoly_one : toPoly (one : ML F) = 1 := by
  unfold one; rw [toPoly_single]; simp

open MvPolynomial in
theorem X_mul_toPoly (x : ℕ) (f : ML F) : X x * toPoly f = toPoly (mulX x f) + corr x f := by
  induction f using ml_induction with
  | h0 => simp [toPoly, corr, mulX]
  | hadd f g hf hg => rw [toPoly_add, mul_add, hf, hg, mulX_add, toPoly_add, corr_add]; ring
  | hs S c =>
    rw [mulX_single, toPoly_single, toPoly_single]
    unfold corr; rw [Finsupp.sum_single_index (by simp)]
    by_cases hx : x ∈ S
    · rw [insert_eq_of_mem hx, if_pos hx, ← Finset.mul_prod_erase S (fun i => X i) hx]; ring
    · rw [if_neg hx, prod_insert hx]; ring

open MvPolynomial in
theorem totalDegree_toPoly (f : ML F) : (toPoly f).totalDegree ≤ mdeg f := by
  unfold toPoly Finsupp.sum
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun S hS => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finset_prod _ _).trans ?_
  simp only [totalDegree_X, sum_const, smul_eq_mul, mul_one]
  exact le_sup (f := Finset.card) hS

/-- The Boolean axioms. -/
def BoolAx : Set (MvPolynomial ℕ F) := {g | ∃ i, g = MvPolynomial.X i ^ 2 - MvPolynomial.X i}

open MvPolynomial in
/-- **Translation**: a degree `D` multilinear derivation gives a degree `D + 1` polynomial
calculus derivation (with Boolean axioms). -/
theorem translate {Ax : Set (ML F)} {Axp : Set (MvPolynomial ℕ F)} {D : ℕ}
    (hAx : ∀ a ∈ Ax, toPoly a ∈ Axp) {g : ML F} (h : MLD Ax D g) :
    PCD₀ (Axp ∪ BoolAx) (D + 1) (toPoly g) := by
  induction h with
  | ax ha hd => exact PCD₀.ax (Or.inl (hAx _ ha)) ((totalDegree_toPoly _).trans (by omega))
  | lin a b _ _ ihf ihg => rw [toPoly_add, toPoly_smul, toPoly_smul]; exact PCD₀.lin a b ihf ihg
  | mul x hf hd ih =>
    rename_i f
    have hdf := mld_mdeg hf
    have htf := totalDegree_toPoly f
    have hXd : (X x * toPoly f).totalDegree ≤ D + 1 := by
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]; omega
    have hXf : PCD₀ (Axp ∪ BoolAx) (D + 1) (X x * toPoly f) := PCD₀.mul x ih hXd
    rcases Nat.eq_zero_or_pos D with hD0 | hDpos
    · have hz : mulX x f = 0 := by
        by_contra hne
        obtain ⟨T, hT⟩ := Finsupp.support_nonempty_iff.2 hne
        obtain ⟨S, -, rfl⟩ := mem_image.1 (support_mulX x f hT)
        have := (le_sup (f := Finset.card) hT).trans hd
        rw [hD0] at this
        have := card_pos.2 ⟨x, mem_insert_self x S⟩; omega
      rw [hz, show toPoly (0 : ML F) = 0 by simp [toPoly]]; exact pcd₀_zero ih
    have hbool : PCD₀ (Axp ∪ BoolAx) (D + 1) (X x ^ 2 - X x) :=
      PCD₀.ax (Or.inr ⟨x, rfl⟩) ((totalDegree_sub _ _).trans (max_le
        ((totalDegree_pow _ _).trans (by rw [totalDegree_X]; omega)) (by rw [totalDegree_X]; omega)))
    have hcorr : PCD₀ (Axp ∪ BoolAx) (D + 1) (corr x f) := by
      unfold corr Finsupp.sum
      refine pcd₀_sum _ _ (pcd₀_zero ih) fun S hS => ?_
      dsimp only
      split_ifs with hx
      · 
        refine pcd₀_mul hbool ?_
        have hP : (C (f S) * ∏ i ∈ S.erase x, (X i : MvPolynomial ℕ F)).totalDegree ≤ (S.erase x).card := by
          refine (totalDegree_mul _ _).trans ?_
          rw [totalDegree_C, zero_add]
          refine (totalDegree_finset_prod _ _).trans ?_
          simp only [totalDegree_X, sum_const, smul_eq_mul, mul_one]; exact le_rfl
        have h2 : (X x ^ 2 - X x : MvPolynomial ℕ F).totalDegree ≤ 2 :=
          (totalDegree_sub _ _).trans (max_le ((totalDegree_pow _ _).trans (by simp))
            (by simp))
        have hS' := (le_sup (f := Finset.card) hS).trans hdf
        have := card_erase_of_mem hx
        have : 0 < S.card := card_pos.2 ⟨x, hx⟩
        omega
      · exact pcd₀_zero ih
    have := PCD₀.lin 1 (-1) hXf hcorr
    convert this using 1
    rw [X_mul_toPoly]; simp

theorem pcd₀_to_pcd {Ax : Set (MvPolynomial ℕ F)} {d : ℕ} (hd : 2 ≤ d) {f : MvPolynomial ℕ F}
    (h : PCD₀ (Ax ∪ BoolAx) d f) : PCD Ax d f := by
  induction h with
  | ax hf hdf =>
    rcases hf with hf | ⟨i, rfl⟩
    · exact PCD.ax hf hdf
    · exact PCD.bool i hd
  | lin a b _ _ ihf ihg => exact PCD.lin a b ihf ihg
  | mul i _ hdf ih => exact PCD.mul i ih hdf

end

end MLPC

end SATurday.ProofComplexity
