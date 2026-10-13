import Theory.ProofComplexity.BraunAugComplex

/-!
# Finite complex covers and the homological cover lemma (R4 Phase 2.1, layer 6i)

Credit. Port of K. Braun's third party development (arXiv 2609.23015, author's Lean development):
`FiniteComplexCover.lean` (`intersection`, `nerve`, `Covers`), `CoverDoubleComplex.lean` (the double
complex of a cover, horizontal exactness at positive vertex degree) and `HomologicalCover.lean`
(`homological_cover`: if the nerve is acyclic through `n` and every genuine intersection is exact
in the range `|J| + r <= n`, then the complex is acyclic through `n`). Cell count conventions as in
`BraunAugComplex`.

LOG: R4 BraunAugCover module (Phase 2.1 layer 6i)
-/

namespace SATurday.ProofComplexity.BraunPC.Aug

noncomputable section

open scoped BigOperators

section Cover
variable {V I : Type*} [DecidableEq V] [DecidableEq I]

def intersection (L : I → Complex V) (J : Finset I) : Complex V where
  faces := {s | ∀ i ∈ J, s ∈ (L i).faces}
  empty_mem := by intro i _; exact (L i).empty_mem
  downward := by intro s t h ht i hi; exact (L i).downward h (ht i hi)
def nerve (L : I → Complex V) : Complex I where
  faces := {J | J = ∅ ∨ ∃ v, ∀ i ∈ J, {v} ∈ (L i).faces}
  empty_mem := Or.inl rfl
  downward := by
    intro S T h hT
    rcases hT with rfl | ⟨v, hv⟩
    · exact Or.inl (Finset.subset_empty.mp h)
    · exact Or.inr ⟨v, fun i hi => hv i (h hi)⟩
def Covers (K : Complex V) (L : I → Complex V) : Prop :=
  ∀ s ∈ K.faces, ∃ i, s ∈ (L i).faces

end Cover

section DoubleComplex
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]


abbrev DoubleCoeff (I V : Type*) := Finset I → Finset V → ZMod 2

def horizontal (d : DoubleCoeff I V) : DoubleCoeff I V :=
  fun J S => boundary (fun T => d T S) J

def vertical (d : DoubleCoeff I V) : DoubleCoeff I V :=
  fun J => boundary (d J)

def Admissible (K : Complex V) (L : I → Complex V) (J : Finset I) (S : Finset V) : Prop :=
  S ∈ K.faces ∧ (∀ i ∈ J, S ∈ (L i).faces) ∧ J ∈ (nerve L).faces

def BiSupported (K : Complex V) (L : I → Complex V) (a b : ℕ)
    (d : DoubleCoeff I V) : Prop :=
  ∀ J S, ¬ (J.card = a ∧ S.card = b ∧ Admissible K L J S) → d J S = 0

omit [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] in
theorem bi_nonzero {K : Complex V} {L : I → Complex V} {a b : ℕ}
    {d : DoubleCoeff I V} (hd : BiSupported K L a b d) {J S} (h : d J S ≠ 0) :
    J.card = a ∧ S.card = b ∧ Admissible K L J S := by
  by_contra hn
  exact h (hd J S hn)

omit [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] in
theorem bi_add {K : Complex V} {L : I → Complex V} {a b : ℕ}
    {d e : DoubleCoeff I V} (hd : BiSupported K L a b d) (he : BiSupported K L a b e) :
    BiSupported K L a b (d+e) := by
  intro J S h
  simp [hd J S h, he J S h]

omit [Fintype V] [DecidableEq V] in
theorem horizontal_add (d e : DoubleCoeff I V) :
    horizontal (d+e) = horizontal d + horizontal e := by
  funext J S
  exact congrFun (boundary_add (fun T => d T S) (fun T => e T S)) J

omit [Fintype I] [DecidableEq I] in
theorem vertical_add (d e : DoubleCoeff I V) :
    vertical (d+e) = vertical d + vertical e := by
  funext J
  exact boundary_add (d J) (e J)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem horizontal_zero : horizontal (0 : DoubleCoeff I V) = 0 := by
  funext J S
  exact congrFun boundary_zero J
omit [Fintype I] [DecidableEq I] in
@[simp] theorem vertical_zero : vertical (0 : DoubleCoeff I V) = 0 := by
  funext J
  exact boundary_zero

omit [Fintype V] [DecidableEq V] in
theorem horizontal_squared (d : DoubleCoeff I V) : horizontal (horizontal d) = 0 := by
  funext J S
  exact congrFun (boundary_boundary (fun T => d T S)) J

omit [Fintype I] [DecidableEq I] in
theorem vertical_squared (d : DoubleCoeff I V) : vertical (vertical d) = 0 := by
  funext J
  exact boundary_boundary (d J)

theorem horizontal_vertical (d : DoubleCoeff I V) :
    horizontal (vertical d) = vertical (horizontal d) := by
  funext J S
  simp only [horizontal, vertical, boundary]
  have hsV (p : Prop) [Decidable p] (f : V → ZMod 2) :
      (if p then 0 else ∑ x, f x) = ∑ x, if p then 0 else f x := by
    split_ifs <;> simp
  have hsI (p : Prop) [Decidable p] (f : I → ZMod 2) :
      (if p then 0 else ∑ x, f x) = ∑ x, if p then 0 else f x := by
    split_ifs <;> simp
  simp_rw [hsV, hsI]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

omit [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] in
theorem admissible_hdown {K : Complex V} {L : I → Complex V} {J T : Finset I}
    {S : Finset V} (h : J ⊆ T) (hT : Admissible K L T S) : Admissible K L J S :=
  ⟨hT.1, (fun i hi => hT.2.1 i (h hi)), (nerve L).downward h hT.2.2⟩

omit [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] in
theorem admissible_vdown {K : Complex V} {L : I → Complex V} {J : Finset I}
    {S T : Finset V} (h : S ⊆ T) (hT : Admissible K L J T) : Admissible K L J S :=
  ⟨K.downward h hT.1, (fun i hi => (L i).downward h (hT.2.1 i hi)), hT.2.2⟩

omit [Fintype V] [DecidableEq V] in
theorem horizontal_supported {K : Complex V} {L : I → Complex V} {a b : ℕ}
    {d : DoubleCoeff I V} (hd : BiSupported K L (a+1) b d) :
    BiSupported K L a b (horizontal d) := by
  intro J S h
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ J
  · simp [hi]
  · simp only [hi, ↓reduceIte]
    apply hd
    intro hh
    apply h
    refine ⟨?_, hh.2.1, admissible_hdown (Finset.subset_insert i J) hh.2.2⟩
    simpa [Finset.card_insert_of_notMem hi] using hh.1

omit [Fintype I] [DecidableEq I] in
theorem vertical_supported {K : Complex V} {L : I → Complex V} {a b : ℕ}
    {d : DoubleCoeff I V} (hd : BiSupported K L a (b+1) d) :
    BiSupported K L a b (vertical d) := by
  intro J S h
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : v ∈ S
  · simp [hv]
  · simp only [hv, ↓reduceIte]
    apply hd
    intro hh
    apply h
    refine ⟨hh.1, ?_, admissible_vdown (Finset.subset_insert v S) hh.2.2⟩
    simpa [Finset.card_insert_of_notMem hv] using hh.2.1

omit [Fintype V] [DecidableEq V] in
/-- At positive vertex count, each row is contracted at a cover index containing S. -/
theorem horizontal_exact (K : Complex V) (L : I → Complex V) (hcover : Covers K L)
    (a b : ℕ) (hb : 0 < b) (d : DoubleCoeff I V) (hd : BiSupported K L a b d)
    (hz : horizontal d = 0) :
    ∃ u, BiSupported K L (a+1) b u ∧ horizontal u = d := by
  classical
  let pick (S : Finset V) (hS : S ∈ K.faces) : I := Classical.choose (hcover S hS)
  have hpick (S : Finset V) (hS : S ∈ K.faces) : S ∈ (L (pick S hS)).faces :=
    Classical.choose_spec (hcover S hS)
  let u : DoubleCoeff I V := fun J S =>
    if hS : S ∈ K.faces ∧ S.card = b then
      cone (pick S hS.1) (fun T => d T S) J else 0
  refine ⟨u, ?_, ?_⟩
  · intro J S hn
    by_contra hne
    have hS : S ∈ K.faces ∧ S.card = b := by
      by_contra h
      exact hne (by simp [u, h])
    let i := pick S hS.1
    have hi : i ∈ J := by
      by_contra h
      exact hne (by simp [u, hS, cone, i, h])
    have hc : d (J.erase i) S ≠ 0 := by
      simpa [u, hS, cone, i, hi] using hne
    obtain ⟨hcard, _, hgood⟩ := bi_nonzero hd hc
    have hcommon : ∀ j ∈ J, S ∈ (L j).faces := by
      intro j hj
      by_cases he : j = i
      · subst j
        exact hpick S hS.1
      · exact hgood.2.1 j (Finset.mem_erase.mpr ⟨he, hj⟩)
    have hvertex : ∃ v, v ∈ S := Finset.card_pos.mp (by omega)
    obtain ⟨v, hv⟩ := hvertex
    apply hn
    refine ⟨?_, hS.2, hS.1, hcommon, Or.inr ⟨v, ?_⟩⟩
    · have he := Finset.card_erase_add_one hi
      omega
    · intro j hj
      exact (L j).downward (Finset.singleton_subset_iff.mpr hv) (hcommon j hj)
  · funext J S
    by_cases hS : S ∈ K.faces ∧ S.card = b
    · have hcycle : boundary (fun T => d T S) = 0 := by
        funext T
        exact congrFun (congrFun hz T) S
      have hc := cone_identity (pick S hS.1) (fun T => d T S)
      have hzero : cone (pick S hS.1) (0 : Coeff I) = 0 := by
        funext T
        simp [cone]
      rw [hcycle, hzero, add_zero] at hc
      simpa [horizontal, u, hS] using congrFun hc J
    · have hdz : d J S = 0 := hd J S (by
        intro h
        exact hS ⟨h.2.2.1, h.2.1⟩)
      simp [horizontal, boundary, u, hS, hdz]

omit [Fintype V] [DecidableEq V] in
theorem horizontal_at_zero {K : Complex V} {L : I → Complex V} {b : ℕ}
    {d : DoubleCoeff I V} (hd : BiSupported K L 0 b d) : horizontal d = 0 := by
  funext J S
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ J
  · simp [hi]
  · simp only [hi, ↓reduceIte]
    apply hd
    intro hh
    simpa [Finset.card_insert_of_notMem hi] using hh.1

omit [Fintype I] [DecidableEq I] in
theorem vertical_at_zero {K : Complex V} {L : I → Complex V} {a : ℕ}
    {d : DoubleCoeff I V} (hd : BiSupported K L a 0 d) : vertical d = 0 := by
  funext J S
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : v ∈ S
  · simp [hv]
  · simp only [hv, ↓reduceIte]
    apply hd
    intro hh
    simpa [Finset.card_insert_of_notMem hv] using hh.2.1

def totalBoundary (d : DoubleCoeff I V) : DoubleCoeff I V := horizontal d + vertical d

theorem totalBoundary_squared (d : DoubleCoeff I V) :
    totalBoundary (totalBoundary d) = 0 := by
  simp only [totalBoundary, horizontal_add, vertical_add, horizontal_squared,
    vertical_squared, zero_add, add_zero, horizontal_vertical]
  funext J S
  exact ZModModule.add_self _



/-- Exact intersections only where they contribute a genuine nerve face. -/
def IntersectionExact (L : I → Complex V) (n : ℕ) : Prop :=
  ∀ J : Finset I, J.Nonempty → J ∈ (nerve L).faces →
    ∀ r, J.card + r ≤ n → ExactAt (intersection L J) r

omit [Fintype V] in
private theorem bottom_horizontal_exact (K : Complex V) (L : I → Complex V)
    (a : ℕ) (hn : ExactAt (nerve L) a) (d : DoubleCoeff I V)
    (hd : BiSupported K L a 0 d) (hz : horizontal d = 0) :
    ∃ u, BiSupported K L (a+1) 0 u ∧ horizontal u = d := by
  classical
  let c : Coeff I := fun J => d J ∅
  have hc : Supported (nerve L) a c := by
    intro J h
    apply hd J ∅
    intro hh
    exact h.elim (fun h => h hh.2.2.2.2) (fun h => h hh.1)
  have hz' : boundary c = 0 := by
    funext J
    exact congrFun (congrFun hz J) ∅
  obtain ⟨f, hf, hfc⟩ := hn c hc hz'
  let u : DoubleCoeff I V := fun J S => if S = ∅ then f J else 0
  refine ⟨u, ?_, ?_⟩
  · intro J S h
    by_cases hS : S = ∅
    · subst S
      simp only [u, ↓reduceIte]
      apply hf
      by_contra hn'
      push Not at hn'
      apply h
      refine ⟨hn'.2, rfl, K.empty_mem, ?_, hn'.1⟩
      intro i _
      exact (L i).empty_mem
    · simp [u, hS]
  · funext J S
    by_cases hS : S = ∅
    · subst S
      simpa [horizontal, u, c] using congrFun hfc J
    · have hdS : d J S = 0 := hd J S (by
        intro h
        exact hS (Finset.card_eq_zero.mp h.2.1))
      simp [horizontal, boundary, u, hS, hdS]

omit [Fintype I] [DecidableEq I] in
private theorem column_vertical_exact (K : Complex V) (L : I → Complex V)
    (hsub : ∀ i, (L i).faces ⊆ K.faces) (n a b : ℕ) (ha : 0 < a)
    (hab : a+b ≤ n) (hex : IntersectionExact L n) (d : DoubleCoeff I V)
    (hd : BiSupported K L a b d) (hz : vertical d = 0) :
    ∃ u, BiSupported K L a (b+1) u ∧ vertical u = d := by
  classical
  have hf (J : Finset I) (hJ : J.card = a ∧ J ∈ (nerve L).faces) :
      ∃ c, Supported (intersection L J) (b+1) c ∧ boundary c = d J := by
    have hs : Supported (intersection L J) b (d J) := by
      intro S h
      apply hd J S
      intro hh
      exact h.elim (fun h => h hh.2.2.2.1) (fun h => h hh.2.1)
    exact hex J (Finset.card_pos.mp (by omega)) hJ.2 b (by omega)
      (d J) hs (congrFun hz J)
  let u : DoubleCoeff I V := fun J =>
    if hJ : J.card = a ∧ J ∈ (nerve L).faces then Classical.choose (hf J hJ) else 0
  refine ⟨u, ?_, ?_⟩
  · intro J S hn
    by_cases hJ : J.card = a ∧ J ∈ (nerve L).faces
    · simp only [u, hJ]
      have hu := (Classical.choose_spec (hf J hJ)).1
      apply hu
      by_contra hneg
      push Not at hneg
      apply hn
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < J.card by omega)
      exact ⟨hJ.1, hneg.2, hsub i (hneg.1 i hi), hneg.1, hJ.2⟩
    · simp [u, hJ]
  · funext J
    by_cases hJ : J.card = a ∧ J ∈ (nerve L).faces
    · simpa [vertical, u, hJ] using (Classical.choose_spec (hf J hJ)).2
    · have hdJ : d J = 0 := by
        funext S
        apply hd
        intro h
        exact hJ ⟨h.1, h.2.2.2.2⟩
      simp [vertical, u, hJ, hdJ]

private theorem closed_horizontal_lift (K : Complex V) (L : I → Complex V)
    (hsub : ∀ i, (L i).faces ⊆ K.faces) (hcover : Covers K L) (n : ℕ)
    (hnerve : AcyclicThrough (nerve L) n) (hex : IntersectionExact L n) (b : ℕ) :
    ∀ a, a+b < n → ∀ d, BiSupported K L a b d → horizontal d = 0 → vertical d = 0 →
      ∃ u, BiSupported K L (a+1) b u ∧ horizontal u = d ∧ vertical u = 0 := by
  induction b with
  | zero =>
    intro a ha d hd hz _
    obtain ⟨u, hu, hud⟩ := bottom_horizontal_exact K L a (hnerve a (by omega)) d hd hz
    exact ⟨u, hu, hud, vertical_at_zero hu⟩
  | succ b ih =>
    intro a ha d hd hz hv
    obtain ⟨x, hx, hxd⟩ := horizontal_exact K L hcover a (b+1) (by omega) d hd hz
    have hhx : horizontal (vertical x) = 0 := by
      rw [horizontal_vertical, hxd, hv]
    obtain ⟨y, hy, hyx, hvy⟩ := ih (a+1) (by omega) (vertical x)
      (vertical_supported hx) hhx (vertical_squared x)
    obtain ⟨z, hzs, hzy⟩ := column_vertical_exact K L hsub n (a+1+1) b
      (by omega) (by omega) hex y hy hvy
    refine ⟨x + horizontal z, bi_add hx (horizontal_supported hzs), ?_, ?_⟩
    · rw [horizontal_add, horizontal_squared, add_zero, hxd]
    · rw [vertical_add, ← horizontal_vertical, hzy, hyx]
      funext J S
      exact ZModModule.add_self _

/-- Cell-count version of the finite homological cover lemma (n=q+2). -/
theorem homological_cover (K : Complex V) (L : I → Complex V)
    (hsub : ∀ i, (L i).faces ⊆ K.faces) (hcover : Covers K L) (n : ℕ)
    (hnerve : AcyclicThrough (nerve L) n) (hex : IntersectionExact L n) :
    AcyclicThrough K n := by
  intro k hk c hc hz
  classical
  let d : DoubleCoeff I V := fun J S => if J = ∅ then c S else 0
  have hd : BiSupported K L 0 k d := by
    intro J S hn
    by_cases hJ : J = ∅
    · subst J
      simp only [d, ↓reduceIte]
      apply hc
      by_contra hneg
      push Not at hneg
      apply hn
      exact ⟨rfl, hneg.2, hneg.1, by simp, Or.inl rfl⟩
    · simp [d, hJ]
  have hv : vertical d = 0 := by
    funext J
    by_cases hJ : J = ∅
    · simpa [vertical, d, hJ] using hz
    · simp only [vertical, d, hJ, ↓reduceIte]
      exact boundary_zero
  obtain ⟨u, hu, hud, huv⟩ := closed_horizontal_lift K L hsub hcover n hnerve hex k
    0 (by omega) d hd (horizontal_at_zero hd) hv
  obtain ⟨z, hzs, hzu⟩ := column_vertical_exact K L hsub n 1 k (by omega)
    (by omega) hex u hu huv
  refine ⟨fun S => horizontal z ∅ S, ?_, ?_⟩
  · intro S hs
    apply horizontal_supported hzs ∅ S
    intro hh
    exact hs.elim (fun h => h hh.2.2.1) (fun h => h hh.2.1)
  · have he : vertical (horizontal z) = d := by
      rw [← horizontal_vertical, hzu, hud]
    funext S
    simpa [vertical, d] using congrFun (congrFun he ∅) S


end DoubleComplex

end

end SATurday.ProofComplexity.BraunPC.Aug
