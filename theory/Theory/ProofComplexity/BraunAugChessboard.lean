import Theory.ProofComplexity.BraunAugCover

/-!
# The chessboard complex is homologically acyclic in the stable range (R4 Phase 2.1, layer 6j)

Credit. Port of K. Braun's third party development (arXiv 2609.23015, author's Lean development):
`ChessboardStarCover.lean`, `ChessboardStarIntersections.lean`, `ChessboardStarNerve.lean`,
`ChessboardParameterArithmetic.lean` and `ChessboardHomology.lean`, which prove
`chessboard_homological_bound` by the closed first row star cover of the chessboard complex
(the homological form of Bjorner, Lovasz, Vrecica, Zivaljevic, Chessboard complexes and matching
complexes, J. London Math. Soc. 49 (1994)): the complex on an `a x b` board is augmented F2 acyclic
through `nu(a,b) = min a (min b ((a+b+1)/3))`. His rank two intersection relabeling is routed here
through `exactAt_subcomplex` directly instead of his chain equivalence.

LOG: R4 BraunAugChessboard module (Phase 2.1 layer 6j)
-/

namespace SATurday.ProofComplexity.BraunPC.Aug

noncomputable section

open scoped BigOperators

/-- The downward-closed family of nonattacking rook sets, including the empty set. -/
def chessboardComplex (s N : ℕ) : Complex (Fin s × Fin N) where
  faces := {M | Set.InjOn Prod.fst (M : Set (Fin s × Fin N)) ∧ Set.InjOn Prod.snd (M : Set (Fin s × Fin N))}
  empty_mem := by simp
  downward := by
    intro A B h hB
    exact ⟨hB.1.mono h, hB.2.mono h⟩

section
variable {V : Type*} [DecidableEq V]

def closedStar (K : Complex V) (v : V) (hv : {v} ∈ K.faces) : Complex V where
  faces := {s | insert v s ∈ K.faces}
  empty_mem := by simpa using hv
  downward := by intro s t h ht; exact K.downward (Finset.insert_subset_insert v h) ht
theorem closedStar_subcomplex (K : Complex V) (v : V) (hv : {v} ∈ K.faces) :
    (closedStar K v hv).faces ⊆ K.faces :=
  fun _ h => K.downward (Finset.subset_insert _ _) h
theorem closedStar_cone (K : Complex V) (v : V) (hv : {v} ∈ K.faces)
    (s : Finset V) (hs : s ∈ (closedStar K v hv).faces) :
    insert v s ∈ (closedStar K v hv).faces := by
  show insert v (insert v s) ∈ K.faces
  rw [Finset.insert_idem]
  exact hs

end

def firstRowStar (a b : ℕ) (j : Fin b) : Complex (Fin (a+1) × Fin b) :=
  closedStar (chessboardComplex (a+1) b) (0,j) (by
    constructor <;> intro x hx y hy _ <;>
      exact (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm)

theorem extend_matching {a b : ℕ} (M : Finset (Fin (a+1) × Fin b))
    (hM : M ∈ (chessboardComplex (a+1) b).faces) (j : Fin b)
    (hr : ∀ x ∈ M, x.1 ≠ 0) (hc : ∀ x ∈ M, x.2 ≠ j) :
    insert (0,j) M ∈ (chessboardComplex (a+1) b).faces := by
  constructor
  · intro x hx y hy he
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · rfl
      · exact False.elim (hr y hy he.symm)
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact False.elim (hr x hx he)
      · exact hM.1 hx hy he
  · intro x hx y hy he
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · rfl
      · exact False.elim (hc y hy he.symm)
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · exact False.elim (hc x hx he)
      · exact hM.2 hx hy he

theorem firstRowStars_cover (a b : ℕ) (hab : a+1 ≤ b) :
    Covers (chessboardComplex (a+1) b) (firstRowStar a b) := by
  intro M hM
  classical
  by_cases hr : ∃ x ∈ M, x.1 = 0
  · obtain ⟨x, hx, he⟩ := hr
    refine ⟨x.2, ?_⟩
    change insert (0,x.2) M ∈ (chessboardComplex (a+1) b).faces
    have hx' : (0,x.2) ∈ M := by simpa [← he] using hx
    simpa [Finset.insert_eq_of_mem hx'] using hM
  · have hr' : ∀ x ∈ M, x.1 ≠ 0 := by
      intro x hx he
      exact hr ⟨x,hx,he⟩
    have hsub : M.image Prod.fst ⊆ Finset.univ.erase 0 := by
      intro r hr
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hr
      simp [hr' x hx]
    have hcard : M.card ≤ a := by
      have := Finset.card_le_card hsub
      simpa [Finset.card_image_of_injOn hM.1] using this
    have hcol : (M.image Prod.snd).card < (Finset.univ : Finset (Fin b)).card := by
      rw [Finset.card_image_of_injOn hM.2]
      simpa using Nat.lt_of_le_of_lt hcard (Nat.lt_of_lt_of_le (Nat.lt_succ_self a) hab)
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hcol
    refine ⟨j, extend_matching M hM j hr' ?_⟩
    intro x hx he
    exact hj (Finset.mem_image.mpr ⟨x,hx,he⟩)

theorem star_intersection_faces (a b : ℕ) (J : Finset (Fin b)) (hJ : 2 ≤ J.card)
    (M : Finset (Fin (a+1) × Fin b)) :
    M ∈ (intersection (firstRowStar a b) J).faces ↔
      M ∈ (chessboardComplex (a+1) b).faces ∧ ∀ x ∈ M, x.1 ≠ 0 ∧ x.2 ∉ J := by
  obtain ⟨j,hj,k,hk,hjk⟩ := Finset.one_lt_card.mp hJ
  constructor
  · intro h
    have hstar (i : Fin b) (hi : i ∈ J) :
        insert (0,i) M ∈ (chessboardComplex (a+1) b).faces := h i hi
    have hrow : ∀ x ∈ M, x.1 ≠ 0 := by
      intro x hx he
      have hxj := (hstar j hj).1 (Finset.mem_insert_of_mem hx) (Finset.mem_insert_self _ _) he
      have hxk := (hstar k hk).1 (Finset.mem_insert_of_mem hx) (Finset.mem_insert_self _ _) he
      exact hjk (congrArg Prod.snd (hxj.symm.trans hxk))
    refine ⟨(chessboardComplex (a+1) b).downward (Finset.subset_insert _ _) (hstar j hj), ?_⟩
    intro x hx
    refine ⟨hrow x hx, ?_⟩
    intro hc
    have hxj := (hstar x.2 hc).2 (Finset.mem_insert_of_mem hx) (Finset.mem_insert_self _ _) rfl
    exact hrow x hx (congrArg Prod.fst hxj)
  · rintro ⟨hM,hr⟩ i hi
    exact extend_matching M hM i (fun x hx => (hr x hx).1)
      (fun x hx he => (hr x hx).2 (he ▸ hi))

def remainingColumns (b : ℕ) (J : Finset (Fin b)) :
    {j : Fin b // j ∉ J} ≃ Fin (b-J.card) :=
  Fintype.equivFinOfCardEq (by simp [Fintype.card_subtype_compl])

def smallerBoardEmbedding (a b : ℕ) (J : Finset (Fin b)) :
    (Fin a × Fin (b-J.card)) ↪ (Fin (a+1) × Fin b) where
  toFun := fun x => (x.1.succ, ((remainingColumns b J).symm x.2).val)
  inj' := by
    intro x y h
    apply Prod.ext
    · exact Fin.succ_injective a (congrArg Prod.fst h)
    · apply (remainingColumns b J).symm.injective
      exact Subtype.ext (congrArg Prod.snd h)

private theorem smaller_map_faces (a b : ℕ) (J : Finset (Fin b)) (hJ : 2 ≤ J.card)
    (S : Finset (Fin a × Fin (b-J.card))) :
    S ∈ (chessboardComplex a (b-J.card)).faces ↔
      S.map (smallerBoardEmbedding a b J) ∈ (intersection (firstRowStar a b) J).faces := by
  rw [star_intersection_faces a b J hJ]
  constructor
  · intro hS
    constructor
    · constructor
      · intro x hx y hy h
        obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hy
        apply congrArg (smallerBoardEmbedding a b J)
        exact hS.1 hu hv (Fin.succ_injective a h)
      · intro x hx y hy h
        obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hy
        apply congrArg (smallerBoardEmbedding a b J)
        exact hS.2 hu hv ((remainingColumns b J).symm.injective (Subtype.ext h))
    · intro x hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hx
      exact ⟨Fin.succ_ne_zero _, ((remainingColumns b J).symm u.2).property⟩
  · rintro ⟨hS,_⟩
    constructor
    · intro x hx y hy h
      apply (smallerBoardEmbedding a b J).injective
      apply hS.1 (Finset.mem_map.mpr ⟨x,hx,rfl⟩) (Finset.mem_map.mpr ⟨y,hy,rfl⟩)
      exact congrArg Fin.succ h
    · intro x hx y hy h
      apply (smallerBoardEmbedding a b J).injective
      apply hS.2 (Finset.mem_map.mpr ⟨x,hx,rfl⟩) (Finset.mem_map.mpr ⟨y,hy,rfl⟩)
      exact congrArg (fun j => ((remainingColumns b J).symm j).val) h

private theorem smaller_range (a b : ℕ) (J : Finset (Fin b)) (hJ : 2 ≤ J.card)
    (T : Finset (Fin (a+1) × Fin b)) (hT : T ∈ (intersection (firstRowStar a b) J).faces) :
    InRange (smallerBoardEmbedding a b J) T := by
  intro x hx
  have hh := ((star_intersection_faces a b J hJ T).mp hT).2 x hx
  refine ⟨(x.1.pred hh.1, remainingColumns b J ⟨x.2,hh.2⟩), ?_⟩
  apply Prod.ext
  · exact Fin.succ_pred _ hh.1
  · exact congrArg Subtype.val ((remainingColumns b J).symm_apply_apply _)


theorem starIntersection_exactAt (a b : ℕ) (J : Finset (Fin b)) (hJ : 2 ≤ J.card)
    (k : ℕ) (h : ExactAt (chessboardComplex a (b-J.card)) k) :
    ExactAt (intersection (firstRowStar a b) J) k :=
  exactAt_subcomplex (smallerBoardEmbedding a b J) _ _
    (smaller_map_faces a b J hJ) (smaller_range a b J hJ) k h

theorem proper_star_intersection_vertex (a b : ℕ) (ha : 1 ≤ a)
    (J : Finset (Fin b)) (hJ : J ≠ Finset.univ) :
    ∃ v, {v} ∈ (intersection (firstRowStar a b) J).faces := by
  classical
  have hj : ∃ j : Fin b, j ∉ J := by
    by_contra h
    apply hJ
    ext j
    simp only [Finset.mem_univ, iff_true]
    exact Classical.not_not.mp (fun hn => h ⟨j,hn⟩)
  obtain ⟨j,hj⟩ := hj
  let r : Fin a := ⟨0,ha⟩
  let v : Fin (a+1) × Fin b := (r.succ,j)
  refine ⟨v, ?_⟩
  intro i hi
  refine extend_matching {v} ?_ i ?_ ?_
  · constructor <;> intro x hx y hy _ <;>
      exact (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm
  · intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact Fin.succ_ne_zero r
  · intro x hx he
    rw [Finset.mem_singleton.mp hx] at he
    have he' : j = i := he
    exact hj (he'.symm ▸ hi)

theorem full_star_intersection_empty (a b : ℕ) (hb : 2 ≤ b)
    (M : Finset (Fin (a+1) × Fin b)) :
    M ∈ (intersection (firstRowStar a b) Finset.univ).faces ↔ M = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hh := ((star_intersection_faces a b Finset.univ (by simpa using hb) M).mp h).2 x hx
    exact hh.2 (Finset.mem_univ _)
  · rintro rfl
    exact (intersection (firstRowStar a b) Finset.univ).empty_mem

theorem firstRowStar_nerve_faces (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b)
    (J : Finset (Fin b)) :
    J ∈ (nerve (firstRowStar a b)).faces ↔ J ⊂ Finset.univ := by
  rw [Finset.ssubset_iff_subset_ne]
  simp only [Finset.subset_univ, true_and]
  constructor
  · intro h he
    subst J
    rcases h with h | ⟨v,hv⟩
    · have hc := congrArg Finset.card h
      simp at hc
      omega
    · have hh := (full_star_intersection_empty a b hb {v}).mp hv
      exact Finset.singleton_ne_empty v hh
  · intro h
    obtain ⟨v,hv⟩ := proper_star_intersection_vertex a b ha J h
    exact Or.inr ⟨v,hv⟩

theorem complex_ext {V : Type*} (K L : Complex V) (h : K.faces = L.faces) : K = L := by
  cases K
  cases L
  cases h
  rfl

theorem firstRowStar_nerve_eq (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b) :
    nerve (firstRowStar a b) = simplexBoundary (Finset.univ : Finset (Fin b))
      (by exact ⟨⟨0,by omega⟩, Finset.mem_univ _⟩) := by
  have hf : (nerve (firstRowStar a b)).faces =
      (simplexBoundary (Finset.univ : Finset (Fin b))
        (by exact ⟨⟨0,by omega⟩, Finset.mem_univ _⟩)).faces := by
    ext J
    exact firstRowStar_nerve_faces a b ha hb J
  exact complex_ext _ _ hf

theorem firstRowStar_nerve_exact (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b)
    (k : ℕ) (hk : k+1 < b) : ExactAt (nerve (firstRowStar a b)) k := by
  rw [firstRowStar_nerve_eq a b ha hb]
  apply simplexBoundary_exact
  simpa using hk

theorem firstRowStar_nerve_acyclic (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b)
    (n : ℕ) (hn : n < b) : AcyclicThrough (nerve (firstRowStar a b)) n := by
  intro k hk
  apply firstRowStar_nerve_exact a b ha hb k
  omega


theorem firstRowStar_exact (a b : ℕ) (j : Fin b) (k : ℕ) :
    ExactAt (firstRowStar a b j) k := by
  apply cone_exact _ (0,j)
  exact closedStar_cone _ _ _

theorem transpose_faces (s N : ℕ) (S : Finset (Fin s × Fin N))
    (hS : S ∈ (chessboardComplex s N).faces) :
    S.map (Equiv.prodComm (Fin s) (Fin N)).toEmbedding ∈ (chessboardComplex N s).faces := by
  constructor
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact congrArg Prod.swap (hS.2 ha hb hxy)
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact congrArg Prod.swap (hS.1 ha hb hxy)


/-- The parameter in the homological chessboard bound. -/
def chessboardNu (a b : Nat) : Nat := min a (min b ((a + b + 1) / 3))

theorem chessboardNu_symm (a b : Nat) : chessboardNu a b = chessboardNu b a := by
  unfold chessboardNu
  omega

theorem chessboardNu_bounds (a b : Nat) :
    chessboardNu a b ≤ a ∧ chessboardNu a b ≤ b ∧
      3 * chessboardNu a b ≤ a + b + 1 := by
  unfold chessboardNu
  omega

theorem chessboardNu_pos {a b : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ chessboardNu a b := by
  unfold chessboardNu
  omega

theorem chessboardNu_zero (b : Nat) :
    chessboardNu 0 b = 0 ∧ chessboardNu b 0 = 0 := by
  unfold chessboardNu
  omega

theorem chessboardNu_one {b : Nat} (hb : 1 ≤ b) : chessboardNu 1 b = 1 := by
  unfold chessboardNu
  omega

theorem chessboardNu_ordered_bound {a b : Nat} (ha : 2 ≤ a) (hab : a ≤ b) :
    chessboardNu a b ≤ b - 1 := by
  unfold chessboardNu
  omega

/-- Additive form of the signed bound mu >= nu-t+1; no truncated subtraction. -/
theorem chessboardNu_intersection {a b t : Nat}
    (ha : 2 ≤ a) (hab : a ≤ b) (ht : 2 ≤ t) (htb : t < b) :
    chessboardNu a b + 1 ≤ chessboardNu (a - 1) (b - t) + t := by
  have hb := chessboardNu_ordered_bound ha hab
  have hn := chessboardNu_bounds a b
  unfold chessboardNu at *
  omega

theorem chessboardNu_intersection_degree {a b t : Nat}
    (ha : 2 ≤ a) (hab : a ≤ b) (ht : 2 ≤ t) (htb : t < b) :
    (chessboardNu a b : Int) - 2 - t + 1 ≤
      (chessboardNu (a - 1) (b - t) : Int) - 2 := by
  have h := chessboardNu_intersection ha hab ht htb
  omega

/-- Either orientation of the intersection has smaller induction measure. -/
theorem chessboard_induction_decrease {a b t : Nat} (ha : 1 ≤ a) (hab : a ≤ b) :
    min (a - 1) (b - t) < min a b ∧ min (b - t) (a - 1) < min a b := by
  omega

theorem chessboardNu_stable_range {s N : Nat} (h : 2 * s - 1 ≤ N) :
    chessboardNu s N = s := by
  unfold chessboardNu
  omega

/-- k counts cells, and k-1 is an integer reduced simplicial degree. -/
theorem chessboard_cell_degree_iff (k n : Nat) :
    (-1 ≤ (k : Int) - 1 ∧ (k : Int) - 1 ≤ (n : Int) - 2) ↔ k < n := by
  omega

/-- A bound strictly below -1 requests no augmented chain degree. -/
theorem chessboard_degree_vacuous {q : Int} (hq : q < -1) (k : Nat) :
    ¬ ((k : Int) - 1 ≤ q) := by
  omega

/-- nu=1 requests only the empty-face coordinate; nu=0 requests none. -/
theorem chessboardNu_base_degree (k : Nat) :
    (((k : Int) - 1 ≤ (1 : Int) - 2) ↔ k = 0) ∧
    ¬ ((k : Int) - 1 ≤ (0 : Int) - 2) := by
  omega


private theorem exact_at_zero {V : Type*} [Fintype V] [DecidableEq V]
    (K : Complex V) (v : V) (hv : {v} ∈ K.faces) : ExactAt K 0 := by
  intro c hc hz
  refine ⟨cone v c, ?_, ?_⟩
  · intro s hs
    by_cases hvs : v ∈ s
    · simp only [cone, hvs, ↓reduceIte]
      by_cases he : s.erase v = ∅
      · have hsingle : s = {v} := by simpa [he] using (Finset.insert_erase hvs).symm
        subst s
        rcases hs with hn | hn
        · exact False.elim (hn hv)
        · simp at hn
      · exact hc _ (Or.inr (fun hcard => he (Finset.card_eq_zero.mp hcard)))
    · simp [cone, hvs]
  · have h := cone_identity v c
    have hzero : cone v (0 : Coeff V) = 0 := by funext s; simp [cone]
    simpa only [hz, hzero, add_zero] using h

private theorem transpose_exact (a b k : ℕ) (h : ExactAt (chessboardComplex a b) k) :
    ExactAt (chessboardComplex b a) k := by
  intro c hc hz
  let e := Equiv.prodComm (Fin b) (Fin a)
  have hd := push_supported e.toEmbedding (chessboardComplex b a) (chessboardComplex a b)
    (transpose_faces b a) k c hc
  have hdz : boundary (push e.toEmbedding c) = 0 := by
    rw [boundary_push, hz]
    exact push_zero _
  obtain ⟨f, hf, hdf⟩ := h _ hd hdz
  refine ⟨push e.symm.toEmbedding f,
    push_supported e.symm.toEmbedding _ _ (transpose_faces a b) (k+1) f hf, ?_⟩
  rw [boundary_push, hdf, push_equiv_inverse]

theorem chessboard_homological_bound (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    AcyclicThrough (chessboardComplex a b) (chessboardNu a b) := by
  suffices hall : ∀ m a b : ℕ, min a b = m → 1 ≤ a → 1 ≤ b →
      AcyclicThrough (chessboardComplex a b) (chessboardNu a b) from
    hall (min a b) a b rfl ha hb
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro a b hab ha hb
    have ordered : ∀ a b : ℕ, min a b = m → 1 ≤ a → a ≤ b →
        AcyclicThrough (chessboardComplex a b) (chessboardNu a b) := by
      intro a b hab ha hab'
      cases a with
      | zero => omega
      | succ a =>
        by_cases hzero : a = 0
        · subst a
          rw [chessboardNu_one (by omega)]
          intro k hk
          have hk0 : k = 0 := by omega
          subst k
          apply exact_at_zero _ (0, ⟨0, by omega⟩)
          constructor <;> intro x hx y hy _ <;>
            exact (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm
        · have ha2 : 2 ≤ a + 1 := by omega
          apply homological_cover (chessboardComplex (a+1) b) (firstRowStar a b)
            (fun j => closedStar_subcomplex _ _ _) (firstRowStars_cover a b hab')
            (chessboardNu (a+1) b)
          · apply firstRowStar_nerve_acyclic a b (by omega) (by omega)
            have hnu := chessboardNu_ordered_bound ha2 hab'
            omega
          · intro J hJ hN r hr
            by_cases hj1 : J.card = 1
            · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hj1
              have he : intersection (firstRowStar a b) {j} = firstRowStar a b j := by
                apply complex_ext
                ext S
                simp [intersection]
              rw [he]
              exact firstRowStar_exact a b j r
            · have hj2 : 2 ≤ J.card := by have := hJ.card_pos; omega
              have hjlt : J.card < b := by
                have hsub := (firstRowStar_nerve_faces a b (by omega) (by omega) J).mp hN
                simpa using Finset.card_lt_card hsub
              apply starIntersection_exactAt a b J hj2 r
              have hsm : min a (b - J.card) < m := by
                rw [← hab]
                simpa using (chessboard_induction_decrease (t := J.card) (by omega) hab').1
              apply ih _ hsm a (b - J.card) rfl (by omega) (by omega) r
              have hn := chessboardNu_intersection ha2 hab' hj2 hjlt
              simp only [Nat.add_sub_cancel] at hn
              omega
    by_cases h : a ≤ b
    · exact ordered a b hab ha h
    · have ht := ordered b a (by simpa [Nat.min_comm] using hab) hb (by omega)
      intro k hk
      apply transpose_exact b a k
      apply ht k
      rw [chessboardNu_symm b a]
      exact hk


end

end SATurday.ProofComplexity.BraunPC.Aug
