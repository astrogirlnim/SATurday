import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Augmented F2 chains on abstract finite complexes (R4 Phase 2.1, layer 6h)

Credit. Port of K. Braun's third party chain development (arXiv 2609.23015, author's Lean
development): `AugmentedChains.lean` (`Complex`, `Coeff`, `Supported`, `boundary`),
`AugmentedBoundarySquared.lean` (`boundary_boundary`), `AugmentedCone.lean` (`cone`,
`cone_identity`, `cone_exact`, `ExactAt`, `AcyclicThrough`), `AugmentedChainMaps.lean` (`push`,
`boundary_push`, `push_supported`, `push_injective`), `AugmentedSubcomplexRelabeling.lean`
(`exactAt_subcomplex`, restated on raw coefficient functions instead of his submodule `chains`) and
`SimplexBoundary.lean` (`simplexBoundary_exact`). Cell counts: `Supported K k c` means `c` is
supported on faces of `K` with exactly `k` vertices (so the augmentation is `k = 0`).

Everything lives in the namespace `Aug` so that it does not clash with the chessboard specific API
of `BraunMomentChains`.

LOG: R4 BraunAugComplex module (Phase 2.1 layer 6h)
-/

namespace SATurday.ProofComplexity.BraunPC.Aug

noncomputable section

open scoped BigOperators

/-- Finite abstract complex including its augmentation face. -/
structure Complex (V : Type*) where
  faces : Set (Finset V)
  empty_mem : ∅ ∈ faces
  downward : ∀ {s t}, s ⊆ t → t ∈ faces → s ∈ faces

abbrev Coeff (V : Type*) := Finset V → ZMod 2

section Basic
variable {V : Type*} [Fintype V] [DecidableEq V]

def Supported (K : Complex V) (k : ℕ) (c : Coeff V) : Prop :=
  ∀ s, s ∉ K.faces ∨ s.card ≠ k → c s = 0

/-- Ambient augmented boundary, simultaneously in all degrees. -/
def boundary (c : Coeff V) : Coeff V :=
  fun s => ∑ v : V, if v ∈ s then 0 else c (insert v s)

theorem boundary_add (c d : Coeff V) : boundary (c + d) = boundary c + boundary d := by
  funext s
  simp only [boundary, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp

@[simp] theorem boundary_zero : boundary (0 : Coeff V) = 0 := by
  funext s
  simp [boundary]

theorem boundary_supported (K : Complex V) (k : ℕ) (c : Coeff V)
    (hc : Supported K (k + 1) c) : Supported K k (boundary c) := by
  intro s hs
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : v ∈ s
  · simp [hv]
  · simp only [hv, ↓reduceIte]
    apply hc
    rcases hs with hs | hs
    · exact Or.inl (fun h => hs (K.downward (Finset.subset_insert v s) h))
    · exact Or.inr (by simpa [Finset.card_insert_of_notMem hv] using hs)

theorem boundary_empty (K : Complex V) (c : Coeff V)
    (hc : Supported K 0 c) : boundary c = 0 := by
  funext s
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : v ∈ s
  · simp [hv]
  · simp only [hv, ↓reduceIte]
    apply hc
    right
    simp [Finset.card_insert_of_notMem hv]

theorem boundary_boundary (c : Coeff V) : boundary (boundary c) = 0 := by
  classical
  funext s
  let f : V × V → ZMod 2 := fun p =>
    if p.1 ∈ s ∨ p.2 ∈ s ∨ p.1 = p.2 then 0 else c (insert p.2 (insert p.1 s))
  have heq : boundary (boundary c) s = ∑ p : V × V, f p := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ s
    · simp [f, hv]
    · simp only [boundary, hv, ↓reduceIte]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : w ∈ s <;> by_cases hvw : v = w <;>
        simp_all [f, Finset.mem_insert, eq_comm]
  rw [heq]
  apply Finset.sum_involution (fun p _ => (p.2, p.1))
  · intro p _
    by_cases hp : p.1 ∈ s ∨ p.2 ∈ s ∨ p.1 = p.2
    · have hp' : p.2 ∈ s ∨ p.1 ∈ s ∨ p.2 = p.1 := by tauto
      simp [f, hp, hp']
    · have hp' : ¬ (p.2 ∈ s ∨ p.1 ∈ s ∨ p.2 = p.1) := by tauto
      simp only [f, hp, hp', ↓reduceIte, Finset.insert_comm]
      exact ZModModule.add_self _
  · intro p _ hp he
    have : p.1 = p.2 := (congrArg Prod.snd he)
    exact hp (by simp [f, this])
  · intro p _
    exact Finset.mem_univ _
  · intro p _
    rfl

/-! ### Cones and exactness -/

def IsCone (K : Complex V) (v : V) : Prop :=
  ∀ s, s ∈ K.faces → insert v s ∈ K.faces

def ExactAt (K : Complex V) (k : ℕ) : Prop :=
  ∀ c, Supported K k c → boundary c = 0 →
    ∃ b, Supported K (k + 1) b ∧ boundary b = c

def AcyclicThrough (K : Complex V) (n : ℕ) : Prop :=
  ∀ k < n, ExactAt K k

def cone (v : V) (c : Coeff V) : Coeff V :=
  fun s => if v ∈ s then c (s.erase v) else 0

theorem cone_identity (v : V) (c : Coeff V) :
    boundary (cone v c) + cone v (boundary c) = c := by
  funext s
  by_cases hv : v ∈ s
  · have hi (w : V) (hw : w ≠ v) :
        (insert w s).erase v = insert w (s.erase v) := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert]
      aesop
    have hsum : boundary c (s.erase v) = c s + boundary (cone v c) s := by
      unfold boundary
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
      simp only [Finset.notMem_erase, ↓reduceIte, Finset.insert_erase hv]
      have he : (∑ w ∈ Finset.univ.erase v,
          if w ∈ s.erase v then (0 : ZMod 2) else c (insert w (s.erase v))) =
          ∑ w : V, if w ∈ s then 0 else cone v c (insert w s) := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
        simp only [hv, ↓reduceIte, add_zero]
        apply Finset.sum_congr rfl
        intro w hw
        have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
        simp [Finset.mem_erase, hwv, cone, hv, hi w hwv]
      rw [he, add_comm]
    simp only [Pi.add_apply, cone, hv, ↓reduceIte]
    rw [hsum]
    calc
      _ = (boundary (cone v c) s + boundary (cone v c) s) + c s := by ac_rfl
      _ = c s := by rw [ZModModule.add_self, zero_add]
  · have hb : boundary (cone v c) s = c s := by
      unfold boundary
      rw [Finset.sum_eq_single v]
      · simp [cone, hv]
      · intro w _ hw
        simp [cone, hv, Ne.symm hw]
      · simp
    simpa [Pi.add_apply, cone, hv] using hb

omit [Fintype V] in
theorem cone_supported (K : Complex V) (v : V) (hv : IsCone K v)
    (k : ℕ) (c : Coeff V) (hc : Supported K k c) :
    Supported K (k+1) (cone v c) := by
  intro s hs
  by_cases hvs : v ∈ s
  · simp only [cone, hvs, ↓reduceIte]
    apply hc
    rcases hs with hs | hs
    · left
      intro h
      exact hs (by simpa [Finset.insert_erase hvs] using hv _ h)
    · right
      intro h
      exact hs (by simpa [Finset.insert_erase hvs] using
        Finset.card_insert_of_notMem (Finset.notMem_erase v s) |>.trans (congrArg (·+1) h))
  · simp [cone, hvs]

theorem cone_exact (K : Complex V) (v : V) (hv : IsCone K v) (k : ℕ) :
    ExactAt K k := by
  intro c hc hz
  refine ⟨cone v c, cone_supported K v hv k c hc, ?_⟩
  have h := cone_identity v c
  have hzero : cone v (0 : Coeff V) = 0 := by funext s; simp [cone]
  simpa [hz, hzero] using h

/-! ### Simplex and its boundary -/

def simplex (T : Finset V) : Complex V where
  faces := {s | s ⊆ T}
  empty_mem := Finset.empty_subset T
  downward := fun h hT => h.trans hT

def simplexBoundary (T : Finset V) (hT : T.Nonempty) : Complex V where
  faces := {s | s ⊂ T}
  empty_mem := Finset.empty_ssubset.mpr hT
  downward := fun {_ t} h (ht : t ⊂ T) => Finset.ssubset_of_subset_of_ssubset h ht

omit [Fintype V] in
theorem simplex_cone (T : Finset V) (v : V) (hv : v ∈ T) :
    IsCone (simplex T) v := by
  intro s hs
  exact Finset.insert_subset hv hs

theorem simplexBoundary_exact (T : Finset V) (hT : T.Nonempty) (k : ℕ)
    (hk : k+1 < T.card) : ExactAt (simplexBoundary T hT) k := by
  intro c hc hz
  obtain ⟨v, hv⟩ := hT
  have hs : Supported (simplex T) k c := by
    intro s h
    apply hc
    rcases h with h | h
    · left
      intro hs
      apply h
      exact (Finset.ssubset_iff_subset_ne.mp (show s ⊂ T from hs)).1
    · exact Or.inr h
  obtain ⟨b, hb, hbc⟩ := cone_exact (simplex T) v (simplex_cone T v hv) k c hs hz
  refine ⟨b, ?_, hbc⟩
  intro s h
  apply hb
  rcases h with h | h
  · by_cases hsub : s ⊆ T
    · right
      intro hcard
      apply h
      exact (show s ⊂ T from Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
        intro he
        have : T.card = k+1 := he ▸ hcard
        omega⟩)
    · exact Or.inl hsub
  · exact Or.inr h

theorem simplexBoundary_acyclic (T : Finset V) (hT : T.Nonempty) (n : ℕ)
    (hn : n < T.card) : AcyclicThrough (simplexBoundary T hT) n := by
  intro k hk
  apply simplexBoundary_exact T hT k
  omega

end Basic

/-! ### Relabeling along injections -/

section Push
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def InRange (e : V ↪ W) (T : Finset W) : Prop :=
  ∀ w ∈ T, ∃ v, e v = w

def push (e : V ↪ W) (c : Coeff V) : Coeff W := by
  classical
  exact fun T => if InRange e T then c (T.preimage e e.injective.injOn) else 0

omit [Fintype V] [Fintype W] in
theorem preimage_insert (e : V ↪ W) (v : V) (T : Finset W) :
    (insert (e v) T).preimage e e.injective.injOn =
      insert v (T.preimage e e.injective.injOn) := by
  ext x
  simp [Finset.mem_preimage, e.injective.eq_iff]

omit [Fintype V] [DecidableEq V] [Fintype W] in
theorem inRange_insert (e : V ↪ W) (v : V) (T : Finset W) :
    InRange e (insert (e v) T) ↔ InRange e T := by
  simp [InRange]

theorem boundary_push (e : V ↪ W) (c : Coeff V) :
    boundary (push e c) = push e (boundary c) := by
  classical
  funext T
  by_cases hT : InRange e T
  · have hout (w : W) (hw : w ∉ Finset.univ.image e) :
        (if w ∈ T then 0 else push e c (insert w T)) = 0 := by
      have hr : ¬ InRange e (insert w T) := by
        intro h
        obtain ⟨v, hv⟩ := h w (Finset.mem_insert_self w T)
        exact hw (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩)
      simp [push, hr]
    calc
      boundary (push e c) T =
          ∑ w ∈ Finset.univ.image e, if w ∈ T then 0 else push e c (insert w T) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro w _ hw
        exact hout w hw
      _ = ∑ v : V, if e v ∈ T then 0 else push e c (insert (e v) T) := by
        rw [Finset.sum_image]
        intro x _ y _ h
        exact e.injective h
      _ = push e (boundary c) T := by
        simp only [push, hT, ↓reduceIte, boundary]
        apply Finset.sum_congr rfl
        intro v _
        simp [inRange_insert, hT, preimage_insert, Finset.mem_preimage]
  · have hi (w : W) : ¬ InRange e (insert w T) := by
      intro h
      exact hT (fun x hx => h x (Finset.mem_insert_of_mem hx))
    simp [boundary, push, hT, hi]

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem map_preimage (e : V ↪ W) (T : Finset W) (hT : InRange e T) :
    (T.preimage e e.injective.injOn).map e = T := by
  ext w
  simp only [Finset.mem_map, Finset.mem_preimage]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact hv
  · intro hw
    obtain ⟨v, rfl⟩ := hT w hw
    exact ⟨v, hw, rfl⟩

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem push_supported (e : V ↪ W) (K : Complex V) (L : Complex W)
    (he : ∀ S ∈ K.faces, S.map e ∈ L.faces) (k : ℕ) (c : Coeff V)
    (hc : Supported K k c) : Supported L k (push e c) := by
  intro T hT
  classical
  by_cases hr : InRange e T
  · simp only [push, hr, ↓reduceIte]
    apply hc
    have hmap := map_preimage e T hr
    rcases hT with hT | hT
    · left
      intro h
      exact hT (hmap ▸ he _ h)
    · right
      intro h
      apply hT
      rw [← hmap, Finset.card_map, h]
  · simp [push, hr]

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem push_apply_map (e : V ↪ W) (c : Coeff V) (S : Finset V) :
    push e c (S.map e) = c S := by
  classical
  have hr : InRange e (S.map e) := by
    intro w hw
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hw
    exact ⟨v, rfl⟩
  simp [push, hr, Finset.preimage_map]

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem push_injective (e : V ↪ W) : Function.Injective (push e) := by
  intro c d h
  funext S
  simpa only [push_apply_map] using congrFun h (S.map e)

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem push_zero (e : V ↪ W) : push e (0 : Coeff V) = 0 := by
  classical
  funext T
  by_cases hT : InRange e T <;> simp [push, hT]

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem push_equiv (e : V ≃ W) (c : Coeff V) (T : Finset W) :
    push e.toEmbedding c T = c (T.map e.symm.toEmbedding) := by
  classical
  have hr : InRange e.toEmbedding T := fun w _ => ⟨e.symm w, e.apply_symm_apply w⟩
  have hpre : T.preimage e.toEmbedding e.injective.injOn = T.map e.symm.toEmbedding := by
    ext v
    simp [Finset.mem_preimage]
  simp only [push, hr, ↓reduceIte]
  rw [hpre]

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
theorem push_equiv_inverse (e : V ≃ W) (c : Coeff V) :
    push e.symm.toEmbedding (push e.toEmbedding c) = c := by
  funext S
  rw [push_equiv, push_equiv]
  congr 1
  ext v
  simp

section Subcomplex
variable (e : V ↪ W) (K : Complex V) (L : Complex W)
  (hf : ∀ S, S ∈ K.faces ↔ S.map e ∈ L.faces)
  (hr : ∀ T ∈ L.faces, InRange e T)

/-- Pull a chain on `L` back to `K` along the relabeling. -/
def pull (c : Coeff W) : Coeff V := fun S => c (S.map e)

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
include hf in
theorem pull_supported (k : ℕ) (c : Coeff W) (hc : Supported L k c) :
    Supported K k (pull e c) := by
  intro S hS
  apply hc
  rcases hS with hS | hS
  · exact Or.inl (fun h => hS ((hf S).mpr h))
  · exact Or.inr (by simpa using hS)

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] in
include hr in
theorem push_pull (k : ℕ) (c : Coeff W) (hc : Supported L k c) :
    push e (pull e c) = c := by
  funext T
  classical
  by_cases hT : InRange e T
  · simp only [push, hT, ↓reduceIte, pull]
    rw [map_preimage e T hT]
  · simp only [push, hT, ↓reduceIte]
    symm
    exact hc T (Or.inl (fun ht => hT (hr T ht)))

include hf hr in
theorem exactAt_subcomplex (k : ℕ) (hK : ExactAt K k) : ExactAt L k := by
  intro c hc hz
  have he : push e (pull e c) = c := push_pull e L hr k c hc
  have hd : boundary (pull e c) = 0 := by
    apply push_injective e
    rw [← boundary_push, he, hz, push_zero]
  obtain ⟨f, hf', hdf⟩ := hK (pull e c) (pull_supported e K L hf k c hc) hd
  refine ⟨push e f, push_supported e K L (fun S hs => (hf S).mp hs) (k+1) f hf', ?_⟩
  rw [boundary_push, hdf, he]

end Subcomplex

end Push

end

end SATurday.ProofComplexity.BraunPC.Aug
