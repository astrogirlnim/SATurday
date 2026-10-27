import Theory.ProofComplexity.ResLinFDag

/-!
# Tree-like `Res(lin F)` into dag-like `Res(lin F)` (referee leftover, dossier Section 16 (v))

`RLF.RLD Ax w L s` counts the leaves `s` of a tree-like derivation. Here `RLN Ax w L s n` is the
same derivation relation that also records the number `n` of nodes (every rule application and
every axiom leaf counts one). `rld_iff_rln` says `RLN` only adds the node count. The theorem
`rln_to_rldag`: a tree-like derivation with `n` nodes yields an `RLDag` derivation with at most `n`
lines containing the conclusion. Hence a lower bound on the number of lines of `RLDag` derivations
is a lower bound on the node count of tree-like derivations (not on the leaf count, which can be
smaller than the node count by the unbounded chains of weakenings and simplifications).
-/

namespace SATurday.ProofComplexity

namespace RLF

open scoped Classical

noncomputable section

variable {F : Type} [Field F]

/-- Tree-like derivations with leaf count `s` and node count `n`. -/
inductive RLN (Ax : Set (Finset (LEq F))) (w : ℕ) : Finset (LEq F) → ℕ → ℕ → Prop
  | ax {C} : C ∈ Ax → C.card ≤ w → RLN Ax w C 1 1
  | weak {L L' s n} : RLN Ax w L s n → L ⊆ L' → L'.card ≤ w → RLN Ax w L' s (n + 1)
  | comb {A B : Finset (LEq F)} {s1 s2 n1 n2 : ℕ} (e1 e2 : LEq F) (α β : F) :
      RLN Ax w A s1 n1 → RLN Ax w B s2 n2 → e1 ∈ A → e2 ∈ B →
      (A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2}).card ≤ w →
      RLN Ax w (A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2}) (s1 + s2) (n1 + n2 + 1)
  | simp {L s n} (c : F) : c ≠ 0 → RLN Ax w (insert ((0 : ℕ →₀ F), c) L) s n →
      RLN Ax w L s (n + 1)

theorem rln_to_rld {Ax : Set (Finset (LEq F))} {w : ℕ} {L : Finset (LEq F)} {s n : ℕ}
    (h : RLN Ax w L s n) : RLD Ax w L s := by
  induction h with
  | ax hC hw => exact RLD.ax hC hw
  | weak _ hsub hw ih => exact RLD.weak ih hsub hw
  | comb e1 e2 α β _ _ h1 h2 hw ih1 ih2 => exact RLD.comb e1 e2 α β ih1 ih2 h1 h2 hw
  | simp c hc _ ih => exact RLD.simp c hc ih

theorem rld_to_rln {Ax : Set (Finset (LEq F))} {w : ℕ} {L : Finset (LEq F)} {s : ℕ}
    (h : RLD Ax w L s) : ∃ n, RLN Ax w L s n := by
  induction h with
  | ax hC hw => exact ⟨1, RLN.ax hC hw⟩
  | weak _ hsub hw ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, RLN.weak hn hsub hw⟩
  | comb e1 e2 α β _ _ h1 h2 hw ih1 ih2 =>
    obtain ⟨n1, hn1⟩ := ih1; obtain ⟨n2, hn2⟩ := ih2
    exact ⟨n1 + n2 + 1, RLN.comb e1 e2 α β hn1 hn2 h1 h2 hw⟩
  | simp c hc _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, RLN.simp c hc hn⟩

theorem rld_iff_rln {Ax : Set (Finset (LEq F))} {w : ℕ} {L : Finset (LEq F)} {s : ℕ} :
    RLD Ax w L s ↔ ∃ n, RLN Ax w L s n :=
  ⟨rld_to_rln, fun ⟨_, h⟩ => rln_to_rld h⟩

/-- Union of two dag derivations is a dag derivation. -/
theorem rldag_union {Ax : Set (Finset (LEq F))} {𝓛1 𝓛2 : Finset (Finset (LEq F))}
    (h1 : RLDag Ax 𝓛1) (h2 : RLDag Ax 𝓛2) : RLDag Ax (𝓛1 ∪ 𝓛2) := by
  induction h2 with
  | empty => simpa using h1
  | ax C _ hC ih =>
    rw [Finset.union_insert]; exact RLDag.ax C ih hC
  | weak L L' _ hL hsub ih =>
    rw [Finset.union_insert]; exact RLDag.weak L L' ih (Finset.mem_union_right _ hL) hsub
  | comb A B e1 e2 α β _ hA hB he1 he2 ih =>
    rw [Finset.union_insert]
    exact RLDag.comb A B e1 e2 α β ih (Finset.mem_union_right _ hA)
      (Finset.mem_union_right _ hB) he1 he2
  | simp L c _ hc h0 ih =>
    rw [Finset.union_insert]; exact RLDag.simp L c ih hc (Finset.mem_union_right _ h0)

/-- **Tree-like into dag-like**: a tree-like derivation with `n` nodes gives a dag derivation with
at most `n` lines containing the conclusion. -/
theorem rln_to_rldag {Ax : Set (Finset (LEq F))} {w : ℕ} {L : Finset (LEq F)} {s n : ℕ}
    (h : RLN Ax w L s n) : ∃ 𝓛, RLDag Ax 𝓛 ∧ L ∈ 𝓛 ∧ 𝓛.card ≤ n := by
  induction h with
  | ax hC _ =>
    refine ⟨{_}, ?_, Finset.mem_singleton_self _, by simp⟩
    have := RLDag.ax _ RLDag.empty hC
    simpa using this
  | @weak L0 L' _ n0 _ hsub _ ih =>
    obtain ⟨𝓛, hD, hL, hc⟩ := ih
    exact ⟨insert L' 𝓛, RLDag.weak L0 L' hD hL hsub, Finset.mem_insert_self _ _,
      (Finset.card_insert_le _ _).trans (by omega)⟩
  | @comb A B _ _ _ _ e1 e2 α β _ _ h1 h2 _ ih1 ih2 =>
    obtain ⟨𝓛1, hD1, hA, hc1⟩ := ih1
    obtain ⟨𝓛2, hD2, hB, hc2⟩ := ih2
    refine ⟨insert _ (𝓛1 ∪ 𝓛2), RLDag.comb _ _ e1 e2 α β (rldag_union hD1 hD2)
      (Finset.mem_union_left _ hA) (Finset.mem_union_right _ hB) h1 h2,
      Finset.mem_insert_self _ _, ?_⟩
    have h3 := Finset.card_union_le 𝓛1 𝓛2
    have h4 := Finset.card_insert_le (A.erase e1 ∪ B.erase e2 ∪ {cmb α β e1 e2}) (𝓛1 ∪ 𝓛2)
    omega
  | @simp L0 s0 n0 c hc _ ih =>
    obtain ⟨𝓛, hD, hL, hcd⟩ := ih
    exact ⟨insert L0 𝓛, RLDag.simp L0 c hD hc hL, Finset.mem_insert_self _ _,
      (Finset.card_insert_le _ _).trans (by omega)⟩

/-- Tree-like refutation with `n` nodes gives a dag-like refutation with at most `n` lines. -/
theorem rln_refutes_to_rldag {Ax : Set (Finset (LEq F))} {w s n : ℕ}
    (h : RLN Ax w ∅ s n) : ∃ 𝓛, RLDag Ax 𝓛 ∧ (∅ : Finset (LEq F)) ∈ 𝓛 ∧ 𝓛.card ≤ n :=
  rln_to_rldag h

end

end RLF

end SATurday.ProofComplexity
