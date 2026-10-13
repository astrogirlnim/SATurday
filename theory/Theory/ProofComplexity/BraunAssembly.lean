import Theory.ProofComplexity.BraunChessboardFilling
import Theory.ProofComplexity.BraunBitPHPTransfer
import Theory.ProofComplexity.BraunCommonKernel
import Theory.ProofComplexity.BraunENSRemoval
import Theory.ProofComplexity.BraunParameterBounds
import Theory.ProofComplexity.BraunDag

/-!
# Assembly: unconditional bit PHP lower bound for dag like `Res(⊕)` (R4 Phase 2.1, layer 8b)

Credit. Port, with our own proofs where they differ, of K. Braun, bit pigeonhole lower bound for dag
like resolution over parities (arXiv 2609.23015), author's Lean development:
`AffineFamilyExclusion.lean` (`affine_family_exclusion_of_square`, `affine_family_exclusion`,
`affine_family_polylog_exclusion`), `BitPHPClauseTransfer.lean` (`registry_system_eq_ensFamily`),
`BitPHPExponential.lean` (`bitPHP_exponential`, `bitPHP_exponential_base_two`) and
`BitPHPSuperpolynomial.lean` (`bitPHP_superpolynomial`). Statements keep his quantifier shape.

Differences from the source. (1) His `AffineDAG` is `Type` valued; ours (`RL.Braun.PDag`) is `Prop`
valued, which is equivalent for these statements (`pdag_to_affineDAG`). (2) The filling hypothesis
`hfill` of layer 6 is discharged by `matchingMomentFilling` (our proof of the chessboard filling
lemma, `BraunChessboardFilling`), so nothing here is conditional.

Main results.
* `BraunPC.bitPHP_exponential`: for `l >= 32`, every affine dag refutation of the usual bit PHP CNF
  with `2^l + 1` pigeons has `S > exp (2^l / (32768 l^2))` nodes.
* `RL.Braun.braunBitPHP`: the `Prop` `BraunBitPHP` of `BraunDag` is true.
* `RL.Braun.bphp_dag_superpolynomial`, `RL.Braun.bphp_dag_exponential`: the bounds for `RL.DagRefutes`
  on `bphpCNF l (2^l + 1)` (`s` lines), unconditionally.

LOG: R4 BraunAssembly module (Phase 2.1 layer 8b)
-/

namespace SATurday.ProofComplexity.BraunPC

noncomputable section

open MvPolynomial Filter
open SATurday.ProofComplexity.BraunLA
open SATurday.ProofComplexity.RL.Braun (BitVar usualInitials)
open scoped BigOperators

theorem registry_system_eq_ensFamily {σ : Type} [Fintype σ] {N : ℕ}
    (C : Fin N → FiniteParityClause σ) (h : ℕ) (old : Set (Poly (ZMod 2) σ)) :
    registrySystem C h old = ensFamilySystem
      (fun c (g : C c) => finiteAffinePolynomial g.val) h old := by
  have ho : registryOld C h = MvPolynomial.rename (Sum.inl : σ → ClauseRegistryVars C h) := by
    rfl
  have he (c : Fin N) : registryFreshEmbedding C h c =
      familyFreshEmbedding (σ := σ) (ι := fun c => C c) (h := h) c := by
    ext z
    cases z <;> rfl
  have hv (c : Fin N) : registryValue C h c = ensFamilyValue
      (fun c (g : C c) => finiteAffinePolynomial g.val) h c := by
    rw [registry_fresh_value, ensFamilyValue, he]
  simp only [registrySystem, ensFamilySystem, registryInput, ho, hv]

 theorem affine_family_exclusion_of_square {κ : Type} [Fintype κ] {ι : κ → Type}
    [∀ b, Fintype (ι b)] (m ℓ M k D : ℕ)
    (hm : 0 < m) (hℓ : 2 ≤ ℓ) (hM : 1 ≤ M) (hkpos : 1 ≤ k) (hk : k ≤ m)
    (hsq : (m:ℝ)*Real.log (4*(M:ℝ)) ≤ (k:ℝ)^2)
    (hD : 2*(3*ℓ)+1 ≤ D) (hpack : 4*(k-1) < 2^ℓ)
    (hB : 2*(k*(D+1))-1 ≤ 2^ℓ)
    (g : ∀ b, ι b → AffineInputMap (Fin m × Fin ℓ))
    (hcount : Nat.card (ProperHighIndex g k) ≤ M) :
    ¬ Derives (ensFamilySystem (fun b i => finiteAffinePolynomial (g b i)) (3*ℓ)
      (compactBitBase m ℓ)) D 1 := by
  intro href
  obtain ⟨f,hf,hne,hw⟩ := common_affine_kernel_of_square m ℓ M k hm (by omega)
    hM hkpos hk hsq g hcount
  have hp := affine_family_removal_with_units
    (fun b i => finiteAffinePolynomial (g b i)) (fun b i => finiteAffinePolynomial_degree (g b i))
    (3*ℓ) k D (by omega) hkpos hD (compactBitBase m ℓ)
    (fun _ h => Or.inl h) f (rowLinearSpace_totalDegree_le hf) hw href
  obtain ⟨_,_,_,_,_,_,hn⟩ := cube_residual_dual_separation_unconditional m ℓ k (k*(D+1)) hℓ hkpos
    (by nlinarith) hpack hB f hf hne
  exact hn hp

 theorem affine_family_exclusion {κ : Type} [Fintype κ] {ι : κ → Type}
    [∀ b, Fintype (ι b)] (m ℓ M D : ℕ)
    (hm : 0 < m) (hℓ : 2 ≤ ℓ) (hM : 1 ≤ M)
    (hk : kernelDegree m M ≤ m) (hD : 2*(3*ℓ)+1 ≤ D)
    (hpack : 4*(kernelDegree m M-1) < 2^ℓ)
    (hB : 2*(kernelDegree m M*(D+1))-1 ≤ 2^ℓ)
    (g : ∀ b, ι b → AffineInputMap (Fin m × Fin ℓ))
    (hcount : Nat.card (ProperBlockIndex g) ≤ M) :
    ¬ Derives (ensFamilySystem (fun b i => finiteAffinePolynomial (g b i)) (3*ℓ)
      (compactBitBase m ℓ)) D 1 :=
  affine_family_exclusion_of_square m ℓ M _ D hm hℓ hM (kernelDegree_pos m M hm hM)
    hk (kernel_ceil_square m M hm hM) hD hpack hB g
    ((proper_high_count_le_proper_count g _).trans hcount)

/-- Polynomial proper-block inventory and any polynomial degree bound in bit length. -/
theorem affine_family_polylog_exclusion (a A d : ℕ) :
    ∀ᶠ ℓ : ℕ in Filter.atTop, ∀ {κ : Type} [Fintype κ] {ι : κ → Type}
      [∀ b, Fintype (ι b)]
      (g : ∀ b, ι b → AffineInputMap (Fin (2^ℓ+1) × Fin ℓ)),
      Nat.card (ProperBlockIndex g) ≤ A*2^(a*ℓ)+1 →
      ∀ D : ℕ, D ≤ A*(ℓ+1)^d →
      ¬ Derives (ensFamilySystem (fun b i => finiteAffinePolynomial (g b i)) (3*ℓ)
        (compactBitBase (2^ℓ+1) ℓ)) D 1 := by
  filter_upwards [eventually_affine_parameters a (A+7) (d+1)] with ℓ hp
  intro κ _ ι _ g hcount D hD href
  obtain ⟨hℓ,hkpos,hk,hsq,hpack,hB⟩ := hp
  have ht : 1 ≤ ℓ+1 := by omega
  have hpow : (ℓ+1)^d ≤ (ℓ+1)^(d+1) := pow_le_pow_right₀ ht (Nat.le_succ d)
  have htbig : ℓ+1 ≤ (ℓ+1)^(d+1) := le_self_pow₀ ht (by omega)
  have hcap : max D (2*(3*ℓ)+1) ≤ (A+7)*(ℓ+1)^(d+1) := by
    apply max_le <;> nlinarith
  have hcount' : Nat.card (ProperHighIndex g (uniformKernel ℓ)) ≤ (A+7)*2^(a*ℓ)+1 :=
    (proper_high_count_le_proper_count g _).trans (hcount.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega : A ≤ A+7)) 1))
  have hB' : 2*(uniformKernel ℓ*(max D (2*(3*ℓ)+1)+1))-1 ≤ 2^ℓ := by
    exact (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right hcap 1))) 1).trans hB
  exact affine_family_exclusion_of_square (2^ℓ+1) ℓ ((A+7)*2^(a*ℓ)+1) (uniformKernel ℓ)
    (max D (2*(3*ℓ)+1)) (by omega) hℓ (by omega) hkpos hk hsq
    (le_max_right _ _) hpack hB' g hcount'
    (href.mono (fun _ h => h) (le_max_left _ _))

theorem bitPHP_exponential : ∀ ℓ ≥ 32, ∀ {S : ℕ}
    (C : Fin S → FiniteParityClause (BitVar (2^ℓ+1) ℓ))
    (_dag : RL.Braun.PDag (usualInitials (2^ℓ+1) ℓ) C)
    (finish : Fin S), C finish = ∅ →
    Real.exp (((2^ℓ:ℕ):ℝ)/(32768*(ℓ:ℝ)^2)) < (S:ℝ) := by
  intro ℓ hℓ S C dag finish hempty
  classical
  by_contra hnot
  let n : ℕ := 2^ℓ
  let x : ℝ := ((n:ℕ):ℝ)/(32768*(ℓ:ℝ)^2)
  have hS : (S:ℝ) ≤ Real.exp x := le_of_not_gt hnot
  have hn1 : 1 ≤ n := Nat.one_le_two_pow
  have hroom : 32768*((2*ℓ+4)*ℓ^2) ≤ n := bitPHP_exponential_room ℓ hℓ
  have hℓℓ : 32*ℓ ≤ ℓ*ℓ := Nat.mul_le_mul_right _ hℓ
  have h64 : 64*ℓ ≤ n := by nlinarith
  -- Real-number bookkeeping.
  have hℓR : (32:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hℓ
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hden : (0:ℝ) < 32768*(ℓ:ℝ)^2 := by positivity
  have hxmul : x*(32768*(ℓ:ℝ)^2) = (n:ℝ) := div_mul_cancel₀ _ hden.ne'
  have hroomR : (32768:ℝ)*((2*(ℓ:ℝ)+4)*(ℓ:ℝ)^2) ≤ (n:ℝ) := by exact_mod_cast hroom
  have hx : 2*(ℓ:ℝ)+4 ≤ x := by
    rw [le_div_iff₀ hden]
    nlinarith
  have hx0 : 0 ≤ x := by linarith
  -- exp x ≥ 16 n².
  have he2 : (2:ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1:ℝ)
    linarith
  have hncast : (n:ℝ) = (2:ℝ)^ℓ := by
    simp only [n]
    push_cast
    ring
  have hexp : 16*(n:ℝ)^2 ≤ Real.exp x := by
    have hmono : Real.exp (((2*ℓ+4:ℕ):ℝ)) ≤ Real.exp x := by
      apply Real.exp_le_exp.mpr
      push_cast
      exact hx
    have hpow : (2:ℝ)^(2*ℓ+4) ≤ Real.exp 1^(2*ℓ+4) :=
      pow_le_pow_left₀ (by norm_num) he2 _
    rw [Real.exp_one_pow] at hpow
    have hring : (2:ℝ)^(2*ℓ+4) = 16*((2:ℝ)^ℓ)^2 := by ring
    rw [hncast, ← hring]
    exact hpow.trans hmono
  -- Inventory.
  let M : ℕ := 3*S + (n+1).choose 2
  have hchoose : (n+1).choose 2 ≤ 4*n^2 := by
    have h := Nat.choose_le_pow (n+1) 2
    nlinarith
  have hM : 1 ≤ M := by
    have h : 0 < (n+1).choose 2 := Nat.choose_pos (by omega)
    omega
  have hMR : (M:ℝ) ≤ 3*Real.exp x + 4*(n:ℝ)^2 := by
    have hc : (((n+1).choose 2:ℕ):ℝ) ≤ 4*(n:ℝ)^2 := by exact_mod_cast hchoose
    simp only [M]
    push_cast
    linarith
  have hMpos : (0:ℝ) < 4*(M:ℝ) := by
    have : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
    linarith
  have h4M : 4*(M:ℝ) ≤ Real.exp (2*x) := by
    rw [two_mul, Real.exp_add]
    have hn2 : (1:ℝ) ≤ (n:ℝ)^2 := one_le_pow₀ hnR
    nlinarith
  have hlog : Real.log (4*(M:ℝ)) ≤ 2*x := (Real.log_le_iff_le_exp hMpos).mpr h4M
  -- The kernel degree k = ⌊n/(32ℓ)⌋.
  let k : ℕ := n/(32*ℓ)
  have hqpos : 0 < 32*ℓ := by omega
  have hkmul : k*(32*ℓ) ≤ n := Nat.div_mul_le_self n (32*ℓ)
  have hkpos : 1 ≤ k := Nat.div_pos (by omega) hqpos
  have hkn : k ≤ n := Nat.div_le_self n (32*ℓ)
  have hklt : n < (k+1)*(32*ℓ) := by
    have h1 := Nat.div_add_mod n (32*ℓ)
    have h2 := Nat.mod_lt n hqpos
    have h3 : (32*ℓ)*(n/(32*ℓ)) = k*(32*ℓ) := Nat.mul_comm _ _
    nlinarith
  have hnk : n ≤ 64*ℓ*k := by nlinarith
  have hnkR : (n:ℝ) ≤ 64*(ℓ:ℝ)*(k:ℝ) := by exact_mod_cast hnk
  have hsq : (((n+1:ℕ):ℝ))*Real.log (4*(M:ℝ)) ≤ (k:ℝ)^2 := by
    have hm : (((n+1:ℕ):ℝ)) ≤ 2*(n:ℝ) := by
      push_cast
      linarith
    have hm0 : (0:ℝ) ≤ ((n+1:ℕ):ℝ) := Nat.cast_nonneg _
    have hstep1 : (((n+1:ℕ):ℝ))*Real.log (4*(M:ℝ)) ≤ (2*(n:ℝ))*(2*x) := by
      calc
        _ ≤ (((n+1:ℕ):ℝ))*(2*x) := mul_le_mul_of_nonneg_left hlog hm0
        _ ≤ (2*(n:ℝ))*(2*x) := mul_le_mul_of_nonneg_right hm (by linarith)
    have hsqr := mul_self_le_mul_self (by linarith : (0:ℝ) ≤ (n:ℝ)) hnkR
    have hfin : (2*(n:ℝ))*(2*x) ≤ (k:ℝ)^2 := by
      have hscaled : ((2*(n:ℝ))*(2*x))*(32768*(ℓ:ℝ)^2) ≤ (k:ℝ)^2*(32768*(ℓ:ℝ)^2) := by
        have : ((2*(n:ℝ))*(2*x))*(32768*(ℓ:ℝ)^2) = 4*(n:ℝ)*(n:ℝ) := by
          rw [← hxmul]
          ring
        rw [this]
        nlinarith [sq_nonneg ((ℓ:ℝ)*(k:ℝ))]
      exact le_of_mul_le_mul_right hscaled hden
    exact hstep1.trans hfin
  have hℓk : k ≤ ℓ*k := Nat.le_mul_of_pos_left _ (by omega)
  have hpack : 4*(k-1) < n := by
    have : 32*k ≤ n := by nlinarith
    omega
  have hB : 2*(k*((12*ℓ+1)+1))-1 ≤ n := by
    have : 2*(k*((12*ℓ+1)+1)) ≤ n := by nlinarith
    omega
  -- Transfer and exclusion.
  obtain ⟨N,R,hN,_,_,_,hpc⟩ := usual_bitPHP_PC_transfer_of_pdag C dag finish hempty (3*ℓ) (by omega)
  let g : ∀ b : Fin N, {f // f ∈ R b} → AffineInputMap (BitVar (2^ℓ+1) ℓ) :=
    fun _ i => i.val
  have hcount : Nat.card (ProperHighIndex g k) ≤ M := by
    apply le_trans ((proper_high_count_le_proper_count g k).trans ?_) hN
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card (ProperBlockIndex g) ≤ Fintype.card (Fin N) := Fintype.card_subtype_le _
      _ = N := Fintype.card_fin _
  have hdegree : max (2*(3*ℓ)+ℓ) (4*(3*ℓ)+1) = 12*ℓ+1 := by omega
  rw [hdegree,registry_system_eq_ensFamily] at hpc
  exact affine_family_exclusion_of_square (2^ℓ+1) ℓ M k (12*ℓ+1) (by omega) (by omega) hM
    hkpos (by omega) hsq (by omega) hpack hB g hcount hpc


/-- The same bound with base two, since `2 ≤ e`. -/
theorem bitPHP_exponential_base_two : ∀ ℓ ≥ 32, ∀ {S : ℕ}
    (C : Fin S → FiniteParityClause (BitVar (2^ℓ+1) ℓ))
    (_dag : RL.Braun.PDag (usualInitials (2^ℓ+1) ℓ) C)
    (finish : Fin S), C finish = ∅ →
    (2:ℝ)^(((2^ℓ:ℕ):ℝ)/(32768*(ℓ:ℝ)^2)) < (S:ℝ) := by
  intro ℓ hℓ S C dag finish hempty
  refine lt_of_le_of_lt ?_ (bitPHP_exponential ℓ hℓ C dag finish hempty)
  have hy : (0:ℝ) ≤ ((2^ℓ:ℕ):ℝ)/(32768*(ℓ:ℝ)^2) := by positivity
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Braun's `bitPHP_superpolynomial`. -/
 theorem bitPHP_superpolynomial (K : ℝ) (_hK : 0 < K) :
    ∃ L : ℕ, ∀ ℓ ≥ L, ∀ {S : ℕ}
      (C : Fin S → FiniteParityClause (BitVar (2^ℓ+1) ℓ))
      (_dag : RL.Braun.PDag (usualInitials (2^ℓ+1) ℓ) C)
      (finish : Fin S), C finish = ∅ → ((2^ℓ:ℕ):ℝ)^K < (S:ℝ) := by
  classical
  let a := max (⌈K⌉₊) 2
  have ha : 2 ≤ a := le_max_right _ _
  have hKa : K ≤ (a:ℝ) := (Nat.le_ceil K).trans (by exact_mod_cast (le_max_left (⌈K⌉₊) 2))
  obtain ⟨L,hL⟩ := eventually_atTop.mp
    ((affine_family_polylog_exclusion a 13 1).and (eventually_ge_atTop 2))
  refine ⟨L,?_⟩
  intro ℓ hℓL S C dag finish hempty
  obtain ⟨hex,hℓ⟩ := hL ℓ hℓL
  by_contra hnot
  have hSreal : (S:ℝ) ≤ ((2^ℓ:ℕ):ℝ)^K := le_of_not_gt hnot
  let n : ℕ := 2^ℓ
  have hn : 1 ≤ n := one_le_pow₀ (by decide)
  have hS : S ≤ n^a := by
    have h := hSreal.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hKa)
    rw [Real.rpow_natCast] at h
    exact_mod_cast h
  obtain ⟨N,R,hN,_,_,_,hpc⟩ := usual_bitPHP_PC_transfer_of_pdag C dag finish hempty (3*ℓ) (by omega)
  have hchoose := Nat.choose_le_pow (n+1) 2
  have hquad : (n+1)^2 ≤ 4*n^2 := by nlinarith
  have hpow : n^2 ≤ n^a := pow_le_pow_right₀ hn ha
  have hN' : N ≤ 13*2^(a*ℓ)+1 := by
    have hb : N ≤ 13*n^a+1 := by nlinarith
    simpa only [n,← pow_mul,Nat.mul_comm] using hb
  let g : ∀ b : Fin N, {f // f ∈ R b} → AffineInputMap (BitVar (2^ℓ+1) ℓ) :=
    fun _ i => i.val
  have hcount : Nat.card (ProperBlockIndex g) ≤ 13*2^(a*ℓ)+1 := by
    apply le_trans ?_ hN'
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card (ProperBlockIndex g) ≤ Fintype.card (Fin N) := Fintype.card_subtype_le _
      _ = N := Fintype.card_fin _
  have hdegree : max (2*(3*ℓ)+ℓ) (4*(3*ℓ)+1) = 12*ℓ+1 := by omega
  rw [hdegree,registry_system_eq_ensFamily] at hpc
  exact hex g hcount (12*ℓ+1) (by simp only [pow_one]; omega) hpc

end

end SATurday.ProofComplexity.BraunPC

namespace SATurday.ProofComplexity.RL.Braun

open Classical

/-- Braun's theorem, as stated in `BraunDag` (`BraunBitPHP`), is proved: for every `K > 0` and large
`l`, every affine dag refutation of the usual bit PHP CNF with `2^l + 1` pigeons and `l` bits has more
than `(2^l)^K` nodes. Credit: K. Braun (arXiv 2609.23015), `bitPHP_superpolynomial`. -/
theorem braunBitPHP : BraunBitPHP := by
  intro K hK
  obtain ⟨L, hL⟩ := BraunPC.bitPHP_superpolynomial K hK
  exact ⟨L, fun l hl S C hd f hf => hL l hl C hd f hf⟩

/-- Unconditional super polynomial lower bound for dag like `Res(⊕)` (`RL.DagRefutes`) on the bit PHP
CNF with `2^l` holes and `2^l + 1` pigeons. -/
theorem bphp_dag_superpolynomial (K : ℝ) (hK : 0 < K) :
    ∃ L : ℕ, ∀ l ≥ L, ∀ s : ℕ, DagRefutes (↑(bphpCNF l (2 ^ l + 1)) : Set Clause) s →
      ((2 ^ l : ℕ) : ℝ) ^ K < (s : ℝ) :=
  braun_implies_dag_lb braunBitPHP K hK

/-- Exponential form (`bitPHP_exponential`): for `l >= 32`, any `s` line dag like `Res(⊕)` refutation of
the bit PHP CNF with `2^l + 1` pigeons has `exp (2^l / (32768 l^2)) < s`. -/
theorem bphp_dag_exponential (l : ℕ) (hl : 32 ≤ l) (s : ℕ)
    (hs : DagRefutes (↑(bphpCNF l (2 ^ l + 1)) : Set Clause) s) :
    Real.exp (((2 ^ l : ℕ) : ℝ) / (32768 * (l : ℝ) ^ 2)) < (s : ℝ) := by
  obtain ⟨S, C, hS, hd, f, hf⟩ := bphp_dag_to_pdag l (2 ^ l + 1) s hs
  exact (BraunPC.bitPHP_exponential l hl C hd f hf).trans_le (by exact_mod_cast hS)

end SATurday.ProofComplexity.RL.Braun
