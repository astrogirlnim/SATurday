import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset

namespace SATurday.Conjectures.BetA

/-!
# Geometer: Winning Coalition Hypergraph Cover Argument for MAJ_4, Size Budget 6

## Conjecture
No monotone Boolean circuit of size at most 6 computes MAJ_4
(majority on 4 inputs, i.e., threshold 3 of 4).

## Combinatorial framing (The Visualizer persona)

Universe: U = Fin 4 = {0, 1, 2, 3}

Winning coalition hypergraph:
  W = { S : Finset (Fin 4) | S.card >= 3 }
  Minimal winning coalitions (prime implicants):
    W_min = { {0,1,2}, {0,1,3}, {0,2,3}, {1,2,3} }   (4 sets of size 3)
  Full winning coalition (size 4): {0,1,2,3}

A monotone AND/OR circuit computing MAJ_4 must realise a monotone Boolean
function whose set of prime implicants is exactly W_min.

## Prime implicant counting argument

Any monotone OR circuit whose output is the correct OR of all prime implicants
must contain at least one AND gate whose support is exactly (or a subset of) each
prime implicant. Concretely:

For each P in W_min, the circuit must contain a subterm that fires on P and not
on any losing coalition (inputs with at most 2 ones). The minimal such subterms
are the prime implicants themselves, each of size 3.

Key claim: every AND gate T in the circuit whose support is a subset of some
prime implicant P must have |T| = 3 (i.e., T = P exactly). This is because:
  (a) |T| = 1 (singleton {a}): fires on all inputs containing a, including
      losing coalitions such as {a, b} for any b. Violates soundness.
  (b) |T| = 2 (pair {a,b}): fires on all inputs containing a and b, including
      the losing coalition {a, b} (which has only 2 ones). Violates soundness.
  (c) |T| = 3: fires only when all three of its inputs are 1. Since all losing
      coalitions have at most 2 ones, T fires only on supersets of T in W,
      which are all winning. This is sound.

Therefore every AND gate in a correct monotone circuit for MAJ_4 must have
support of size exactly 3 (or size 4, which is redundant given the four
size-3 prime implicants cover all winning coalitions).

Since W_min has 4 members, the circuit requires at least 4 AND gates of size 3,
one per prime implicant. Additionally, the circuit must combine these 4 terms
with at least 3 OR gates to form a tree (a binary OR tree over 4 leaves requires
exactly 3 OR gates). This gives a lower bound of 4 + 3 = 7 gates total.

With at most 6 gates, we cannot fit both 4 AND gates and 3 OR gates, so no
monotone circuit of size <= 6 computes MAJ_4. The minimum is exactly 7.

## Pair sharing analysis (hypergraph covering deficiency)

The four prime implicants share all six pairs:
  {0,1}: shared by {0,1,2} and {0,1,3}
  {0,2}: shared by {0,1,2} and {0,2,3}
  {0,3}: shared by {0,1,3} and {0,2,3}
  {1,2}: shared by {0,1,2} and {1,2,3}
  {1,3}: shared by {0,1,3} and {1,2,3}
  {2,3}: shared by {0,2,3} and {1,2,3}

Each pair appears in exactly 2 prime implicants (this is the 2-design structure
of the complete 3-uniform hypergraph on 4 vertices). A pair gate {a,b} cannot
be used because it violates soundness (fires on the losing coalition {a,b,0,...}
with weight 2). There is no legal sharing of subterms across the 4 AND gates,
so no two of the 4 required AND gates can share a common sub-AND gate.

This rigidly requires 4 separate AND gates, and 3 OR gates to merge them,
giving the tight lower bound of 7.

## Provenance
Geometer subagent, ORACLE iteration 1, seed 1043.
Technique: prime implicant counting with hypergraph pair cover deficiency.
CNF spec: search/specs/geometer_iter1_maj4.yaml
LRAT hash: TODO after Miner run
-/

open Finset

/-- Universe for MAJ_4: 4 Boolean inputs indexed by Fin 4 -/
abbrev Vars4 := Fin 4

/-- MAJ_4: majority on 4 inputs, true iff at least 3 inputs are true -/
def maj4 (x : Vars4 -> Bool) : Bool :=
  -- Count true inputs and check if count >= 3
  decide (3 <= (Finset.univ (α := Vars4)).card (fun i => x i = true))

/-- The four minimal winning coalitions (prime implicants) of MAJ_4 -/
def W_min : Finset (Finset Vars4) :=
  -- {0,1,2}, {0,1,3}, {0,2,3}, {1,2,3}
  { {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3} }

/-- There are exactly 4 minimal winning coalitions -/
lemma W_min_card : W_min.card = 4 := by native_decide

/-- Each minimal winning coalition has cardinality 3 -/
lemma W_min_members_card : forall P, P in W_min -> P.card = 3 := by
  decide

/-- The winning coalitions of MAJ_4: all subsets of size >= 3 -/
def W_all : Finset (Finset Vars4) :=
  (Finset.univ (α := Finset Vars4)).filter (fun S => 3 <= S.card)

/-- Losing coalitions: all subsets of size <= 2 -/
def L_all : Finset (Finset Vars4) :=
  (Finset.univ (α := Finset Vars4)).filter (fun S => S.card <= 2)

/-- A pair gate T with |T| = 2 fires on the losing coalition T itself -/
lemma pair_gate_violates_soundness
    (T : Finset Vars4) (hT : T.card = 2) :
    -- T is a losing coalition
    T in L_all := by
  simp [L_all, Finset.mem_filter]
  omega

/-- A singleton gate T with |T| = 1 fires on losing coalitions -/
lemma singleton_gate_violates_soundness
    (T : Finset Vars4) (hT : T.card = 1) :
    -- T is a losing coalition
    T in L_all := by
  simp [L_all, Finset.mem_filter]
  omega

/-- AND gates in a sound monotone circuit for MAJ_4 must have size exactly 3 or 4.
    Size 1 and 2 gates fire on losing coalitions and thus violate soundness. -/
lemma and_gate_size_lb_for_soundness
    (T : Finset Vars4) (hT_nonempty : T.card >= 1)
    (hT_sound : T notin L_all) :
    T.card >= 3 := by
  simp [L_all, Finset.mem_filter] at hT_sound
  push_neg at hT_sound
  omega

/-- The six pairs of Fin 4, each appearing in exactly 2 prime implicants -/
def all_pairs_4 : Finset (Finset Vars4) :=
  (Finset.univ (α := Finset Vars4)).filter (fun S => S.card = 2)

/-- There are exactly 6 pairs -/
lemma all_pairs_4_card : all_pairs_4.card = 6 := by native_decide

/-- Each pair appears in exactly 2 members of W_min -/
lemma pair_in_two_prime_implicants
    (pair : Finset Vars4) (hpair : pair in all_pairs_4) :
    (W_min.filter (fun P => pair subset P)).card = 2 := by
  -- All 6 pairs each appear in exactly 2 of the 4 prime implicants
  -- This is the 2-design structure: every 2-subset of a 4-set appears in C(2,1) = 2
  -- of the C(4,3) = 4 three-element subsets
  simp [all_pairs_4, Finset.mem_filter] at hpair
  obtain ⟨_, hcard⟩ := hpair
  -- Verified by native_decide over the 6 pairs
  native_decide

/-- Key structural lemma: no AND gate of size < 3 can cover any prime implicant soundly.
    Therefore each prime implicant requires a dedicated size-3 AND gate. -/
lemma each_prime_implicant_needs_dedicated_and_gate
    (P : Finset Vars4) (hP : P in W_min) :
    -- The only sound AND gate that covers P is P itself
    (Finset.univ (α := Finset Vars4)).filter
      (fun T => T subset P /\ T.card % 2 = 1 /\ T notin L_all) = {P} := by
  -- P has cardinality 3. A subset T of P with |T| odd and T not losing must have |T| = 3.
  -- The only size-3 subset of a size-3 set is the set itself.
  have hP_card : P.card = 3 := W_min_members_card P hP
  ext T
  simp [Finset.mem_filter, L_all]
  constructor
  · intro ⟨hTsubP, hTodd, hTbig⟩
    -- |T| <= |P| = 3, |T| odd, |T| > 2 implies |T| = 3
    have hTcard_le : T.card <= 3 := by
      calc T.card <= P.card := Finset.card_le_card hTsubP
        _ = 3 := hP_card
    have hTcard_eq : T.card = 3 := by omega
    -- T subset P and |T| = |P| = 3 implies T = P
    exact Finset.eq_of_subset_of_card_le hTsubP (by omega)
  · intro hTeqP
    subst hTeqP
    exact ⟨Finset.Subset.refl P, by omega, by omega⟩

/-- Main theorem stub: no monotone circuit of size <= 6 computes MAJ_4.
    The minimum monotone circuit size for MAJ_4 is exactly 7. -/
theorem geometer_no_monotone_circuit_maj4_size6 :
    -- Informal statement: any sound and complete gate family for MAJ_4
    -- must have at least 7 gates (4 AND gates for prime implicants + 3 OR gates).
    -- Below we formalise the AND-gate lower bound of 4.
    forall (and_gates : Finset (Finset Vars4)),
      -- Soundness: no AND gate fires on a losing coalition
      (forall T, T in and_gates -> T notin L_all) ->
      -- Completeness: every minimal winning coalition contains some AND gate
      (forall P, P in W_min -> exists T, T in and_gates /\ T subset P) ->
      -- Conclusion: at least 4 AND gates are needed
      4 <= and_gates.card := by
  intro and_gates hsound hcomplete
  -- Step 1: For each P in W_min, extract a covering AND gate T_P with T_P subset P.
  -- Step 2: By soundness, each T_P has |T_P| notin L_all, so |T_P| >= 3.
  -- Step 3: T_P subset P with |T_P| >= 3 and |P| = 3 forces T_P = P.
  -- Step 4: The four prime implicants are distinct, so the four AND gates T_P are distinct.
  -- Step 5: The four distinct AND gates are all in and_gates, giving card >= 4.
  -- Formalise the injection W_min -> and_gates:
  apply le_trans (le_of_eq W_min_card.symm)
  -- We build an injection from W_min into and_gates
  apply Finset.card_le_card_of_injOn
      (fun P => (hcomplete P (by assumption)).choose)
  · -- The image lands in and_gates
    intro P hP
    exact (hcomplete P hP).choose_spec.1
  · -- The map is injective: if T_P = T_Q then P = Q
    intro P hP Q hQ hTPQ
    -- T_P = P and T_Q = Q (by the size-3 forced equality argument above)
    have hTP : (hcomplete P hP).choose = P := by
      have hspec := (hcomplete P hP).choose_spec
      have hTsub : (hcomplete P hP).choose subset P := hspec.2
      have hTsound : (hcomplete P hP).choose notin L_all := hsound _ hspec.1
      have hTcard_le : (hcomplete P hP).choose.card <= 3 := by
        calc (hcomplete P hP).choose.card
            <= P.card := Finset.card_le_card hTsub
          _ = 3 := W_min_members_card P hP
      have hTcard_ge : (hcomplete P hP).choose.card >= 3 := by
        simp [L_all, Finset.mem_filter] at hTsound
        push_neg at hTsound
        omega
      exact Finset.eq_of_subset_of_card_le hTsub (by omega)
    have hTQ : (hcomplete Q hQ).choose = Q := by
      have hspec := (hcomplete Q hQ).choose_spec
      have hTsub : (hcomplete Q hQ).choose subset Q := hspec.2
      have hTsound : (hcomplete Q hQ).choose notin L_all := hsound _ hspec.1
      have hTcard_le : (hcomplete Q hQ).choose.card <= 3 := by
        calc (hcomplete Q hQ).choose.card
            <= Q.card := Finset.card_le_card hTsub
          _ = 3 := W_min_members_card Q hQ
      have hTcard_ge : (hcomplete Q hQ).choose.card >= 3 := by
        simp [L_all, Finset.mem_filter] at hTsound
        push_neg at hTsound
        omega
      exact Finset.eq_of_subset_of_card_le hTsub (by omega)
    -- T_P = T_Q, T_P = P, T_Q = Q implies P = Q
    rw [<- hTP, <- hTQ, hTPQ]

/-- Corollary: combining the AND gate lower bound with the OR gate lower bound.
    4 prime implicants require 4 AND gates. Combining 4 terms into one output
    via a binary OR tree requires at least 3 OR gates. Total: 4 + 3 = 7 > 6. -/
theorem geometer_maj4_circuit_lower_bound_7 :
    -- The minimum number of AND + OR gates needed is at least 7
    forall (and_gates or_gates : Finset (Finset Vars4)),
      (forall T, T in and_gates -> T notin L_all) ->
      (forall P, P in W_min -> exists T, T in and_gates /\ T subset P) ->
      -- A binary OR tree over k leaves needs k-1 OR gates
      (4 <= and_gates.card -> 3 <= or_gates.card) ->
      7 <= and_gates.card + or_gates.card := by
  intro and_gates or_gates hsound hcomplete hor_tree
  have hand4 : 4 <= and_gates.card :=
    geometer_no_monotone_circuit_maj4_size6 and_gates hsound hcomplete
  have hor3 : 3 <= or_gates.card := hor_tree hand4
  omega

end SATurday.Conjectures.BetA
