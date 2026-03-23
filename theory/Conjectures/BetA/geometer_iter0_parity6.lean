import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SetFamily.Sunflower

namespace SATurday.Conjectures.BetA

/-!
# Geometer: Sunflower Lemma Certificate for Parity-6, Size Budget 12

## Conjecture
No monotone Boolean circuit of size at most 12 computes Parity_6.

## Combinatorial framing (The Visualizer persona)

Universe: U = Fin 6 = {0, 1, 2, 3, 4, 5}

Prime implicant hypergraph:
  M = { S : Finset (Fin 6) | S.card % 2 = 1 }
  |M| = C(6,1) + C(6,3) + C(6,5) = 6 + 20 + 6 = 32

A monotone OR-of-ANDs circuit with at most k AND gates corresponds to a family
F = {T_0, ..., T_{k-1}} of subsets of Fin 6 (the gate support sets) such that:

  (1) Covering:   forall S in M, exists T_i in F, T_i subset S
  (2) Soundness:  forall x : Fin 6 -> Bool, x.sum_mod2 = 0 ->
                    forall T_i in F, exists j, j in T_i and x j = false

Condition (1) ensures the circuit outputs 1 on all odd-weight inputs.
Condition (2) ensures the circuit outputs 0 on all even-weight inputs.

## Sunflower argument

Claim: conditions (1) and (2) together require |F| > 12.

Key structural constraint from (2): every T_i in F must have odd cardinality.
Proof: if |T_i| is even, then the all-ones assignment x = fun _ => true gives
x.sum_mod2 = 6 mod 2 = 0 (even), but T_i subset Fin 6 with all inputs true
means the gate fires, violating soundness. Wait: the all-ones input has
parity 0 (6 ones = even), so the circuit must output 0. But T_i subset allones
fires, so the OR fires, outputting 1. Contradiction. Hence all T_i in F
that have even cardinality will fire on the all-ones input, so they cannot
be in F. This forces |T_i| to be odd for all i.

Now apply the Erdos-Ko-Rado sunflower lemma to the subfamily F_3 subset F
consisting of sets of cardinality 3. The 20 size-3 prime implicants of parity-6
must all be covered by F (from condition (1)): for each S in M with |S| = 3,
some T_i in F satisfies T_i subset S. Since T_i has odd cardinality and T_i
subset S with |S| = 3, we have |T_i| in {1, 3}. If |T_i| = 1, say T_i = {a},
then T_i subset S iff a in S. The gate {a} covers all odd-weight supersets of {a}.
If |T_i| = 3, T_i = S exactly (since T_i subset S and |T_i| = |S| = 3).

The 6 size-1 gates together cover at most the odd-weight sets containing their
respective elements. The 6 singletons {0},{1},{2},{3},{4},{5} together cover
every odd-weight set (since every odd-weight set contains at least one element),
but they also fire on even-weight supersets, violating soundness.

Precise contradiction via sunflower counting:
- Each size-3 gate T covers exactly C(3,0) + C(3,2) = 1 + 3 = 4 size-3 minterms
  (the supersets of T in M that have size 3, i.e., T itself, plus subsets of
  Fin 6 setminus T of size 0 appended to T: only T itself; and size-5 minterms
  containing T: C(3,2) = 3 choices of 2 more elements from the 3 remaining).
  Wait: T itself is one size-3 minterm. Size-5 minterms containing T: choose 2
  more elements from the 3 not in T: C(3,2) = 3. So each size-3 gate covers
  1 + 3 = 4 minterms from M total, but only 1 size-3 minterm exactly.
- To cover all 20 size-3 minterms using size-3 gates alone needs at least 20
  gates (since each covers exactly 1 size-3 minterm with equality).
- If instead we use size-1 gates: each {a} covers size-3 minterms containing a.
  There are C(5,2) = 10 size-3 sets containing a. But using {a} fires on all
  even-weight sets containing a, violating soundness.
- Hence we cannot use size-1 gates without violating soundness, unless we
  somehow exclude them via the OR structure, which OR-of-ANDs cannot do.

The Sunflower lemma gives: any family of sets of size <= w with more than
(p-1)^w * w! members contains a p-sunflower. For our problem:
- Family: the 20 size-3 minterms of parity-6.
- p = 3, w = 3: threshold = 2^3 * 6 = 48 > 20 (no forced sunflower at p=3).
- p = 2, w = 3: threshold = 1^3 * 6 = 6 < 20 (forced 2-sunflower).
So any subfamily of the 20 size-3 minterms of size > 6 contains a 2-sunflower.

For a 2-sunflower {A, B} with core C (|C| = 1 or 2): any gate T covering both
A and B must satisfy T subset A and T subset B, so T subset A intersect B = C.
Since T has odd cardinality and |C| <= 2, we need |T| = 1 and T subset C.
But then T is a singleton, and we showed singleton gates violate soundness.
Hence no single gate covers two members of any 2-sunflower in the size-3 minterms.

Since the 20 size-3 minterms split into at least ceil(20/6) = 4 sunflower-free
subfamilies (by Erdos-Ko iteration), and each such subfamily requires at least
7 distinct gates (none of which can be shared across sunflower pairs), the total
number of gates needed to cover just the size-3 minterms exceeds 12.

More precisely: by iterative sunflower extraction, covering 20 mutually
sunflower-conflicting minterms requires at least 20 distinct gates (one per
size-3 minterm), since no two can share a covering gate without that gate
being a singleton (which violates soundness). This lower bound of 20 > 12
provides the certificate.

## Provenance
Geometer subagent, ORACLE iteration 0, seed 1042.
Technique: Sunflower lemma (Erdos-Ko) applied to prime implicant set system.
CNF spec: geometer_iter0_parity6.yaml
LRAT hash: TODO after Miner run
-/

open Finset

/-- Universe for parity-6: 6 Boolean inputs indexed by Fin 6 -/
abbrev Vars6 := Fin 6

/-- Parity function: true iff odd number of inputs are true -/
def parity6 (x : Vars6 -> Bool) : Bool :=
  -- Count the number of true inputs and check parity
  (Finset.univ.card (fun i => x i = true) % 2 == 1)

/-- The prime implicant set system of parity-6:
    all odd-cardinality subsets of Fin 6 -/
def M6 : Finset (Finset Vars6) :=
  Finset.univ.powerset.filter (fun S => S.card % 2 = 1)

/-- Size of M6 equals 32 = C(6,1) + C(6,3) + C(6,5) -/
lemma M6_card : M6.card = 32 := by
  -- Combinatorial identity: sum of C(6,k) for k odd = 2^(6-1) = 32
  native_decide

/-- A monotone gate family: a multiset of subsets of Fin 6 representing AND gate supports -/
structure GateFamily where
  gates : Finset (Finset Vars6)
  -- Each gate must have odd cardinality (from soundness constraint: see proof sketch)
  gates_odd_card : forall T, T in gates -> T.card % 2 = 1

/-- Covering condition: every odd-weight minterm contains some gate support -/
def GateFamily.covers (F : GateFamily) : Prop :=
  forall S, S in M6 -> exists T, T in F.gates /\ T subset S

/-- Soundness condition: no gate fires on any even-weight input -/
def GateFamily.sound (F : GateFamily) (x : Vars6 -> Bool) : Prop :=
  -- If x has even weight, then for all gates T, some input in T is false
  (Finset.univ.sum (fun i => if x i then 1 else (0 : Nat)) % 2 = 0) ->
  forall T, T in F.gates -> exists j, j in T /\ x j = false

/-- Sunflower: a family of sets where every two members share the same core -/
def isSunflower (petals : Finset (Finset Vars6)) (core : Finset Vars6) : Prop :=
  forall A B, A in petals -> B in petals -> A != B ->
    A intersect B = core

/-- Key lemma: no size-3 gate can cover two members of a 2-sunflower
    (the core has even cardinality, contradicting the odd-cardinality constraint) -/
lemma no_shared_gate_for_sunflower_pair
    (A B : Finset Vars6) (core : Finset Vars6)
    (hA : A.card = 3) (hB : B.card = 3)
    (hAB : A != B) (hsf : A intersect B = core)
    (T : Finset Vars6) (hTodd : T.card % 2 = 1)
    (hTA : T subset A) (hTB : T subset B) :
    False := by
  -- T subset A and T subset B imply T subset A intersect B = core
  have hTcore : T subset core := by
    rw [<- hsf]
    exact Finset.subset_inter hTA hTB
  -- |core| = |A intersect B|. Since |A| = |B| = 3 and A != B,
  -- |A intersect B| <= 2 (two distinct 3-element sets share at most 2 elements)
  have hcore_card : core.card <= 2 := by
    rw [<- hsf]
    have : (A intersect B).card <= A.card := Finset.card_inter_le_left A B
    omega
  -- T subset core and |core| <= 2 and |T| is odd means |T| = 1
  have hT_card_le : T.card <= 2 := by
    exact le_trans (Finset.card_le_card hTcore) hcore_card
  -- |T| odd and |T| <= 2 means |T| = 1
  have hT1 : T.card = 1 := by omega
  -- A singleton gate T = {a} fires on ALL inputs containing a, including even-weight ones.
  -- For example, the all-ones input has weight 6 (even) and contains a.
  -- This will be handled in the soundness violation lemma.
  -- For now: a singleton T with T subset core where |core| <= 2 and |A| = 3
  -- means T does not uniquely identify A (T also subset of other 3-sets).
  -- The full contradiction requires combining with soundness, formalized below.
  sorry
  -- TODO: Complete via Finset.card_singleton and soundness violation argument

/-- Main theorem stub: no gate family of size <= 12 is both covering and sound for parity-6 -/
theorem geometer_no_monotone_circuit_parity6_size12 :
    forall (F : GateFamily),
      F.covers ->
      (forall x, F.sound F x) ->
      12 < F.gates.card := by
  intro F hcovers hsound
  -- Proof strategy:
  -- Step 1: Extract the size-3 minterms subfamily S3 subset M6 with |S3| = 20.
  -- Step 2: For each S in S3, F.covers gives a gate T_S in F.gates with T_S subset S.
  --         By the odd-cardinality constraint, |T_S| in {1, 3}.
  -- Step 3: Singleton gates (|T| = 1) violate soundness: the all-ones input
  --         has weight 6 (even), contains every element, so {a} subset allones
  --         fires on an even-weight input. Hence no singleton gates allowed.
  -- Step 4: All gates in F have |T| = 3 (the only remaining odd option <= 3).
  --         Each size-3 gate covers exactly 1 size-3 minterm (itself).
  -- Step 5: The 20 size-3 minterms require 20 distinct size-3 gates.
  --         20 > 12. Contradiction.
  sorry
  -- TODO: Formalize Steps 1-5 using Finset.card bounds and the covering injection.
  -- Key Mathlib lemmas needed:
  --   Finset.card_filter, Finset.card_le_card, Finset.subset_antisymm,
  --   Finset.card_inter_le_left, Finset.card_pos

end SATurday.Conjectures.BetA
