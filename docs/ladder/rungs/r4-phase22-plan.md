# R4 Phase 2.2 plan: tree-like Res(lin F_p) lower bound for Tseitin mod q

Status: active, uncertified. Branch r4/prover-phase22.

## Statement from the paper

F. Part, I. Tzameret, "Resolution with Counting: Dag-Like Lower Bounds and Different Moduli",
ITCS 2020 (LIPIcs 151, 19:1-19:37); Computational Complexity 30(1), 2021; arXiv 1806.09383 v2.
Checked 2026-10-13 against the arXiv v2 text (Sections 2.3.2 and 7), not the journal version.

- Corollary 46 (Tseitin mod p lower bounds): for every prime p there is d0(p) such that if
  d >= d0, G is a d-regular Ramanujan graph on n vertices (with an orientation) and F is a finite
  field with char(F) != p, then for every sigma with the Tseitin mod p formula unsatisfiable, every
  tree-like Res(lin F) refutation has size 2^{Omega(dn)}.
- Proof in the paper: Theorem 45 (Res(lin F) refutation of width w gives a PC_F refutation of
  degree w), Theorem 44 (tree-like size-width: w0(phi |- bot) <= log2 S + w0(phi) + 2, with w0 the
  principal width where parallel hyperplanes count once, so w <= |F| w0), and the PC_F degree
  Omega(dn) of Alekhnovich-Razborov 2001 (Cor. 4.5) for Boolean edge variables.

Differences to flag (mark as such in any statement):
1. The paper's formula uses one Boolean variable per directed edge and equations mod p. Our
   certified PC bound (`tseitin_bool_degree_Fp`, Buss-Grigoriev-Impagliazzo-Pitassi style) is for
   the one hot encoding `tcnf G q b` on cubic MGG expanders, field ZMod p with p not dividing q.
   So the target is the one hot variant, NOT the paper's exact formula; the Alekhnovich-Razborov
   non binomial degree bound is not in the repo. Result: size 2^{Omega(n)} for cubic expanders,
   not 2^{Omega(dn)}.
2. Gap in the paper's Case 4 of Theorem 45 as read here: when the resolvent equation already
   occurs among the side disjuncts the product a(C)a(D)f3 is not what is derived and the degree
   count fails. Our formalization uses a variant rule with side condition (resolvent not already in
   the side clauses), and degree w+1 instead of w (the +1 is harmless). Unverified whether the
   variant is as strong as the paper's system.
3. Only finite fields ZMod p are needed for the application.

## Dependency map

- PolyCalc.lean: `PCD`, `PCD₀`, closure (`pcd₀_mul`), `cnfAx`, `clausePoly`.
- TseitinBool.lean: `tcnf`, `tseitin_bool_degree_Fp` (no PC degree d refutation of tcnf over ZMod p).
- ResLin.lean: tree-like Res(xor) for F_2 only (ZMod 2, parity decision trees); not reusable for
  F_p except as a template for the inductive derivation type. Dag-like foundations (ResLinDag,
  ResLinGame) are F_2-only and not used.
- TseitinSize.lean: PC size bound; not needed.

## Layers and estimates

- L1 `ResLinF.lean` (~250 lines): Res(lin F) over a field F: equations `(c : N->0 F, a)`, linear
  clauses, tree-like derivations `RLD` indexed by width and size, rules axiom, Boolean axiom,
  weakening, resolution-combination with scalars, simplification; soundness.
- L2 `ResLinFPC.lean` (~300 lines): Theorem 45: `RLD` of width w gives `PCD` of degree w+1 for the
  arithmetization; CNF specialisation `rld_refutation_pc`.
- L3 `ResLinFWidth.lean` (~2000-3000 lines, the hard layer): Theorem 44, size-width for tree-like
  Res(lin F) over finite F: substitution x <- l inside linear clauses and derivations, narrow
  derivations of f=0 from the clauses f != A (Prop 12/14), principal width. May be better done
  directly as: tree-like size s refutation of linear clauses phi gives a PC refutation of degree
  O(|F| (log s + width phi)), avoiding the width-bounded Res(lin) intermediate.
- L4 `ResLinTseitin.lean` (~200 lines): assembly: width of `tcnf` clauses is <= max(q,3);
  combine L2, L3 and `tseitin_bool_degree_Fp` to get `2^{Omega(n)}` for tree-like Res(lin F_p)
  refutations of `tcnf G q b` on the MGG cubic expanders, p prime, p not dividing q.

## Feasibility call

L1, L2 and L4 are routine and finishable in the next session or two. L3 is the real work: an
induction on the number of variables with variable-to-linear-form substitution and width control,
with several sub-lemmas the paper only sketches (Prop 12, 14). I estimate several sessions and
real risk of the width bookkeeping (principal width, finite-field bound |F|) taking longer; the
statement is believable and the route is sound, so I rate completion likely but not quick.
The dag-like case is not covered (the paper proves tree-like only for finite fields).

## Progress log (append-only)

