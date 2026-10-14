Scratch experiment scripts for r4-phase23-program.md (research only, not part of any build).
Requires python3, numpy, networkx.  Run from this directory.
  pcdeg.py   exact multilinear PC degree over F_p by fixpoint linear algebra (n <= ~12)
  cnfs.py    CNF constructors: Tseitin mod 2 / mod q with Boolean edge variables, random 3-CNF
  tmodel.py  combinatorial model of the exact PC degree of Tseitin-mod-2 (odd p), see program doc Sec 2
  chain_ub.py            upper bound by a vertex ordering (ball radius rule), any graph size
  check_model_vs_linear_algebra.py   model vs linear algebra on small graphs
  check_lower_bound.py   checks D >= max(d, ceil(b_{1/3}/2)) on random regular graphs, V <= 14

Round 3 (r4-phase23-r3.md), all need r3lib.py (+ pcdeg.py, cnfs.py for r3_e3):
  r3lib.py  function-basis rank machinery: stack_rank (c_P(K) of Pang), quotient by C_D
  r3_e1.py  dim of degree<=K polys supported on an affine subspace (kernel of 1-g), p=2,3
  r3_e2.py  greedy Pang rounds for random subcube/affine families (C=0)
  r3_e3.py  same with a C_D from PC closure (no formula with PC degree>=5 found at n<=10 in time; unfinished)
  r3_e4.py  flatness table (exact formula) and disjoint-block family greedy rounds
  r3_e5.py  first-round best gain vs single-term kernel fraction, block family

Kill test (r4-phase23-killtest.md), p=2, C_D=0 unless stated:
  kt_opt.py     exact multi-round optimum for the disjoint-block family via subspace orbits of F_2^s (s<=7); sampled upper bound for s=8
  kt_round1.py  exact first-round optimum (all q weights), n up to 18
  kt_deg.py     exact PC degree of PHP and Tseitin(K5,K6) instances
  kt_search.py  random 3-CNF search for PC degree >= 5 (slow, unfinished)
  kt_cd.py      greedy Pang rounds with/without C_3 for PHP 4->3 (needs r3_e2.py, r3_e3.py)

Overlap test (r4-phase23-overlap.md), p=2, C_D=0, overlapping subcube families:
  ov_lib.py          family constructors (all pairs/triples, cycle, cubic, random, linear triple system) + rank machinery
  ov_exact_small.py  EXACT first round, all pairs, n<=7 (all graphs up to isomorphism, needs networkx)
  ov_exact_sparse.py EXACT first round for any family with s<=16 terms (all 2^s-1 vectors)
  ov_search.py       SAMPLED greedy rounds (clique/random seeds + flip hill climbing); usage in its docstring
