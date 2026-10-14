Scratch experiment scripts for r4-phase23-program.md (research only, not part of any build).
Requires python3, numpy, networkx.  Run from this directory.
  pcdeg.py   exact multilinear PC degree over F_p by fixpoint linear algebra (n <= ~12)
  cnfs.py    CNF constructors: Tseitin mod 2 / mod q with Boolean edge variables, random 3-CNF
  tmodel.py  combinatorial model of the exact PC degree of Tseitin-mod-2 (odd p), see program doc Sec 2
  chain_ub.py            upper bound by a vertex ordering (ball radius rule), any graph size
  check_model_vs_linear_algebra.py   model vs linear algebra on small graphs
  check_lower_bound.py   checks D >= max(d, ceil(b_{1/3}/2)) on random regular graphs, V <= 14
