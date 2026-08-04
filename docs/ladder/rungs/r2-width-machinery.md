# R2: Width Machinery and More Families

Status: active
Lean home: theory/Theory/ProofComplexity/ (module split decided at adoption)

## Statement

1. Ben-Sasson-Wigderson width-size tradeoff in general form: short resolution
   refutations imply narrow refutations; quantitative version.
2. Width lower bounds, hence size lower bounds, for: random k-CNF at suitable
   clause density (Chvatal-Szemeredi) and Tseitin contradictions over expander
   graphs.

## Why this rung

The width method is the workhorse of resolution lower bounds; formalizing it in
general form turns R1-style results into a reusable machine. Expander-based Tseitin
bounds introduce the expansion toolkit needed at higher rungs.

## Falsification test

Calibration only: falsifier proof-size curves for random k-CNF around the
threshold density and for Tseitin instances; curves must match the known theory
(exponential at the relevant densities).

## Barrier notes

Same as R1: no applicable wall at resolution level. Expansion arguments are the
technique most likely to survive upward, worth auditing for reuse at R3 and R4.

## Session log (append-only)

- 2026-08-03 reboot: rung proposed.
- 2026-08-03 falsify (early smoke calibration, budgets enforced): Tseitin
  odd-charge on the 3-regular circulant, n = 6..16 even, all UNSAT within
  milliseconds with proof lines in the tens to low hundreds; random 3-CNF at
  density 5, n = 20..44 step 4: 5 UNSAT, 2 SAT (small-n fluctuation near the
  threshold, expected and recorded honestly). Two conclusions for rung design:
  the circulant chord graph is not a strong expander, so the R2 Tseitin family
  must switch to genuine expanders (random 3-regular with expansion check, or an
  explicit Ramanujan-style construction) before hardness curves mean anything;
  and the random 3-CNF density should rise toward 5.5 or n should grow before it
  is used as a hardness calibration family. Ledger: search/logs/falsifier_runs.jsonl.

- 2026-08-04 adopt: rung opened to active by R1 certification
  (path A honest-rate close). Next: prove cycle to pin the BSW size-width statement and Lean module split.
