import Theory.Basic
import Theory.ProofComplexity.Resolution
import Theory.ProofComplexity.PHP
import Theory.ProofComplexity.CriticalAssignments
import Theory.ProofComplexity.ClauseComplexity
import Theory.ProofComplexity.MonotoneWidth
import Theory.ProofComplexity.MatchingRestriction
import Theory.ProofComplexity.MonotoneCalculus
import Theory.ProofComplexity.Width
import Theory.ProofComplexity.SizeWidth
import Theory.ProofComplexity.FinGraph
import Theory.ProofComplexity.MGG
import Theory.ProofComplexity.MGG.Factor2Inv4
import Theory.ProofComplexity.Tseitin
import Theory.ProofComplexity.CSExpansion
import Theory.ProofComplexity.CuttingPlanes
import Theory.ProofComplexity.CuttingPlanesInterp
import Theory.ProofComplexity.Sunflower
import Theory.ProofComplexity.MonotoneClique
import Theory.ProofComplexity.CliqueBound
import Theory.ProofComplexity.CliqueArith
import Theory.ProofComplexity.CliqueFinal
import Theory.ProofComplexity.RealToBool
import Theory.ProofComplexity.CuttingPlanesStar
import Theory.ProofComplexity.CuttingPlanesFinal
import Theory.ProofComplexity.AC0pFrege
import Theory.ProofComplexity.Bridge.Encoding
import Theory.ProofComplexity.Bridge.Complexity
import Theory.ProofComplexity.Bridge.FormulaEncoding
import Theory.ProofComplexity.Bridge.ProofSystem
import Theory.ProofComplexity.Bridge.CookReckhow
import Theory.ProofComplexity.Bridge.CookLevin
import Theory.ProofComplexity.Bridge.StackProg
import Theory.ProofComplexity.Bridge.Tableau
import Theory.ProofComplexity.Bridge.FProg
import Theory.ProofComplexity.Bridge.Generator
import Theory.ProofComplexity.Bridge.GeneratorCost
import Theory.ProofComplexity.Bridge.GeneratorOk
import Theory.ProofComplexity.Bridge.GeneratorBound
import Theory.ProofComplexity.Bridge.TM2CM
import Theory.ProofComplexity.Bridge.Reduction
import Theory.ProofComplexity.Bridge.Hard

/-!
# SATurday Theory Library

Main entry point for the SATurday formal verification library.

Reboot (2026-08-03): the library now targets the proof complexity ladder.
The old circuit, sunflower, and sheaf modules were archived to archive/theory
after the program audit; see docs/postmortems/ for the reasons.

## Modules
- `Theory.Basic`: fundamental smoke lemmas verifying the Lean setup
- `Theory.ProofComplexity.*`: the active ladder (resolution first)
- `Theory.ProofComplexity.CuttingPlanes`: R3 cutting planes and clique coloring
- `Theory.ProofComplexity.Bridge.*`: R5 Cook Reckhow bridge (P NP coNP)

Acceptance bar for anything imported here: compiles, zero sorries, and
axioms limited to propext, Classical.choice, Quot.sound
(enforced by scripts/check_axioms.sh).

LOG: Theory library root module for the proof complexity ladder
-/
