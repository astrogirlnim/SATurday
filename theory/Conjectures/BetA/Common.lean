import Theory.Circuits

/-!
# Common imports and utilities for Bet A conjectures

This module re-exports the shared namespace so individual proof files can
use a single `import Conjectures.BetA.Common` line instead of repeating
all upstream imports.

LOG: Common BetA module recreated after session 6 cleanup
-/

-- Re-export the core namespace so proof files open it.
open SATurday.Circuits
