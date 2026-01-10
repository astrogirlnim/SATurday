import Lake
open Lake DSL

package «theory» where
  -- Package configuration
  -- LOG: Theory package for SATurday formal verification

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Theory» where
  -- Main theory library
  -- LOG: Core complexity theory modules

lean_lib «Tactics» where
  -- Tactic libraries for circuit complexity proofs
  globs := #[.submodules `Tactics]

-- Test script to verify basic lemmas
script test do
  IO.println "LOG: Running SATurday theory tests..."
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", "Theory/Tests/BasicTests.lean"]
  }
  if out.exitCode = 0 then
    IO.println "LOG: All theory tests passed!"
    return 0
  else
    IO.eprintln s!"LOG: Tests failed with exit code {out.exitCode}"
    IO.eprintln out.stderr
    return out.exitCode
