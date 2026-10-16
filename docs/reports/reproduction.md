# Pinned reproduction recipe

Date: 2026-10-15. Branch `r4/refrepair`. Nothing here is a certification claim.

## Versions

- Lean toolchain: `leanprover/lean4:v4.30.0-rc1` (`theory/lean-toolchain`).
- Mathlib: `50d5513e83c4cee78eecdd834de6b690d58bdf68` (`theory/lake-manifest.json`; the lakefile requires
  `mathlib` from git with no pinned revision, so the manifest is what pins it; do not run `lake update`).
- Other packages from the manifest: plausible `a3b459a8`, LeanSearchClient `c5d5b8fe`, importGraph `4411c5f8`,
  proofwidgets `82d457fb` (v0.0.97), aesop `f74c7555`, Qq `7aa86cb2`, batteries `bf597c77`, Cli `f7d0ca7c`.
- Repository base for this work: `bd5dd3b` (local `main` before the refrepair merge). The commit that contains this file
  is the merge of `r4/refrepair`; take `git rev-parse HEAD` of a checkout of that merge as the pinned hash.

## Commands

    git clone <repo> SATurday && cd SATurday && git checkout <pinned hash>
    cd theory
    find . -name '._*' -not -path './.lake/*' -delete    # needed on ExFAT drives (AppleDouble sidecars)
    lake build                                           # must exit 0
    cd .. && bash scripts/check_axioms.sh                # runs lake build, the sorry scan, then `#print axioms`

`check_axioms.sh` fails if (1) `lake build` fails, (2) any `sorry` occurs in a file lacking the marker `Frontier`,
(3) any declaration listed in `scripts/accepted_declarations.txt` depends on an axiom other than the accepted list.

## Accepted axioms

Exactly `propext`, `Classical.choice`, `Quot.sound`. Frontier-quarantined `sorry`s (11 at last run, in
`AC0pFrege`, `CuttingPlanes`, `MGG/SpectralFrontier`, `MGG/Factor2Inv4`, `Tseitin`, `CSExpansion`) are outside the
accepted declarations list.

## Caveats (honest)

- All gate runs recorded so far, including the ones for this branch, were made on trees with a warm `.lake` (Mathlib
  oleans already built, project oleans copied from the main checkout). A build from an empty `.lake` (fetching and
  compiling Mathlib, then about 8500 jobs) has not been run on this machine. Cold `import Mathlib` is slow on the
  external drive (about 20 to 35 minutes for the first process).
- The accepted-declaration list was extended by this branch with the 18 new final theorems (see
  `docs/reports/response-to-referee.md`, section "Prover status").
