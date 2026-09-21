# Proof sources cache

Local cache of foreign ITP developments used by the SATurday loop for
**proof import** (see `docs/prd/proof-import.md`).

Auto wakes **only read** this tree. Populate it with the CLI:

```bash
satday proof-source status
satday proof-source fetch afp-expander-graphs-mgg --from-dir /path/to/afp/thys/Expander_Graphs
satday proof-source ladder afp-expander-graphs-mgg
```

`ladder` parses vendored theories into an ordered micro plan (general for any
catalog entry with `primary_theories` + `maps_to_frontier` + optional
`lean_module`). Does not invent Lean axioms.

Network fetch is off by default (`saturday_loop.proof_import.allow_network_fetch`).

## Layout

```text
search/proof_sources/
  README.md
  <root>/
    LICENSE
    SOURCE.json
    ATTRIBUTION.md
    thys/          # vendored .thy files (gitignored bulk)
    plans/         # import plans written by M2+ prove cycles
    downloads/     # optional tar.gz from --network (gitignored)
```

Do not copy these files into `theory/`. They are blueprints for Lean ports, not
Lean axioms.
