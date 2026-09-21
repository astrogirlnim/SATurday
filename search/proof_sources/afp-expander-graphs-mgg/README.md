# AFP Expander Graphs (MGG) cache slot

Catalog id: `afp-expander-graphs-mgg`

Maps to R2 Frontier:

- `MGGFrontier.mgg_has_multi_cheeger_of_gabber_galil`
- `MGGFrontier.mggGraph_hasExpansionInv`

## Vendor (offline)

1. Download AFP current from https://www.isa-afp.org/download/
2. Unpack and find `thys/Expander_Graphs`
3. Run:

```bash
satday proof-source fetch afp-expander-graphs-mgg \
  --from-dir /path/to/afp/thys/Expander_Graphs
satday proof-source status afp-expander-graphs-mgg
```

Ready requires `LICENSE`, `SOURCE.json`, and primary `.thy` files under `thys/`.
