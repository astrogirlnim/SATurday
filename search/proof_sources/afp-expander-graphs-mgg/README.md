# AFP Expander Graphs (MGG) cache slot

Catalog id: `afp-expander-graphs-mgg`

Block A MGG Inv pins discharged on `mggF2Graph` (2026-09-24):

- `MGGFrontier.mgg_has_multi_cheeger_of_gabber_galil` (`MggF2HasMultiCheeger`)
- `MGGFrontier.mggGraph_hasExpansionInv` (`HasExpansionInv (mggF2Graph m _) mggInvK`)
- `exists_mgg_simple_hasExpansionInv_family`

Next R2 inhabit is cubicization (`TseitinFrontier`), not these spectral pins.

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
