# PRD: Loop Native Proof Import

Status: proposed  
Owner: saturday loop (`satday auto` / `satday saturday`)  
Audience: implementers of `search/saturday/` and role prompts  
Non audience: Cursor chat agents doing one off manual ports for the repo

## 1. Summary

Add a **proof import** capability to the SATurday research loop so that, when a
Frontier obligation is already machine checked in another proof assistant
(Isabelle/HOL AFP, Coq, Agda, HOL Light, etc.), the loop can **ingest that
source**, **map it onto our Lean targets**, and **formalize Lean certificates**
using the same local or remote LLM path as ordinary `prove` / `formalize`
cycles.

The importer is a **first class loop feature**. It must run under `satday`
with the configured local Ollama models or OpenRouter remote models
(`--remote`). It must **not** depend on a human or Cursor agent interrupting
the loop to rewrite proofs by hand.

## 2. Problem

### 2.1 Current gap

- R2 Block A is blocked on Margulis Gabber Galil style expansion
  (`MggHasMultiCheeger`, `mggGraph_hasExpansionInv`).
- A complete formalization already exists in Isabelle AFP
  (`Expander_Graphs`, theory `Expander_Graphs_MGG`), including Cheeger and the
  spectral bound used in the literature.
- Mathlib has graph Laplacians but not this construction.
- Today the loop only knows how to invent prose or grind Lean from rung memory.
  It has no structured way to treat a foreign ITP development as the
  authoritative proof source.
- Leaving a spectral `sorry` in Frontier is not an acceptable close for the
  critical path. Closing Block A requires zero `sorry` on accepted
  declarations and a green axiom gate.

### 2.2 Why the loop must own this

Manual Cursor ports do not scale, do not resume after crashes, and fight the
autonomy contract (`satday auto`). The same wake machinery that already
formalizes accepted prose should formalize **imported** lemma plans, one
cluster per cycle, with reflect, auto apply, and kill switch unchanged.

## 3. Goals

1. Let the loop discover or be given a **foreign proof source** for an open
   Lean Frontier obligation.
2. Run a **prove (import plan)** cycle that produces a lemma ordered port map
   into our modules (no Lean in that cycle).
3. After `accept_prose`, run **formalize (import cluster)** cycles that emit
   Lean 4 from the cached foreign source plus the port map, using local or
   remote models per existing `saturday_loop` config.
4. Enforce the same acceptance bar as ordinary formalize: lake build green,
   zero `sorry` outside Frontier, standard axioms only, `scripts/check_axioms.sh`
   PASS before merge into the accepted tree.
5. Keep R2 / R5 parallel ownership unchanged. Import work on R2 only touches
   non Bridge modules; R5 is out of scope unless a later source is pinned.

## 4. Non goals

- Automatic binary translation of Isabelle/Coq proof objects into Lean (no
  shared kernel; no trusted bridge).
- New Lean axioms that cite “Isabelle already proved it.”
- Replacing mathlib with AFP content wholesale.
- Cursor agent one shot ports as the delivery vehicle.
- Closing R5 Cook Reckhow FinTM2 obligations via import (no suitable foreign
  source identified; R5 stays write from scratch).
- Fetching the live internet on every wake when offline policy forbids it;
  sources must be cacheable under the repo or a configured local mirror.

## 5. Users and operators

| Role | Need |
| --- | --- |
| Operator | Pin or approve an import source once; then `satday auto` (local or `--remote`) continues. |
| Loop chooser / reflect | Prefer import formalize when an accepted import plan exists and Frontier still open. |
| Local LLM | Prove plans and formalize clusters when `--remote` is off. |
| Remote LLM | Same roles when `saturday_loop.remote` is enabled. |
| Human gate | `accept_prose` for the import plan; `merge_certified` for Lean clusters. |

## 6. Definitions

- **Foreign source**: a versioned, text readable development from another ITP
  (example: AFP entry `Expander_Graphs`, theory `Expander_Graphs_MGG`).
- **Source cache**: local tree under something like
  `search/proof_sources/<source_id>/` holding fetched or vendored theory text,
  license note, and a pinned revision or release tag.
- **Import plan**: prose artifact in the rung session log that maps foreign
  lemmas to Lean names, modules, and dependency order. Produced by `prove`
  with `action` flavor import (see below).
- **Import cluster**: one formalize wake that ports a contiguous slice of the
  plan (definitions first, then lemmas), not an entire AFP session in one call.
- **Critical path close**: Frontier sorry for the pinned obligation is removed
  and the declaration is accepted under the axiom gate.

## 7. Proposed product shape

### 7.1 Action surface (loop)

Prefer **extending** existing actions over a fifth top level action:

| Cycle | Behavior |
| --- | --- |
| `prove` with import target | Build or revise the import plan from source cache + open Frontier. No Lean. |
| `formalize` with import plan in memory | Emit one Lean cluster guided by the next unfinished plan step and the relevant foreign theory excerpts. |
| `audit` | Optional: check that the plan does not smuggle new axioms or revive a twice blocked method. |

Optional later: `action_type: import` as sugar that chooser expands to prove or
formalize based on whether an accepted plan exists. First ship can stay on
prove / formalize with explicit targets such as
`import plan: AFP Expander_Graphs_MGG -> MggHasMultiCheeger`.

### 7.2 Chooser / reflect hooks

When:

- rung is `prose_accepted` or `active`, and
- an **accepted import plan** is recorded for that rung, and
- the plan’s next Lean obligation is still open (Frontier or missing decl),

then prefer `formalize` with target equal to the next plan step.

When:

- Frontier names match a **configured import catalog** entry (example:
  `mgg_has_multi_cheeger_of_gabber_galil` -> AFP MGG), and
- no accepted import plan exists,

then prefer `prove` with target `import plan for <source_id>`.

Reflect plateau rules stay: obligation set must shrink; helper only drafts
reject; sticky operator `force_actions` unchanged.

### 7.3 Source catalog (config)

Extend `infra/config/defaults.yaml` under `saturday_loop`:

```yaml
saturday_loop:
  proof_import:
    enabled: true
    cache_dir: "search/proof_sources"
    # Offline by default: only use already cached trees.
    allow_network_fetch: false
    catalog:
      - id: "afp-expander-graphs-mgg"
        itps: ["isabelle"]
        title: "AFP Expander Graphs MGG"
        # Relative to cache_dir after vendor/fetch
        root: "afp-expander-graphs-mgg"
        license: "BSD"
        maps_to_rungs: ["r2-width-machinery"]
        maps_to_frontier:
          - "MGGFrontier.mgg_has_multi_cheeger_of_gabber_galil"
          - "MGGFrontier.mggGraph_hasExpansionInv"
        primary_theories:
          - "Expander_Graphs_MGG"
        notes: "Hoory style Fourier proof; spectral bound 5/8 sqrt 2"
```

Network fetch (optional operator command, not every wake):

```bash
satday proof-source fetch afp-expander-graphs-mgg
satday proof-source status
```

Fetch writes into `cache_dir` and records revision metadata. Auto wakes only
**read** the cache.

### 7.4 Prompt and skill changes

- **Prover system / user prompt**: if the target is an import plan, instruct the
  model to treat the foreign development as known content to adapt, not to
  invent a new expansion proof. Require: source id, theory list, ordered Lean
  lemma map, gap classes, self adversarial pass, and explicit “no new axioms /
  no sorry on critical path close.”
- **Formalizer prompt**: inject (a) next plan step, (b) truncated foreign
  theory excerpt for that step, (c) our existing Lean surface (`mggGraph`,
  cut loss, Inv packaging). Forbid inventing alternate identifiers that ignore
  the plan. Still Lean 4 `by` tactics only; Frontier only for unfinished
  suffixes of the plan.
- Skills (`.cursor/skills/prover`, `formalizer`, `saturday`): document import
  as a supported prove / formalize mode for the CLI loop. Cursor chat remains
  optional; **CLI is the driver**.

### 7.5 Artifacts and memory

Per successful prove (import plan):

- Append rung memory entry with source id, revision, lemma map, and
  `gate_pending: accept_prose`.
- Write machine readable plan JSON under
  `search/proof_sources/<id>/plans/<rung>_<timestamp>.json` (and latest
  symlink or pointer in control/progress).

Per formalize cluster:

- Same drafts / auto apply / axiom gate path as today.
- Session JSONL notes must include `import_source_id` and `import_plan_step`.

### 7.6 Acceptance bar (unchanged, restated)

A critical path obligation is **closed** only when:

1. The declaration lives outside Frontier (or Frontier namespace is empty of
   that name).
2. No `sorry` in its proof.
3. `scripts/check_axioms.sh` PASS for accepted declarations.
4. Rung memory records the merge.

Import does not weaken this bar.

## 8. Primary use case (R2)

**Source:** AFP `Expander_Graphs` / `Expander_Graphs_MGG` (Karayel).  
**Lean targets (existing):**

- `MGGFrontier.mgg_has_multi_cheeger_of_gabber_galil`
- `MGGFrontier.mggGraph_hasExpansionInv`
- then packaging already certified (`exists_mgg_simple_hasExpansionInv_family_of_inv`,
  Inv-15 from multi Cheeger, cubicization path).

**Expected import plan outline (illustrative):**

1. Fourier / character surface on `(Z/mZ)^2` aligned to `mggDecode` / `mggEncode`.
2. Rayleigh quotient / adjacency form for the labeled 8 regular multi star
   (`mggNeighbor`).
3. Hoory / Jimbo Maruoka style bound lemmas needed for the spectral or
   Cheeger inequality used by AFP.
4. Discharge `MggHasMultiCheeger`.
5. Glue to existing Inv packaging (Inv-4 with twelfth loss, or Inv-15 from
   multi Cheeger alone) **without** leaving sorry on the closed pin.
6. Later wakes: cubicize toward `exists_cubic_hasExpansionInv_family`.

Each numbered item is one or more formalize wakes, not one LLM call.

## 9. Model routing

Reuse existing config; no special cloud only path.

| Role | Local default | Remote (`--remote`) |
| --- | --- | --- |
| Import prove (plan) | `saturday_loop.prove.model` | `remote.prove_model` (+ fallback) |
| Import formalize | `saturday_loop.formalize.model` | `remote.formalize_model` (+ fallback) |
| Audit of plan | `saturday_loop.audit.model` | optional `remote.audit_model` |

Escalate (`--escalate`) keeps current meaning: try local first, then remote on
failure. Import does not invent a third endpoint.

## 10. Offline and license constraints

- Default: `allow_network_fetch: false`. Operator vendors AFP (or other)
  sources into `search/proof_sources/` before auto.
- Cache must include LICENSE / attribution for the foreign entry.
- Imported **ideas** become Lean proofs we maintain; we do not copy Isabelle
  sources into `theory/` as executable code.
- Offline policy in `infra/config/defaults.yaml` remains authoritative for
  solver and auto wakes.

## 11. Success metrics

1. **Functional:** With cache present and import plan accepted, `satday auto`
   (local) eventually removes `mgg_has_multi_cheeger_of_gabber_galil` sorry
   and lands an accepted Inv family inhabitant path without human Lean edits.
2. **Process:** At least 80% of import formalize wakes either shrink the open
   Frontier set for the mapped names or are rejected by reflect as near
   duplicate / same error (no silent thrash without pause).
3. **Hygiene:** Zero new axioms; no accepted declaration with `sorry`.
4. **Autonomy:** No requirement that a Cursor session perform the port for
   progress to continue.

## 12. Risks and mitigations

| Risk | Mitigation |
| --- | --- |
| Local coder models invent Lean 3 or nonexistent names | Existing reflect + apply error digest; import prompt pins plan names; reject drafts that ignore plan step ids. |
| Context window cannot hold full AFP theory | Plan steps cite file slices; prompt injects only the excerpt for the current step. |
| Port stalls on Fourier analysis | Reflect plateau after N wakes switches to audit or prove plan revision, not kill unless `auto_kill_on_plateau`. |
| License / attribution miss | Fetch/status CLI refuses import prove if LICENSE missing in cache. |
| Treating AFP as an axiom | Explicit ban in prompts and audit checklist; gate still checks axioms. |
| Operator sticky `force_actions: formalize` without a plan | Chooser should fall back to import prove when catalog matches and plan absent. |

## 13. Milestones

### M0 — Spec landed (this PRD)

- [x] PRD merged under `docs/prd/proof-import.md`.
- [x] Catalog stub for AFP MGG in config (can be disabled).

### M1 — Cache + CLI

- [x] `search/proof_sources/` layout + `satday proof-source status|fetch`.
- [x] Vendor script or documented manual vendor steps for AFP Expander Graphs.
- [x] No LLM changes required to pass M1.

Populate theories (offline):

```bash
satday proof-source fetch afp-expander-graphs-mgg \
  --from-dir /path/to/afp/thys/Expander_Graphs
satday proof-source status
```

### M2 — Prove import plan in loop

- [x] Prompt + chooser hooks.
- [ ] First accepted import plan on `r2-width-machinery` for MGG Cheeger / spectral
  discharge (human or gate_auto `accept_prose`).

### M3 — Formalize import clusters in loop

- Formalize prompt injects plan step + source excerpt.
- Session records carry `import_source_id`.
- Auto apply / axiom gate unchanged.

### M4 — Critical path close

- `MggHasMultiCheeger` (or equivalent) accepted with zero sorry.
- Inv pin closed via packaging already in tree.
- Checklist / critical path docs updated by the loop’s normal checklist rules.

## 14. Open questions

1. Should `import` be a distinct `action_type` in JSONL, or only a target
   prefix under prove / formalize? (Recommendation: target prefix in M2;
   distinct type only if metrics need it.)
2. How large may a single theory excerpt be in the formalize prompt (tokens)?
   Needs a measured default after first local runs.
3. Do we vendor AFP as a git submodule, a release tarball, or a sparse copy of
   only `Expander_Graphs*` theories?
4. Is Inv-15 from multi Cheeger an acceptable intermediate pin once Cheeger is
   sorry free, or must Inv-4 close in the same milestone?

## 15. Implementation touchpoints (existing files; prefer edit)

| Area | Likely files |
| --- | --- |
| Config | `infra/config/defaults.yaml`, `infra/config/schemas.py` |
| Chooser / reflect | `search/saturday/chooser.py`, `search/saturday/reflect.py` |
| Prompts | `search/saturday/prompts.py` |
| Actions / cycle | `search/saturday/actions.py`, `search/saturday/cycle.py` |
| CLI | `search/` entrypoints that register `satday` subcommands |
| Skills | `.cursor/skills/saturday/SKILL.md`, `prover/SKILL.md`, `formalizer/SKILL.md` |
| Source cache | `search/proof_sources/` (new tree; not under `theory/`) |
| Rung memory | `docs/ladder/rungs/r2-width-machinery.md` (append only via loop) |

Do **not** create duplicate formalizer agents or a second research loop.

## 16. Decision

Ship proof import as **loop native prove / formalize modes** driven by a
**versioned source cache** and **catalog**, using **local or remote models**
already configured for SATurday. Cursor chat may observe or unkill; it is not
the importer of record.
