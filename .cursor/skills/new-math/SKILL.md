---
name: new-math
description: >
  Proposes new mathematical approaches to P vs NP, debates them with the user,
  then pursues the chosen approach. Use when the current chain is barrier-blocked,
  or when the user says "new math", "new direction", or "what next for P vs NP".
---

# NEW-MATH: Mathematical Strategy and Pursuit

## Purpose

Identify a mathematical approach to P vs NP that plausibly evades all three
known barriers, agree on it with the user, then pursue it using the existing
proof and mining infrastructure.

## The Loop

```
  Step 0   Literature Search   (orchestrator)
     |      WebSearch: current barrier-evading approaches
     v
  Step 1   Proposer   (subagent)
     |      proposes 3 approaches grounded in literature
     v
  Step 2   Debate   (HITL loop)
     |  ^   user argues, subagent defends
     |  |   repeat until user says "go with X"
     v  |
  Step 3   Commit   (orchestrator)
     |      create research/<slug>/, lock approach
     v
  Step 4   Pursue   (proof-sprint or ORACLE)
     |      close theorems or generate LRAT evidence
     v
  Step 5   Barrier Validator   (subagent)
     |  |   WebSearch: recent critiques of this technique
     |  +-- BARRIER_BLOCKED --> back to Step 2
     v
  Step 6   Victory Check   (orchestrator + HITL)
     |  |
     |  +-- not yet --> back to Step 4
     v
  DONE: P != NP proved, human confirmed
```

---

## Step 0: Literature Search (orchestrator — no subagent)

Run these four web searches using the WebSearch tool. Collect the results into
a `LiteratureContext` block that is passed verbatim to the Proposer in Step 1.

```
Search 1: "P vs NP barrier evading proof techniques 2025 2026"
Search 2: "non-relativizing non-naturalizing circuit complexity lower bound recent"
Search 3: "geometric complexity theory Mulmuley progress 2024 2025"
Search 4: "proof complexity circuit lower bound separation 2024 2025"
```

From the results, extract and summarize:
- Any named approaches published or discussed in the last two years
- Any approaches explicitly shown to fail (to avoid proposing dead ends)
- Any arxiv papers with plausible barrier-evasion claims (note: unverified)

Format as:

```
LITERATURE CONTEXT (for Proposer)

Recent active directions:
  <direction name>: <one-sentence summary> (source: <paper or author>)
  ...

Recently refuted or critiqued directions:
  <direction>: <why it failed> (source: <paper or author>)
  ...

Unverified but notable recent claims:
  <arxiv id or title>: <one-sentence claim>
  ...
```

If all searches return no useful results, write: "LITERATURE_SPARSE: proceed
with prior knowledge only."

---

## Step 1: Proposer (spawn subagent)

Spawn one subagent. It proposes exactly 3 approaches. Each must state explicitly
which of the three barriers it evades and how. No hedging.

**The three barriers (pass verbatim to the subagent):**
- Relativization (BGS 1975): proof must behave differently with vs without a PSPACE oracle
- Natural proofs (Razborov-Rudich 1997): proof must not be polynomial-time checkable on random functions
- Algebraization (AW 2008): proof must not extend to algebrized oracle models

**Subagent prompt:**
```
You are a research mathematician proposing approaches to separate P from NP.

The current approach (Razborov monotone lower bounds) is blocked by all three
barriers: relativization, natural proofs, and algebraization.

CRITICAL CONSTRAINT: Do NOT propose extensions of existing work. The user wants
genuinely novel approaches based on the fundamental structure of the problem and
a clear gap in all prior mathematical attempts. Any proposal that is "more of the
same but harder" will be rejected.

Do not propose: diagonalization, monotone lower bounds, time hierarchy variations,
Geometric Complexity Theory variations, lifting theorem extensions, MCSP
amplification, or any approach that extends an existing research program.

Literature gathered this session:
  {LITERATURE_CONTEXT}

Use the literature only to avoid repeating approaches already shown to fail.

Propose exactly 3 genuinely novel approaches. For each:
1. Name and one-sentence plain-English description.
2. What fundamental insight about P vs NP this exploits (the actual gap it fills,
   in plain English anyone can understand).
3. Which of the three barriers it evades and why (plain English, one sentence each).
4. Which barriers it does NOT evade (be honest).
5. The single first theorem to prove in Lean 4 if this approach were pursued.
6. Estimated difficulty: months, years, or decade.
7. Why no one has seriously tried this before (required field).

Present each proposal in two layers:
PLAIN ENGLISH (2-3 sentences a CEO could understand)
TECHNICAL DETAIL (for the mathematician)

You will argue for these proposals against the user. Do not concede unless
the user raises a valid technical argument. Defend your reasoning.

Return a markdown list. No JSON. No hyphens. No emojis. Be direct.
```

---

## Step 2: Debate (HITL loop — no subagent)

Print the Proposer output to the user, then enter a discussion loop.

**Print verbatim:**
```
------------------------------------------------------------
MATHEMATICAL APPROACH PROPOSALS
------------------------------------------------------------
<Proposer output here>

------------------------------------------------------------
Your turn. Push back, ask questions, or propose your own direction.
When you are ready to commit to one approach, say: "go with <name>"
------------------------------------------------------------
```

For each user message that is not "go with X":
- Spawn a new Proposer subagent with the conversation history
- Let it defend or revise the proposals in plain English plus technical detail
- Print its response
- Repeat

All Proposer output must be written in two layers:
  PLAIN ENGLISH: 2-3 sentences a non-technical executive could understand.
  TECHNICAL DETAIL: the mathematical substance for the researcher.

The subagent should argue. It should not capitulate to social pressure. It should
concede only to valid mathematical arguments (e.g., "that approach relativizes
because..."). If the user proposes something new, evaluate it by the same barrier
criteria and say whether it qualifies, in plain English first.

When the user says "go with <name>", proceed to Step 3.

---

## Step 3: Commit (orchestrator — no subagent)

Derive a slug from the approach name (lowercase, spaces to underscores, no special chars).
Example: "Geometric Complexity Theory" -> `geometric_complexity_theory`.

Create the approach folder and scaffold:
```bash
SLUG="<slug>"
BASE="/Users/nmm/Development/SATurday/research/$SLUG"
mkdir -p "$BASE/lean" "$BASE/sat" "$BASE/logs" "$BASE/notes"

# Seed the literature notes file with what was found in Step 0
cat > "$BASE/notes/literature.md" <<DOC
# Literature Notes: <Approach Name>

## Step 0 search results
<paste LITERATURE_CONTEXT here>

## Step 5 search results
(populated when Barrier Validator runs)

## Step 6 search results
(populated when Victory Check runs)
DOC

# README with approach summary from the debate
cat > "$BASE/README.md" <<DOC
# <Approach Name>

## One-line description
<from Proposer>

## Barrier evasion claimed
Relativization: <verdict and mechanism>
Natural proofs:  <verdict and mechanism>
Algebraization:  <verdict and mechanism>

## First Lean target
<first_lean_target from Proposer>

## Status
Active. Session started: <date>.
DOC
```

Folder layout:
```
research/<slug>/
  README.md          approach summary and barrier verdicts
  lean/              Lean 4 source files for this approach
  sat/               CNF files and LRAT certificates
  logs/              JSONL logs specific to this approach
  notes/             freeform scratch notes from debate
```

Record the chosen approach:
```bash
python3 -c "
import json, time
entry = {
  'timestamp': int(time.time()),
  'chosen_approach': '<name from user>',
  'slug': '$SLUG',
  'folder': 'research/$SLUG',
  'barrier_evasion_claimed': '<from debate summary>',
  'first_lean_target': '<from Proposer output>'
}
print(json.dumps(entry))
" >> /Users/nmm/Development/SATurday/search/logs/new_math_proposals.jsonl
```

Print:
```
Approach locked: <name>
Folder created:  research/<slug>/
First Lean target: <target>
Routing to proof-sprint / ORACLE as appropriate.
```

Then route:
- If first target is a Lean theorem: hand off to `.cursor/skills/proof-sprint/SKILL.md`
  with the chosen approach's first_lean_target as the Navigator's context.
- If first target needs empirical SAT evidence first: hand off to `.cursor/skills/run-oracle/SKILL.md`.

---

## Step 4: Pursue

Follow whichever skill was routed to in Step 3. Return the outcome
(closed / published / stuck / timeout) when done.

---

## Step 5: Barrier Validator (orchestrator + subagent)

**5a. Literature check (orchestrator — no subagent)**

Before spawning the Validator, run two targeted searches on the specific
technique that was just pursued:

```
Search 1: "<approach name> barrier relativization natural proof complexity theory"
Search 2: "<approach name> P vs NP refutation or confirmation 2024 2025 2026"
```

Summarize findings into a `ValidationLiterature` block:
- Any papers that have formally analyzed this technique against the barriers
- Any known refutations of barrier-evasion claims for this technique
- Any endorsements from recognized complexity theorists

If the search finds a published refutation of the barrier-evasion claim,
skip the subagent and go directly to BARRIER_BLOCKED with the citation.

**5b. Barrier Validator (spawn subagent)**

Pass the theorem, proof summary, and ValidationLiterature to the subagent.

**Subagent prompt:**
```
You are a skeptical complexity theorist. A proof attempt has produced the
following result:

  Theorem: <theorem name and statement>
  Proof technique: <summary of approach>
  Barrier evasion claimed: <from Step 3 record>
  Literature on this technique: {VALIDATION_LITERATURE}

Use the literature to inform your verdicts. If a published paper has already
shown this technique to be relativizing or to constitute a natural proof, cite
it and rule BARRIER_BLOCKED immediately.

Apply each barrier test:

Relativization: Does this proof work relative to a PSPACE oracle?
  If yes, it is relativizing and cannot separate P from NP.

Natural proofs: Is the hardness property used here polynomial-time checkable
  on random functions? Is it largeness-closed?
  If yes to both, it is a natural proof.

Algebraization: Does the argument extend to algebrized oracle models?
  If yes, it algebrizes.

For each barrier: verdict (blocked / evades / unclear) and one-sentence reason.
Overall verdict: BARRIER_CLEAR or BARRIER_BLOCKED.
If BARRIER_BLOCKED: name the blocking barrier and suggest how to modify the approach.

Write your verdict in two layers:
PLAIN ENGLISH: what this means in 2 sentences a non-technical executive can understand.
TECHNICAL DETAIL: the formal barrier analysis.
```

If verdict is BARRIER_BLOCKED: return to Step 2 with the blocking barrier as new
context for the debate.

If verdict is BARRIER_CLEAR: proceed to Step 6.

---

## Step 6: Victory Check (orchestrator — no subagent)

**6a. Final literature check**

Run one search before presenting the result to the user:

```
Search: "<theorem name> OR <approach name> P vs NP proof 2025 2026"
```

If any result indicates the claimed separation is already known to be flawed,
append that finding to the HITL prompt so the user can weigh it.

**6b. Lean and sorryAx checks**

A result only counts as separating P from NP if ALL of the following hold:

```bash
# 1. The target theorem is sorry-free in Lean
SORRY_COUNT=$(cd /Users/nmm/Development/SATurday/theory && \
  grep -rn ":= sorry\|^ *sorry$" --include="*.lean" \
  <path to approach theorem file> 2>/dev/null | wc -l | tr -d ' ')

# 2. No sorryAx in the axiom set
cd /Users/nmm/Development/SATurday/theory && lake build 2>/dev/null
lake env lean --stdin <<'LEAN' 2>&1 | grep -q "sorryAx" && echo "SORRY_AX" || echo "CLEAN"
#print axioms <theorem_name>
LEAN

# 3. The theorem statement actually separates P from NP
# (must be verified by human - see HITL below)
```

If SORRY_COUNT=0 and output is CLEAN:

**Print HITL prompt and wait for human confirmation:**
```
============================================================
POTENTIAL P != NP SEPARATION
============================================================
Theorem: <name>
Statement: <statement>
Barrier Validator verdict: BARRIER_CLEAR
No sorry. No sorryAx.

HUMAN VERIFICATION REQUIRED.
Does this theorem constitute a separation of P from NP?
Does the theorem statement correctly formalize P and NP?
Does the proof technique match what the Barrier Validator analyzed?

Enter YES to confirm, or describe what is missing:
```

If user enters YES:
```
============================================================
P != NP PROVED
============================================================
Theorem: <name>
Human confirmed: yes
Barrier clear: yes
Lean verified: yes

Commit and notify.
============================================================
```

```bash
cd /Users/nmm/Development/SATurday
git add -f theory/ search/logs/
git commit -m "P != NP proved: <theorem name>"
```

---

## Conventions

**N1 — User has final say on approach.** The subagent argues but does not override.

**N2 — Barrier verdicts are mandatory.** No approach proceeds without explicit
verdicts on all three barriers from the Proposer and the Validator.

**N3 — Human confirms victory.** No automated commit of a P vs NP result.
The loop always stops for human review before the final commit.

**N4 — One approach at a time.** Do not pursue multiple directions in parallel.
Finish or abandon the current approach before starting a new one.

**N6 — Literature search at every proposal and validation boundary.** Step 0
searches before any subagent is spawned. Step 5a searches before the Barrier
Validator runs. Step 6a searches before the Victory HITL prompt. A known
refutation in the literature short-circuits the subagent and returns
BARRIER_BLOCKED immediately with a citation. Save all search summaries to
`research/<slug>/notes/literature.md` for the permanent record.

**N5 — One folder per approach.** Every approach that passes Step 3 gets a
`research/<slug>/` folder. All Lean files, SAT certificates, logs, and notes
for that approach live there — never in the top-level `theory/` or `proofs/`
directories. This keeps approaches isolated and makes it unambiguous which
evidence belongs to which mathematical direction.
