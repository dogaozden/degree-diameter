# Evolve: LLM program search, first aimed at bipartite degree-diameter

Date: 2026-10-10. Status: approved in chat (structure, problem, pilot). The user waived the written-spec review and asked for build and pilot without stopping.

## Goal

Build a reusable evolutionary program-search engine that runs on Doğa's Claude subscription. Then aim it at a quiet open problem: the largest bipartite graph with maximum degree d and diameter D.

The engine is the main product. The graph problem is the first plug-in. A new record would be great, but it is not the bar for success.

## Decisions made in chat

- The first runs happen on the Mac (an M4 MacBook Air with 10 cores and 16 GB), lid open and on power. Cloud sessions come later, and only if the pilot shows promise.
- The pilot is capped at about 5% of the weekly allowance (5 WCU). The budget for longer runs is decided after we measure.
- Approach A: one-shot Haiku. Each mutation is one `claude -p` call that returns a whole program, with one retry that includes the error message. A plain Python script runs the loop. It is not an LLM agent.
- No API keys and no paid services. Model calls go through `claude -p` on the logged-in Max plan, with no `--bare`.

## Why this target

The Combinatorics Wiki table for bipartite degree-diameter has barely moved since January 2012. Only two cells changed, both in 2021 (Araujo-Pardo and López). We found no AI-assisted entries. The general (non-bipartite) table, by contrast, has been rewritten by AI-assisted contributors through Aug–Oct 2026. Checking a candidate is exact and cheap. The best known graphs come from structured recipes (lifts, Cayley-type graphs, modified projective planes), which suits program search better than local search. Source: http://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs (checked 2026-10-10).

## Architecture

There are two separate pieces. The engine knows nothing about graphs.

### Engine (`evolve/`)

- **Loop** (`loop.py`, `cli.py`). `python -m evolve run <config>` runs generations. Each generation: select parents, ask the mutator for N new programs, evaluate every new program on every case, write results, update the status file, then commit and push. `python -m evolve status <run-dir>` prints progress.
- **Mutator** (`mutator.py`). Builds the prompt and calls `claude -p` in isolated mode: no settings, no CLAUDE.md, no MCP, no slash commands, and no tools. It uses a pinned full model ID (`claude-haiku-5-5`), never an alias or a fallback. It pulls the last fenced Python block out of the reply. It compiles the code and smoke-tests it on the smallest case. If that fails, it makes one retry that includes the previous code and the error. It refuses to run if the CLI reports an API key instead of the subscription login. It stops cleanly when either rate-limit window reaches 90%. It logs tokens, the API-equivalent cost estimate and time for every call. A `FakeMutator` with scripted replies is used in tests, so tests spend no allowance.
- **Runner** (`runner.py`, `_harness.py`). Runs one program on one case in its own process, with a wall-clock limit (time limit plus 5 s grace, after which the whole process group is killed). Numeric libraries are pinned to one thread. The program's `build(...)` result is written as JSON. Statuses are `ok`, `timeout`, `crash` and `bad_output`. Programs never see the checker or the scores.
- **Selection** (`select.py`). Fitness is the weighted mean of per-case scores. The parent pool is the top `elite_k` programs by fitness, plus the best program on each case, so specialists survive. Roles are sampled by weight: `default` (improve), `crossover` (combine two parents), `invent` (add a new idea or helper) and `moonshot` (a risky rewrite). Everything is seeded and repeatable.
- **Store** (`store.py`). An append-only run folder. Nothing is overwritten. A generation is complete when its summary file exists. On restart, the run evaluates programs that have no results, generates any missing programs, and carries on.
- **Budget guard.** There is a hard cap on model calls per run (`max_calls`, which counts retries). It also stops on the 90% rate-limit reading, or on a subscription-limit error. A stopped run finishes evaluating what it has, writes its summary, commits, and exits with code 3.

### Problem plug-in (`problems/bipartite_dd/`)

- **Interface for candidates.** A candidate is one Python file defining `build(d, D, seed, time_limit)`. It returns `(n, edges)` or `{"n": n, "edges": edges}`, with vertices numbered `0..n-1`. It may import `numpy`, the standard library, and `lib` (our helper library). It must return within `time_limit` seconds.
- **Checker** (`checker.py`, trusted). It rejects:
  - malformed output, labels out of range, self-loops and duplicate edges
  - any vertex with more than d neighbours
  - a graph that is not bipartite (checked by 2-colouring)
  - any pair of vertices more than D steps apart (bitset reachability over D rounds)

  A valid graph scores `n`. Any rejection scores 0 and records the reason.
- **Second checker** (`checker_nx.py`). A separate implementation on networkx (bipartite test, degrees, eccentricities). It runs whenever a graph ties or beats a record, or reaches a calibration case's known value. Both checkers must agree before anything is saved under `records/`.
- **Helper library** (`lib.py`), readable by Haiku and importable by candidates:
  - finite fields GF(q) for prime powers q
  - the projective plane PG(2,q) incidence graph
  - cyclic voltage lifts of a base multigraph (loops and parallel edges allowed)
  - Haar graphs, i.e. bipartite bi-Cayley graphs of Z_m with a connection set
  - fast degree, bipartite and diameter self-checks
- **Starter program** (`seed.py`). If D=3 and d−1 is a prime power, it returns the PG(2,d−1) incidence graph. Otherwise it searches random Haar graphs over Z_m, growing m and keeping the largest one that passes, until the time limit.
- **Notes for Haiku** (`notes.md`): short hints covering lifts over cyclic groups, Cayley and Haar graphs, adding a few vertices to projective-plane incidence graphs (Araujo-Pardo and López), duplication and compounding, and local search with repair.
- **Cases** (`cases.toml`). Scores are `n / record`. A score of 1.0 ties the record, and anything above 1 is a new record (flagged loudly). A value above the ceiling means a checker bug and stops the run.

| id | d | D | record | ceiling | kind | weight |
|---|---|---|---|---|---|---|
| d3D3 | 3 | 3 | 14 | 14 | calibration | 1 |
| d4D3 | 4 | 3 | 26 | 26 | calibration | 1 |
| d5D3 | 5 | 3 | 42 | 42 | calibration | 1 |
| d6D3 | 6 | 3 | 62 | 62 | calibration | 1 |
| d3D4 | 3 | 4 | 30 | 30 | calibration | 1 |
| d4D4 | 4 | 4 | 80 | 80 | calibration | 1 |
| d3D5 | 3 | 5 | 56 | 56 | calibration | 1 |
| d7D3 | 7 | 3 | 80 | 80 | calibration | 1 |
| d4D5 | 4 | 5 | 160 | 236 | target | 2 |
| d5D5 | 5 | 5 | 336 | 676 | target | 2 |
| d6D5 | 6 | 5 | 684 | 1556 | target | 2 |
| d7D4 | 7 | 4 | 346 | 518 | target | 2 |
| d11D3 | 11 | 3 | 190 | 220 | target | 2 |

## Data layout

```text
evolve/                      engine
problems/bipartite_dd/       problem plug-in
configs/pilot.toml           run settings
runs/<run_id>/
  config.toml                copy of the config used
  candidates/<cid>/program.py
  candidates/<cid>/meta.json     generation, parents, role, mutator attempts and usage
  candidates/<cid>/result.json   per-case status, value, score, reason, time; fitness
  generations/<g>.json       summary: candidates, best fitness, best per case, calls, broken count
  calls.jsonl                one line per model call
  status.md                  human-readable progress
records/bipartite_dd/<case>/<n>-<run>-<cid>.json   doubly verified graphs
tests/
```

Candidate ids are `g{generation:03d}-c{index:02d}`. Generation 0 holds only the starter program, `g000-seed`.

## Error handling

- A broken, crashing, timed-out or invalid program scores 0 on that case. The reason is recorded, and the run continues.
- A failed mutation (no code block, compile error, or a smoke test that still fails after the retry) produces no candidate and is counted as broken.
- Transient CLI errors (429, 529, 5xx) back off and retry up to 3 times. A subscription-limit error stops the run as a budget stop.
- Git commit or push failures are logged and are not fatal.

## Testing

- Checker: the Heawood graph passes (3,3), and the Tutte–Coxeter graph passes (3,4). K4, a degree violation, a 16-cycle under D=3, duplicate edges, self-loops and bad labels all fail. Both checkers agree on many random graphs.
- Library: for q in 2, 3, 4, 5, 7, 8, 9 and 11, the PG(2,q) incidence graph is a valid (q+1, 3) graph with 2(q²+q+1) vertices. Finite-field axioms hold. Haar graphs are bipartite and regular.
- Runner: ok, timeout, crash and bad output are each detected.
- Engine: selection is deterministic for a given seed. Store resume works. A full fake-mutator run of 2 generations works. A run killed partway through resumes and finishes without double-counting.
- One real Haiku call proves subscription auth (`apiKeySource` is `none`) before the pilot.

## Pilot

Five generations of 8 programs, 1 evaluation seed, 20 s per case, 8 eval workers and 4 concurrent Haiku calls. `max_calls` starts at 100 and is adjusted after measuring one real generation, so that the pilot stays near 5 WCU.

Pass criteria:
- the plumbing works end to end, including resume
- evolution improves on the starter on at least one case the starter does not already solve

Hoped-for outcome: it reaches a known value on d4D4 (80), d3D5 (56) or d7D3 (80).

At the end, report cost per call, broken rate, what climbed, and the best graphs found.

## Out of scope for now

Cloud sessions and routines, island models, an HTML dashboard, larger targets (D=6 and beyond, d=13, 15 and 16), and submitting records. Each can follow once the pilot shows the engine works.
