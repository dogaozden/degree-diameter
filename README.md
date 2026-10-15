# degree-diameter

Eight new records for the **bipartite degree–diameter problem**, and a new theorem behind three of them,
found by an evolutionary search in which Claude Haiku 5.5 agents rewrite graph-building programs. Every record
graph and the theorem are checked in Lean 4.

**See it:** [dogaozden.com/haiku-frontier](https://dogaozden.com/haiku-frontier/) shows every record graph in 3D,
how the search found them, and the theorem.

## The problem

Build the largest graph you can such that

1. it is **bipartite**: every vertex is one of two colours and every edge joins the two colours;
2. every vertex has at most **Δ** neighbours;
3. any two vertices are joined by a path of at most **D** edges (the diameter).

The largest possible size, N<sup>b</sup>(Δ, D), is unknown for almost every (Δ, D). The best known graphs are
collected in the Combinatorics Wiki's
[bipartite degree–diameter table](http://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs).
A record is a lower bound: one valid graph that is bigger than the table entry.

## Results

| (Δ, D) | Table | Ours | Old record set by | Stood |
|---|---|---|---|---|
| (7, 4) | 346 | **359** | Delorme & Farhi, 1984 | 42 years |
| (11, 4) | 1734 | **1774** | Delorme & Farhi, 1984 | 42 years |
| (4, 5) | 160 | **162** | Hafner; Loz, by 2009 | 17+ years |
| (5, 5) | 336 | **354** | Eyal Loz (project with Pérez-Rosés & Pineda-Villavicencio), by 2009 | 17+ years |
| (7, 5) | 1134 | **1140** | Eyal Loz (project with Pérez-Rosés & Pineda-Villavicencio), by 2009 | 17+ years |
| (11, 3) | 190 | **192** | Feria-Purón, Miller & Pineda-Villavicencio, 2013 | 14 years |
| (13, 3) | 274 | **276** | Araujo-Pardo & López, 2022 | 5+ years |
| (15, 3) | 374 | **376** | Araujo-Pardo & López, 2022 | 5+ years |

"By 2009" marks entries the table cites no paper for; the year is the earliest table we found them in
(Eyal Loz's degree–diameter table, January 2009). Years are journal years; "Stood" counts from when the record
entered the table (the 2013 and 2022 papers were on arXiv in 2012 and 2020). Full references, upper bounds and the literature check are in
[`records/bipartite_dd/CANDIDATES.md`](records/bipartite_dd/CANDIDATES.md). Each graph is stored as JSON
(`[n, [[u, v], ...]]`) next to the program that built it, under `records/bipartite_dd/`.

These are not yet in the published table; the next step is to send them to its moderators.

## The +2 theorem

> For every finite projective plane of order q ≥ 4 there is a bipartite graph with 2(q² + q + 6) vertices,
> maximum degree q + 2 and diameter 3.

Araujo-Pardo and López (2022) built such graphs with 2(q² + q + 5) vertices and listed improving the construction
as an open problem. The search found graphs exactly 2 larger at q = 9, 11 and 13. All three add a fourth "hat" pair
(a copy of a point and a copy of a line) and rotate three incidences to make room. The general rule, its proof
and computer checks are in [`research/plus2/REPORT.md`](research/plus2/REPORT.md); a short note for
mathematicians is in [`research/plus2/note/`](research/plus2/note/).

## Checked in Lean

`lean/` is a Lean 4 + Mathlib project.

- [`lean/BipartiteDD/Records.lean`](lean/BipartiteDD/Records.lean) proves all eight records:
  `∃ G : SimpleGraph (Fin n), IsBipartiteDegDiam G Δ D`, by a checker proved sound once and run in the kernel
  (`decide +kernel`, no `native_decide`).
- [`lean/BipartiteDD/Plus2/`](lean/BipartiteDD/Plus2/) proves the +2 theorem for every finite projective plane
  (`plus2`, and `plus2_of_order` for q ≥ 4).

`#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` for every theorem
([`lean/Axioms.out.txt`](lean/Axioms.out.txt), [`lean/BipartiteDD/Plus2/Axioms.out.txt`](lean/BipartiteDD/Plus2/Axioms.out.txt)).
An independent session rebuilt everything from scratch, compiling Mathlib from source, with the same result
([`lean/CHECK.txt`](lean/CHECK.txt)).

Besides Lean, every record graph passes three independent checkers (bitsets, networkx, and a from-scratch
search from every vertex). Seven of the eight were rebuilt from their own programs on a second machine; the
1,774 program gives 1,773, so that graph is the island's saved copy.

## How it was found

The engine in [`evolve/`](evolve/) is an evolutionary program search in the spirit of Google DeepMind's
[AlphaEvolve](https://arxiv.org/abs/2506.13131), inspired by Ryan Xu's
[square-packing post](https://slightlysupervised.substack.com/p/improving-25-square-packing-upper):

1. **Pick parents** from the best programs found so far.
2. **Haiku rewrites**: Claude Haiku 5.5 gets a parent's code plus a page of hints and writes a changed version
   (the mutation step).
3. **Run**: each program gets 60 seconds to build a graph.
4. **Check**: a strict checker tests the three rules; a broken graph scores zero, a valid one scores by size.
5. **Survive**: the best join the population. Repeat.

The search ran as separate populations ("islands") in Claude Code cloud sessions: 68 were launched and 61 got a
machine and ran, up to 48 at a time with eight Haiku calls each, some specialised in one cell and some using a fast
C engine. In total Haiku wrote about 32,500 programs. Five hours on one laptop matched two records and beat none;
once the islands ran in the cloud, the first record fell after 31 minutes and six fell within 82. Claude Opus 5.5 coordinated, checked every record, and turned the +2 pattern
into a proof; Haiku 5.5 agents also wrote the Lean proofs.

## Reproduce

```bash
python -m venv .venv && .venv/bin/pip install numpy networkx pytest

# check a record graph with all three checkers
.venv/bin/python scripts/verify_record.py records/bipartite_dd/d7D4/359-spec-d7d4-g017-c11.json 7 4

# run the tests
.venv/bin/python -m pytest -q

# rebuild the +2 graphs for q = 4 … 16
.venv/bin/python research/plus2/construction.py

# build the Lean proofs (needs elan; downloads Mathlib's cache)
cd lean && lake exe cache get && lake build
```

Running the search itself needs the [Claude Code](https://claude.com/claude-code) CLI: the mutator calls
`claude -p --model claude-haiku-5-5`. `python -m evolve run CONFIG --fake` runs the loop with a stand-in mutator, for
testing without model calls:

```bash
.venv/bin/python -m evolve run configs/smoke.toml --fake
.venv/bin/python -m evolve status runs/smoke-001
```

## Layout

| Path | What it is |
|---|---|
| `evolve/` | the evolutionary engine: loop, Haiku mutator, sandboxed runner, selection, budget guard |
| `problems/bipartite_dd/` | the problem plug-in: checkers, cases, hints, starter programs (Python and C) |
| `configs/` | one config per run and island |
| `runs/` | run logs and every candidate program from the Mac runs |
| `records/bipartite_dd/` | the record graphs, their programs, and the literature check |
| `lean/` | Lean proofs of the records and the +2 theorem |
| `research/plus2/` | the +2 construction, proof, checks and note |
| `reports/` | the interactive pages and the scripts that build their data |
| `scripts/` | record verification, fleet launching and keeping |
| `docs/` | design plan and briefs |

Island runs in the cloud pushed their logs to their own branches.

## Credits

Doğa Özden, with Claude Code (Claude Opus 5.5 coordinating; Claude Haiku 5.5 searching and writing Lean).
Prior work: the table's authors listed above, and the Combinatorics Wiki's maintainers.

## License

Code (`evolve/`, `problems/`, `scripts/`, `tests/`, `lean/`) is under the [MIT License](LICENSE). The record
graphs, run logs, research write-ups, pages and documents are under
[CC BY 4.0](LICENSE-DATA): reuse them freely, with credit.
