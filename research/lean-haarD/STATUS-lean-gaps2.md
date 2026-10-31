# Status: lean-gaps2 (more Lean proofs from GAPS.md, Haar and lift records up to 50,000 vertices)

Branch `claude/lean-gaps2-haar-proofs-9qjlsg`, started from `claude/lean-gaps-proofs-3qf4j2` (the six proofs and
tools of the previous job are there and are not redone). The gap list is `research/lean-haarD/GAPS.md`. Every file
here is new; no existing file is changed.

## Proved

| # | Cell | Vertices | Construction | Module folder (`lean/BipartiteDD/Haar/`) | Theorem | Method | Axioms |
|---|---|---:|---|---|---|---|---|
| 1 | (8,5) | 2,048 | route-chart lift (affine fibre maps), 8-regular | `D8D5N2048` | `nb_8_5_n2048` | staged (`gen_d8D5_n2048.py` → `gen_staged_lift.py`) | propext, Classical.choice, Quot.sound |

Edge list used: `research/theorems/chartlift/graphs/d8D5_n2048.edges.gz` (copy in the folder). The construction is
not a plain regular voltage lift as built, which GAPS.md notes; the Lean statement needs only the graph, so the
staged pipeline applies unchanged.

## How the link to the edge file is checked

`research/lean-haarD/gen_d8D5_n2048.py` reads the edge file, checks it (simple, 8-regular, bipartite, every pair within
5 steps by a bitset check), writes `Graph.lean` with the neighbour and colour lists, reads `Graph.lean` back and asserts
that its lists equal the edge file. The staged check then runs as for the other staged records.

## Build measurements

Each module was built with its own `lake build <module>`, one at a time, under a Python wrapper that reads the
largest child's peak RSS (`getrusage`); `/usr/bin/time` is not installed in this sandbox. Machine: 4 cores, 15 GB.

| Module | Wall time | Peak RSS |
|---|---:|---:|
| `D8D5N2048.Graph` | 28.8 s | 1.00 GB |
| `D8D5N2048.Level01` | 19.1 s | 1.89 GB |
| `D8D5N2048.Level02` | 10.4 s | 1.89 GB |
| `D8D5N2048.Level03` | 8.9 s | 1.89 GB |
| `D8D5N2048.Level04` | 9.7 s | 1.90 GB |
| `D8D5N2048.Levels` | 3.8 s | 1.81 GB |
| `D8D5N2048.Check` (local test, one module) | 46.2 s | 4.67 GB |
| `D8D5N2048.Stage00` … `Stage04` | 24–30 s each | 3.56–3.58 GB |
| `D8D5N2048.Record` | 3.5 s | 1.82 GB |
| `Axioms.lean` (`lake env lean`) | 2.1 s | 1.80 GB |

Toolchain: `leanprover/lean4:v4.34.1` installed with elan in this sandbox, Mathlib from the cache
(`lake exe cache get`, 8,908 files, about one minute).
