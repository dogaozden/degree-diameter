# d58-sl17: a (5,8) Haar graph on SL(2,17), 9,792 vertices (job d58-sl17, Haiku, Oct 31 2026)

**Status: in progress.** This file is updated as the search runs. Target: a graph with d = 5, D = 8 on
H(SL(2,17), S), N = 4,896, 9,792 vertices (record to beat: 9,760).

## Setup

- Code: `src/sl17.c`, a copy of `research/selfdual-hi/src/haar_sd.c` (plain mode = `research/structured/haar_sym.c`
  bit-parallel cost, validated there) with three additions:
  - `INIT=file`: start from a given S (five lines `a b c d`, first line the identity).
  - `DUMP=file`, `DUMPMAX=c`: append every new best state with cost <= c (`BEST t=... steps=... cost | a b c d | ...`).
  - `ENDG=k`: exhaustive endgame around the INIT state: every replacement of 1 (k=1) or 2 (k=2) elements of S
    (positions 1..4, s_0 = e fixed), cost by the same evaluation; cost 0 -> written through `check_and_write`.
- Cost (one-sided, even D): number of B-side elements not within distance D-1 = 7 of (e,A). Equivalent to
  |G \ S X^3|, X = S^-1 S. Cross-checked against an independent BFS (`tools/check_cost.py`, `tools/sl17lib.py`):
  MATCH on the smoke-test states.
- Acceptance: `tools/rebuild_from_S.py` builds the edge list from S alone (own SL(2,17) arithmetic, vertex (g,A) = g,
  (g,B) = N+g, edges (g,A)-(sg,B)); `research/lifts/coordinator_check/apsp.c` must print `RESULT VALID d=5 D=8`
  and `RESULT INVALID` at D=7. Pipeline sanity check: a cost-2 state gives diameter 9: INVALID at D=8, VALID at D=9.
- Throughput: about 150,000 evaluations/s per core (4 cores).

## Runs

Wave 1 (`runs/jobs_wave1.txt`, `run_wave.sh`): seeds 101-124, plain annealing (K = 8 candidates per step), 600 s each,
dump of every best state with cost <= 1. Logs under `logs/sl17_s*.log`.

