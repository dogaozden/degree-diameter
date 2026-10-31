# d58-sl17: no (5,8) Haar graph on SL(2,17) found (job d58-sl17, Haiku, Oct 31 2026)

**Result: nothing closed.** No S with d = 5 in SL(2,17) (N = 4,896, 9,792 vertices) gave diameter 8. The best
states have one uncovered element; every one has diameter 9 under `research/lifts/coordinator_check/apsp.c`
(`RESULT INVALID` at D = 8). No edge list was accepted, so `records/` is not created.

## What was run

Setup. `src/sl17.c` is `research/selfdual-hi/src/haar_sd.c` (plain mode, the bit-parallel cost of
`research/structured/haar_sym.c`) with three additions: `INIT=file` (start from a given S), `DUMP=file DUMPMAX=c`
(record every new best state with cost <= c), and `ENDG=k` (exhaustive 1- or 2-element replacement around the INIT
state; any cost 0 goes through the existing full check and solution writer). Cost = B-side elements not within
distance 7 of (e,A) (one-sided, D even), about 150,000 evaluations/s per core, 4 cores.

| batch | runs | start | time per run | runs reaching best 1 | best counts (per run) |
|---|---|---|---|---|---|
| wave 1, seeds 101-124 | 24 | random | 600 s | 2 | 1: 2, 2: 15, 3: 7 |
| wave 2, seeds 205-208 | 4 | random, TMAX 1.5 | 600 s | 2 | 1: 2, 2: 1, 3: 1 |
| wave 3, seeds 301-316 | 16 | random, TMAX 1.5 | 600 s | 3 | 1: 3, 2: 8, 3: 5 |
| wave 2, seeds 201-204 | 4 | restart from a best-1 state, TMAX 0.4 | 600 s | 4 (never improved) | 1: 4 |

Total: 48 annealing runs, about 3.9e9 evaluations. Seven best-1 states were found (seeds 111, 115, 206, 208, 305,
310, 315). They are pairwise non-conjugate (canonical forms in `best1_states.txt`), so the search did not just
revisit one state.

Endgames. On each of the seven best-1 states:
- every replacement of one element (positions 1..4, s_0 = e fixed): 19,568 candidates, none with cost 0;
- every replacement of two elements (6 position pairs, all N^2 pairs): 143,589,984 candidates each,
  1.0e9 in total, none with cost 0. The cost histograms are in `logs/endg_*.log`.
  Neighbours mostly jump to cost 8 or more, so the landscape around a best-1 state is rugged.

Checks. Every best-1 state was re-scored by an independent Python BFS (`tools/sl17lib.py`, `tools/check_cost.py`):
all seven match the C cost of 1. Each S was rebuilt from its 2x2 matrices alone (`tools/rebuild_from_S.py`) and run
through apsp: diameter 9 in all seven, `RESULT INVALID` at D = 8 (`best1_states.txt`).

## What was not done

- No tabu search. The two-move exhaustive endgame was run instead.
- No normalisation of s_1 to conjugacy-class representatives during the search. Repeats were checked after the
  fact by canonical form.
- PSL(2,17) x C2 and the other orders above 4,880 were not searched in this job. The earlier job's plain
  runs there gave best 12 (`research/selfdual-hi/logs/K5D8/hsd/plain_psl17x2_s1.log`), far from 0.
- About 48 annealing runs of 600 s, not hundreds of seeds. Four cores over three hours give about 40 runs per hour.

## Reading

Plain annealing on SL(2,17) reaches 1 uncovered element in about 1 run in 6 (7 of 44 random starts), and never
below 1 (earlier job: 10 runs, best 1; this job: 48 runs, best 1). Restarting from a best-1 state at low temperature
did not improve it. Two-move exhaustion around seven distinct best-1 states found no cost-0 set. This is
consistent with the earlier job's finding that SL(2,17) plain sets come within one element of a (5,8) graph and
self-dual families are exhausted. It is not a proof: the 1.0e9 two-move candidates and 4e9 annealing evaluations
cover only a small part of the roughly 1e13 sets of size 5.

## Files

- `src/sl17.c`: annealer with INIT / DUMP / ENDG (built with `gcc -O3 -march=native -fopenmp`).
- `run_wave.sh`, `run_wave2.sh`: job drivers; `runs/jobs_wave*.txt`: the job lists.
- `logs/`: all RESULT and endgame logs; `runs/dump_*.txt`: best-state dumps; `runs/init_*_b1.txt`: the seven best-1 states.
- `best1_states.txt`: the seven states with cost, independent cost, apsp diameter and canonical form.
- `tools/`: independent builder, BFS cost check, state extraction, one- and two-move endgame driver.
