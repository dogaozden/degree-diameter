# c7-throughput (handsoff-108): more good descents per CPU-hour

Question: which schedule draws more low chain minima (energy <= 12, <= 9; ORBW=3 units) per CPU-hour on psl 23 97?

## Method
- `haar_c7.c` = copy of research/d10D8/sym2/haar_sym2.c plus instrumentation (patch_c7.py, same search otherwise):
  - `CPUCLOCK=1`: schedule (T halving, REHEAT stall), chain times and budget run on process CPU time. The machine is
    shared (load > 4 from other workers), so wall-clock chains would get fewer evaluations under contention.
  - `IMLOG=1`: one line per chain, `IM n end <chain CPU s> min M ev E ab A n N t:E ...` = every new chain minimum
    with its chain time. A chain's trajectory before its stop does not depend on REHEAT (the schedule restarts at each
    chain start), so stall rules REHEAT=r <= 30 and "abort at chain time t if chain min > thr" are replayed exactly from
    these lines by analyze.py (self-check: the REHEAT=30 replay reproduces every logged end and min).
  - `ABORTPOL="t:thr,..."`: live early abort (not used in the runs below; the replays cover it).
- run_variant.sh NAME SEED SECS [VAR=val ...]: one heavy process, nice 10, THREADS=1, ulimit 1.5 GB, timeout 4000 s.
- Reference F15W3 = ORBIT="3 3 1" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3 K=8 (as the grind), CPU clock.

## Runs
- v0_ref: F15W3 (COOL=15 REHEAT=30 K=8 ORBW=3), CPUCLOCK=1, seed 108801, 1800 CPU-s, 35 chains, best 3. Log v0_ref.log.
  Chain-min distribution: 3:1, 6:1, 15:6, 18:13, 21:11, 24:3. Low states (3, 6): c7_low_states.tsv.
- v1_cool75: COOL=7.5 REHEAT=30, seed 108802, 1800 CPU-s, started 23:17 UTC. Log v1_cool75.log (live).

## Replay results (analyze.py; exact for stall rules and abort rules, see Method)
Self-check: the REHEAT=30 replay reproduces all logged chain ends and minima (0 mismatches).

Per CPU-hour (v0, 35 chains, 0.497 CPU-h). Counts in brackets.

| stall REHEAT | <=12 /CPU-h | <=15 /CPU-h | <=18 /CPU-h | CPU-h |
|---|---|---|---|---|
| 30 (as run) | 4.0 [2] | 16.1 [8] | 42.2 [21] | 0.497 |
| 20 | 3.1 [1] | 15.5 [5] | 37.1 [12] | 0.323 |
| 15 | 4.4 [1] | 13.3 [3] | 26.6 [6] | 0.225 |
| 10 | 6.7 [1] | 13.5 [2] | 27.0 [4] | 0.148 |
| 5 | 0 [0] | 0 [0] | 14.1 [1] | 0.071 |

Shorter stall windows lose the late improvements (the minima 3, 6 and 15 came at 30, 7 and 34 s), so REHEAT
below 20 s hurts; the 10-30 s range is flat within noise.

Early-abort ("stop at chain time t if chain min > thr"), per CPU-hour (<=15 / <=12):
- best candidates: t=8, thr 24: 19.9 / 5.7 (7 and 2 events); t=15, thr 27 (no-op): 16.1 / 4.0.
- aggressive cuts (thr 18-21 at t=5-10) cut the late successes with the chains: rates 11-17 per CPU-h.
- Conclusion: no abort rule separates from the as-run schedule at this sample size (35 chains). Not live-tested.

Cross-check with the grind logs (g1.log + g2.log, 245 chains, 14.4 M evaluations, wall-clock schedule under contention):
- counts <=12: 5, <=15: 26, <=18: 74, <=9: 0 (no chain at or below 9 in 245 descents).
- per Mevals: <=12 0.35, <=15 1.80, <=18 5.13. v0 (CPU clock): <=12 0.46, <=15 1.83, <=18 4.79.
  So the CPU-clock reference matches the grind per evaluation; the wall-clock contention does not visibly change the
  chain-min distribution at this level.

## Live run: v1_cool75 (COOL=7.5, REHEAT=30, seed 108802), 23:17-00:14 UTC, exited normally
- 40 chains, 0.491 CPU-h, 4.45 M evals (RESULT best 13 = unweighted count; chain min 15 in ORBW=3 units).
- Chain minima: 15:12, 18:14, 21:11, 24:3. No chain below 15.
- Compared with v0 (COOL=15, 35 chains, 0.497 CPU-h, 4.38 M evals):

| schedule | chains | <=9 | <=12 | <=15 per CPU-h (count) | <=18 per CPU-h | <=12 per Mevals |
|---|---|---|---|---|---|---|
| COOL 15 (v0) | 35 | 2 | 2 | 16.1 (8) | 42.2 (21) | 0.46 |
| COOL 15 (grind g1+g2, wall clock) | 245 | 0 | 5 | (26 in 3.0 wall-h) | (74) | 0.35 |
| COOL 7.5 (v1) | 40 | 0 | 0 | 24.4 (12) | 52.9 (26) | 0.00 |

Reading: COOL 7.5 moves the bulk down (<=15 about 1.5x per CPU-h, Poisson p around 0.4, not significant) but gives no
chain below 15. Expected <=12 events in v1 at the COOL 15 rate (0.37 per Mevals) is about 1.6; observed 0 (p around 0.2).
The deep tail, which is what cost 0 needs, is not resolved by 40 chains: the decisive count is about 10x more CPU.

## Verdicts so far
- Stall REHEAT: 10-30 s flat within noise; below 20 s loses late improvements. Keep 30.
- Early abort: no rule beats the as-run schedule on replay (best t=8 thr=24: 19.9 vs 16.1 per CPU-h at <=15, 7 vs 8 events).
- COOL: 7.5 looks better on the bulk and worse-or-equal on the deep tail; undecided.
- The CPU clock matches the grind per evaluation (<=15: 1.82 vs 1.80 per Mevals), so the instrumentation is sound.
- Practical lever is volume: a rate test at <=9 or <=12 needs roughly 20-40 CPU-hours per arm, not 30 minutes.

## Next (if continued)
- COOL 30 (v2, 900 CPU-s, low power, started 00:14 UTC).
- Combine v0 and v1 trajectories for abort rules with more events (v1 abort replay is in analyze.py: `--dump`).
- Use the grind's per-chain CHAIN lines (wall clock) only for the tail, not for schedule comparisons.

## Live run: v2_cool30 (COOL=30, REHEAT=30, seed 108803), 00:14-00:43 UTC, 900 CPU-s, exited normally
- 19 chains, 0.247 CPU-h, 2.29 M evals, RESULT best 9 (unweighted). Chain minima: 9:1, 12:1, 15:5, 18:4, 21:6, 24:2.
- Low-power run (900 CPU-s): the single chain at 9 is the deepest of this worker after v0's 3 and 6.

## Final table, live runs (CPU clock, same binary, seeds 108801-108803)

| schedule | chains | CPU-h | <=9 (per CPU-h) | <=12 (per CPU-h) | <=15 (per CPU-h) | <=18 (per CPU-h) |
|---|---|---|---|---|---|---|
| COOL 15 (v0, reference) | 35 | 0.497 | 2 (4.0) | 2 (4.0) | 8 (16.1) | 21 (42.2) |
| COOL 7.5 (v1) | 40 | 0.491 | 0 (0) | 0 (0) | 12 (24.4) | 26 (52.9) |
| COOL 30 (v2) | 19 | 0.247 | 1 (4.0) | 2 (8.1) | 7 (28.3) | 11 (44.5) |
| grind g1+g2 (wall clock, COOL 15) | 245 | 3.0 wall-h | 0 | 5 | 26 | 74 |

Per chain, <=12: v0 2/35, v1 0/40, v2 2/19, grind 5/245. Per Mevals, <=12: 0.46, 0.00, 0.87, 0.35.

## Conclusions
- None of the schedules separates on the deep tail (<=9, <=12) at this size. Counts of 0-2 per arm, Poisson-noise.
- COOL 7.5 and 30 both give more chains at <=15 per CPU-hour than v0 (about 1.5-1.8x), but the sign on <=12 flips
  between the two, so the schedule effect is unresolved. A decision needs about 10-40 CPU-hours per arm.
- REHEAT: keep 30. Replays show 10-30 s flat within noise, and shorter windows lose late improvements.
- Early abort: no replayed rule beats the as-run schedule; not run live.
- Instrumentation check: CPU-clock reference matches the grind per evaluation for <=15 and <=18 (1.82 vs 1.80, 4.79 vs 5.13 per Mevals).
- Note: RESULT best= is the unweighted uncovered count; CHAIN and IM minima are ORBW=3 energies.
- Scoreboard: one line (first result, chain min 3, 2026-10-31 23:16 UTC). No new best since; good_states already has 3.
- Stopped: no processes of mine running at the end (checked 00:43 UTC).
