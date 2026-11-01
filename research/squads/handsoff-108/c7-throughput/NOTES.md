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
