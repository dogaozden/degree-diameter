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
