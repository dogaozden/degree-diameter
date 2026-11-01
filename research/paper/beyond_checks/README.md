# Second checks run by job paper-beyond (2026-11-01)

Rows of the BEYOND.md table that had only one checker (or only the finder's own check) were re-checked here with a
checker written separately from the one already used. Each log starts with the file and its sha256, and the checker.

- Haar graphs of SL(2,p) x Z_n / PSL(2,p) x Z_n from branch claude/beyond-d13-search-z35z61 (research/frontier/sols/):
  `research/frontier/haarcheck_sl.c` / `research/structured/tools/haarcheck_psl.c` from master 9a97f7a5 (gcc -O3,
  single-threaded). The search session had checked them with haarcheck_gen. `*.ref.txt` = both BFS in one run;
  `*.refA.txt` / `*.refB.txt` = BFS from (e,A) / (e,B) in two runs (both halves are needed).
- Metacyclic Haar graphs: `research/frontier/build_haar2.py` (master) on the two D = 13, 14 files the search session
  had checked with its own metacheck/metacheck2; `research/frontier/beyond13/metacheck.py` (branch
  claude/beyond-d13-search-z35z61) on master's (5,12) and (6,11) files, which had been checked by build_haar2.py only.
- Edge lists: `research/lifts/coordinator_check/apsp.c` (all pairs, no symmetry), also at D - 1, where it must fail.
  (3,11) 1,474 from branch claude/new-cells-beyond-etos3t (research/frontier/beyond/graphs/), (17,5) 35,728 from branch
  claude/beyond-small-cells-fwb6si (research/squads/beyond-small/graphs/).

The solution files and edge lists were taken unchanged from those branches (git show); the sha256 in each log
identifies them.
