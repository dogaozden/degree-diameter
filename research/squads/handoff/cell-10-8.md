# Handoff: job cell-10-8 ((10,8), table 1,176,480), state at 2026-10-25 16:05 UTC

Branch: `claude/bipartite-10-8-cell-um2c1t` (PR #353, draft), which contains the first session's branch
`claude/cell-10-8-search-t6pwvg` merged with master.

- Not beaten. Best: cost 6 (four states; sets in the `CHAIN ... min 6` lines of research/d10D8/runs/*F15W3*.log).
- Notes: research/squads/cells/d10D8.md (status at the top, §8 second session, §9 what to do next).
- To resume the search: build `research/d10D8/sym2/haar_sym2.c` (gcc -O3 -march=native -fopenmp -lm), then per core
  `research/d10D8/launch.sh d10D8_psl_23_97_orb3_F15W3_s<N> <N> "psl 23 97" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3`
  (or the group "prod psl 7 sl 8 7"). Expected cost: about 55 CPU-hours to the first cost-0 set (factor 5 either way).
  A cost-0 set is written to runs/<TAG>.txt after haar_sym2's full check; then run `research/d10D8/verify.sh`.
- Squad rounds: research/squads/d10D8-r1, -r2, -r4 (r3 was briefed only); LOG.md has all of them.
