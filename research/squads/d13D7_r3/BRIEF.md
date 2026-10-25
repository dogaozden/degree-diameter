# Squad round 3 (job cell-13-7): beat 397 pairwise-opposite points of H(11)

Same problem, scorer, tools and machine rules as round 2: READ research/squads/d13D7_r2/BRIEF.md FIRST (the problem,
the affine model, the coset graph, oppcheck, fiblift, rules, output format). Every extra point = +2 vertices of our
(13,7) graph (1,062,936 + 2|R|). Write only inside research/squads/d13D7_r3/<card>/, scoreboard
research/squads/d13D7_r3/scoreboard.jsonl, best set as <card>/best_idx.txt (point indices, checked with oppcheck).

**What round 2 found (all verified by Opus):**
- 397 points (research/squads/d13D7_r2/c6/best_idx.txt) by LARGE NEIGHBOURHOOD SEARCH (c6, code
  research/squads/d13D7_r2/c6/lns.c, documented in its header; usage `lns HEXFILE INIT_IDX OUT_IDX CPU_SECONDS SEED
  [MODE CMAX JMAX GMAX PFIBER NODELIMIT]`). Key move: the 320 fibration set (e4 + 29 affine lines) was not 1-swap
  optimal: removing e4 freed 90 points at infinity (x0 = 0) blocked only by e4, of which 62 are pairwise opposite
  (+61); LNS then reached 397 and plateaued.
- 364 points (research/squads/d13D7_r2/c4/best_idx.txt) as a union of orbits of a cyclic subgroup of order 44 of
  O(7,11) (code research/squads/d13D7_r2/c4/orbit_union.py; generator not saved). Orders 55 -> 362, 110 -> 340.
- Clique searches in the coset graph never beat 29 lines; other fibrations, symmetric cliques and line-stars gave
  nothing.
Useful facts: a point x at infinity (x0 = 0, x != e4) is orthogonal exactly to the affine points on an affine
hyperplane H_x of F_11^5; points at infinity are pairwise orthogonal iff their images in e4^perp/e4 = Q(4,11) (a GQ)
are collinear, so at most 122 points at infinity can be used. For x in R, its "private candidates" are the points
blocked only by x (cnt = 1 in lns.c terms); a point with many private candidates is a good removal target.

Machine: as in round 2 (OMP_NUM_THREADS=1, `timeout 900 nice -n 10`, internal CPU limit <= 600 s per run, <= 1.5 GB,
no git). The machine is busy (Opus runs a 4-thread check), so prefer CPU-time limits (clock()) to wall-clock ones.
