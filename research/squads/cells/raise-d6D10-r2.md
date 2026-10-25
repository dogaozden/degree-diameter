# raise-d6D10, round 2: notes (in progress)

Job "raise2-6-10". Record to beat: **524,160** (N = 262,080, prod sl 5 psl 7 x Z13, orbit k=3 m=2 f=0).
Round 1 ended at psl 17 x Z109 (N = 266,832, 2N = 533,664 would be a record) stuck at cost 1 in 11 of 14 runs,
never 0 (branch claude/raise-d6d10-haar-mrmqi7, research/squads/cells/raise-d6D10.md).

## Round 2, step 1: which element is the endgame miss? (DUMPFIX)

Added `DUMPFIX=1` to research/structured/haar_sym.c: when a new best energy is reached at raw cost <= 1, print the
uncovered alpha-fixed elements (dumpfix). Logs in research/structured/runs/raise_d6D10_r2/.

- Run seed 101 (ORBIT="3 2 0" ORBW=3 RESTART=1, 1500 s): first cost-1 state, uncovered fixed element
  **elem 85020 = mat(3,3,15,4), z = 0**. Trace 7, det 1, nonsplit torus; x^3 has trace -1, so x has order 9 in
  PSL(2,17). It is a generator of the fixed torus Z_9 = C(alpha).
- Seeds 102, 103: no cost-1 state in the first minutes.

(Update below as the runs finish.)
