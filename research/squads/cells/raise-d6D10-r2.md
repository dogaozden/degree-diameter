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
- Seeds 102, 103 (20 min each): cost 3 (one free orbit) all the time, no cost-1 state.
- So the cost-1 valley is rare in this batch. Seed 101 reached it once in 1500 s.

## Step 2: is the torus element structurally missed? (FIXHIST)

Added `FIXHIST=1` (with RANDORB): counts, per alpha-fixed element, how often a random symmetric S leaves it
uncovered. 4000 samples each:

| group | |Fix| (+e) | per-element uncovered rate | random median cost | random min |
|---|---|---|---|---|
| psl 17 x Z109 (N 266,832, mu 28.4) | 8 (+e) | 0.19 for every element, e included | 407 | 6 |
| prod sl 5 psl 7 x Z13 (N 262,080, mu 23.6, record) | 17 (+e) | 0.23 for every element | 292 | 3 |

So under random S the torus element is not special. The fixed points are not what separates psl 17 from the
record; the free-orbit part has the larger mu (9.5 vs 7.9 expected missed orbits), and the annealer does not find
a zero.

## Step 3: tails of the untried candidates (RANDORB 3000, one core)

| group | N | mu | min | p1 | p10 | median |
|---|---|---|---|---|---|---|
| psl 19 x Z79 | 270,180 | 32.2 | 12 | 25 | 66 | 357 |
| prod psl 5 sl 4 x Z73 | 262,800 | 24.3 | 9 | 33 | 129 | 2178 |
| prod psl 5 sl 5 x Z37 | 266,400 | 27.9 | 10 | 32 | 93 | 1718 |
| psl 13 x Z247 | 269,724 | 31.6 | 27 | 76 | 234 | 1703 |
| psl 11 x Z403 | 265,980 | 27.4 | 53 | 144 | 376 | 2914 |
| sl 8 x Z523 | 263,592 | 25.0 | 156 | 334 | 697 | 5265 |
| psl 9 x Z733 / Z739 | 263,880 / 266,040 | 25.3 / 27.5 | 405-580 | ~900 | ~3000 | ~33000 |
| sl 7 x Z787, pgl 7 x Z787 | 264,432 | 25.9 | 993 / 1153 | | | |
| prod psl 3 psl 9 x Z61 | 263,520 | 25.0 | 15 | 54 | 319 | 175,680 |

Nothing has a better tail than the record group. psl 19 x Z79 is close to psl 17 x Z109 but has a larger mu.

## Step 4: ENDG, the exhaustive one-orbit scan

Added `ENDG=1` (with `ENDGC=c`): whenever a new best energy is reached at raw cost <= c, the current state is
checked against every valid orbit replacement of each slot (about 89 k representatives per slot, about 40 s). Test
on psl 17 with ENDGC=3: 88,940 orbits per slot, best raw 3 (no zero). Found nothing at that state.

ENDG batch (4 seeds, 2400 s each, plateau scan at raw cost <= 3, at most 10 scans per run, 5000 steps apart):
- 40 scans in total. In 12 of them the best one-orbit neighbour of the state was cost 1; in 28 it was cost 3.
  No neighbour was cost 0 (over 40 x 2 x 88,940 orbit replacements).
- All 4 runs ended at best 3 after about 1.2e7 evaluations each.

## Tally for round 2

- Runs: 3 DUMP runs (1500 s), 1 ENDG test, 4 ENDG runs (2400 s): about 7.5e7 orbit evaluations on psl 17 x Z109.
  Round 1 added about 1.4e8 on the same group.
- Solutions above 524,160: **none.** Nothing was added to research/frontier/sols/.
- Screen of the window 262,081 to 272,400 (RANDORB 2000, partial, cut short): research/structured/runs/raise_d6D10_r2/screen_window_partial.txt.

## Decision

I stopped here. The cell has not been proved stuck, but these methods give no zero:
- psl 17 x Z109 is at a floor of cost 1 to 3 (one free orbit or one fixed element missed). Random S shows the fixed
  elements are missed uniformly (about 19 %), so no element is structurally blocked. The exhaustive one-orbit
  neighbourhood of the floor has no cost-0 member.
- The other candidates in the window have worse tails or larger mu than the record group.

Suggested next steps for a later session (not done here):
1. Exhaustive two-orbit moves at the cost-1 floor (pairs from the best 1-orbit neighbours), which the one-orbit scan
   does not cover.
2. A route-chart or voltage lift (research/theorems/BEAT_16_5_SQUAD.md) for (6,10); the orbit search at this mu does
   not reach zero in these runs.
