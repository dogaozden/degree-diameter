# c3b-sl23x49 notes (descents on SL(2,23) x Z49, relaunch of c3)

Started 2026-10-31 21:56 UTC. Target N = 595,056 (2N = 1,190,112), ORBIT "3 3 1", units ORBW (energy), seeds 108451-108499.

## Plan (one heavy process at a time, all queued by driver.sh and screen.sh)
1. d1: F15W3 (RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3), sl 23 49, seed 108451, 4000 s (~67 min). Log d1.log.
2. d2: same with ORBW=2, seed 108452, 1200 s. Log d2.log.
3. d3: same with ORBW=4, seed 108453, 1200 s. Log d3.log.
4. screen.sh (after driver.done): RANDORB=1000 on sl 13 271, sl 9 823, sl 8 1171, sl 7 1753, sl 7 1777, sl 5 4903,
   sl 5 4921, sl 7 1783 (seeds 108461-108468). These are the SL(q) x Z_n groups of the window with q >= 5 from
   c4-groups/candidates.tsv; c4 screens the whole list in N order, so these are the ones it reaches last or not at all
   for q >= 7. sl 2 and sl 3 are left to c4.

## Tools
- `haar_c3b` = research/d10D8/sym2/haar_sym2.c plus one mode (EVALSET, source haar_c3b.c, same search code):
  `ORBIT="3 3 1" ORBW=3 EVALSET="<10 element indices, e first>" ./haar_c3b 10 8 1 1 8 /dev/null sl 23 49`
  prints `EVAL raw=R fixmiss=F energyW2 energyW3 energyW4`. Checked: the CHAIN 1 state of c3's sl23_49.log gives
  raw 16, fixmiss 1, energyW3 18, as logged. Use it to re-score chain states in raw units (ORBW=1) for comparisons.
- `driver.sh`, `screen.sh`: queues (see above). `chains.py`: c3-twist/tools/chains.py (chain-minimum summary).

## Reference numbers (from other folders)
- psl 23 97, F15W3 ORBW=3 (c3-twist and c1 notes): chain minima median 18-21, P(min <= 9) about 1 in 15.
- sl 23 x Z49 RANDORB=1000 (c3 notes): min 47, p1 58, p10 82, median 132, mu 70.4, |Fix alpha| = 23.
- c3's 6 sl 23 x Z49 descents: minima 18, 18, 24, 24, 27, 27 (median 24).

## Results
(filled in below as runs finish)

### Status 01:27 UTC (Nov 1): driver.sh ended after d3 (23:42) but never wrote driver.done (cause not found), so
screen.sh waited forever. Killed it; the screens ran by hand as screen2.sh (seeds 108461-108468). All my runs are finished.

## Results

### Descents (F15W3, sl 23 x Z49, seed 108451 / 108452 / 108453; d*.log, eval tables d*.eval.tsv)
| run | ORBW | seconds | descents | min | median | mean | P(<=15) | P(<=12) | P(<=9) |
|---|---|---|---|---|---|---|---|---|---|
| d1 | 3 | 4000 | 88 | 12 | 24 | 24.4 | 2/88 | 1/88 | 0/88 |
| d2 | 2 | 1200 | 26 | 17 | 23 | 23.9 | 0/26 | 0/26 | 0/26 |
| d3 | 4 | 1200 | 24 | 18 | 24 | 23.9 | 0/24 | 0/24 | 0/24 |
Reference (same schedule, ORBW=3, c1-grind/g1.log, psl 23 97, still running, 294 descents, nice 15): min 9, median 21,
mean 20.2, P(<=15) 47/294 = 0.16, P(<=12) 12/294 = 0.041, P(<=9) 3/294 = 0.010. Second group (g2, prod psl 7 sl 8 7,
289 descents): median 21, P(<=12) 7/289. Eval rate: d1 1379 evals/s, g1 1405 evals/s (same load, close).

Conclusion: sl 23 x Z49 is NOT at least as good as psl 23 97 per chain. Its chain-minimum distribution is shifted up by
about 3 units (median 24 vs 21), and P(<=15) is 2/88 vs 0.16. The condition for the extra F15W3 run to 03:15 UTC is not
met, so I did not start it.

ORBW 2 and 4: each weight has its own units. Re-scored with haar_c3b (EVALSET, raw uncovered count):
ORBW=3 chains: raw min 12, median 24 (n 88). ORBW=2: raw min 16, median 22 (n 26). ORBW=4: raw min 18, median 23 (n 24).
No weight is clearly better at 20-67 minutes and 24-88 descents. Keep ORBW=3 (the reference weight).

### RANDORB=1000 screens (ORBIT 3 3 1, ORBW=3; rand_*.out)
| group | N | mu | min | p1 | p10 | median | |Fix alpha| |
|---|---|---|---|---|---|---|---|
| sl 23 x Z49 (c3, reference here) | 595,056 | 70.4 | 47 | 58 | 82 | 132 | 23 |
| sl 13 x Z271 | 591,864 | 66.7 | 49 | 102 | 154 | 306 | 11 |
| sl 9 (poly x^2+1) x Z823 | 592,560 | 67.5 | 155 | 225 | 424 | 1198 | 17 |
| sl 8 (poly x^3+x+1) x Z1171 | 590,184 | 64.8 | 155 | 261 | 445 | 1135 | 8 |
| sl 7 x Z1753 | 589,008 | 63.5 | 429 | 664 | 1305 | 4375 | 5 |
| sl 7 x Z1777 | 597,072 | 72.8 | 526 | 798 | 1344 | 4164 | 5 |
| sl 7 x Z1783 | 599,088 | 75.3 | 357 | 709 | 1387 | 4548 | 5 |
| sl 5 x Z4903 | 588,360 | 62.8 | 4071 | 5835 | 9708 | 34362 | 5 |
| sl 5 x Z4921 | 590,520 | 65.2 | 3219 | 6198 | 10110 | 36657 | 5 |
(psl 23 x Z97 reference from c3: min 36, p1 51, p10 81, median 136.)
Only sl 23 x Z49 and sl 13 x Z271 are in the usable range, and sl 13 x Z271 is far worse (median 306). Large n with
small q (sl 5, sl 7) is hopeless: the Z-part makes too many words collide. Nothing new to descend on.

### Scoreboard
- 21:57 first result: chain min 27 (ORBW=3). Best of run: chain min 12 (d1 chain 61, ORBW=3), logged at 01:26.
  Intermediate lines (21, 18, 15) were not logged; the 12 line says so.

## Verdict and what I would try next
- sl 23 x Z49 F15W3 is worse than psl 23 97 per chain (median 24 vs 21 over 88 vs 294 descents). The RANDORB medians
  (132 for sl 23 x Z49 vs 136 for psl 23 x Z97) did not predict the descents (24 vs 21). Drop it.
- The other sl(q) x Z_n in the window (q = 5, 7, 8, 9, 13) are all far worse in RANDORB.
- Untested: psl 23 x Z97 variants with different ORBW are c1/c7 territory; not repeated here.

## Processes
- None of mine is running. d1, d2, d3, screen2.sh (8 screens) all finished. The psl runs g1/g2 are c1's.
