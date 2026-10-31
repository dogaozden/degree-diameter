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
