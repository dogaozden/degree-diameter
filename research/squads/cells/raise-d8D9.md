# raise-d8D9 round 3: beat the (8,9) record of 1,341,600 vertices

Job "raise3-8-9" (Haar worker, Haiku 5.5, 2026-10-26). Branch: claude/raise-d8d9-record-3-sqwtju.
Rounds 1 and 2 (claude/raise-d8d9-record-ogr1zr, claude/raise-d8d9-record-2-qz3qcj) ended with no new record.
Record: N = 670,800 (2N = 1,341,600), sl 25 x Z43. Target: any valid Haar graph with N >= 670,801.

## What round 2 tried (do not repeat)
- psl 47 x Z13 with ORBW=3 (2 h x 4 runs): stuck at cost 3 (involutions, odd D).
- sl 17 x Z139 (mu 34.7): stuck at 12-36.
- prod psl 5 x psl 7 x Z67, prod sl 4 x psl 7 x Z67, sl 13 x Z313, sl 8 x Z1333/Z1339, sl 7 x Z1999, sl 11 x Z511,
  sl 9 x Z937, psl 13 x Z619: screened, poor tails.
- k = 7 one-orbit structure (f = 1, m = 1): hopeless.

## Round 3 plan
1. Screen every window group with `tools/orb_screen.py 8 9 670801 690000 "3 2 2" --anyn`. Round 2 used the default
   filter (all prime factors of n = 1 mod 3), which silently dropped Z17, Z23, Z56, Z165, Z275, ...
2. Check |Fix(alpha)|. A composite cyclic factor with a prime p = 2 mod 3 forces alpha to be trivial on Z_p, and
   gcd(r-1, n) adds fixed points. sl 13 x Z308: |Fix| = 527, min 1026 in 200 samples. Ruled out.
3. Run the best survivors with the annealer on 4 cores.

## Screen results
Full window screen, `orb_screen.py 8 9 670801 690000 "3 2 2" --anyn --samples 3000` (255 candidates, ~25 min).
Ranked by (p1+p10)/2. Top rows (N, mu, |Fix|, min, p1, median):

| group | N | mu | |Fix| | min | p1 | median | round 2? |
|---|---|---|---|---|---|---|---|
| psl 47 x Z13 | 674,544 | 31.5 | 23 | 30 | 48 | 169 | yes (plateau 3) |
| psl 23 x Z111 | 673,992 | 31.3 | 35 | 30 | 78 | 413 | **new** |
| sl 29 x Z28 | 682,080 | 35.6 | 119 | 42 | 80 | 374 | new |
| sl 17 x Z139 | 680,544 | 34.7 | 17 | 42 | 126 | 520 | yes (stall 12-36) |
| prod sl 4 x psl 7 x Z67 | 675,360 | 32.0 | 8 | 48 | 108 | 1128 | yes |
| sl 23 x Z56 | 680,064 | 34.5 | 191 | 84 | 132 | 1140 | new, poor |
| psl 19 x Z199 | 680,580 | 34.8 | 8 | 54 | 132 | 822 | new, checked by hand, poor |
| sl 16 x Z165 | 673,200 | 30.9 | 2474 | 146,062 | 180,874 | 491,100 | new, dead |
| sl 13 x Z308 | 672,672 | 30.6 | 527 | 1026 (200 samples) | - | - | new, dead (|Fix| too big) |

The only SL-type group (unique involution) with a tail near the record is sl 17 x Z139, which round 2 already found
stalled. So the screen points at psl 23 x Z111 (min 30 at 3,000 samples, same as psl 47 x Z13's best). The record's
sl 25 x Z43 had min 28 and p1 66 at 1,000 samples.

## Round 3 runs (3600 s each, 1 thread, nice 5, in the scratchpad r3/)
psl 23 x Z111, ORBIT "3 2 2":
- s1: default weights
- s2: ORBW=3
- s3: ORBW=3, RESTART=1
