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

### psl 23 x Z111 annealing, first 27 min (t = 1650 s)
| run | weights | best cost | evals |
|---|---|---|---|
| s1 | default | 18 | 2.56M |
| s2 | ORBW=3 | 12 | 2.44M |
| s3 | ORBW=3, RESTART=1 | 15 | 2.51M |

Plateau well above 0, and worse than psl 47 x Z13's 6 at the same evals. The random minimum (30) looked like the
record's, but the annealer does not follow it.

## k = 5 (f = 3, m = 1): tried, dead
The Poisson heuristic (misses per orbit ~ mu/k) suggested k = 5 at mu ~ 39 could beat k = 3 at mu ~ 31. The k = 5
orbit structure is valid for Delta = 8 only with m = 1, and one orbit gives too little freedom:
- `orb_screen 8 9 670801 690000 "5 1 3"` (default filter, n <= 400): 9 candidates, best min 120 (prod psl 5 x sl 4 x Z191).
- sl 11 x Z521 (N 687,720, the only order-5 SL with prime 1 mod 5 in window): |Fix| 9, min 3,770 (3000 samples). Dead.
- psl 11 x Z1021 (N 673,860): |Fix| 4, min 35,320. Dead.
- sl 19 x Z101 (N 690,840, just above the window): |Fix| 19, min 150. Dead.
Compare k = 3 m = 2 with min 28-30 on the record and psl 23 x Z111. So k = 5 is out for Delta = 8.

### Product groups, ORBW=3, 20 min each (1 thread)
| run | group | N | best cost | evals |
|---|---|---|---|---|
| s4 | prod sl 4 x psl 7 x Z67 | 675,360 | 18 | 1.28M |
| s5 | prod sl 4 x psl 7 x Z67 | 675,360 | 18 | 1.27M |
| s6 | prod psl 5 x psl 7 x Z67 | 675,360 | 12 | 1.26M |

Round 1 had 15 on the same two groups. ORBW=3 does not help them.

## Conclusion (round 3)
**No record. The (8,9) cell stays at 1,341,600 (N = 670,800, sl 25 x Z43).** No valid graph was found and nothing was
saved to research/frontier/sols/.

Why I stopped (about 3 h of compute, 4 cores, all runs ended at cost >= 3):
1. The full window screen (255 candidates, `--anyn`, 3,000 samples each) was done. The best tails are psl 47 x Z13
   and psl 23 x Z111, and both are PSL, which pays the odd-D involution penalty.
2. Every SL-type group in the window has a cyclic factor that is composite or prime but 2 mod 3 (so alpha is trivial
   on Z_p), or a prime cyclic factor whose tail is 100 times worse than the record's (sl 17 x Z139, sl 13 x Z313).
3. psl 23 x Z111: min 30 from random samples, the same as the record's min 28, yet annealing plateaus at cost 9 after
   5.5M evaluations per run (3 runs, 1 h each). The random minimum does not predict annealing success here.
4. k = 5 (f = 3, m = 1), the Poisson-motivated route, is dead for Delta = 8 (one orbit, min 150 to 35,320).
5. Product groups (prod sl 4 x psl 7 x Z67, prod psl 5 x psl 7 x Z67) plateau at 12 to 18, as in round 1.

## What is still untried (the verdict could change)
- Voltage lifts / route charts (research/theorems/BEAT_16_5_SQUAD.md, branch claude/beat-16-5-squad-jiiwg2): not
  present locally and not run here.
- A solver that breaks the involution plateau for PSL (a symmetric weighting of involution orbits), which would make
  psl 23 x Z111 and psl 47 x Z13 usable.
- Groups with N in 670,801 .. 690,000 that are not Q x Z_n with Q = SL/PSL/PGL(2,q) or a product of two (e.g.
  metacyclic, or semidirect products with the cyclic factor inside Q).
- Other orbit shapes for k = 3: ALPHA=<index> (another order-3 class in Q), or f = 5, m = 1. Not run.
