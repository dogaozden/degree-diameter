# c4: alpha-closed Delta=7 families in PSL(2,q) x Z_m (alpha(x,z) = (w x w^-1, r z))

Files: gen_c4.py (generator, prints 7 lines), screen.py (enumeration/sampling on q-list via haar_ecc),
rescore.py (top-K on q=23,31,41), full_m{7,13,19,37}.json (family_score --qrange 23 113 --json), m1_screen.jsonl,
m{7,13,19,31,37}_s23.jsonl (screens), m*_top.jsonl (rescored top lists).

Setup: X, Y in SL(2,Z) with entries in [-2,2] up to sign (26 reps each), t = 1 WLOG (z -> t^-1 z commutes with alpha),
u in 1..m-1 or r/r^2, r = either order-3 root mod m. Random samples: 500 (m=7,13,19), 200 (m=31,37) of the
about 676*2m candidates; not exhaustive. Many candidates are disconnected (m=7: about 1 in 25 connected).

Results (excess = diam - log_6(|PSL| m); 22 primes in [23,113] for full scores; "screen" = mean over q=23,31,41):

| m  | best screen (q=23,31,41) | full mean_excess | best full family |
|----|--------------------------|------------------|------------------|
| 1  | 2.982 (of all 676)       | 3.69             | X=0,1,-1,-2 Y=1,-2,0,1 (m=1) |
| 1  | random gen_random_orb 1 2 SEED: seeds 1,2,3 | 3.054, 3.236, 3.054 | (baseline) |
| 7  | 2.896                    | 3.331            | X=2,1,-1,0 Y=1,2,0,1 u=2 r |
| 13 | 2.883                    | 3.122            | X=2,1,-1,0 Y=1,1,-2,-1 u=6 R |
| 19 | 2.672                    | 3.274            | X=0,1,-1,-2 Y=1,0,2,1 u=7 R |
| 31 | 3.065                    | not run          | X=2,1,-1,0 Y=1,0,1,1 u=17 R |
| 37 | 2.966                    | 3.493            | X=1,2,-1,-1 Y=1,1,-1,0 u=28 r |

Reading: screening on three primes is optimistic by about 0.3-0.8 relative to the full 22-prime mean (selection bias).
The best full family per m is 3.12-3.49, and the random m=1 baseline is 3.05-3.24. The cyclic factor does not lower
the excess of these uniform families below the random m=1 baseline. It does lower the excess relative to the best
screened m=1 integer family (3.69 full). No monotone trend in m.
