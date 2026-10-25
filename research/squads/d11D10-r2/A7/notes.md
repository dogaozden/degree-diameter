# Card A7 (search wildcard, groups) - notes

Start 12:51:39 UTC, time box 40 min. Screens: RANDORB=30 each, through gate.sh, THREADS unset, binary
`research/structured/haar_sym` (not rebuilt, no code change). Logs in this folder: `s1_*.log` ... `s4_*.log`.

## Target and figure of merit

Vertices = 2N, N = |GROUP| x n. Range 148.8M-157.8M vertices = 74.4M-78.9M for N.
lambda = W/N with W = 1,111,111,111; mu = N e^(-lambda); clumps = mu/k; a fixed element of alpha is missed with
probability about e^(-lambda/k) (its words form alpha-orbits of size k), so expected fixed-point misses ~ |Fix| e^(-lambda/k).

| group (N) | vertices | lambda | mu | mu/5 | mu/3 | mu/10 | Fix(alpha) (predicted) | status |
|---|---|---|---|---|---|---|---|---|
| psl 243 x Z11 (main, reference) | 157.8M | 14.08 | 60.6 | 12.1 | 20.2 | 6.1 | 12 (PSL(2,3)) | reference |
| psl 89 x Z211 (our 148.7M solution) | 148.7M | 14.94 | 24.1 | 4.8 | 8.0 | 2.4 | ~44 | reference |
| psl 32 x Z2281 (N = 74,670,816) | 149.3M | 14.88 | 25.8 | 5.2 | 8.6 | 2.6 | 5 + e (S3 = SL(2,2)) | screened k=5 and k=10 |
| heis 191 x Z11 (N = 76,646,581) | 153.3M | 14.50 | 38.8 | 7.8 | 12.9 | 3.9 | 0 (+e) | screened k=5 and k=10 |
| psl 125 x Z79 (N = 77,143,500) | 154.3M | 14.40 | 42.9 | 8.6 | 14.3 | 4.3 | 60 (PSL(2,5)) | analytic only |
| psl 125 x Z78 (N = 76,167,000) | 152.3M | 14.59 | 35.2 | 7.0 | 11.7 | 3.5 | 360 | analytic only |
| heis 421 (N = 74,618,461) | 149.2M | 14.89 | 25.5 | 5.1 | 8.5 | 2.5 | 0 (+e) | not screened (see below) |
| pgl 421 / psl 421 x Z2 / sl 421 (N = 74.6M) | 149.2M | 14.89 | 25.5 | 5.1 | 8.5 | 2.5 | ~210-420 | excluded (analytic) |
| psl 41 x Z2161 (card reference, median/mu 3.9) | 148.8M | 14.93 | 24.2 | | | | ~20 | card data |

Commands used for the table above are plain arithmetic (python3 one-liner), no haar_sym run.

## Why these candidates

- Conjugation-type alpha of order 5 on PSL/PGL/SL(2,p) with p prime (about 421): an element of order 5 lies in a split
  torus of order (p-1)/2 or p-1 (about 210-420), so Fix(alpha) is about 210-420 and the expected misses are about 10+.
  Excluded without a run.
- prod psl 41 x psl 13 x Z2 (about 75.2M): PSL(2,13) has no element of order 5, so alpha = (g, e) and Fix contains
  C(g) x PSL(2,13), about 21,000 elements. Excluded.
- Field automorphisms: Frobenius of order 5 on PSL(2,2^5) = SL(2,32) has fixed subgroup SL(2,2) = S3 (6 elements).
  With n = 2281 (prime, 2281 = 1 mod 5), N = 74,670,816 and the Z_n part gets z -> r z with r of order 5 mod 2281
  (chosen by choose_alpha, gcd(r-1, 2281) = 1), so Fix = 5 + e. For k = 10 the Z_n multiplier is r = 2280 (= -1, order 2),
  which gives alpha of order 10 (AR=2280 given explicitly, since the automatic choice would pick order 5).
  This is the best combination of mu and Fix found in this round.
- heis q (Heisenberg over GF(q)), scaling alpha (a,b,c) -> (zeta a, zeta b, zeta^2 c) with zeta of order k: the only
  fixed element is e (k = 5 and 10 both). heis 191 x Z11 is in range (76.6M). heis 421 (74.6M) has no cyclic subgroup of order
  <= 63 (every non-identity element has order 421), so haar_sym falls back to H of order 1 (N one-bit rows, very slow). Not screened.
- k = 3 (PSL(2,125) x Z_n, Frobenius of order 3): clumps mu/3 = 11.7 to 14.3, worse than the k = 5 psl 243 reference (12.1).
  Fix = 60 (or 360 for n = 78). Predicted total clumps about 14.5-15. Not screened.
- Metabelian families (meta, agl1): large abelian normal subgroup; not screened.

## Screens (RANDORB=30)

All four runs finished normally (full RANDORB lines in the logs; none was killed by the 13:24 stop). Slot time used: about 1.5 min
of the 8 allowed. Gate call form: `gate.sh 300 env -u THREADS ...` with haar_sym unchanged. Cost = uncovered B-side elements.

| run (log) | command (haar_sym args `11 10 60 5 8 /dev/null GROUP n`) | N | Fix (+e) | mu | min | p10 | median | median/mu | mean | time |
|---|---|---|---|---|---|---|---|---|---|---|
| s1 | `ORBIT="5 2 1" AFROB=1` psl 32 2281 (Frobenius order 5, Z_n multiplier auto, order 5) | 74,670,816 | 5 | 25.75 | 35 | 55 | 80 | 3.1 | 953 (one large outlier) | 13.5 s |
| s2 | `ORBIT="5 2 1"` heis 191 11 (scaling zeta of order 5, r = 3 on Z11) | 76,646,581 | 0 | 38.79 | 18,425,580 | 18,457,380 | 21,060,485 | 5.4e5 | 23,245,375 | 4.9 s |
| s3 | `ORBIT="10 1 1" AFROB=1 AR=2280` psl 32 2281 (alpha = Frobenius x (z -> -z), order 10) | 74,670,816 | 5 | 25.75 | 74,048,832 | 74,048,834 | 74,049,008 | 2.9e6 | 74,110,396 | 7.0 s |
| s4 | `ORBIT="10 1 1" AR=2` heis 191 11 (zeta of order 10, r = 2 on Z11) | 76,646,581 | 0 | 38.79 | 76,273,920 | 76,273,920 | 76,273,920 | 2.0e6 | 76,318,744 | 4.3 s |

Reading the numbers:
- s1 is the only run with ordinary samples: median 80 = 3.1 mu (median/k = 16 clumps against mu/k = 5.2). The reference
  psl 243 x Z11 (k = 5) has median/mu about 1.1 and psl 89 x Z211 about 1.4. So PSL(2,32) x Z2281 has the same mixing defect the
  card reports for psl 41 x Z2161 (large cyclic factor). Its minimum 35 (1.4 mu) is inside the psl 243 minima range
  (31-51), but the typical sample is twice as bad as psl 243's and more than twice as bad as psl 89 x Z211.
- s2 (heis, k = 5): every sample is degenerate, covering about 72 % of B side at the median and 76 % at best; fixed-point count
  is 0 as predicted, but nilpotent structure kills the covering.
- s3 (Frobenius, k = 10): covers 0.8 % of B side in every sample. Not diagnosed. One observation: alpha^5 = (id, -1) maps
  (x, z) to (x, -z), so S contains both, which may be the cause (untested).
- s4 (heis, k = 10): covers 0.5 % in every sample.

Not screened (analytic reasons, all in the table above or below):
- pgl 421, psl 421 x Z2, sl 421 (N about 74.6M): an order-5 conjugation has a torus centralizer, so |Fix| is about 210-420 and
  the expected misses are about 10 or more.
- prod psl 41 psl 13 x Z2 (about 75.2M): PSL(2,13) has no element of order 5, so alpha = (g, e) and Fix contains
  C(g) x PSL(2,13), about 21,000 elements.
- psl 125 x Z79 and psl 125 x Z78 (k = 3, Frobenius of order 3): mu/k = 14.3 and 11.7 against 12.1 for the psl 243 reference;
  Fix = 60 and 360.
- heis 421 (N = 74,618,461, Fix 0, mu 25.5): every element has order 421, so haar_sym falls back to a cyclic subgroup of
  order 1 (about 74.6M one-bit rows), too slow for a screen. Not run; the heis result at N = 76.6M makes it unpromising.
- meta, agl1: solvable with a large abelian normal subgroup. Not run.

Conclusion: none of the screened groups or automorphisms gives median/mu near 1. The best, PSL(2,32) x Z2281 with k = 5, is
worse on mixing than psl 89 x Z211 (our 148.7M family) and psl 243 x Z11, so it is not worth annealing. Heis with a scaling
alpha and the k = 10 Frobenius variant are degenerate. No VALID graph was produced (score 0).
The coordinator reports the cell solved at 157,835,304 (k = 10, AR = 3, psl 243 x Z11); I have not re-checked that.
