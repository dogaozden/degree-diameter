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

RESULTS_PLACEHOLDER
