# h13: same-side ball growth and uncovered elements for random S (Delta = 4)

Script: `ball.py` (BFS on the full Haar graph H(G,S), level-synchronous numpy; `summ.py` = 30-seed summaries).
Outputs: `out_*.txt` (8 seeds, per-seed balls), `summary_30seeds_all.txt`, `summary_F907_151.txt`.
Setup: S = {e} + 3 uniform random non-identity elements; 30 seeds per group (12 for N = 136,957); both sides
(A from (e,A), B from (e,B)); balls X_t = #same-side vertices within distance t, t even; "uncovered" = same-side
vertices at distance > 10. Model: W_t = non-backtracking same-side walks of length <= t = 1 + sum_{j even, 2..t} 4*3^(j-1)
(W_8 = 9,841; W_10 = 88,573), mu_model = N exp(-W_10/N). Types: identity, central (+-I x Z_n in SL), other.

## Table (A side; medians over seeds unless stated)

| group | N | mu_model (t=10) | uncov@10 median | mean | min (either side) | median/mu | X_6/model | X_8/model | X_10/model | involution (non-central) | central holes (median) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Z4801 x| Z3 (k=3) | 30.7 | 12,032 | 11,705 | 10,820 | 392 | 0.35 | 0.15 | 0.17 | 0 | 0 |
| Z2003 x| Z7 (k=7) | 25.3 | 99 | 221 (pooled) | 18 | 3.9 | 1.00 | 0.94 | 1.00 | 0 | 0 |
| Z1093 x| Z13 (k=13) | 27.9 | 44 | 99 (pooled) | 8 | 1.6 | 1.00 | 0.99 | 1.00 | 0 | 0 |
| Z761 x| Z19 (k=19, the (4,11) winner) | 31.6 | 34 | 384 (pooled) | 6 | 1.1 | 1.01 | 1.00 | 1.00 | 0 | 0 |
| SL(2,13) x Z7 | 15,288 | 46.6 | 241 | 774 (pooled) | 59 | 5.2 | 0.93 | 0.89 | 0.99 | 0 | 3.5 |
| SL(2,23) x Z1 | 12,144 | 8.3 | 41 (A) / 36 (pooled) | 420 (pooled) | 0 | 4.3 | 0.98 | 0.92 | 1.00 | 0 | 0 |
| Z907 x| Z151 (k=151, 12 seeds) | 71,733 | 77,085 | 79,543 | 71,082 | 1.07 | 1.00 | 0.99 | 0.92 | 0 | 0 |

"pooled" = both sides in one list (mean/min are over seeds x sides). X_t/model columns are medians of the per-seed A-side
ratio X_t / (N(1-exp(-W_t/N))). Every entry of "other" accounts for >95 % of uncovered elements; involutions other than
-I do not exist in these groups (SL(2,p) has the unique involution -I; Frobenius groups of odd order have none).

## Conclusion

The Frobenius groups are better in the typical random S, not only in the best one. With Z_p x| Z_k and k = 13 or 19,
the median number of uncovered elements at radius 10 is 1.1-1.6 times the size-law mu, while SL(2,p) x Z_n sits at 4-5
times mu (median 41 against mu 8.3 for SL(2,23); 241 against 46.6 for SL(2,13) x Z7). The gap is in the middle levels:
at t = 8 the Frobenius balls reach 0.99-1.00 of the iid model, while SL(2,p) loses 8-11 % of its level-8 ball to
collisions, and those collisions carry to the end as the 4-5x excess. The end-level ball ratios look alike (about 1.0 in
all groups) only because mu is small relative to N; the uncovered counts show the difference. Involution and centre holes
are not the explanation: no non-central involutions exist in these groups, and the central holes are 0-3.5 per side in the
median. The k dependence is sharp: k = 3 is catastrophic (X_8 at 0.15 of the model, since 1 + r + r^2 = 0 in Z_p makes
length-8 words collide heavily), k = 7 is mildly worse (0.94 at t = 8, median 3.9 mu), and k = 13, 19 are neutral.
The mean is dominated by a heavy tail of bad S (max 7,802 for k = 19 against median 34), so search that starts from
the body of the distribution (median or min) is what turns the gap into a solution.

Caveats: 30 seeds per group, one Delta (4), radius-10 same-side balls only (the cross-side and A-B odd-distance conditions were not
measured). The k = 151 group (N = 136,957) is in the W/N < 1 regime where nothing solves, so it only shows the model holds there.
