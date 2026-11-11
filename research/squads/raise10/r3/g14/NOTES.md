# g14: which product shapes to use at (5,10) and (6,10)

Measurement only (no graph beats the current values: 95,472 at (5,10), 524,160 at (6,10)). All numbers are holes (cost)
of random generator sets S, from `haar_gen3 ... RANDSAMPLE=m` (no search). mu = N exp(-W/N), W = d * sum_{i<D/2} (d-1)^(2i)
(size law, 349,525 at d=5; 2,441,406 at d=6). Raw output: samp510.txt, samp610.txt (sample.sh, mu.py, findspecs.py here).

## (5,10), d = 5, targets N ~ 48,000 (2N > 95,472)

| family (haar_gen3 spec) | N | mu | min (200) | median (200) | median (20) | median/mu |
|---|---:|---:|---:|---:|---:|---:|
| A4 x (Z239 x| Z17): `prod psl 3 meta 239 17 6 1` | 48,756 | 37.6 | 14 | 56 | 82 | 1.5 |
| Z7 x| Z3 x (Z137 x| Z17): `prod meta 7 3 2 meta 137 17 16 1` | 48,909 | 38.5 | 14 | 58 | 75 | 1.5 |
| Z1783 x| Z27: `meta 1783 27 255 1` | 48,141 | 33.8 | 11 | 67 | 52 | 2.0 |
| Z1453 x| Z33: `meta 1453 33 11 1` | 47,949 | 32.7 | 11 | 64 | 59 | 2.0 |
| PSL(2,7) x (Z97 x| Z3): `prod psl 7 meta 97 3 35 1` | 48,888 | 38.4 | 34 | 300 | 269 | 7.8 |
| Z2017 x| Z24: `meta 2017 24 122 1` | 48,408 | 35.4 | 91 | 790 | 1503 | 22 |
| SL(2,3) x (Z509 x| Z4): `prod sl 3 meta 509 4 208 1` | 48,864 | 38.2 | 696 | 7318 | 7092 | 190 |

## (6,10), d = 6, targets N ~ 263k (2N > 524,160)

| family | N | mu | min (100) | median (100) | median (20) | median/mu |
|---|---:|---:|---:|---:|---:|---:|
| Z6397 x| Z41: `meta 6397 41 503 1` | 262,277 | 23.8 | 10 | 30 | 23 | 1.3 |
| Z10501 x| Z25: `meta 10501 25 608 1` | 262,525 | 24.0 | 13 | 36 | 34 | 1.5 |
| A4 x (Z811 x| Z27): `prod psl 3 meta 811 27 7 1` | 262,764 | 24.2 | 19 | 62 | 44 | 2.6 |
| Z8053 x| Z33: `meta 8053 33 190 1` | 265,749 | 27.2 | - | - | 42 | (20 samples) |
| PSL(2,7) x (Z113 x| Z14): `prod psl 7 meta 113 14 4 1` | 265,776 | 27.2 | - | - | 83 (min 30) | 3.1 |
| SL(2,3) x (Z457 x| Z24): `prod sl 3 meta 457 24 70 1` | 263,232 | 24.7 | - | - | 117 (min 38) | 4.7 |

(The 200-sample pass at (6,10) was cut by the 110 s limit; the (6,10) rows with "-" have 20 samples only.)

## Ranking and reading

- Single Frobenius groups Z_p x| Z_k with k = 27..41 are the cleanest random-S families: at (6,10), Z6397 x| Z41 has a
  median within 1.3x of the size-law mu, and at
  (5,10) Z1783 x| Z27 and Z1453 x| Z33 are about 2x mu.
- At (5,10), A4 x F and Z7 x| Z3 x F (N ~ 48.9k) are tied at about 1.5x mu, both with min 14 among 200 samples.
  Adding PSL(2,3) = A4 is worth it; adding SL(2,3) is not: its minimum (696) is far above every other family, which
  suggests the central involution of SL(2,3) forces a structured hole set that random S cannot escape.
- PSL(2,7) x F and SL(2,3) x F are 3-8x mu at both D = 10 sizes. Use them only with the orbit or Sidon restrictions.
- Random-S statistics do not predict solves on their own: 80 s annealing (haar_gen3s, seed 7, K 8) reached cost 8 on
  Z7 x| Z3 x (Z137 x| Z17) (start 33), cost 5 on A4 x (Z239 x| Z17) and cost 5 on Z6397 x| Z41.
  None of the three solved. One 80 s run is far from the 1-cost states found by the earlier chains (r2/e07, r2/e08).

## Next

Run chains (80 s links, SAVEBEST/START) on Z1783 x| Z27 (5,10) and Z10501 x| Z25 (6,10), which had no anneal run here, and
compare their hole distributions with the Sidon-restricted sampler (r2/e14) on the same groups.

## Late addition: anneals on Z1783 x| Z27 (5,10)

Three 80 s runs (seeds 7, 8; chain links from the seed-7 best): best cost 2 (seed 7, start 32,094; seed 8 best 4;
chained link from the cost-2 state stayed at 2). The start cost of 32,094 is one unlucky random S (a generator set in a
proper subgroup, probably), not a typical value (the sampled median is 67). Z1783 x| Z27 is the closest family to a
(5,10) solve in these runs (cost 2 vs 5 for A4 x F and 8 for Z7 x| Z3 x F), but it has no solve yet.
Logs: an510_z1783.log, an510_z1783b.log, an510_z1783c.log, an510_z1783d.log; states an510_z1783*.best.
