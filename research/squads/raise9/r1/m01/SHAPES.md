# m01 SHAPES: random-S cost statistics at D = 9 for the (17,9) and (20,9) rungs

Card m01, round 1, job raise-d9. Tool: haar_m01 = copy of research/frontier/beyond11/haar_big0.c with one added env
UNCDUMP=<file> (appends every uncovered element of every RANDORB sample, with its side). Source and binary are in this
folder (haar_m01.c, haar_m01). Command per row: `ORBIT="3 5 2" RANDORB=6 THREADS=1 UNCDUMP=unc/<key>.txt
haar_m01 17 9 60 1 1 /dev/null <sl|psl> p n` (about 2-4 s per sample at N = 2.8e8 with the machine loaded).

Cost = number of uncovered elements of a random symmetric S (both sides), i.e. what the annealer starts from.
mu from the program (N exp(-W/N), W = 4.58e9). Samples: 6 unless noted (SL(653) x Z1 has 10). Medians of 6 samples
are noisy (about +-20 %); mins are the more telling statistic.

Classes (uncovered element x = (M,z), both sides together, average per sample):
central = M = +-I; involution = order 2 in G (non-central); alpha-fixed = fixed by conj(g) x (z -> r z), not central
or involution; generic = the rest.

| group | orbit | mu | min | p10 | median | mean | central/s | involution/s | alpha-fixed/s | generic/s | samples |
|---|---|---|---|---|---|---|---|---|---|---|---|
| SL(653) x Z1 | 3 5 2 | 19.9 | 34 | 36 | 42 | 44.6 | 0.0 | 0.0 | 3.8 | 40.8 | 10 |
| SL(277) x Z13 | 3 5 2 | 17.4 | 24 | 24 | 40 | 36.3 | 0.33 | 0.0 | 2.0 | 34.0 | 6 |
| SL(313) x Z9 | 3 5 2 | 17.0 | 34 | 34 | 54 | 50.3 | 0.67 | 0.0 | 9.67 | 40.0 | 6 |
| SL(151) x Z79 (director's solved rung) | 3 5 2 | 13.2 | 2 | 2 | 38 | 29.3 | 0.67 | 0.0 | 0.67 | 28.0 | 6 |
| SL(79) x Z560 | 3 5 2 | 17.1 | 172 | 172 | 254 | 753.0 | 103.0 | 0.0 | 97.0 | 553.0 | 6 |
| SL(73) x Z711 | 3 5 2 | 17.7 | 30 | 30 | 60 | 57.0 | 22.67 | 0.0 | 1.33 | 33.0 | 6 |
| SL(157) x Z73 | 3 5 2 | 25.6 | 36 | 36 | 48 | 45.7 | 2.0 | 0.0 | 1.67 | 42.0 | 6 |
| SL(337) x Z7 | 3 5 2 | 10.0 | 12 | 12 | 20 | 20.0 | 0.33 | 0.0 | 1.67 | 18.0 | 6 |
| SL(277) x Z13 | 3 4 5 | 17.4 | 48 | 48 | 90 | 82.0 | 0.0 | 0.0 | 0.0 | 82.0 | 6 |
| PSL(349) x Z13 | 3 5 2 | 17.4 | 50 | 50 | 75 | 70.0 | 0.0 | 35.67 | 0.33 | 34.0 | 6 |
| PSL(307) x Z19 | 3 5 2 | 15.9 | 36 | 36 | 62 | 62.7 | 0.0 | 19.0 | 0.67 | 43.0 | 6 |
| PSL(191) x Z79 | 3 5 2 | 16.2 | 47 | 47 | 57 | 57.3 | 0.0 | 14.67 | 0.67 | 42.0 | 6 |
| PSL(233) x Z43 | 3 5 2 | 13.1 | 21 | 21 | 44 | 38.7 | 0.0 | 11.0 | 0.67 | 27.0 | 6 |
| PSL(197) x Z73 | 3 5 2 | 20.7 | 27 | 27 | 57 | 53.8 | 0.0 | 13.5 | 0.33 | 40.0 | 6 |
| PSL(431) x Z7 | 3 5 2 | 22.2 | 51 | 51 | 112 | 102.8 | 0.0 | 48.5 | 3.33 | 51.0 | 6 |
| PSL(821) x Z1 | 3 5 2 | 17.8 | 197 | 197 | 252 | 237.3 | 0.0 | 187.0 | 2.33 | 48.0 | 6 |

(20,9): ORBIT "3 6 2", one sample of SL(997) x Z1 (N = 9.9e8, mu 13.8): cost 26 (uncovered elements listed in
unc/sl997n1.txt). It took 112 s under load, and the program reports 1.50 GB for N = 9.9e8, over the 600 MB cap. The
card's "about 500 MB" estimate is wrong, so (20,9) needs a leaner build or a smaller N. Only one sample, so no
(20,9) statistics.

## Findings
- PSL pays the involution holes, as ODD_D_HOLES.md predicts: involution holes per sample grow with p^2 (p = 191: 15;
  307: 19; 349: 36; 431: 49; 821: 187). PSL medians are 2-5 times mu.
- SL with n = 1, 9, 13 has almost no involution or central holes (-I is the only involution). Its uncovered elements
  are nearly all generic. Central holes grow with n (n = 711: 23 per sample; n = 560: 103).
- n = 560 (composite, gcd(r-1, n) = 80) is bad: 80 alpha-fixed z values give 97 alpha-fixed holes per sample. Use n
  prime or with small gcd(r - 1, n).
- f = 5 (ORBIT "3 4 5") is worse than f = 2 on SL(277) x Z13 (median 90 vs 40).
- Mins at mu 17-20: SL(277) x Z13 24, SL(73) x Z711 30, SL(653) x Z1 34, SL(313) x Z9 34; PSL 21-50. The solved
  SL(151) x Z79 rung had min 2 in 6 samples (mu 13.2), the best of all 16 groups measured, so mins separate the
  shapes better than medians do.

## Rule for the director at D = 9, mu ~ 17-20
Use SL(2,p) x Z_n with p prime and n = 1, 9 or 13, or n prime with small gcd(r-1, n), with ORBIT "3 5 2"
(for example SL(277) x Z13 at mu 17.4, SL(653) x Z1 at mu 19.9). Avoid PSL when p > 300 (involution holes) and
composite n with large gcd(r-1, n) (n = 560).
