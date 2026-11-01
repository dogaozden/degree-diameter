# c4-groups (squad handsoff-108): screen of direct-product groups for N in [588241, 600000]

Goal: a Haar graph with Delta 10, D 8, N = |Q| n >= 588241 (2N > 1,176,480). Card: `../cards.md` (c4-groups).
Work started 21:45 UTC, all runs are plain `haar_sym2` (`research/d10D8/sym2/haar_sym2`), ORBIT="3 3 1".

## What was done
1. `enumerate_groups.py` -> `candidates.tsv`: 3850 groups Q x Z_n with N in the window (k = 3).
   Families: sl q (257), pgl q (257), psl q, q odd (123), agl1 q (413), prod of two base groups (736; meta not in
   products), meta p k r (p prime, k | p-1, k >= 3, one group per (p, k): 2064 with n mixed in). n = 1 or all primes
   of n = 1 mod 3 (orb_screen's rule). Heisenberg, cyc, tpgl, csl: not in this card's list (c3 and c7 cover twists).
2. `screen.py` (resumable): `ORBIT="3 3 1" RANDORB=S ORBW=3 haar_sym2 10 8 1 108501 8 /dev/null <spec>`, one process
   at a time, nice 10, timeout 120 s. Output `screen300.tsv` (300 samples, 473 non-meta groups with n <= 5000),
   `recheck1000.tsv` (1000 samples, the top 30 of the 300-sample ranking), `pilot_big.tsv` (100 samples, 40 random
   groups with n > 5000), `pilot_meta.tsv` (100 samples, 14 meta groups). `rank.py <file> [top]` ranks by
   (p1+p10)/2/mu (lower is better; mu = N e^(-5380840/N)).
3. Reference, same seed 108501, RANDORB=1000: psl 23 97: min 38, p1 55, p10 78, median 138 (card: 36/52/84/135).

## Ranking (RANDORB=1000, the top 30 of the 300-sample screen; plain uncovered units)
| rank | group | N | mu | fix | min | p1 | p10 | median | score (p1+p10)/2/mu |
|---|---|---|---|---|---|---|---|---|---|
| 1 | prod psl 7 pgl 8 x Z7 | 592704 | 67.6 | 26 | 31 | 51 | 73 | 133 | 0.917 (same group as the grind's prod, PGL(2,8)=SL(2,8)) |
| 2 | prod psl 7 sl 8 x Z7 | 592704 | 67.6 | 26 | 31 | 52 | 74 | 124 | 0.932 (grind group) |
| 3 | **psl 29 x Z49** | 596820 | 72.5 | 14 | 45 | 58 | 81 | 135 | 0.959 (NEW: descents run 1) |
| 4 | sl 23 x Z49 | 595056 | 70.4 | 23 | 36 | 54 | 81 | 129 | 0.959 (c3/c3b own it, not run here) |
| 5 | **psl 27 x Z61** | 599508 | 75.8 | 26 | 39 | 61 | 96 | 163 | 1.035 (NEW: descents run 2) |
| 6 | pgl 23 x Z49 | 595056 | 70.4 | 23 | 42 | 61 | 85 | 159 | 1.037 |
| 7 | psl 23 x Z97 (reference) | 588984 | 63.5 | 11 | 38 | 55 | 78 | 138 | 1.048 |
| 9 | prod sl 4 x psl 27 x Z1 | 589680 | 64.2 | 80 | 45 | 65 | 95 | 172 | 1.246 |
| 10 | prod psl 5 x psl 27 x Z1 | 589680 | 64.2 | 80 | 41 | 66 | 99 | 177 | 1.285 |
| 11 | prod pgl 3 x sl 8 x Z49 | 592704 | 67.6 | 26 | 47 | 69 | 106 | 236 | 1.294 |
| 17 | psl 17 x Z241 | 589968 | 64.5 | 8 | 54 | 75 | 115 | 210 | 1.472 (card: bad) |
Full 1000-sample list: `recheck1000.tsv`. Other rows of the 300-sample screen: `screen300.tsv`.

Reading: psl 29 x Z49 has the same absolute cost as psl 23 x Z97 but a 14 % larger mu, so its median/mu (1.86)
is better; psl 27 x Z61 has the smaller duplicate rate that cell notes section 5 predicts (PSL(2,27) x Z61 3.7 %
vs psl 23 x Z97 5.9 % generic loss), but a bigger mu (75.8). Neither beats the reference in RANDORB alone.

## What was ruled out (by screen or pilot)
- n > 5000 (1308 groups, 40-group pilot at 100 samples): every pilot group has median cost 92k to 520k (mu 63-75).
  Q is too small for the Z-part (|Q| < 150 when n > 4000). Not screened further.
- 500 < n <= 5000 (360 groups, all screened at 300 samples): all in the table; nothing new below rank 3.
- Meta groups (2064 in the list): slow path. haar_sym2 finds no cyclic subgroup of order 64..63 in meta groups
  ("wide rows: no cyclic subgroup of order >= 64 found"), so one sample costs about 0.2 s instead of 0.003 s;
  a 300-sample screen of one meta group took 8-20 s. Pilot (100 samples): k = 3 with n = 1: median cost
  543k-569k (broken: almost every element uncovered). k = 4..8, n = 1: median 3.4k (p = 118801, k = 5), 38.9k
  (p = 73609, k = 8), 283k, 543k. Not screened in full (n > 1 meta: 1311 groups, not run).
- agl1 q with n in the window: 28 of 413 screened (n <= 5000); the rest n > 5000, as above.
- Groups with n = 1 mod 3-prime-free Z-part and no order-3 conjugation: fail in choose_alpha ("no conjugation of
  order dividing 3 found"), e.g. meta 147977 4 33976 1.

## Descents (ORBW=3, RESTARTAFTER=0 COOL=15 REHEAT=30, 30 min each, nice 10, one at a time)
- run 1: psl 29 x Z49, seed 108502, `d1.log`, `d1.out`, CKPT `d1.ckpt`.
- run 2: psl 27 x Z61, seed 108503, `d2.log`, `d2.out`, CKPT `d2.ckpt`.
- Reference (card): psl 23 x Z97 chain minima median 18-21, P(min <= 9) about 1/15, ~50 s per chain.
