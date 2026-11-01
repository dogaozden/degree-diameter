# c3-twist notes (cut the abelian tax with a twisted cyclic factor)

Started 2026-10-31 ~21:46 UTC. Target: N = |G| >= 588,241 (cell 10-8), ORBIT "3 3 1", ORBW=3. Seeds 108401-108499.

## Files
- `haar_tw.c` = research/d10D8/sym2/haar_sym2.c with two changes (both in orbit_main/alpha):
  - ORBIT mode now accepts `tpgl q` (the old check "plain groups only" removed). alpha = conj by PGL element x (z -> r z);
    this is an automorphism for tpgl because chi is a class function. Checked on 20,000 random pairs at start-up.
  - `csl` in ORBIT mode: alpha conjugates the SL(2,q) representative and moves the sign of the product into z
    (s*n/2). Checked the same way. Built as `haar_csl` (handles tpgl and csl); `haar_tw` is the tpgl-only build.
- `tools/cands.py` (candidate list in the N window), `tools/twist_score.py` (f_k densities of tpgl by brute force,
  uses wave3/group_score.score), `tools/chains.py` (summary of CHAIN lines of a log).
- `chain_runs.sh`: driver that queued the screens and the tpgl run after the sl run (one heavy process at a time).

## Candidates (cands.py; order-3 scaling of Z_n needed for ORBIT 3 3 1)
- csl q with n = 2 mod 4 is NOT twisted: (SL(2,q) x Z_n)/<(-I,n/2)> = SL(2,q) x Z_{n/2}, via
  (M,z) -> ((-1)^z M, z mod n/2) (kernel {(I,0),(-I,n/2)}, onto). So csl 23 98 = sl 23 x Z49, csl 13 542 = sl 13 x Z271,
  csl 17 242 = sl 17 x Z121 etc. Only csl with 4 | n is a genuine central product (csl 17 244, csl 13 540, csl 11 892,
  csl 7 3504; csl 31 40 has no order-3 scaling of Z_40).
- tpgl q in window (q >= 7, order-3 scaling exists): q=7 n=1753/1754/..., q=11 n=446 (N 588720) and 453,
  q=13 n=271 (591864), n=273, q=17 n=122 (597312), q=23 n=49 (595056).

## Measurements
RANDORB=1000 (raw uncovered count, ORBIT 3 3 1, ORBW irrelevant here), mu = N exp(-W/N):

| group | N | mu | min | p1 | p10 | median | |Fix alpha| |
|---|---|---|---|---|---|---|---|
| psl 23 x Z97 (reference) | 588,984 | 63.5 | 36 | 51 | 81 | 136 | 11 |
| sl 23 x Z49 (= csl 23 98) | 595,056 | 70.4 | 47 | 58 | 82 | 132 | 23 |
| tpgl 23 x Z49 | 595,056 | 70.4 | 69 | 97 | 145 | 345 | 23 |
| tpgl 13 x Z271 | 591,864 | 66.7 | 128 | 196 | 327 | 1387 | 11 |
| csl 17 x Z244 (4 divides n) | 597,312 | 73.1 | 66 | 75 | 115 | 207 | 35 |
| csl 11 x Z892 (4 divides n) | 588,720 | 63.2 | 94 | 126 | 167 | 372 | 23 |
| csl 13 x Z540 (4 divides n) | 589,680 | 64.2 | 18943 | 23858 | 41921 | 153763 | 1079 |
| csl 7 x Z3504 (4 divides n) | 588,672 | 63.1 | 617 | 811 | 1683 | 17636 | 143 |

Element-order densities (tools/twist_score.py; score = group_score score, lower is better):

| group | f2 | involutions | score |
|---|---|---|---|
| tpgl 23 x Z49 | 2.3e-2 | 13,777 | 0.0257 |
| tpgl 13 x Z271 | 3.6e-2 | 21,229 | 0.120 |
| tpgl 11 x Z446 | 5.0e-2 | 29,547 | 0.135 |
| tpgl 7 x Z1753 | 8.3e-2 | 49,105 | 0.250 |
| psl 23 x Z97 | 4.3e-4 | 253 | 5.36e-4 |
| sl 23 x Z49 | 1.7e-6 | 1 | 1.07e-4 |

Why tpgl has a glut of short cycles (structural, not a tuning problem): for an outer g (chi(g) = -1) of even order o,
(g,z)^o = (1, 0) for every z, so each outer involution g gives n involutions (g,z). The outer part of PGL(2,q) has
~q^2/2 involutions over |G| ~ q^3 n, so f2 ~ 1/(2q) for every tpgl. A nontrivial chi on Z_n always comes with such
elements (for PGL the index-2 subgroup is PSL, and SL/PSL have no twist). So twisting Z_n cannot remove the short
cycles that the abelian tax is paired with; the Z-collision effect (cell notes 5) is small next to the involution glut.

## Results so far
- sl 23 x Z49 F15W3 (seed 108401, 45 min): see below (filled in at the end).

## Status at stop (2026-10-31 21:53 UTC, stopped early on request)
- sl 23 x Z49 F15W3 (seed 108401, ORBW=3 units): 6 descents, 271 cpu-s, chain minima 18,18,24,24,27,27
  (median 24; P(min <= 12) = 0/6). Too few to compare with psl 23 97 (median 18-21, P(<=9) ~ 1/15).
- tpgl 23 x Z49 F15W3: NOT run (driver stopped before it started).
- RANDORB screens of tpgl 11 x Z446, tpgl 17 x Z122, tpgl 13 x Z273, tpgl 7 x Z1753, sl 13 x Z271 and sl 13 x Z273: NOT run.
- No haar_tw/haar_csl process left alive; driver chain_runs.sh stopped.
- Duplicate-word rate: not measured.
- Scoreboard: one line (first chain min 18, ORBW=3 units). No new best.

## Read of what was measured
- RANDORB does not support the card's premise: tpgl 23 x Z49 is worse than sl 23 x Z49 at equal mu (median 345 vs 132,
  p1 97 vs 58). The short-cycle glut of tpgl (f2 2.3e-2) dominates.
- csl with n = 2 mod 4 is SL(2,q) x Z_{n/2} (no twist). csl with 4 | n is much worse in RANDORB.
- Untested next step: sl 23 x Z49 F15W3 for 40+ minutes (best untwisted candidate in the window).
