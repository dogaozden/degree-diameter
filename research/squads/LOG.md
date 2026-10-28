# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-27 23:20 UTC, thm-haar-families (Opus, branch claude/thm-haar-families-pmi32i), round thmfam-r1

Goal: uniform families (S by a formula in q, m) in the shape of the D = 8-10 Haar records, and tests of the note's
theorems on small q. 18 Haiku cards (model haiku, effort high), scorer `research/theorems/haar_families/family_score.py`
(mean excess diam - log_{Delta-1}|G| over primes 23 <= q <= 113; lower is better). Baselines: LPS p = 5: 4.00; one
random orbit-closed draw at Delta 6: 3.18-3.50; records 2.0-2.3.

| card | direction | best |
|---|---|---|
| c1 | integer lifts, Delta 6 | 3.36 (random 3.18-3.50) |
| c2 | integer lifts, Delta 7 | 3.10 (random mean 3.07) |
| c3 | integer lifts, Delta 8, 10 | 3.84, 3.40 (random 3.30, 2.76): worse |
| c4 | integer lifts x Z_m | 3.12 (m = 13); no gain over random m = 1 |
| c5 | records lifted to SL(2,Z), used at other q | 2.87-3.24 (records 2.0-2.1 at their own q) |
| c6 | LPS(5) x Z_m, labels searched per (q,m) | 99.4 % of table at (6,10), 95.3 % at (6,8) |
| c7 | LPS(7), LPS(13) x Z_m, searched labels | 98.9 % of table at (8,8) |
| c8 | verify Thm 2.6 (cycle types) and Thm 3.2 | 0 failures for q >= 7; found a side-mixing bug in lps_haar.c |
| c9 | far vertices of LPS | conjecture "far = pure quaternions" fails at ecc - 1 (score 0.07) |
| c10 | primitive-root formulas, Delta 7 | 2.96 (random 2.96-3.24) |
| c11 | Dickson / trace / power formulas | 3.13 at Delta 6 (random 3.18-3.50), 3.16 at Delta 8 |
| c12 | torus orbits, Delta ~ q | diameter 5-7, at most 1.8 % of Moore |
| c13 | random baselines | (pending at log time) |
| c14 | larger q trend | LPS excess slope 0.41 in log_5|G| (theory 1/3), random -0.04 |
| c15 | order 5/6 symmetry | worse than k = 3 at the same Delta |
| c16 | conic model (Cayley transforms) | 3.34 at Delta 8 (random 3.25-3.30) |
| c17 | growing cyclic factor m ~ q | 3.38 (random m = 1: 3.38) |
| c18 | LPS repair by an extra orbit | 3.24 at Delta 9 (random 2.72-2.86) |

Kept: LPS x Z_m covers (c6, c7). Dropped: every formula family (they sit at the level of one random draw). The
director proved Theorem 3.2 (exact distance to psi(i)) meanwhile; c8 and the director's own check (251/251) confirm it.
Next: round 2 on label rules for LPS x Z_m (uniform in q and m) and how far covers go.

## 2026-10-27 23:50 UTC, thm-haar-families, round thmfam-r2

Goal: LPS x Z_m covers, the only round-1 direction near the table: label rules given by a formula in m (uniform in q
and m), how far covers go, and a numerical audit of the note. 11 Haiku cards; scorer
`research/theorems/haar_families/cover_score.py` (mean excess over a (q, m) grid) plus vertices/table per cell.

| card | direction | best |
|---|---|---|
| c1 | label rules, p = 5 (45 cells) | t = 3: mean excess 2.86 (random t: 2.93-3.09, mean 3.01) |
| c2 | label rules, p = 7 (45 cells) | 14 rules 2.63-2.88, best 2.63-2.66 (random t: 2.73); members above the 2013 table at (8,8) 210,528 (q=17, m=43) and (8,9) 1,105,104 (q=23, m=91); director re-checked with haar_ecc, verify_cover.py and (8,8) with all-pairs apsp.c |
| c3 | label rules, p = 11 (p = 13 not run) | best of 10 rules 2.53 against random labels 2.56: a tie |
| c4 | push p = 5 covers past the table, labels hill-climbed per (q, m) | no FULL cover beat the table at (6,8), (6,9), (6,10) |
| c5 | push p = 7 covers past the table | its (q, m) = (11, 163) entries marked diam 8 had 18 vertices unreached within 8 steps (cA = 215,151 < 215,160): diameter 9, not a table beat (director re-check) |
| c6 | Delta 4 covers at (4,8), (4,9) | 66 % and 88 % of the table (exhaustive labels); no record |
| c7 | Delta 12, 14 covers | 51 % of the table at (12,9); nothing at D = 8 beyond plain LPS |
| c8 | numerical audit of the note | one discrepancy (odd-D count in Appendix B), fixed; all identities, Lemma 2.5(c), Prop. 4.1 passed |
| c9 | second quaternion algebra (-1,-3) | distance to psi(i) = the Hamilton threshold in 65/66 cases (Prop. 3.6) |
| c10 | random and exhaustive label baselines | p = 5: random equivariant 2.97, free 3.10, best t per cell 2.71 (35 cells); p = 7: random 2.68 |
| c11 | nonlinear arithmetic labels | z = sum (a_k mod 3) r^(k-1): 2.82 at p = 5 (24 cells) |

Kept: the label rule of c2 (two members above the 2013 table, below the lab's records). Stopped here: no direction
came near the lab's records, and the theorem part (Theorems 2.6, 3.2) did not depend on more search.
