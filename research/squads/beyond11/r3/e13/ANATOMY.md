# e13: hole anatomy at EVEN D, (d,D) = (8,12), ORBIT "3 2 2" (f = 2, m = 2)

Job beyond-d11, round 3, card e13. Analysis only (no search). Classifier: research/squads/beyond11/r2/d04/haar_hole with
CLASS=1 (the d04 binary, run with d=8, D=12). Driver: `run_seed.sh kind p n seed` (random start S from a 1 s generator run,
then CLASS=1 EVAL). Summary: `anatomy.py`, per-seed table `ANATOMY_table.txt`. Per-run files: `<tag>.sol.start`,
`.gen.log`, `.eval.log`, `.cls.txt` (one HOLE line per uncovered element).

## Setup and classes
- Groups at mu ~ 9-11 from `pick.py 8 12 8 12 3 2000`: PSL(2,653) x Z_1 (N = 1.39e8, mu 8.86); SL(2,271) x Z_7 (N = 1.39e8,
  mu 8.97); PSL(2,97) x Z_307 (mu 9.87); PSL(2,79) x Z_571 (mu 10.71); PSL(2,61) x Z_1237 (mu 10.21).
- Seeds: 12 (PSL(2,653), SL(2,271) x Z_7), 10 (PSL(2,97) x Z_307), 8 (PSL(2,79) x Z_571), 6 (PSL(2,61) x Z_1237).
  The card asked for 3 each; more were run to reduce noise. Memory 0.07-0.18 GB per run (PUSHMAX=65536).
- Classes, in priority order: central = scalar matrix (+-I; for PSL the centre is Z_n, i.e. (1,z)); involution = projective
  order 2 with z = 0; alpha = fixed by conjugation by the order-3 matrix AG (with z -> AR z); other.
- Side: at even D the classifier computes one side only (cost = B-side elements not within D-1 of (e,A)). Every hole is
  reported on side A, and side B is always 0. The side split carries no information at even D.

## Table: holes per random S (cost), by class
| group (mu) | seeds | holes per seed | median | geo-mean | central | involution | alpha | other |
|---|---|---|---|---|---|---|---|---|
| PSL(2,653) x Z_1 (8.86) | 12 | 12, 14, 22, 6, 13753, 20, 7, 244, 30, 14, 455, 19 | 19.5 | 43 | 0 | 81 | 49 | 14466 |
| SL(2,271) x Z_7 (8.97) | 12 | 6, 19, 34, 13, 13, 9, 16, 24, 16, 9, 11, 19 | 14.5 | 14 | 0 | 0 | 12 | 177 |
| PSL(2,97) x Z_307 (9.87) | 10 | 27, 1602, 7, 183, 82, 11016, 42, 15, 9, 53937 | 62 | 165 | 3 | 0 | 2 | 66915 |
| PSL(2,79) x Z_571 (10.71) | 8 | 54, 30, 36, 451, 60, 105, 621, 42 | 57 | 90 | 3 | 0 | 1 | 1395 |
| PSL(2,61) x Z_1237 (10.21) | 6 | 32499, 65536 (capped), 25155, 6564, 5226, 65536 (capped) | 28827 | 22223 | 21 | 0 | 0 | 200495 |

Projective orders of the "other" holes: they sit in the regular tori, i.e. orders (p-1)/2 and (p+1)/2 (PSL(2,653): 326, 327;
PSL(2,97): 48, 49; PSL(2,79): 39, 40; SL(2,271): 135, 136). Only the p = 61 runs show a large unipotent (order p) share.
Sum over runs of "other" holes with order (p-1)/2, (p+1)/2 or p: PSL(2,653) 8625 of 14466 (60%); PSL(2,97) 41631 of 66915
(62%); SL(2,271) 102 of 177 (58%); PSL(2,61) 130642 of 200495 (65%).

## Answers
1. Alpha-fixed elements are not the only special holes. They are enriched in some groups: 49 of 14596 holes for PSL(2,653)
   (0.3%; about 3-4% in the runs with fewer than 1000 holes) and 12 of 189 for SL(2,271) x Z_7 (6%). The group share of
   alpha-fixed elements is about p/N, i.e. about 2e-6 for these groups, so the enrichment there is 1e4 or more. In PSL(2,97),
   PSL(2,79) and PSL(2,61) the alpha-fixed holes are 0-2 per group, so they are not special there at this sample size.
   Most holes in every group are "other" elements in the regular tori.
2. Central and involution holes. Involution holes (projective order 2, z = 0) appear only in PSL(2,653) (81, all in the
   high-cost seeds). Central holes appear only when n > 1 for PSL (Z_n centre): 21 in PSL(2,61) x Z_1237, 3 each in PSL(2,79) x
   Z_571 and PSL(2,97) x Z_307. SL(2,271) x Z_7 has none.
3. Smaller p does not give fewer holes. The median cost at mu ~ 9-11 is 14.5 (SL(2,271) x Z_7), 19.5 (PSL(2,653)), 57
   (PSL(2,79) x Z_571), 62 (PSL(2,97) x Z_307) and 28827 (PSL(2,61) x Z_1237). The p = 61 family with n = 1237 is far off
   the size law (cost 5e3 to 6.5e4 against mu 10). Small p and large n are confounded here, and p = 61 is the only group with
   unipotent holes.
4. Heavy tail. Costs far above mu occur in PSL(2,653) (2 of 12 seeds: 13753, 455), PSL(2,97) x Z_307 (3 of 10 seeds above
   1000: 1602, 11016, 53937), PSL(2,79) x Z_571 (seed 7: 621) and every PSL(2,61) x Z_1237 seed. SL(2,271) x Z_7 has none above 34.
   The median is far below mu, so mu is a poor predictor for a random start at even D. These runs are not diagnosed.

## Heavy tail: small-order generators (checked after the table)
Projective orders of the six non-identity generators of each start S (sol.start), against the hole cost (all runs with a
`.cls.txt`):
- Every run whose S contains an involution (projective order 2) has a cost above 10^4: PSL(2,653) seed 5 (13753) and PSL(2,97)
  seed 10 (53937). Involution generators make S = S^-1 locally, so words collapse and the radius-11 ball is smaller.
- Every run with minimum generator order >= 100 has cost <= 455 (PSL(2,653) and SL(2,271) starts, the typical runs).
- Between these, min order 3-16 gives a mixed picture (SL(2,271) seed 10 with order 3: cost 9; PSL(2,97) seed 6 with order 12:
  cost 11016). The order-2 link is clear, the rest is not.
Practical rule: reject start S with a generator of small projective order before counting holes or setting mu.

## Caveats
- Random starts only (1 s generator, no search), so these are typical random S, not searched S.
- Alpha enrichment is computed against the share p/N, which falls with n (the alpha-fixed elements must have z = 0 when
  gcd(AR - 1, n) = 1), so it is only comparable across groups with the same n.
- Hole lists are capped at UCAP = 65536; the two capped PSL(2,61) runs have true costs above 65536.
