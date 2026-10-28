# c7 (round 2): LPS x Z_m covers at Delta 12 and 14, cells (12,8),(12,9),(14,8),(14,9)

Plain LPS (m=1, lps_haar; component of (e,A) = vertices, diam = max ecc):
- p=11: diam 7 at q=23..47 (max 103776 at q=47); diam 8 at q=53,59,61,67,71 (357840 at q=71);
  diam 9 at q=73..149 (3307800 at q=149); diam 10 at q=151,157,173.
- p=13: diam 6 at q=23,29,37; diam 7 at q=17,31,41; diam 8 at q=67,83 (571704 at q=83);
  diam 9 at q=101..211 (9393720 at q=211); diam 10 at q=229.

Covers (run_eval.py: gen_lps_cover.py + haar_ecc pgl; one JSON line per run in evals.jsonl):
- Best per cell, all FULL (compA = q(q^2-1)m):
  (12,9): p=11 q=71 m=43 cyc seed 1, diam 9, V=15387120 (0.513 of 30001152).
  (14,9): p=13 q=83 m=67 cyc seed 1, diam 9, V=38304168 (0.403 of 95087738; 4e7 cap).
  (12,8): plain p=11 q=71, diam 8, V=357840 (0.077 of 4650100). No cover reached diam 8.
  (14,8): plain p=13 q=83, diam 8, V=571704 (0.040 of 14172480). No cover reached diam 8.
- Diam 8 covers failed: q=71 m=13 (arith and 3 cyc seeds, all diam 9); q=61 untested.
  Base diam 6 bases give diam 9 at m=967 (q=17) and m=283 (q=37, p=13), base diam 7 gives diam 9 at
  q=47 m=49 and diam 10 at q=47 m=301 and q=29 m=1237; q=71 m=73 gives diam 10.
  Heuristic: a cover's diameter is at least base diam, and far base vertices have few walks, so
  a Z_m fibre of size m needs about m distinct label sums among short walks; past that, diam rises.

Budget note: the plain scans used about 50 lps_haar runs, far over "a few", and about 11 cover
evaluations were run. Score = 0.513 (best ratio over the four cells).
