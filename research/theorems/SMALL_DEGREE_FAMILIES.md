# Formulas behind the small-degree records (thm-smallfamilies, 2026-10-24): work in progress

Job "thm-smallfamilies" (Opus). Scripts and outputs in `smallfam/`. This file is being written; the first
findings are below and will be ranked properly at the end of the session.

- Loz's table values (3,9) = 506 and (4,9) = 4970 are Haar graphs of the Frobenius groups Z23 ⋊ Z11 and
  Z71 ⋊ Z35 (rebuilt by exhaustive search up to automorphism: `smallfam/runs/d3D9_z23x11_exhaustive.txt`,
  `smallfam/runs/d4D9_z71x35_normalform.txt`). In both, every solution has a single j-pattern up to translation
  and sign: {0, 1, 6} in Z11 (an arithmetic progression) and {0, 1, 13, 19} in Z35.
- Δ = 3, all Z_p ⋊ Z_k with p prime, exhaustive: the largest Haar graphs of diameter 7, 8, 9, 10 have 140, 234, 506,
  660 vertices (`smallfam/runs/frob_d3D*.txt`). Only (3,9) reaches the table.
