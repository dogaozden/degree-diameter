# s15 table: (15,9) random-S cost statistics, k = 3 vs k = 5 orbits (haar_big0 RANDORB, THREADS=1)
Bar N >= 104,241,601 (current SL(2,5) x SL(2,19) x Z127, mu 24.9). Costs are the number of uncovered B-side elements of random
symmetric S (lower is better). Seed 12 unless noted. mean is distorted by outliers (disconnected samples, cost ~1e6-1e8).

group | ORBIT | N | mu | samples | min | p10 | median | mean | bar
--- | --- | --- | --- | --- | --- | --- | --- | --- | ---
psl 151 x Z61 | 5 3 0 | 105,005,400 | 28.05 | 8 (seed 11) | 63 | 63 | 94 | 93.5 | above
psl 151 x Z61 | 5 3 0 | 105,005,400 | 28.05 | 16 | 49 | 57 | 80 | 78.7 | above
psl 151 x Z61 | 3 5 0 | 105,005,400 | 28.05 | 12 | 39 | 41 | 72 | 72.8 | above
psl 83 x Z367 | 3 5 0 | 104,907,684 | 27.63 | 12 | 60 | 72 | 96 | 100.1 | above
sl 67 x Z349 | 3 5 0 | 104,942,904 | 27.78 | 12 | 60 | 66 | 96 | 92.8 | above
sl 157 x Z27 | 3 4 3 | 104,482,872 | 25.88 | 12 | 56 | 62 | 94 | 98.3 | above
sl 157 x Z27 | 3 5 0 | 104,482,872 | 25.88 | 12 | 70 | 72 | 110 | 778 (outlier) | above
sl 89 x Z148 | 3 4 3 | 104,322,240 | 25.24 | 12 | 40 | 58 | 90 | 353 (outlier) | above
sl 89 x Z148 | 3 5 0 | 104,322,240 | 25.24 | 12 | 50 | 60 | 80 | 8.7e6 (outlier) | above
sl 79 x Z211 | 5 3 0 | 104,014,560 | 24.05 | 12 | 46 | 46 | 64 | 69.8 | BELOW bar (N too small)

## Anneals (haar_big0 15 9, K = 4, THREADS=1, 95-100 s, fresh seed; only ~25 evaluations each: ~4 s per evaluation under load)
- psl 151 x Z61, ORBIT "3 5 0", seed 21: best 39 after 25 evals (stuck from the first start). Log: anneal_psl151_61_350.log
- psl 151 x Z61, ORBIT "5 3 0", seed 22: best 24 after 25 evals (cost 39 -> 24 at step 5). Log: anneal_psl151_61_503.log
  Best state: b_psl151_61_503.txt.best (orbit form b_psl151_61_503.txt.best.orb). Not a solution; cost > 0.

## Reading
- No SL group tested beats PSL(2,151) x Z61 in random-S median at similar mu (k = 3 medians 62-110 across the four SL and PSL
  groups vs 72-80 for PSL(2,151) x Z61). SL(2,89) x Z148 and SL(2,157) x Z27 produce disconnected or near-disconnected samples
  (mean in the millions), i.e. the central/even-n effect (n even or 27 | n) costs holes at odd D.
- SL(2,79) x Z211 with "5 3 0" has the lowest median (64) but N = 104,014,560 is below the bar, so it cannot be a record.
- Only 25 evaluations per anneal: no conclusion about convergence; the 100 s anneal result is noise-level (39 vs 24).
