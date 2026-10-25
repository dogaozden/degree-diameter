# (k,3,-2) SAT calibration (kissat 4.x, 1 core, this container)

| k | naive (enc_d3m2.py) | grid (enc_grid.py) | grid + lex-leader (enc_grid.py --sym) | expected |
|---|---|---|---|---|
| 3 | SAT 0.00 s | SAT 0.00 s | SAT 0.00 s | exists (unique) |
| 4 | SAT 0.01 s | SAT 0.00 s | SAT 0.01 s | exists (unique) |
| 5 | UNSAT 0.09 s | UNSAT 0.05 s | UNSAT 0.05 s | none (Δ, Δ-2 not squares) |
| 6 | UNSAT 23 min | UNSAT 2.7 s | UNSAT 0.14 s | none (Delorme et al. 2009) |
| 7 | — | > 10 min | UNSAT 48.5 s | none |
