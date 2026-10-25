# (k,3,-2) SAT calibration (kissat 4.x, 1 core, this container)

| k | naive (enc_d3m2.py) | grid (enc_grid.py) | grid + lex-leader (enc_grid.py --sym) | expected |
|---|---|---|---|---|
| 3 | SAT 0.00 s | SAT 0.00 s | SAT 0.00 s | exists (unique) |
| 4 | SAT 0.01 s | SAT 0.00 s | SAT 0.01 s | exists (unique) |
| 5 | UNSAT 0.09 s | UNSAT 0.05 s | UNSAT 0.05 s | none (Δ, Δ-2 not squares) |
| 6 | UNSAT 23 min | UNSAT 2.7 s | UNSAT 0.14 s | none (Delorme et al. 2009) |
| 7 | — | > 10 min | UNSAT 48.5 s | none |

## Quotient form (enc_quot.py), kissat, 1 core

The quotient form uses Theorem Q (SUMMARY.md): oriented graph A on m = k(k-1)/2 vertices + weighing-matrix signing.

| k | m | A only (--sym) | A + signs (--signs --sym) | expected |
|---|---|---|---|---|
| 3 | 3 | SAT 0.00 s | SAT 0.00 s | exists |
| 4 | 6 | SAT 0.00 s | SAT 0.01 s | exists |
| 5 | 10 | UNSAT 0.01 s | UNSAT 0.01 s | none |
| 6 | 15 | UNSAT 0.12 s | UNSAT 0.07 s | none |
| 7 | 21 | UNSAT 0.16 s | UNSAT 0.19 s | none |
| 8 | 28 | UNSAT 1.3 s | UNSAT 2.0 s | none |
| 9 | 36 | **SAT** 1.1 s | UNSAT 148 s | none (so the signing is what fails at k = 9) |
| 10 | 45 | running | — | none (W(45,8) impossible: odd order needs square weight) |
| 11 | 55 | running | running | open |
