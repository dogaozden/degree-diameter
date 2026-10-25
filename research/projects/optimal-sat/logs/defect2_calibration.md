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

## Other things tried on the A-only instance (2026-10-25, machine partly loaded)

| method | k = 9 (SAT) | k = 10 (UNSAT) |
|---|---|---|
| kissat, `--sym --nf2` | 1.7 s | 211 s |
| kissat, `--sym --nf2 --ntt --alltr` | 1.6 s | 163 s |
| kissat `--unsat` preset, same CNF | — | 210 s (loaded machine; no clear gain) |
| CaDiCaL + LRAT (binary), same CNF | — | 551 s (loaded), proof 218 MB |
| RoundingSat (OPB, linear pair equalities, `enc_pb.py`) | 1.5 s | not done in 25 min |
| cube-and-conquer, 2 rows of B (86 cubes) | — | about 10 s per cube, about 5× the monolithic work |
| march_cu lookahead cubing, depth 8 | — | 7 min just to cube (37 cubes) |

Symmetric searches for k = 11 (`cayley_search.py`, `semireg_search.py`): no Cayley digraph on either group of order 55
(complete); A with a fixed-point-free automorphism of order 11 or 5: not decided in 900 s each.

## k = 11 cube experiments (kissat, 300 s cap unless noted; machine shared with 2 monolithic runs)

Rules for choosing the base. Each rule must be used for **all** cubes of a split. A cube may omit its rule's extra
constraint but must never mix two rules.
- R0, no rule: degree cubes (α, β), with α ≥_lex β by arc reversal (245,667 cubes; `ablist.py`).
- R1, vertex 0 lies on the most directed triangles: same cube list as R0 (reversal keeps every vertex's triangle
  count); a cube may add "every vertex on ≤ t = Σα triangles" (`abcube.py --maxt`; cheap only for small t).
- R2, arc 0→1 lies on the most directed triangles: cubes with β₁ ≤ α₁, no reversal halving (338,049 cubes;
  `ablist.py --maxtau`); a cube may add "every arc on ≤ α₁ triangles" (`abcube.py base --maxtau α₁`).

| cube | R0 | R1 (--maxt) | R2 (--maxtau) |
|---|---|---|---|
| 0^9 / 0^9 (t = 0) | > 900 s | 53 s (certified LRAT: 55 s) | — |
| 1,0^8 / 1,0^8 (t = 1) | > 900 s | 106 s | — |
| 4,4,3,2,2,1,1,1,1 / 5,4,2,2,2,2,2,0,0 (t = 19) | > 600 s | > 1200 s | **2.9 s** |
| 6,2^8 / 5,4,3,2,2,2,2,1,1 | 134 s (96 s) | — | — |
| 20 random R0 cubes | 16 × ~1 s, 3 s, 19 s, 262 s, > 300 s | — | — |
| 8 random R2 cubes with α₁ = 6 | — | — | 5.5–8 s each (larger file to parse) |
| 3 random R2 cubes with α₁ = 4 | — | — | 9 s, 206 s, > 300 s |

Coarse splits that did not work: by t only (t = 36: > 30 min); by the largest triangle count on any arc only
(`tausplit.py`: M = 0 in 31 s, M = 1 and M = 2 > 15 min); "every vertex on ≤ 2 / ≤ 5 triangles" (`tmax.py le`):
> 22 / > 52 min.
