# lean-all: status

Missing Lean ✓ in README.md's table, in table order (41 rows). Worker A takes rows 1–21, worker B rows 22–41.
Claims: a worker writes its claim here before it starts a record. Status: claimed / building / done (with the Lean name) / blocked.

| # | (Δ, D) | Table | Ours | Method | Worker | Status | Lean name / note |
|---|---|---:|---:|---|---|---|---|
| 1 | (8, 5) | 1,710 | 2,048 | route-chart lift | A | — | |
| 2 | (10, 5) | 4,000 | 4,800 | generalized quadrangle construction | A | — | |
| 3 | (11, 5) | 5,850 | 7,020 | generalized quadrangle construction | A | — | |
| 4 | (12, 5) | 8,200 | 9,840 | generalized quadrangle construction | A | — | |
| 5 | (13, 5) | 11,480 | 11,486 | finite geometry (unit design) | A | — | |
| 6 | (14, 5) | 14,760 | 17,568 | generalized quadrangle construction | A | — | |
| 7 | (15, 5) | 20,496 | 20,736 | route-chart lift | A | — | |
| 8 | (16, 5) | 27,300 | 33,792 | route-chart lift | A | — | |
| 9 | (11, 6) | 142,464 | 148,944 | finite geometry | A | — | |
| 10 | (13, 6) | 374,452 | 388,972 | finite geometry | A | — | |
| 11 | (15, 6) | 842,048 | 870,440 | finite geometry | A | — | |
| 12 | (16, 6) | 884,062 | 940,846 | finite geometry | A | — | |
| 13 | (4, 7) | 840 | 864 | vertex-transitive (Cayley-type) | A | — | |
| 14 | (7, 7) | 23,436 | 23,580 | hexagon + hub vertices | A | — | |
| 15 | (9, 7) | 117,648 | 118,224 | hexagon + hub vertices | A | — | |
| 16 | (10, 7) | 224,694 | 225,128 | hexagon + hub vertices | A | — | |
| 17 | (11, 7) | 398,580 | 407,162 | hexagon + hub vertices | A | — | |
| 18 | (12, 7) | 664,300 | 680,068 | hexagon cover + hub vertices | A | — | |
| 19 | (13, 7) | 1,062,936 | 1,064,448 | hexagon + hub vertices | A | — | |
| 20 | (14, 7) | 1,771,560 | 1,774,584 | hexagon cover + hub vertices | A | — | |
| 21 | (15, 7) | 2,480,184 | 2,484,720 | hexagon cover + hub vertices | A | — | |
| 22 | (6, 8) | 29,790 | 31,680 | orbit search (Haar) | B | **done** | `nb_6_8_31680` (`lean/BipartiteDD/Haar/D6D8P11/Record.lean`), axioms propext, Classical.choice, Quot.sound |
| 23 | (11, 8) | 2,246,940 | 2,258,520 | orbit search (Haar) | B | blocked: per-element certificate ≈26 h of kernel time (3·order(G) codes, order(G) = N/2, ≈28 ms each); needs a family argument | |
| 24 | (13, 8) | 5,314,680 | 6,999,552 | finite geometry | B | not started: finite-geometry row; needs the family theorem (no per-group certificate fits) | |
| 25 | (15, 8) | 14,172,480 | 18,128,880 | orbit search (Haar) | B | blocked: per-element certificate ≈212 h of kernel time (3·order(G) codes, order(G) = N/2, ≈28 ms each); needs a family argument | |
| 26 | (8, 9) | 1,091,232 | 1,326,960 | finite geometry | B | not started: finite-geometry row; needs the family theorem (no per-group certificate fits) | |
| 27 | (9, 9) | 2,961,536 | 3,499,776 | orbit search (Haar) | B | blocked: per-element certificate ≈41 h of kernel time (3·order(G) codes, order(G) = N/2, ≈28 ms each); needs a family argument | |
| 28 | (10, 9) | 7,057,400 | 8,003,856 | orbit search (Haar) | B | blocked: per-element certificate ≈93 h of kernel time (3·order(G) codes, order(G) = N/2, ≈28 ms each); needs a family argument | |
| 29 | (11, 9) | 15,200,448 | 16,792,080 | orbit search (Haar) | B | blocked: per-element certificate ≈196 h of kernel time (3·order(G) codes, order(G) = N/2, ≈28 ms each); needs a family argument | |
| 30 | (12, 9) | 30,001,152 | 34,026,720 | orbit search (Haar) | B | blocked: per-element certificate ≈397 h of kernel time (3·order(G) codes, order(G) = N/2, ≈28 ms each); needs a family argument | |
| 31 | (13, 9) | 50,990,610 | 67,742,688 | orbit search (Haar) | B | blocked: per-element certificate ≈790 h of kernel time (3·order(G) codes, order(G) = N/2, ≈28 ms each); needs a family argument | |
| 32 | (14, 9) | 95,087,738 | 116,068,656 | orbit search (Haar) | B | blocked: per-element certificate ≈1,354 h of kernel time (3·order(G) codes, order(G) = N/2, ≈28 ms each); needs a family argument | |
| 33 | (15, 9) | 168,016,334 | 208,029,120 | orbit search (Haar) | B | blocked: per-element certificate ≈2,427 h of kernel time (3·order(G) codes, order(G) = N/2, ≈28 ms each); needs a family argument | |
| 34 | (16, 9) | 288,939,118 | 337,394,400 | orbit search (Haar) | B | blocked: per-element certificate ≈3,936 h of kernel time (3·order(G) codes, order(G) = N/2, ≈28 ms each); needs a family argument | |
| 35 | (7, 10) | 1,987,380 | 2,237,760 | finite geometry | B | not started: finite-geometry row; needs the family theorem (no per-group certificate fits) | |
| 36 | (8, 10) | 6,927,210 | 7,818,096 | finite geometry | B | not started: finite-geometry row; needs the family theorem (no per-group certificate fits) | |
| 37 | (9, 10) | 20,017,260 | 23,975,280 | orbit search (Haar) | B | blocked: per-element certificate ≈280 h of kernel time (3·order(G) codes, order(G) = N/2, ≈28 ms each); needs a family argument | |
| 38 | (10, 10) | 50,331,156 | 60,141,120 | orbit search (Haar) | B | blocked: per-element certificate ≈702 h of kernel time (3·order(G) codes, order(G) = N/2, ≈28 ms each); needs a family argument | |
| 39 | (12, 10) | 300,383,050 | 325,832,976 | orbit search (Haar) | B | blocked: per-element certificate ≈3,801 h of kernel time (3·order(G) codes, order(G) = N/2, ≈28 ms each); needs a family argument | |
| 40 | (13, 10) | 617,330,936 | 677,714,400 | orbit search (Haar) | B | blocked: per-element certificate ≈7,907 h of kernel time (3·order(G) codes, order(G) = N/2, ≈28 ms each); needs a family argument | |
| 41 | (14, 10) | 1,213,477,190 | 1,326,627,120 | orbit search (Haar) | B | blocked: per-element certificate ≈15,477 h of kernel time (3·order(G) codes, order(G) = N/2, ≈28 ms each); needs a family argument | |

## Notes
- Ticks in README.md are not edited by this project (brief: do not edit records, README or RESULTS.md); the coordinator
  should mark row 22 once it has checked `nb_6_8_31680`.
- Row 22 check: `research/frontier/build_haar2.py research/frontier/sols/d6D8_psl_11_24_orb2f0_s1.txt` gives
  n = 31680, degree 6, ecc 8 from both sides, VALID.
- The row 22 Lean proof is the first of this project and is the pattern for other Haar rows (see HANDOFF.md).
