# lean-all status

Every record in README.md's table without a ✓ in the Lean column (41 cells, table order). Split: worker A takes rows 1–20, worker B takes rows 21–41. A worker claims a row here (commit and push) before starting it.

Status values: `open` (not started), `claimed` (someone is working on it), `partial` (a file exists but does not yet check), `done` (builds with the standard axioms only, no sorry/admit/native_decide, and is listed in `lean/Axioms.lean`), `blocked` (exact reason in the notes).

| # | (Δ, D) | Ours | Method (README) | Lean now | Worker | Status | Lean file / notes |
|---:|:---:|---:|---|:---:|:---:|:---|---|
| 1 | (8, 5) | 2,048 | route-chart lift | — | A | open | Not started. |
| 2 | (10, 5) | 4,800 | generalized quadrangle construction ¹ | — | A | open | Not started. |
| 3 | (11, 5) | 7,020 | generalized quadrangle construction ¹ | — | A | open | Not started. |
| 4 | (12, 5) | 9,840 | generalized quadrangle construction ¹ | — | A | open | Not started. |
| 5 | (13, 5) | 11,486 | finite geometry (unit design) ¹ | — | A | open | Not started. |
| 6 | (14, 5) | 17,568 | generalized quadrangle construction ¹ | — | A | open | Not started. |
| 7 | (15, 5) | 20,736 | route-chart lift | — | A | open | Not started. |
| 8 | (16, 5) ² | 33,792 | route-chart lift ¹ | — | A | open | Not started. |
| 9 | (11, 6) | 148,944 | finite geometry | — | A | open |  |
| 10 | (13, 6) | 388,972 | finite geometry | — | A | open |  |
| 11 | (15, 6) | 870,440 | finite geometry | — | A | open |  |
| 12 | (16, 6) | 940,846 | finite geometry | — | A | open |  |
| 13 | (4, 7) | 864 | vertex-transitive (Cayley-type) | — | A | claimed | Haar graph of Heis(F_9) ⋊ C_16 (`research/theorems/smallfam/graphs/build_d4D7_n864.py`); see HANDOFF.md. |
| 14 | (7, 7) | 23,580 | hexagon + hub vertices ¹ | — | A | open |  |
| 15 | (9, 7) | 118,224 | hexagon + hub vertices ¹ | — | A | open |  |
| 16 | (10, 7) | 225,128 | hexagon + hub vertices ¹ | — | A | open |  |
| 17 | (11, 7) | 407,162 | hexagon + hub vertices ¹ | — | A | open |  |
| 18 | (12, 7) | 680,068 | hexagon cover + hub vertices ¹ | — | A | open |  |
| 19 | (13, 7) | 1,064,448 | hexagon + hub vertices ¹ | — | A | open |  |
| 20 | (14, 7) | 1,774,584 | hexagon cover + hub vertices ¹ | — | A | open |  |
| 21 | (15, 7) | 2,484,720 | hexagon cover + hub vertices ¹ | — | B | open |  |
| 22 | (6, 8) | 31,680 | orbit search (Haar) ¹ | — | B | open |  |
| 23 | (11, 8) | 2,258,520 | orbit search (Haar) | — | B | open |  |
| 24 | (13, 8) | 6,999,552 | finite geometry | — | B | open |  |
| 25 | (15, 8) | 18,128,880 | orbit search (Haar) | — | B | open |  |
| 26 | (8, 9) | 1,326,960 | finite geometry ¹ | — | B | open |  |
| 27 | (9, 9) | 3,499,776 | orbit search (Haar) | — | B | open |  |
| 28 | (10, 9) | 8,003,856 | orbit search (Haar) | — | B | open |  |
| 29 | (11, 9) | 16,792,080 | orbit search (Haar) | — | B | open |  |
| 30 | (12, 9) | 34,026,720 | orbit search (Haar) | — | B | open |  |
| 31 | (13, 9) | 67,742,688 | orbit search (Haar) | — | B | open |  |
| 32 | (14, 9) | 116,068,656 | orbit search (Haar) | — | B | open |  |
| 33 | (15, 9) | 208,029,120 | orbit search (Haar) | — | B | open |  |
| 34 | (16, 9) | 337,394,400 | orbit search (Haar) | — | B | open |  |
| 35 | (7, 10) | 2,237,760 | finite geometry ¹ | — | B | open |  |
| 36 | (8, 10) | 7,818,096 | finite geometry ¹ | — | B | open |  |
| 37 | (9, 10) | 23,975,280 | orbit search (Haar) | — | B | open |  |
| 38 | (10, 10) | 60,141,120 | orbit search (Haar) | — | B | open |  |
| 39 | (12, 10) | 325,832,976 | orbit search (Haar) | — | B | open |  |
| 40 | (13, 10) | 677,714,400 | orbit search (Haar) | — | B | open |  |
| 41 | (14, 10) | 1,326,627,120 | orbit search (Haar) | — | B | open |  |
