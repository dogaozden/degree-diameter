# lean-all: status of every record without a Lean ✓ in README.md

Started 2026-10-25 (cloud session, branch `claude/lean-all-jvj7b0`). Lean files are in `lean/BipartiteDD/LeanAll/`;
axioms in `lean/BipartiteDD/LeanAll/Axioms.out.txt` (only propext, Classical.choice, Quot.sound).

| cell | record | construction | status | theorem / file |
|---|---:|---|---|---|
| (11,6) | 148,944 | Theorem D, q = 9, m = 2 | **done** | `nb_11_6`, LeanAll/D6.lean |
| (13,6) | 388,972 | Theorem D, q = 11, m = 2 | **done** | `nb_13_6`, LeanAll/D6.lean |
| (15,6) | 870,440 | Theorem D, q = 13, m = 2 | **done** | `nb_15_6`, LeanAll/D6.lean |
| (16,6) | 940,846 | Theorem D, q = 13, m = 3 | **done** | `nb_16_6`, LeanAll/D6.lean |
| (8,5) | 2,048 | route-chart lift | todo | |
| (4,7) | 864 | Haar / Cayley-type | todo | |
| (10,5) | 4,800 | GQ doubled-matching lift, W(7), Z6 | todo | |
| (11,5) | 7,020 | GQ lift, W(8) | todo | |
| (12,5) | 9,840 | GQ lift, W(9) | todo | |
| (13,5) | 11,486 | unit design | todo | |
| (14,5) | 17,568 | GQ lift, W(11) | todo | |
| (15,5) | 20,736 | route-chart lift | todo | |
| (16,5) | 33,792 | route-chart lift | todo | |
| (6,8) | 31,680 | Haar, PSL(2,11) × Z24 | todo | |
| (7,7) … (15,7) | 23,580 … 2,484,720 | hexagon + hubs | todo | |
| D = 8–10 Haar cells | 1.3M … 1.3B | Haar | todo | |

The D = 6 cells are instances of the Theorem D family already in Lean (`HexagonD.theoremD`, any finite field of odd
characteristic): the vertex formula 2(q+1)(q⁴+q²+1) + (m−1)(q⁴+2q³+q²+2q+2 + m(q³+q+2) + m²) + (m−1)(q⁴−q²) gives
exactly the four record values.
