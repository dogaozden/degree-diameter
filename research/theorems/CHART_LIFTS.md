# Chart lifts: the (16,5) route-chart lift as a family (job thm-chartlift)

Opus theorist session, branch `claude/chart-lift-family-wko52j`, started 2026-10-24. Scripts and outputs:
`research/theorems/chartlift/`. This file is updated as the run goes; the ranked write-up is at the end.

## Status (running)

- **(12,5): 8,748 > 8,200 (table).** Route-chart lift of K₃,₃ + doubled perfect matching over Z₁₈, fibre F₃⁴,
  4 letters × 3 scalars, 12-regular. apsp.c: RESULT VALID d=12 D=5 n=8748 (INVALID with D=4); bfs_all.c: max
  eccentricity 5, distance histogram sums to 8,748². Builder `chartlift/graphs/build_d12D5_n8748.py` (self-contained),
  edges `chartlift/graphs/d12D5_n8748_k33m_z18_f3.edges.gz`, check `chartlift/graphs/d12D5_n8748_check.txt`.
- **(15,5): 20,736 > 20,496 (table).** 5 letters × 3 scalars: a 5-regular base on 2 + 2 vertices lifted by the dicyclic
  group of order 64 (m = 128), fibre F₃⁴, chart `charts/r2_k5_q3.txt` (112 singular patterns, pencils complete).
  Controller found by squad r1-chartlift card c6; rebuilt and checked here: apsp VALID d=15 D=5 n=20736, bfs_all max
  eccentricity 5. Builder `chartlift/graphs/build_d15D5_n20736.py`, check `chartlift/graphs/d15D5_n20736_check.txt`.
- **(8,5): 2,048 > 1,764 (lab) > 1,710 (table).** 4 letters × 2 scalars: K₄,₄ (Latin-square colouring) lifted by
  Z₂ × Z₈ (m = 64), fibre F₂⁴, chart `charts/c4s2_k4_q2.txt` (48 singular patterns, pencils complete, diagonal covered
  so no 4-cycles are needed). Controller found by squad card c4; rebuilt and checked here: apsp VALID d=8 D=5 n=2048,
  bfs_all max eccentricity 5. Builder `chartlift/graphs/build_d8D5_n2048.py`, check `chartlift/graphs/d8D5_n2048_check.txt`.
- (9,5): 2,592 > 2,496 (table), below the lab's 2,662. (12,5) via 3 letters × 4: 8,192, just under 8,200. Both are
  the same 32-vertex cubic controller (a Z₈-lift of the 2+2 base [[2,1],[1,2]] with a 4-cycle at every vertex) with
  zero-singular, pencil-complete charts over F₃⁴ and F₄⁴; apsp VALID for both.
- Tools reproduce the 33,792 graph exactly from the squad's controller and chart (`check_u8.py`, lift.py + apsp).
