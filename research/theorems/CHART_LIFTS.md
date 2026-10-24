# Chart lifts: the (16,5) route-chart lift as a family (job thm-chartlift)

Opus theorist session, branch `claude/chart-lift-family-wko52j`, started 2026-10-24. Scripts and outputs:
`research/theorems/chartlift/`. This file is updated as the run goes; the ranked write-up is at the end.

## Status (running)

- **(12,5): 8,748 > 8,200 (table).** Route-chart lift of K₃,₃ + doubled perfect matching over Z₁₈, fibre F₃⁴,
  4 letters × 3 scalars, 12-regular. apsp.c: RESULT VALID d=12 D=5 n=8748 (INVALID with D=4); bfs_all.c: max
  eccentricity 5, distance histogram sums to 8,748². Builder `chartlift/graphs/build_d12D5_n8748.py` (self-contained),
  edges `chartlift/graphs/d12D5_n8748_k33m_z18_f3.edges.gz`, check `chartlift/graphs/d12D5_n8748_check.txt`.
- Tools reproduce the 33,792 graph exactly from the squad's controller and chart (`check_u8.py`, lift.py + apsp).
