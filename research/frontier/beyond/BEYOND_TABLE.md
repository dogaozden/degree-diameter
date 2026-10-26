# Beyond the 2013 table: first values for 48 new cells

Job new-cells-beyond (Opus director + Haiku squads, cloud session, 2026-10-26, branch claude/new-cells-beyond-etos3t).
The 2013 bipartite table (DS14v2, Table 4) stops at Δ = 16 and D = 10. This file gives a checked lower bound for every
cell in the next band: Δ = 17..20 at D = 3..10 (32 cells) and D = 11, 12 at Δ = 3..10 (16 cells), with an upper bound
and the comparison with the formula families. As far as we know (literature card r2/d10) no bipartite values have been
published for these cells, so every value here is a first value, not a record.

## Upper bounds

M_b(Δ,D) = 2(1 + (Δ−1) + … + (Δ−1)^(D−1)) is the bipartite Moore bound. For D = 5, 7, 8, 9, 10, 11, 12 we use
M_b − 6: Feria-Purón and Pineda-Villavicencio, "On bipartite graphs of defect at most 4", Discrete Appl. Math. 160
(2012), Prop. 6.4 (Δ ≥ 3, 5 ≤ D ≤ 187, D ≠ 6; the arXiv version 1010.5651 was read for this). For D = 3, 4, 6 the
bound is M_b itself: it is attained at Δ = 17, 18, 20 (Δ − 1 a prime power), and at Δ = 19 it would need a projective
plane, generalized quadrangle or generalized hexagon of order 18, whose existence is open.

## How each kind of value was checked

- Edge lists up to ~100k vertices: research/lifts/coordinator_check/apsp.c (all pairs, no symmetry), re-run by the
  director on every squad graph; logs in checks/.
- Haar graphs: research/frontier/build_haar2.py (≤ 2M vertices) or the low-memory checkers hcheck5 (SL(2,p) × Z_n)
  and hcheckpsl (PSL(2,p) × Z_n), which BFS from (e,A) and from (e,B); logs in runs/check_*. Solution files in
  research/frontier/sols/ (names d<Δ>D<D>_...).
- Formula families too large for an all-pairs run here (D = 6, 7): the theorem, a full check of the same builder at
  small q, and BFS from sampled vertices of the large instance (see the D = 6 and D = 7 notes).

<!-- TABLE -->
| (Δ,D) | value | % of M_b | upper bound | construction | check | best formula family (for comparison) |
|---|---:|---:|---:|---|---|---|
| (17,3) | **546** | 100.00 | 546 | PG(2,16) incidence graph (Moore graph) | apsp: checks/d17D3_n546_pg2_16.apsp.txt | 546 (PG(2,16) incidence graph (Moore)) |
| (17,4) | **8,738** | 100.00 | 8,738 | W(16) incidence graph (Moore graph) | apsp: checks/d17D4_n8738_W16.apsp.txt | 8,738 (W(16) incidence graph (Moore)) |
| (17,5) | **33,792** | 24.17 | 139,804 | the (16,5) route-chart lift (max degree 16 <= 17); nothing larger found | apsp (research/theorems/graphs/d16D5_n33792_check.txt) | 33,320 (polygon cover 7xW(13) (j=3)) |
| (17,6) | open | | 2,236,962 | | | 2,236,962 (H(16) incidence graph (Moore)) |
| (17,7) | open | | 35,791,388 | | | 5,631,276 (polygon cover 7xH(13) (j=3)) |
| (17,8) | **41,373,072** | 7.22 | 572,662,300 | Haar graph SL(2,53) x Z139, S = {e} + 1 fixed + 5 orbits of size 3 | haarcheck_sl (c15) and hcheck5 (director): VALID | 67,575,312 ([unpublished 2013 green formula, no construction known] q=13, j=3) |
| (17,9) | open | | 9,162,596,892 | | | — |
| (17,10) | open | | 146,601,550,364 | | | — |
| (18,3) | **614** | 100.00 | 614 | PG(2,17) incidence graph (Moore graph) | apsp: checks/d18D3_n614_pg2_17.apsp.txt | 614 (PG(2,17) incidence graph (Moore)) |
| (18,4) | **10,440** | 100.00 | 10,440 | W(17) incidence graph (Moore graph) | apsp: checks/d18D4_n10440_W17.apsp.txt | 10,440 (W(17) incidence graph (Moore)) |
| (18,5) | **47,600** | 26.82 | 177,476 | multi-doubled-matching lift of W(13): 2 doubled matchings, Z2 x Z5 (18-regular) | apsp: checks/d18D5_n47600_W13_2dm_Z10.apsp.txt | 42,840 (polygon cover 9xW(13) (j=4)) |
| (18,6) | open | | 3,017,196 | | | 3,017,196 (H(17) incidence graph (Moore)) |
| (18,7) | open | | 51,292,328 | | | 7,240,212 (polygon cover 9xH(13) (j=4)) |
| (18,8) | open | | 871,969,674 | | | 108,603,180 ([unpublished 2013 green formula, no construction known] q=13, j=4) |
| (18,9) | open | | 14,823,484,556 | | | — |
| (18,10) | open | | 251,999,237,550 | | | — |
| (19,3) | **624** | 90.96 | 686 | fourth hat R(17;2,3), POLISHED.md Thm 2.2 (19-regular) | apsp: checks/d19D3_n624_fourthhat_q17.apsp.txt | 624 (fourth hat, q=17 (POLISHED Thm 2.2)) |
| (19,4) | **10,982** | 88.92 | 12,350 | AS(17) + clones of two elliptic quadrics, POLISHED.md Cor. A1 (19-regular) | apsp: checks/d19D4_n10982_AS17_clones.apsp.txt | 10,982 (Thm B, q=17: 2q^2 Delta) |
| (19,5) | open | | 222,296 | | | 52,428 (doubled matching 6x W(16) (DM_D5, annealed)) |
| (19,6) | open | | 4,001,438 | | | 3,203,968 (Thm D, q=17, m=2) |
| (19,7) | open | | 72,025,880 | | | 11,184,810 (polygon cover 5xH(16) (j=2)) |
| (19,8) | open | | 1,296,465,944 | | | 159,284,664 ([unpublished 2013 green formula, no construction known] q=13, j=5) |
| (19,9) | open | | 23,336,387,096 | | | — |
| (19,10) | open | | 420,054,967,832 | | | — |
| (20,3) | **762** | 100.00 | 762 | PG(2,19) incidence graph (Moore graph) | apsp: checks/d20D3_n762_pg2_19.apsp.txt | 762 (PG(2,19) incidence graph (Moore)) |
| (20,4) | **14,480** | 100.00 | 14,480 | W(19) incidence graph (Moore graph) | apsp: checks/d20D4_n14480_W19.apsp.txt | 14,480 (W(19) incidence graph (Moore)) |
| (20,5) | **75,000** | 27.26 | 275,116 | route-chart lift over F5 (4 letters x 5 scalars, fibre F5^4): K3,3 + doubled matching over Z20 (m = 60), chart with 22 singular patterns (squad r1 c04); also 66,640 by the multi-doubled-matching lift of W(13), Z2 x Z7 (MDM.md) | apsp: checks/d20D5_n75000_routechart_F5_Z20.apsp.txt; checks/d20D5_n66640_W13_3dm_Z14.apsp.txt | 82,500 (route chart 4 letters x F5, m=66 controller (2*m*q^4)) |
| (20,6) | open | | 5,227,320 | | | 5,227,320 (H(19) incidence graph (Moore)) |
| (20,7) | open | | 99,319,076 | | | 15,658,734 (polygon cover 7xH(16) (j=3)) |
| (20,8) | open | | 1,887,062,554 | | | 219,619,764 ([unpublished 2013 green formula, no construction known] q=13, j=6) |
| (20,9) | open | | 35,854,188,636 | | | — |
| (20,10) | open | | 681,229,584,194 | | | — |
| (3,11) | **1,008** | 24.62 | 4,088 | Haar graph of PSL(2,7) x Z3, S = {e, x, y} | apsp: research/squads/beyond/r1/c11/check_n1008.txt; director re-run VALID | — |
| (4,11) | **17,600** | 9.94 | 177,140 | metacyclic Haar graph Z440 x| Z20 (r = 107) | apsp (c13 and director) | — |
| (5,11) | **158,928** | 5.68 | 2,796,196 | Haar graph SL(2,43), S = {e} + 2 orbits of size 2 | build_haar2.py (c14 and director) | — |
| (6,11) | **659,568** | 2.70 | 24,414,056 | Haar graph SL(2,13) x Z151, S = 2 free orbits of size 3 | build_haar2.py (c14 and director) | — |
| (7,11) | **10,648,176** | 7.34 | 145,118,816 | Haar graph SL(2,43) x Z67, S = {e} + 2 orbits of size 3 | hcheck5 VALID (runs/check_hcheck5_d7D11_sl_43_67_orb3_s1.txt) | — |
| (8,11) | **43,702,560** | 6.63 | 659,108,908 | Haar graph SL(2,89) x Z31, S = {e} + 1 fixed + 2 orbits of size 3 | hcheck5 VALID (runs/check_hcheck5_d8D11_sl_89_31_orb3_s1.txt) | — |
| (9,11) | open | | 2,454,267,020 | | | — |
| (10,11) | open | | 7,845,264,896 | | | — |
| (3,12) | **1,320** | 16.12 | 8,184 | Haar graph of PSL(2,11), S = {e, a, b} | apsp: c12/checks/apsp_3_12_n1320_psl2_11.txt; director re-run VALID | — |
| (4,12) | **48,000** | 9.03 | 531,434 | metacyclic Haar graph Z1200 x| Z20 (r = 413) | apsp (c13 and director) | — |
| (5,12) | **229,824** | 2.05 | 11,184,804 | Haar graph PSL(2,3) x PSL(2,7) x Z57 | build_haar2.py (c14 and director) | — |
| (6,12) | open | | 122,070,306 | | | — |
| (7,12) | **56,297,592** | 6.47 | 870,712,928 | Haar graph PSL(2,163) x Z13, S = {e} + 2 orbits of size 3 | hcheckpsl VALID (runs/check_hcheckpsl_d7D12_psl_163_13_orb3_s1.txt) | — |
| (8,12) | **268,496,208** | 5.82 | 4,613,762,394 | Haar graph SL(2,163) x Z31, S = {e} + 1 fixed + 2 orbits of size 3 | hcheck5 VALID (runs/check_hcheck5_d8D12_sl_163_31_orb3_s1.txt) | — |
| (9,12) | **1,055,973,600** | 5.38 | 19,634,136,204 | Haar graph SL(2,199) x Z67, S = {e} + 2 fixed + 2 orbits of size 3 | hcheck5 VALID (runs/check_hcheck5_d9D12_sl_199_67_orb3_s1.txt) | — |
| (10,12) | open | | 70,607,384,114 | | | — |
<!-- /TABLE -->

## Notes by diameter

(filled in below as the run goes)
