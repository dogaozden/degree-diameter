# Beyond the 2013 table: first values for 48 new cells

Job new-cells-beyond (Opus director + Haiku squads, cloud session, 2026-10-26, branch claude/new-cells-beyond-etos3t).
The 2013 bipartite table (DS14v2, Table 4) stops at Δ = 16 and D = 10. This file gives a checked lower bound for every
cell in the next band: Δ = 17..20 at D = 3..10 (32 cells) and D = 11, 12 at Δ = 3..10 (16 cells), with an upper bound
and the comparison with the formula families. As far as we know (literature card r2/d10) no bipartite values have been
published for these cells, so every value here is a first value, not a record.

## Summary

- **Optimal (Moore graphs), 9 cells:** (17|18|20, 3), (17|18|20, 4), (17|18|20, 6) — incidence graphs of PG(2,q),
  W(q), H(q) with q = Δ − 1 = 16, 17, 19.
- **Theorems of the lab, Δ = 19:** (19,3) 624 (fourth hat), (19,4) 10,982 (Theorem A), (19,6) 3,203,968 (Theorem D).
- **D = 5, new construction:** multi-doubled-matching lifts of W(q) (MDM.md): (18,5) 47,600 and, inside the old
  table, a record (13,5) 11,700 (was 11,486). (19,5) 52,428 is the k = 1 case (DM on W(16)); (20,5) 75,000 is a
  route-chart lift over F5 from squad round 1. (17,5) has only the floor 33,792 (the (16,5) graph).
- **D = 7:** level graphs (polygon covers) of H(13) and H(16), 5.6M–15.7M vertices (classical theorem).
- **D = 8 .. 12:** Haar graphs of SL(2,p) × Z_n / PSL(2,p) × Z_n with automorphism-orbit generator sets, up to
  billions of vertices, each checked by an independent low-memory BFS from both sides; the small cells (Δ = 3, 4) by
  exhaustive or annealed Haar searches.
- Every value is at least the trivial floor from the neighbouring cells (n_b(Δ,D) ≥ n_b(Δ−1,D), n_b(Δ,D−1)).

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
| (17,6) | **2,236,962** | 100.00 | 2,236,962 | H(16) incidence graph (split Cayley hexagon; Moore graph) | classical (Tits); built with research/d10D7/hexgen2.c, BFS from 94 vertices: ecc 6 and Moore level sizes (checks/d17D6_n2236962_H16.sampled.txt) | 2,236,962 (H(16) incidence graph (Moore)) |
| (17,7) | **5,631,276** | 15.73 | 35,791,388 | level graph of H(13): 7 copies joined by 3 matchings, voltages 1, 2, 3 in Z7 (polygon cover; D7_HEXAGON.md Thm A) | theorem (any matchings); builder all-pairs at q = 3, 4, r = 1..3 (r1/c09 small/); this instance: BFS from 64 random vertices, max ecc 7 (checks/d7_levelgraphs_sampled.txt) | 5,631,276 (polygon cover 7xH(13) (j=3)) |
| (17,8) | **41,373,072** | 7.22 | 572,662,300 | Haar graph SL(2,53) x Z139, S = {e} + 1 fixed + 5 orbits of size 3 | haarcheck_sl (c15) and hcheck5 (director): VALID | 2013-table D=8 pattern (no construction known): 67,575,312 (q=13, j=3); Haar size law at mu = 5: 2N = 3.78e+07 |
| (17,9) | **501,707,400** | 5.48 | 9,162,596,892 | Haar graph PSL(2,101) x Z487, S = {e} + 1 fixed + 5 orbits of size 3 | hcheckpsl VALID (runs/check_hcheckpsl_d17D9_psl_101_487_orb3_s2.txt) | Haar size law at mu = 5: 2N = 5.16e+08 |
| (17,10) | **7,022,052,336** | 4.79 | 146,601,550,364 | Haar graph PSL(2,313) x Z229, S = {e} + 1 fixed + 5 orbits of size 3 | hcheckpsl VALID (runs/check_hcheckpsl_d17D10_psl_313_229_orb3_s1.txt) | Haar size law at mu = 5: 2N = 7.19e+09 |
| (18,3) | **614** | 100.00 | 614 | PG(2,17) incidence graph (Moore graph) | apsp: checks/d18D3_n614_pg2_17.apsp.txt | 614 (PG(2,17) incidence graph (Moore)) |
| (18,4) | **10,440** | 100.00 | 10,440 | W(17) incidence graph (Moore graph) | apsp: checks/d18D4_n10440_W17.apsp.txt | 10,440 (W(17) incidence graph (Moore)) |
| (18,5) | **47,600** | 26.82 | 177,476 | multi-doubled-matching lift of W(13): 2 doubled matchings, Z2 x Z5 (18-regular) | apsp: checks/d18D5_n47600_W13_2dm_Z10.apsp.txt | 42,840 (polygon cover 9xW(13) (j=4)) |
| (18,6) | **3,017,196** | 100.00 | 3,017,196 | H(17) incidence graph (Moore graph) | classical; BFS from 96 vertices: ecc 6, Moore levels (checks/d18D6_n3017196_H17.sampled.txt) | 3,017,196 (H(17) incidence graph (Moore)) |
| (18,7) | **7,240,212** | 14.12 | 51,292,328 | level graph of H(13): 9 copies, 4 matchings, Z9 | same theorem; BFS from 64 random vertices, max ecc 7 (checks/d7_levelgraphs_sampled.txt) | 7,240,212 (polygon cover 9xH(13) (j=4)) |
| (18,8) | **57,637,680** | 6.61 | 871,969,674 | Haar graph SL(2,61) x Z127, S = {e} + 2 fixed + 5 orbits of size 3 | hcheck5 VALID (runs/check_hcheck5_d18D8_sl_61_127_orb3_s2.txt) | 2013-table D=8 pattern (no construction known): 108,603,180 (q=13, j=4); Haar size law at mu = 5: 2N = 5.61e+07 |
| (18,9) | **790,626,816** | 5.33 | 14,823,484,556 | Haar graph SL(2,127) x Z193, S = {e} + 2 fixed + 5 orbits of size 3 | hcheck5 VALID (runs/check_hcheck5_d18D9_sl_127_193_orb3_s2.txt) | Haar size law at mu = 5: 2N = 8.14e+08 |
| (18,10) | **11,787,972,672** | 4.68 | 251,999,237,550 | Haar graph PSL(2,223) x Z1063, S = {e} + 2 fixed + 5 orbits of size 3 | hcheckpsl VALID, ecc 10/10 (runs/check_hcheckpsl_d18D10_psl_223_1063_orb3_s1.txt) | Haar size law at mu = 5: 2N = 1.21e+10 |
| (19,3) | **624** | 90.96 | 686 | fourth hat R(17;2,3), POLISHED.md Thm 2.2 (19-regular) | apsp: checks/d19D3_n624_fourthhat_q17.apsp.txt | 624 (fourth hat, q=17 (POLISHED Thm 2.2)) |
| (19,4) | **10,982** | 88.92 | 12,350 | AS(17) + clones of two elliptic quadrics, POLISHED.md Cor. A1 (19-regular) | apsp: checks/d19D4_n10982_AS17_clones.apsp.txt | 10,982 (Thm B, q=17: 2q^2 Delta) |
| (19,5) | **52,428** | 23.58 | 222,296 | doubled-matching lift of W(16) over Z6 (DM_D5.md; = MDM with k = 1); nu, sigma annealed by squad r1/c05 (dmfast, routes allowed) | apsp: checks/d19D5_n52428_W16_dm_Z6.apsp.txt | 52,428 (doubled matching 6x W(16) (DM_D5, annealed)) |
| (19,6) | **3,203,968** | 80.07 | 4,001,438 | Theorem D of POLISHED.md, q = 17, m = 2 (doubling of H(17) with levels and exact whiskers; max degree 19) | theorem (paper + Lean for all odd q); builder checked all-pairs at q = 5, 7 (checks/thmD_builder_q5_q7.apsp.txt); q = 17 instance: BFS from 96 vertices, ecc 6 (checks/d19D6_n3203968_thmD_q17.sampled.txt) | 3,203,968 (Thm D, q=17, m=2) |
| (19,7) | **11,184,810** | 15.53 | 72,025,880 | level graph of H(16): 5 copies joined by 2 matchings, voltages 1, 2 in Z5 (polygon cover; D7_HEXAGON.md Thm A) | theorem (any matchings); builder all-pairs at q = 3, 4, r = 1..3 (r1/c09 small/); this instance: BFS from 64 random vertices, max ecc 7 (checks/d7_levelgraphs_sampled.txt) | 11,184,810 (polygon cover 5xH(16) (j=2)) |
| (19,8) | **86,317,296** | 6.66 | 1,296,465,944 | Haar graph PSL(2,103) x Z79, S = {e} + 6 orbits of size 3 | hcheckpsl VALID (runs/check_hcheckpsl_d19D8_psl_103_79_orb3_s1.txt) | 22,369,620 (polygon cover n+2: 10x H(16)); 2013-table D=8 pattern (no construction known): 159,284,664 (q=13, j=5); Haar size law at mu = 5: 2N = 8.15e+07 |
| (19,9) | **1,218,394,320** | 5.22 | 23,336,387,096 | Haar graph SL(2,131) x Z271, S = {e} + 6 orbits of size 3 | hcheck5 VALID (runs/check_hcheck5_d19D9_sl_131_271_orb3_s2.txt) | Haar size law at mu = 5: 2N = 1.25e+09 |
| (19,10) | **19,233,722,496** | 4.58 | 420,054,967,832 | Haar graph SL(2,607) x Z43, S = {e} + 6 orbits of size 3 | hcheck5 VALID, ecc 10/10 (runs/check_hcheck5_d19D10_sl_607_43_orb3_s1.txt) | Haar size law at mu = 5: 2N = 1.96e+10 |
| (20,3) | **762** | 100.00 | 762 | PG(2,19) incidence graph (Moore graph) | apsp: checks/d20D3_n762_pg2_19.apsp.txt | 762 (PG(2,19) incidence graph (Moore)) |
| (20,4) | **14,480** | 100.00 | 14,480 | W(19) incidence graph (Moore graph) | apsp: checks/d20D4_n14480_W19.apsp.txt | 14,480 (W(19) incidence graph (Moore)) |
| (20,5) | **75,000** | 27.26 | 275,116 | route-chart lift over F5 (4 letters x 5 scalars, fibre F5^4): K3,3 + doubled matching over Z20 (m = 60), chart with 22 singular patterns (squad r1 c04); also 66,640 by the multi-doubled-matching lift of W(13), Z2 x Z7 (MDM.md) | apsp: checks/d20D5_n75000_routechart_F5_Z20.apsp.txt; checks/d20D5_n66640_W13_3dm_Z14.apsp.txt | 82,500 (route chart 4 letters x F5, m=66 controller (2*m*q^4)) |
| (20,6) | **5,227,320** | 100.00 | 5,227,320 | H(19) incidence graph (Moore graph) | classical; BFS from 100 vertices: ecc 6, Moore levels (checks/d20D6_n5227320_H19.sampled.txt) | 5,227,320 (H(19) incidence graph (Moore)) |
| (20,7) | **15,658,734** | 15.77 | 99,319,076 | level graph of H(16): 7 copies, 3 matchings, Z7 | same theorem; BFS from 64 random vertices, max ecc 7 (checks/d7_levelgraphs_sampled.txt) | 15,658,734 (polygon cover 7xH(16) (j=3)) |
| (20,8) | **122,739,120** | 6.50 | 1,887,062,554 | Haar graph PSL(2,71) x Z343, S = {e} + 1 fixed + 6 orbits of size 3 | hcheckpsl VALID (runs/check_hcheckpsl_d20D8_psl_71_343_orb3_s1.txt) | 30,171,960 (polygon cover n+2: 10x H(17)); 2013-table D=8 pattern (no construction known): 219,619,764 (q=13, j=6); Haar size law at mu = 5: 2N = 1.16e+08 |
| (20,9) | **1,823,175,864** | 5.08 | 35,854,188,636 | Haar graph PSL(2,163) x Z421, S = {e} + 1 fixed + 6 orbits of size 3 | hcheckpsl VALID (runs/check_hcheckpsl_d20D9_psl_163_421_orb3_s2.txt) | Haar size law at mu = 5: 2N = 1.88e+09 |
| (20,10) | **30,518,778,360** | 4.48 | 681,229,584,194 | Haar graph PSL(2,421) x Z409, S = {e} + 1 fixed + 6 orbits of size 3 | hcheckpsl VALID, ecc 10/10 (runs/check_hcheckpsl_d20D10_psl_421_409_orb3_s1.txt) | Haar size law at mu = 5: 2N = 3.12e+10 |
| (3,11) | **1,474** | 36.00 | 4,088 | metacyclic Haar graph Z67 x|_9 Z11, S = {e, 67, 336} (director sweep of all metacyclic groups of order 541-1,100, exhaustive pairs); earlier 1,080 (A5 x Z9, r3/e01) | apsp VALID, diameter exactly 11 (checks/d3D11_n1474_meta67_11_9.apsp.txt) | Haar size law at mu = 5: 2N = 908 |
| (4,11) | **19,152** | 10.81 | 177,140 | Haar graph SL(2,8) x Z19, S = {e} + 1 orbit of size 3 (haar_sym, squad r3/e03); earlier 18,480 (SL(2,11) x Z7) | apsp (director: checks/d4D11_n19152_sl8xZ19.apsp.txt), build_haar2.py (e03) | Haar size law at mu = 5: 2N = 2.29e+04 |
| (5,11) | **253,080** | 9.05 | 2,796,196 | Haar graph PSL(2,19) x Z37, random S (haar_sym, director); earlier 158,928 (r1/c14) | hcheckpsl and build_haar2.py VALID (checks/d5D11_psl_19_37_s1.check.txt) | Haar size law at mu = 5: 2N = 2.74e+05 |
| (6,11) | **1,971,744** | 8.08 | 24,414,056 | Haar graph PSL(2,47) x Z19, S = 2 free orbits of size 3 (haar_sym ORBIT 3 2 0, director); earlier 659,568 (r1/c14) | hcheckpsl and build_haar2.py VALID (checks/d6D11_psl_47_19_orb3f0_s1.check.txt) | Haar size law at mu = 5: 2N = 2e+06 |
| (7,11) | **10,648,176** | 7.34 | 145,118,816 | Haar graph SL(2,43) x Z67, S = {e} + 2 orbits of size 3 | hcheck5 VALID (runs/check_hcheck5_d7D11_sl_43_67_orb3_s1.txt) | Haar size law at mu = 5: 2N = 1.05e+07 |
| (8,11) | **43,702,560** | 6.63 | 659,108,908 | Haar graph SL(2,89) x Z31, S = {e} + 1 fixed + 2 orbits of size 3 | hcheck5 VALID (runs/check_hcheck5_d8D11_sl_89_31_orb3_s1.txt) | Haar size law at mu = 5: 2N = 4.31e+07 |
| (9,11) | **145,258,344** | 5.92 | 2,454,267,020 | Haar graph PSL(2,197) x Z19, S = {e} + 2 fixed + 2 orbits of size 3 | hcheckpsl VALID (runs/check_hcheckpsl_d9D11_psl_197_19_orb3_s4.txt) | Haar size law at mu = 5: 2N = 1.49e+08 |
| (10,11) | **445,709,568** | 5.68 | 7,845,264,896 | Haar graph SL(2,193) x Z31, S = {e} + 3 orbits of size 3 | hcheck5 VALID (runs/check_hcheck5_d10D11_sl_193_31_orb3_s1.txt) | Haar size law at mu = 5: 2N = 4.45e+08 |
| (3,12) | **1,958** | 23.91 | 8,184 | metacyclic Haar graph Z89 x|_2 Z11, S = {e, 178, 535} (director sweep of metacyclic groups of order 931-2,500, exhaustive pairs); earlier 1,860 (AGL(1,31), r3/e02) | apsp VALID, diameter exactly 12 (checks/d3D12_n1958_meta89_11_2.apsp.txt) | Haar size law at mu = 5: 2N = 1.61e+03 |
| (4,12) | **50,160** | 9.44 | 531,434 | Haar graph SL(2,11) x Z19, S = {e} + 1 orbit of size 3 (haar_sym, squad r2/d09); earlier 48,000 metacyclic (r1/c13) | apsp (d09 and director: checks/d4D12_n50160_sl11xZ19.apsp.txt), build_haar2.py, haarcheck_sl | Haar size law at mu = 5: 2N = 6.1e+04 |
| (5,12) | **912,576** | 8.16 | 11,184,804 | Haar graph PSL(2,97), random S (haar_sym, director); earlier 229,824 (r1/c14) | hcheckpsl and build_haar2.py VALID (checks/d5D12_psl_97_1_s1.check.txt) | Haar size law at mu = 5: 2N = 9.74e+05 |
| (6,12) | **9,303,840** | 7.62 | 122,070,306 | Haar graph SL(2,71) x Z13, S = 2 free orbits of size 3 (haar_sym ORBIT 3 2 0); earlier 8,924,736 (SL(2,47) x Z43) | hcheck5 VALID (checks/d6D12_sl_71_13_orb3f0_s2.check.txt) | Haar size law at mu = 5: 2N = 8.91e+06 |
| (7,12) | **56,297,592** | 6.47 | 870,712,928 | Haar graph PSL(2,163) x Z13, S = {e} + 2 orbits of size 3 | hcheckpsl VALID (runs/check_hcheckpsl_d7D12_psl_163_13_orb3_s1.txt) | Haar size law at mu = 5: 2N = 5.6e+07 |
| (8,12) | **268,496,208** | 5.82 | 4,613,762,394 | Haar graph SL(2,163) x Z31, S = {e} + 1 fixed + 2 orbits of size 3 | hcheck5 VALID (runs/check_hcheck5_d8D12_sl_163_31_orb3_s1.txt) | Haar size law at mu = 5: 2N = 2.7e+08 |
| (9,12) | **1,055,973,600** | 5.38 | 19,634,136,204 | Haar graph SL(2,199) x Z67, S = {e} + 2 fixed + 2 orbits of size 3 | hcheck5 VALID (runs/check_hcheck5_d9D12_sl_199_67_orb3_s1.txt) | Haar size law at mu = 5: 2N = 1.06e+09 |
| (10,12) | **3,500,976,768** | 4.96 | 70,607,384,114 | Haar graph PSL(2,193) x Z487, S = {e} + 3 orbits of size 3 | hcheckpsl VALID (runs/check_hcheckpsl_d10D12_psl_193_487_orb3_s1.txt) | Haar size law at mu = 5: 2N = 3.58e+09 |
<!-- /TABLE -->

## Notes by diameter

### D = 3 and D = 4 (squad r1/c01, r1/c02, r1/c03)

Δ = 17, 18, 20: incidence graphs of PG(2,q) and W(q), q = Δ − 1 = 16, 17, 19 (Moore graphs, optimal). Δ = 19: the
fourth-hat graph R(17; 2, 3) of POLISHED.md Theorem 2.2 (624 = 2(q² + q + 6), 19-regular) and Corollary A1 of
POLISHED.md (AS(17) plus one clone of each point of two elliptic quadrics, 10,982 = 2q²(q+2), 19-regular). All eight
graphs were built from the definitions, saved, and checked all-pairs twice (card and director). Upper bounds at
Δ = 19 are the Moore bounds 686 and 12,350 (a plane / quadrangle of order 18 is not ruled out). c01 also tried to add
a pair to R(17;2,3) by deleting flags; every single deletion breaks a concurrency, so no quick +1 pair (analysis only).
c03 tried Theorem B on Q(4,q) (ovoid clones plus shadow lines on lines pairwise disjoint off the ovoid): it gives
(2q+3)(q²+1) + |M| and beats Theorem A iff |M| > q² − 2q − 3. At q = 5 it reproduces the lab's (7,4) = 359 (|M| = 21),
but at q = 9 the best |M| found was 54 against the 61 needed, so it is not expected to beat 10,982 at q = 17.

### D = 5

- **Multi-doubled-matching lifts (new, MDM.md).** DM_D5.md's Z6 lift of W(q) with one doubled matching extends to k
  doubled matchings over Z2 × Z(2k+1): degree q+1+2k, 4(2k+1)(q+1)(q²+1) vertices, diameter ≤ 5 as soon as one
  parity labelling ν of the flags splits the q+1 geodesics of every opposite pair (condition (A)); the matchings can be
  anything. On W(13), dmfast with NOROUTE=1 finds such a ν in 8 seconds (641 failing pairs at random). One ν gives
  (16,5) 28,560, (18,5) **47,600** and (20,5) 66,640. The polygon covers with plain matchings give one sheet less per
  pair of extra degrees (9 and 13 copies of W(13) at Δ = 18, 20). A referee card (r2/d06) found no gap in the proof,
  and a ν with exactly one pair failing (A) gives diameter 6, as the proof predicts.
- **(19,5) 52,428**: the k = 1 case (DM_D5.md) on W(16); ν and σ from card r1/c05's dmfast run (routes allowed),
  lift built and checked by the director. The polygon cover 11·|W(13)| = 52,360 holds for any matchings.
- **(20,5) 75,000: route-chart lift over F5 (squad r1/c04).** The (16,5) record's construction with fibre F5⁴ (degree
  4·5 = 20): a pencil-complete chart with 22 singular nonbacktracking 4-patterns (of 216) and K3,3 + doubled matching
  lifted by Z20 (60 controller vertices per side), above the MDM value 66,640. Z21 and Z22 stall at 2 and 4 uncovered
  pairs (r2/d01, also with a 20-singular chart); 5 letters × F4 gives 51,200 (r2/d02).
- **(17,5) 33,792 (floor only)**: the (16,5) route-chart lift itself (maximum degree 16 ≤ 17). Nothing larger was
  found: MDM needs an even number of extra degrees over W(q) (Δ = 17 = 14 + 3 at q = 13; a plain extra matching adds
  no sheet), the polygon cover 7·|W(13)| = 33,320 is smaller, three parallel copies over Z9 fail by counting (DM_D5.md),
  blind annealing of Z8 lifts of W(13) stayed in the millions of uncovered pairs (r1/c06), a route chart with a plain
  fifth letter stayed at 1.2M (r2/d04), building flag graphs cap at 31,460 (r1/c16), and Haar graphs at D = 5 sit near
  19k. Spare degree on the 28,560-vertex MDM lift of W(13) could carry at most 28,560/17 hub vertices (30,240 total).

### Side result inside the old table: (13,5) ≥ 11,700

The multi-doubled-matching lift with q = 8, k = 2 (W(8), Z2 × Z5, 13-regular) has 11,700 vertices. Pure condition (A)
stalls near 20 failing pairs on W(8), but routes through the two matchings cover them: squad card r2/d05 annealed ν,
σ_1, σ_2 against the route-aware count and reached 0 in about two minutes. apsp and bfs_all both give diameter exactly
5; the graph is rebuilt identically from the card's saved state. The previous best for (13,5) was 11,486 (lab, unit
design), table 11,480. Files: graphs/d13D5_n11700_W8_2dm_Z10.edges.gz, checks/d13D5_n11700_W8_2dm_Z10.check.txt.
No other cell of the old table improves this way (MDM.md).

### D = 6 and D = 7: formula families, sampled checks

- D = 6, Δ = 17, 18, 20: H(16), H(17), H(19) (split Cayley hexagon, Tits; Moore graphs, 2.2M–5.2M vertices).
  Δ = 19: Theorem D of POLISHED.md at q = 17, m = 2 (3,203,968 vertices, maximum degree 19), proved for every odd q
  and Lean-checked for every finite field of odd characteristic. All-pairs BFS of 2–5M-vertex graphs is out of reach
  here (n²Δ/64 word operations); squad card r1/c08 built each graph (the lab's hexgen2.c and a faster variant with
  identical output; its own Theorem D builder) and ran BFS from 94–100 vertices each (random plus a whole point and
  line neighbourhood): eccentricity 6, and for H(q) the level sizes 1, q+1, (q+1)q, … of a Moore graph. The Theorem D
  builder was checked all-pairs at q = 5 (9,592, the lab's (7,6) value) and q = 7 (45,428).
- D = 7: level graphs (polygon covers) of H(q): 2r+1 copies of H(q) joined by r perfect matchings with voltages
  1..r in Z(2r+1), diameter ≤ 7 for any matchings (D7_HEXAGON.md Theorem A, classical; REGULARITIES.md §1.3). Best
  (q, r) per cell: (17,7) q = 13, r = 3; (18,7) q = 13, r = 4; (19,7) q = 16, r = 2; (20,7) q = 16, r = 3. Card r1/c09
  wrote the builder (lift7.c) and checked it all-pairs at q = 3, 4 (r = 1..3); the director ran its bit-parallel BFS
  from 64 random vertices on each of the four instances (max eccentricity 7, checks/d7_levelgraphs_sampled.txt).
  Hub surgery (D7_HEXAGON.md, card r3/e04) was verified at q = 4, 5 but its hub condition was not established for
  q = 13, 16; the predicted gains are 0.1–0.4 %, so the plain covers are listed.
- Haar graphs and random constructions are far below these values at D = 6, 7 (size law: about 0.5M at (19,6) and
  2.9M at (17,7)).

### D = 11, 12 at small Δ

Δ = 3: (3,11) 1,080 = Haar graph of A5 × Z9 and (3,12) 1,860 = Haar graph of AGL(1,31). Card r3/e01 searched all
pairs {x, y} exhaustively for about 45 groups of order 504–1,100 at D = 11 (A5 × Z9 the only one above 1,008; AGL(1,23)
misses by one hole); metacyclic scans (r1/c11), voltage lifts of small cubic bases (r2/d07, r2/d08) and annealing over
PSL/SL/PGL(2,q) (r1/c12: SL(2,11) cost 16, PSL(2,13) cost 24 at D = 12) found nothing larger. Δ = 4: Haar graphs
SL(2,8) × Z19 (D = 11) and SL(2,11) × Z19 (D = 12) with S = {e} ∪ one orbit of size 3 (r3/e03, r2/d09), above the
metacyclic values 17,600 / 48,000 of r1/c13; at D = 12, PSL(2,11) × Z39 (51,480) misses by one hole. Δ = 5, 6:
haar_sym (plain random S at Δ = 5, two free 3-orbits at Δ = 6) at μ ≈ 2–10, solved in seconds, 2–4 times the
round-1 card values. Δ = 7..10: haar_big.

### D = 8 .. 12: Haar graphs

H(G,S) with G = SL(2,p) × Z_n or PSL(2,p) × Z_n and S = {e} ∪ (fixed generators) ∪ (orbits of an automorphism α of
order 3), found with research/bighaar/haar_big.c (64-bit indices, N/2 bytes of memory). This job added odd D to
haar_big: for odd D the same-side words from (e,A) are (S⁻¹S)^k but from (e,B) they are (SS⁻¹)^k, which differ for a
non-abelian G, so the cost is the hole count of H(G,S) plus that of H(G,S⁻¹) (a first version counted only one side;
the independent checkers, which BFS from both sides, caught it on a (10,11) candidate, and that file was discarded). It
also added fixed generators (ORBIT f > 1: f − 1 random α-fixed elements kept fixed; with f = 3 at μ ≈ 12 this stalled
at (18,8), at μ ≈ 8 it solved). Group orders were chosen with the size law (SIZE_LAW.md) at μ = N·e^(−W/N) ≈ 3–13
(per side), with small cyclic factors n: SL(2,23) × Z433 at (7,11) stalled at 31 holes for 1,000 evaluations, while
SL(2,43) × Z67 at the same order solved in 25 (with 7 generators, 10-step words do not spread evenly over Z433).
Order-2 orbits did much worse than order-3 orbits at (9,11) and (5,11) (181 and 388 holes). At D = 10 and D = 12,
μ ≈ 3 solved in 1–9 evaluations even at N = 1.5·10¹⁰. Each find was checked by hcheck5 (SL) or hcheckpsl (PSL), which
BFS from (e,A) and (e,B) in 4 bits per element; the largest, (20,10) with 30.5 billion vertices, needs 7.6 GB.
Values are typical size-law values, not pushed to the limit (the lab's orbit searches gain 5–15 % in comparable cells
at much higher cost, and each check of a 10¹⁰-element group takes about an hour here).

## What failed, and why it matters for the next attempt

- (17,5) has no construction of its own (see D = 5). It is the one cell where the formula families leave a gap:
  MDM and polygon covers want q + 1 + (even) = Δ, route charts want Δ = letters × field size, and 17 is neither for any
  usable q. A degree-17 idea that adds a sheet with one extra edge per vertex is the open problem.
- Route charts over F3 (6 letters) and F2 (9 letters) were far from competitive in 25-minute boxes (best 29,160 at
  (18,5)); the singular-pattern counts of the charts (312 of 1,500 over F3) look like the bottleneck.
- The 2013 table's D = 8 values follow (2j+1)(⌊(q−1)/2⌋ + 3(j−1))·|H(q)| (REGULARITIES.md); card r1/c10 found a Z20
  lift of H(3) + 2 matchings with diameter 8 (14,560 = the pattern's value at q = 3, j = 2) by annealing, but q = 4
  stalled at 150 holes. If that construction were known it would give about 1.6–1.9 times our Haar values at D = 8
  (e.g. (20,8) ≥ 2.2·10⁸ against 1.2·10⁸).
- Blind voltage annealing on W(13) (r1/c06, r1/c07) failed where the structured MDM lift succeeds in seconds: the
  structure (one parity condition, matchings free) mattered more than search effort.

## Rebuilding

- Edge lists: graphs/*.edges.gz (first line n, then "u v"); check with research/lifts/coordinator_check/apsp.c.
- Haar graphs: research/frontier/sols/d<Δ>D<D>_*.txt; check with research/frontier/build_haar2.py (small),
  research/squads/d16D10-r1/c5/hcheck5.c (SL) or research/squads/d16D10-r2/checker/hcheckpsl.c (PSL); search runs and
  check logs in runs/ (runs/check_*), job lists in queue*.txt, driver hq.sh / runq.sh.
- MDM lifts: mdm/build_mdm.py with mdm/nu_q13_s2.txt (q = 13) or mdm/dm_q16_s11_c05.sol.gz (q = 16); (13,5) from
  research/squads/beyond/r2/d05/ (mdm8.c, st_run2.txt; command in its scoreboard line).
- D = 6: research/squads/beyond/r1/c08/ (hexgen2fast.c, thmd.c, hexbfs.c). D = 7: research/squads/beyond/r1/c09/lift7.c
  (`lift7 q r seed edges OUT` or `lift7 q r seed bfs 64`).
- The table below the summary is generated by results.py (one entry per cell) and splice.py; plan.py and groups.py
  give the Moore bounds, formula families, size-law orders and candidate groups.
