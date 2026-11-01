# Beyond the 2013 table: first values for 69 new cells

Job new-cells-beyond (Opus director + Haiku squads, cloud session, 2026-10-26, branch claude/new-cells-beyond-etos3t).
The 2013 bipartite table (DS14v2, Table 4) stops at Δ = 16 and D = 10. This file gives a checked lower bound for every
cell in the next band: Δ = 17..20 at D = 3..10 (32 cells) and D = 11, 12 at Δ = 3..10 (16 cells), with an upper bound
and the comparison with the formula families. As far as we know (literature card r2/d10) no bipartite values have been
published for these cells, so every value here is a first value, not a record.

Extended 2026-11-01 by job beyond-d11 (branch claude/new-cells-d11-d12-beyond-8sas9r): seven more cells, D = 11 at
Δ = 11..14 and D = 12 at Δ = 11..13, and new values for (4..10, 11) and (4..10, 12); see the section "D = 11 at
Δ = 11..14 and D = 12 at Δ = 11..13" below.

Extended 2026-11-01 by job beyond-d13 (branch claude/beyond-d13-search-z35z61): fourteen more cells, D = 13 at Δ = 3..10
and D = 14 at Δ = 3..8, and new values for (4,11), (5,11), (4,12), (5,12); see the section "D = 13 at Δ = 3..10 and
D = 14 at Δ = 3..8" below.

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
- **D = 11 at Δ = 11..14, D = 12 at Δ = 11..13 (beyond-d11):** Haar graphs of SL(2,p) x Z_n (odd D) and
  PSL(2,p) x Z_n (even D) with alpha-orbit generator sets, 1.24 to 20.0 billion vertices; (12,12) and (13,12) sit at the
  job's 20-billion-vertex size limit. At odd D the hard elements are involutions and central elements (exact lemma and
  hole counts in research/frontier/beyond11/ODD_D_HOLES.md), which is why SL with small n is used there.
- **D = 13 at Δ = 3..10, D = 14 at Δ = 3..8 (beyond-d13):** Δ = 3: cyclic voltage lifts of the Desargues graph
  (Z166 and Z280); Δ = 4, 5: Haar graphs of odd-order groups (Frobenius groups Z_m x|_r Z_k and products) or
  SL(2,97) x Z7 with random S; Δ = 6..10: SL/PSL(2,p) x Z_n with alpha-orbit S, (10,13) at the 20-billion cap. The
  odd-order groups also raised (4,11), (5,11), (4,12) and (5,12) (research/frontier/beyond13/THEORY.md).
- Every value is at least the trivial floor from the neighbouring cells (n_b(Δ,D) ≥ n_b(Δ−1,D), n_b(Δ,D−1)).

## Upper bounds

M_b(Δ,D) = 2(1 + (Δ−1) + … + (Δ−1)^(D−1)) is the bipartite Moore bound. For D = 5, 7, 8, 9, 10, 11, 12, 13, 14 we use
M_b − 6: Feria-Purón and Pineda-Villavicencio, "On bipartite graphs of defect at most 4", Discrete Appl. Math. 160
(2012), Prop. 6.4 (Δ ≥ 3, 5 ≤ D ≤ 187, D ≠ 6; the arXiv version 1010.5651 was read for this). For D = 3, 4, 6 the
bound is M_b itself: it is attained at Δ = 17, 18, 20 (Δ − 1 a prime power), and at Δ = 19 it would need a projective
plane, generalized quadrangle or generalized hexagon of order 18, whose existence is open.

(Job beyond-d11, squad card r2/d14, re-read Prop. 6.4 on p. 25 of arXiv 1010.5651 v2: "For natural numbers Δ ≥ 3 and
5 ≤ D ≤ 187 (D ≠ 6), N_b(Δ, D) ≤ M_b(Δ, D) − 6"; quotes in research/squads/beyond11/r2/d14/BOUNDS.md.)

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
| (17,8) | **41,373,072** | 7.22 | 572,662,300 | Haar graph SL(2,53) x Z139, S = {e} + 1 fixed + 5 orbits of size 3 | haarcheck_sl (r1/c15/check_17_8_sl53_139.txt) and hcheck5 (director: checks/d17D8_sl_53_139_orb3_c15.hcheck5.txt): VALID | 2013-table D=8 pattern (no construction known): 67,575,312 (q=13, j=3); Haar size law at mu = 5: 2N = 3.78e+07 |
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
| (20,5) | **75,000** | 27.26 | 275,116 | route-chart lift over F5 (4 letters x 5 scalars, fibre F5^4): K3,3 + doubled matching over Z20 (m = 60), chart with 22 singular patterns (squad r1 c04); also 66,640 by the multi-doubled-matching lift of W(13), Z2 x Z7 (MDM.md) | apsp: checks/d20D5_n75000_routechart_F5_Z20.apsp.txt; checks/d20D5_n66640_W13_3dm_Z14.apsp.txt | 82,500 (route chart 4 letters x F5 IF a controller with m = 66 per side existed (not found; 2*m*q^4)) |
| (20,6) | **5,227,320** | 100.00 | 5,227,320 | H(19) incidence graph (Moore graph) | classical; BFS from 100 vertices: ecc 6, Moore levels (checks/d20D6_n5227320_H19.sampled.txt) | 5,227,320 (H(19) incidence graph (Moore)) |
| (20,7) | **15,658,734** | 15.77 | 99,319,076 | level graph of H(16): 7 copies, 3 matchings, Z7 | same theorem; BFS from 64 random vertices, max ecc 7 (checks/d7_levelgraphs_sampled.txt) | 15,658,734 (polygon cover 7xH(16) (j=3)) |
| (20,8) | **122,739,120** | 6.50 | 1,887,062,554 | Haar graph PSL(2,71) x Z343, S = {e} + 1 fixed + 6 orbits of size 3 | hcheckpsl VALID (runs/check_hcheckpsl_d20D8_psl_71_343_orb3_s1.txt) | 30,171,960 (polygon cover n+2: 10x H(17)); 2013-table D=8 pattern (no construction known): 219,619,764 (q=13, j=6); Haar size law at mu = 5: 2N = 1.16e+08 |
| (20,9) | **1,823,175,864** | 5.08 | 35,854,188,636 | Haar graph PSL(2,163) x Z421, S = {e} + 1 fixed + 6 orbits of size 3 | hcheckpsl VALID (runs/check_hcheckpsl_d20D9_psl_163_421_orb3_s2.txt) | Haar size law at mu = 5: 2N = 1.88e+09 |
| (20,10) | **30,518,778,360** | 4.48 | 681,229,584,194 | Haar graph PSL(2,421) x Z409, S = {e} + 1 fixed + 6 orbits of size 3 | hcheckpsl VALID, ecc 10/10 (runs/check_hcheckpsl_d20D10_psl_421_409_orb3_s1.txt) | Haar size law at mu = 5: 2N = 3.12e+10 |
| (3,11) | **1,474** | 36.00 | 4,088 | metacyclic Haar graph Z67 x|_9 Z11, S = {e, 67, 336} (director sweep of all metacyclic groups of order 541-1,100, exhaustive pairs); earlier 1,080 (A5 x Z9, r3/e01) | apsp VALID, diameter exactly 11 (checks/d3D11_n1474_meta67_11_9.apsp.txt) | Haar size law at mu = 5: 2N = 908 |
| (4,11) | **27,554** | 15.55 | 177,140 | Haar graph of the odd-order Frobenius group Z599 x|_498 Z23, S random (hmeta, squad r3/f15; solution research/frontier/beyond13/sols/d4D11_meta_599_23_498_f15.txt; also metacheck VALID); raises the beyond-d11 value 24,360 (PSL(2,29), orbit S); mu = 22.24 | research/frontier/beyond13/checks/d4D11_n27554_meta599_23_498.apsp.txt (graph research/frontier/beyond13/graphs/d4D11_n27554_meta599_23_498.edges.gz) | Haar size law at mu = 5: 2N = 2.29e+04 |
| (5,11) | **299,222** | 10.70 | 2,796,196 | Haar graph of the odd-order group (Z29 x|_7 Z7) x (Z67 x|_9 Z11) (order 149,611), S random (haar_gen3, squad r4/g04; solution research/frontier/beyond13/sols/d5D11_prodmeta_29_7_67_11_g04.txt); raises the beyond-d11 value 297,648 (SL(2,53), orbit S); mu = 13.08 | research/frontier/beyond13/checks/d5D11_prodmeta_29_7_67_11_g04.metacheck.txt | Haar size law at mu = 5: 2N = 2.74e+05 |
| (6,11) | **2,094,960** | 8.58 | 24,414,056 | Haar graph SL(2,29) x Z43, S = 2 free orbits of size 3 (squad r4/f02); was 1,971,744; mu = 9.10 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d6D11_sl_29_43_orb3-2-0_f02.gen.txt) | Haar size law at mu = 5: 2N = 2e+06 |
| (7,11) | **11,012,976** | 7.59 | 145,118,816 | Haar graph SL(2,53) x Z37, S = {e} + 2 orbits of size 3 (squad r2/d09); was 10,648,176; mu = 10.43 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d7D11_sl_53_37_orb3-2-1_d09.gen.txt) | Haar size law at mu = 5: 2N = 1.05e+07 |
| (8,11) | **45,329,808** | 6.88 | 659,108,908 | Haar graph SL(2,283), S = {e} + 1 fixed + 2 orbits of size 3 (squad r3/e04); was 43,702,560; mu = 10.98 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d8D11_sl_283_1_orb3-2-2_e04.gen.txt) | Haar size law at mu = 5: 2N = 4.31e+07 |
| (9,11) | **155,250,816** | 6.33 | 2,454,267,020 | Haar graph SL(2,223) x Z7, S = 3 free orbits of size 3 (squad r2/d08); was 145,258,344; mu = 10.58 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d9D11_sl_223_7_orb3-3-0_d08.gen.txt) | Haar size law at mu = 5: 2N = 1.49e+08 |
| (10,11) | **460,691,568** | 5.87 | 7,845,264,896 | Haar graph SL(2,613), S = {e} + 3 orbits of size 3 (squad r2/d13); was 445,709,568; mu = 9.26 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d10D11_sl_613_1_orb3-3-1_d13.gen.txt) | Haar size law at mu = 5: 2N = 4.45e+08 |
| (11,11) | **1,241,299,248** | 5.59 | 22,222,222,216 | Haar graph SL(2,853), S = {e} + 1 fixed + 3 orbits of size 3 (director, 892 evals at mu 10.4); earlier 1,210,478,448 (SL(2,317) x Z19, squad r2/d01) and 1,170,162,000 (SL(2,251) x Z37); mu = 10.42 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d11D11_sl_853_1_orb3-3-2_s1.gen.txt) | Haar size law at mu = 5: 2N = 1.19e+09 |
| (12,11) | **2,976,066,240** | 5.22 | 57,062,334,116 | Haar graph SL(2,239) x Z109, S = 4 free orbits of size 3 (f = 0, haar_big0; squad r1/c04); earlier 2,874,207,072 (SL(2,263) x Z79, director); mu = 7.01 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d12D11_sl_239_109_orb3-4-0_c04.gen.txt) | Haar size law at mu = 5: 2N = 2.93e+09 |
| (13,11) | **6,781,213,392** | 5.02 | 135,092,431,028 | Haar graph SL(2,563) x Z19, S = {e} + 4 orbits of size 3 (director); earlier 6,508,747,920 (SL(2,229) x Z271); mu = 7.56 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d13D11_sl_563_19_orb3-4-1_s1.gen.txt) | Haar size law at mu = 5: 2N = 6.65e+09 |
| (14,11) | **14,381,398,080** | 4.81 | 298,693,399,000 | Haar graph SL(2,1009) x Z7, S = {e} + 1 fixed + 4 orbits of size 3 (director); mu = 6.87 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d14D11_sl_1009_7_orb3-4-2_s1.gen.txt) | Haar size law at mu = 5: 2N = 1.42e+10 |
| (3,12) | **2,176** | 26.57 | 8,184 | metacyclic Haar graph Z68 x|_3 Z16, S = {e, 68, 205} (director sweep of metacyclic groups, exhaustive pairs; best of 7 hits at orders 979-1,088); earlier 1,860 (AGL(1,31), r3/e02) | apsp VALID, diameter exactly 12 (checks/d3D12_n2176_meta68_16_3.apsp.txt) | Haar size law at mu = 5: 2N = 1.61e+03 |
| (4,12) | **74,066** | 13.94 | 531,434 | Haar graph of the odd-order metacyclic group Z1277 x|_964 Z29 (order 37,033), S random (hmeta, squad r5/h08; solution research/frontier/beyond13/sols/d4D12_meta_1277_29_964_h08.txt; also metacheck VALID); raises the beyond-d11 value 68,544 (SL(2,17) x Z7, orbit S); mu = 28.34 | research/frontier/beyond13/checks/d4D12_n74066_meta1277_29_964.apsp.txt (graph research/frontier/beyond13/graphs/d4D12_n74066_meta1277_29_964.edges.gz) | Haar size law at mu = 5: 2N = 6.1e+04 |
| (5,12) | **1,042,898** | 9.32 | 11,184,804 | Haar graph of the odd-order metacyclic group Z17981 x|_15904 Z29 (order 521,449), S random (hmeta, squad r5/h08; solution research/frontier/beyond13/sols/d5D12_meta_17981_29_15904_h08.txt); raises the beyond-d11 value 1,041,768 (PSL(2,53) x Z7, orbit S); mu = 11.47 | research/frontier/beyond13/checks/d5D12_meta_17981_29_15904_h08.metacheck.txt | Haar size law at mu = 5: 2N = 9.74e+05 |
| (6,12) | **9,366,240** | 7.67 | 122,070,306 | Haar graph PSL(2,79) x Z19, S = 2 free orbits of size 3 (squad r3/e08); was 9,303,840; mu = 10.24 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d6D12_psl_79_19_orb3-2-0_e08.gen.txt) | Haar size law at mu = 5: 2N = 8.91e+06 |
| (7,12) | **59,838,504** | 6.87 | 870,712,928 | Haar graph PSL(2,67) x Z199, S = {e} + 2 orbits of size 3 (squad r3/e09); was 56,297,592; mu = 14.34 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d7D12_psl_67_199_orb3-2-1_e09.gen.txt) | Haar size law at mu = 5: 2N = 5.6e+07 |
| (8,12) | **284,095,056** | 6.16 | 4,613,762,394 | Haar graph PSL(2,167) x Z61, S = {e} + 1 fixed + 2 orbits of size 3 (squad r4/f10); was 268,496,208; mu = 12.57 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d8D12_psl_167_61_orb3-2-2_f10.gen.txt) | Haar size law at mu = 5: 2N = 2.7e+08 |
| (9,12) | **1,105,785,120** | 5.63 | 19,634,136,204 | Haar graph PSL(2,241) x Z79, S = 3 free orbits of size 3 (squad r3/e11); was 1,055,973,600; mu = 10.75 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d9D12_psl_241_79_orb3-3-0_e11.gen.txt) | Haar size law at mu = 5: 2N = 1.06e+09 |
| (10,12) | **3,712,424,352** | 5.26 | 70,607,384,114 | Haar graph PSL(2,337) x Z97, S = {e} + 3 orbits of size 3 (squad r4/f12); was 3,500,976,768; mu = 10.20 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d10D12_psl_337_97_orb3-3-1_f12.gen.txt) | Haar size law at mu = 5: 2N = 3.58e+09 |
| (11,12) | **11,189,148,096** | 5.04 | 222,222,222,216 | Haar graph PSL(2,223) x Z1009, S = {e} + 1 fixed + 3 orbits of size 3 (director, 17 evals); earlier 10,966,037,544 and 10,474,157,232; mu = 13.26 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d11D12_psl_223_1009_orb3-3-2_s2.gen.txt) | Haar size law at mu = 5: 2N = 1.07e+10 |
| (12,12) | **19,980,294,768** | 3.18 | 627,685,675,338 | Haar graph PSL(2,503) x Z157, S = 4 free orbits of size 3; at the job's 20-billion-vertex cap (first S solved); mu = 0.00 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d12D12_psl_503_157_orb3-4-0_s1.gen.txt) | Haar size law at mu = 5: 2N = 2.88e+10 |
| (13,12) | **19,993,487,976** | 1.23 | 1,621,109,172,404 | Haar graph PSL(2,307) x Z691, S = {e} + 4 orbits of size 3; at the job's 20-billion-vertex cap (first S solved); mu = 0.00 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d13D12_psl_307_691_orb3-4-1_s1.gen.txt) | Haar size law at mu = 5: 2N = 7.14e+10 |
| (3,13) | **3,320** | 20.27 | 16,376 | Z166 voltage lift of the Desargues graph GP(10,3) (director: many 20-s anneals cooling over L = 1,200 evaluations, lift.c of squad r2/e16); not a Haar graph; earlier 3,260 (Z163), 3,200 (Z160, r2/e16) and 2,880 (Haar graph of A6 x Z4, r1/c03); mu = 11.94 | research/frontier/beyond13/checks/d3D13_n3320_lift_gp10_Z166.apsp.txt (graph research/frontier/beyond13/graphs/d3D13_n3320_lift_gp10_Z166.edges.gz) | Haar size law at mu = 5: 2N = 2.89e+03 |
| (4,13) | **186,314** | 11.69 | 1,594,316 | Haar graph of the odd-order metacyclic group Z4903 x|_230 Z19, S random (haar_gen3, squad r1/c15); edge list rebuilt by meta2edges.py; beats the Haar SL/PSL values 170,520 (PSL(2,29) x Z7, orbit scan r1/c05) and 117,600 (PSL(2,49), r1/c16); mu = 17.90 | research/frontier/beyond13/checks/d4D13_n186314_meta4903_19_230.apsp.txt (graph research/frontier/beyond13/graphs/d4D13_n186314_meta4903_19_230.edges.gz) | Haar size law at mu = 5: 2N = 1.64e+05 |
| (5,13) | **3,525,298** | 7.88 | 44,739,236 | Haar graph of the odd-order group (Z29 x|_16 Z7) x (Z457 x|_289 Z19) (product of two Frobenius groups, order 1,762,649), S random (haar_gen3, squad r3/f08; solution research/frontier/beyond13/sols/d5D13_prodmeta_29_7_457_19_f08.txt); earlier 3,514,394 ((Z79 x|_64 Z13) x (Z59 x|_4 Z29), r2/e12) and 3,217,056 (PSL(2,47) x Z31, orbit S, r1/c07); mu = 5.43 | research/frontier/beyond13/checks/d5D13_prodmeta_29_7_457_19_f08.metacheck.txt | Haar size law at mu = 5: 2N = 3.5e+06 |
| (6,13) | **41,734,392** | 6.84 | 610,351,556 | Haar graph PSL(2,83) x Z73, S = 2 free orbits of size 3 (squad r3/f11, first link, mu 9.3); earlier 41,519,712 (SL(2,103) x Z19, r2/e09) and 40,427,088 (PSL(2,103) x Z37, r1/c09); mu = 9.29 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d6D13_psl_83_73_orb3-2-0_f11.gen.txt) | Haar size law at mu = 5: 2N = 4.01e+07 |
| (7,13) | **312,227,760** | 5.98 | 5,224,277,600 | Haar graph SL(2,229) x Z13, S = {e} + 2 orbits of size 3 (squad r2/e10, chained links); earlier 310,628,640 (SL(2,281) x Z7, r1/c11) and 299,455,200 (SL(2,199) x Z19); mu = 8.45 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d7D13_sl_229_13_orb3-2-1_e10.gen.txt) | Haar size law at mu = 5: 2N = 3.03e+08 |
| (8,13) | **1,739,514,000** | 5.39 | 32,296,336,796 | Haar graph SL(2,499) x Z7, S = {e} + 1 fixed + 2 orbits of size 3 (director, 33 evaluations, mu 7.5); earlier 1,676,500,800 (SL(2,401) x Z13, director) and 1,512,114,240 (SL(2,911), squad r1/c13); mu = 7.52 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d8D13_sl_499_7_orb3-2-2_s2.gen.txt) | Haar size law at mu = 5: 2N = 1.7e+09 |
| (9,13) | **7,508,907,120** | 4.78 | 157,073,089,676 | Haar graph SL(2,661) x Z13, S = 3 free orbits of size 3 (director, 5 evaluations, mu 3.1); mu = 3.09 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d9D13_sl_661_13_orb3-3-0_s1.gen.txt) | Haar size law at mu = 5: 2N = 7.68e+09 |
| (3,14) | **5,600** | 17.09 | 32,760 | Z280 voltage lift of the Desargues graph GP(10,3) (annealed voltages; director run of squad r2/e16 lift.c, 12 s); not a Haar graph; mu = 8.06 | research/frontier/beyond13/checks/d3D14_n5600_lift_gp10_Z280.apsp.txt (graph research/frontier/beyond13/graphs/d3D14_n5600_lift_gp10_Z280.edges.gz) | Haar size law at mu = 5: 2N = 5.23e+03 |
| (4,14) | **490,070** | 10.25 | 4,782,962 | Haar graph of the odd-order metacyclic group Z7001 x|_4532 Z35 (order 245,035), S random (hmeta, squad r4/g13; solution research/frontier/beyond13/sols/d4D14_meta_7001_35_4532_g13.txt; also metacheck VALID); earlier 482,160 (PSL(2,41) x Z7, orbit S, r1/c06); mu = 14.15 | research/frontier/beyond13/checks/d4D14_n490070_meta7001_35_4532.apsp.txt (graph research/frontier/beyond13/graphs/d4D14_n490070_meta7001_35_4532.edges.gz) | Haar size law at mu = 5: 2N = 4.47e+05 |
| (5,14) | **12,776,064** | 7.14 | 178,956,964 | Haar graph SL(2,97) x Z7, S random (haar_gen3, squad r5/h06, 265 evaluations); earlier 12,352,392 (PSL(2,53) x Z83, r4/g09), 12,057,264, 11,757,096 and 11,696,856; the orbit form "3 1 2" stalls at Δ = 5; mu = 5.27 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d5D14_sl_97_7_g3_h06.gen.txt) | Haar size law at mu = 5: 2N = 1.27e+07 |
| (6,14) | **187,990,656** | 6.16 | 3,051,757,806 | Haar graph SL(2,97) x Z103, S = 2 free orbits of size 3 (squad r4/g07: RANDORB screen, then two links); earlier 187,698,768 (PSL(2,137) x Z73, r3/f12), 186,910,464 and 186,466,200; mu = 8.37 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d6D14_sl_97_103_orb3-2-0_g07.gen.txt) | Haar size law at mu = 5: 2N = 1.83e+08 |
| (7,14) | **1,671,605,424** | 5.33 | 31,345,665,632 | Haar graph SL(2,163) x Z193, S = {e} + 2 orbits of size 3 (squad r3/f13, three chained links from a random start); earlier 1,587,571,920 (SL(2,109) x Z613, r1/c12); mu = 6.00 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d7D14_sl_163_193_orb3-2-1_f13.gen.txt) | Haar size law at mu = 5: 2N = 1.66e+09 |
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

(Δ = 4..10 at D = 11, 12 were raised on 2026-11-01 by job beyond-d11, squad rounds 2-4: SL(2,p) x Z_n with small n at
D = 11 and PSL/SL with moderate n at D = 12; see the beyond-d11 section and the table. The text below describes the
earlier values.)

Δ = 3: cubic Haar graphs H(G, {e, x, y}), with all pairs searched exhaustively per group (x over class
representatives, y over the group; research/squads/beyond/r3/e02/exh3.c, about 0.1–2 s per group). The director swept
every metacyclic group Z_m ⋊_r Z_k (one r of each order k per m) of order 541–1,100 at D = 11 (641 groups) and of order
931–2,500 at D = 12 (cubic/sweep_meta.py): the best are Z67 ⋊ Z11 (1,474 vertices, D = 11; the only metacyclic hit
of that order range) and Z68 ⋊ Z16 (2,176 vertices, D = 12; seven metacyclic hits at orders 979–1,088, none above that up to order 1,728, where the sweep was stopped (cubic/sweep_D12_out.txt; D = 11: cubic/sweep_D11_out.txt)). Before that, the squad's exhaustive
search over ~45 non-metacyclic groups gave A5 × Z9 (1,080, r3/e01) and AGL(1,31) (1,860, r3/e02); annealing over
PSL/SL/PGL(2,q) (r1/c12) and voltage lifts of small cubic bases (r2/d07, r2/d08) did worse. Δ = 4: Haar graphs
SL(2,8) × Z19 (D = 11) and SL(2,11) × Z19 (D = 12) with S = {e} ∪ one orbit of size 3 (r3/e03, r2/d09), above the
metacyclic values 17,600 / 48,000 of r1/c13; at D = 12, PSL(2,11) × Z39 (51,480) misses by one hole after four
seeds. Δ = 5, 6: haar_sym (plain random S at Δ = 5, two free 3-orbits at Δ = 6) at μ ≈ 2–10, solved in seconds, 2–4
times the round-1 card values. Δ = 7..10: haar_big.

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

### D = 11 at Δ = 11..14 and D = 12 at Δ = 11..13 (job beyond-d11, 2026-11-01)

Job beyond-d11 (Opus director + four Haiku squad rounds of 16 cards, cloud session, branch
claude/new-cells-d11-d12-beyond-8sas9r). Seven new cells, and the D = 11, 12 values at Δ = 4..10 raised. Size limit
for the job: at most about 20 billion vertices, so that the low-memory checkers finish in a few hours.

**Method.** Haar graphs H(G,S), G = SL(2,p) x Z_n or PSL(2,p) x Z_n, S closed under alpha = (conjugation by a matrix
of order 3) x (z -> r z, r of order 3 mod n); research/frontier/beyond11/haar_big0.c is haar_big (64-bit, N/2 bytes,
bit-parallel BFS) plus two changes: f = 0 (S = free 3-orbits without e, evaluated as S s_0^-1; the right choice for
3 | Δ, so (12,11) and (12,12)), and a fix in the choice of alpha (haar_big took the first g with g^k = +-I, which for
k = 4, 6, 10 is an element of order 2 or 3; k = 3 and 5 were unaffected, so no earlier result changes). Every value is
checked by research/frontier/haarcheck_gen.c (own group code, BFS from (e,A) and (e,B)); logs in
research/frontier/runs/cloudcheck/<stem>.gen.txt, solutions in research/frontier/sols/.

**Even D was easy, odd D was not.** At D = 12 the first S solved at mu ~3 (one to five evaluations) and (11,12) solved
at mu 13.3 in 17 evaluations; (12,12) and (13,12) are limited by the 20-billion cap (mu ~ 0 there), not by the search.
At D = 11 the searches stall at cost 1-3 near mu 7-10, and the last holes are special elements. The reason
(research/frontier/beyond11/ODD_D_HOLES.md): for odd D = 2h+1 the same-side sets (S^-1 S)^h and (S S^-1)^h are closed
under inversion, so the words reaching an involution pair up, and the words reaching a central element are closed under
rotation (h rotations), and a central element is a hole on both sides at once. So involutions are missed with
probability ~exp(-lambda/2), central elements ~exp(-lambda/h), against exp(-lambda) for an ordinary element
(lambda = W/N ~ 19 here). PSL(2,p) has ~p^2/2 involutions, SL(2,p) only -I; G x Z_n has n or 2n central elements.
Hole counts of random S (squad card r2/d04) and a 22-group fit (r3/e14) agree with these rates within a factor 1.3-2.
Consequence, used for the D = 11 values found after round 1: SL(2,p) x Z_n with small n (1-43) and large p. (The
exceptions are (12,11), SL(2,239) x Z109 from round 1, and (4,11), PSL(2,29), where the group is tiny.) PSL with n = 1
is the worst shape at odd D (all ~130 holes per random S are involutions) although it is fine at even D.

**Squad (64 Haiku cards in 4 rounds; research/squads/LOG.md, research/squads/beyond11/r1..r4).** Round 1 mapped
structures and found the choose_alpha bug (two cards independently), the -I and torus near misses, and the size-law
calibration (mu ~7 within ~300 evaluations, ~10 within ~1,000). Round 2's hole anatomy (d04) explained the odd-D
failures; the director redirected seven running cards from PSL to SL mid-round, and four of them then raised cells.
Rounds 3-4 applied the rule to the cheap cells and raised (4..10, 11) and (4..10, 12) by 1-37 %. Cards that found
nothing: k = 2, 4, 5, 6 orbits at D = 11, self-dual (transpose-closed) S, annealing knobs, fixed-generator moves, -I as a
generator, a meet-in-the-middle near-miss finisher, composite n at (7,11).

**What failed or was not tried.**
- Pushing the odd-D cells past mu ~10: (12,11) SL(2,601) x Z7 (mu 10.7) stopped at cost 2 after ~230 evaluations,
  SL(2,193) x Z211 (mu 10.3) at cost 2 with -I its only hole; (11,11) PSL(2,257) x Z73 (mu 10.1) at 9 (SL(2,853) at the
  same mu solved after 892 evaluations); (11,12) PSL(2,241) x Z829 (mu 28) at 8.
- Near misses that stayed at cost 1-3 for thousands of evaluations: (6,11) SL(2,103), (7,11) SL(2,67) x Z19, (9,11)
  SL(2,137) x Z31, (6,12) PSL(2,211), (9,12) PSL(2,167) x Z241 and PSL(2,331) x Z31.
- (12,12) and (13,12) sit at the job's cap; larger groups would solve at once but their checks would exceed the
  checkers' budget.
- Checking cost depends on p, not only on the size: haarcheck_gen multiplies matrices through p^2-entry field tables,
  which leave the L2 cache for p ~ 850-1,000. The 14.4-billion-vertex (14,11) check (SL(2,1009) x Z7) took about
  4.4 CPU-hours (10,919 s wall on 2 threads, partly shared with squad jobs), and the 1.24-billion (11,11) check of
  SL(2,853) about 40 CPU-minutes, against 7 CPU-minutes for the 1.17-billion SL(2,251) x Z37. For the coordinator's
  second check, the PSL/SL-specific checkers should be much faster for p > 600.

### D = 13 at Δ = 3..10 and D = 14 at Δ = 3..8 (job beyond-d13, 2026-11-01)

Job beyond-d13 (Opus director + four Haiku squad rounds of 16 cards, cloud session, branch
claude/beyond-d13-search-z35z61). Fourteen new cells (nothing was recorded at D = 13, 14 before), and two D = 11 values
raised. Size limit: at most about 20 billion vertices. Files: research/frontier/beyond13/ (cells.txt, cells_other.txt,
rows13.py for the rows; sols/, runs/ (haarcheck_gen logs), checks/ (apsp, metacheck), graphs/ (edge lists),
THEORY.md); squad cards and scoreboards research/squads/beyond13/r1..r4; log research/squads/LOG.md.

**What won where.**
- Δ = 3 (both D): cyclic voltage lifts of the Desargues graph GP(10,3), annealed voltages (squad r2/e16's lift.c):
  Z160 at D = 13 (3,200), Z280 at D = 14 (5,600, director). Better than every Haar graph tried (A6 x Z4 2,880 by
  exhaustive pairs at D = 13; PSL(2,7) x Z15 5,040 at D = 14). Why (r3/f03, THEORY.md section 2): in a Z_n lift a walk's
  end depends only on its net traversal vector; GP(10,3) (girth 6, Betti number 11) keeps 82 % of the 24,574
  nonbacktracking walks of length <= 13 distinct.
- Δ = 4, 5 at odd D, and Δ = 4 at D = 14: Haar graphs of odd-order groups with random S: Frobenius groups
  Z_m x|_r Z_k (m prime, k odd) and products of two (haar_gen3, or the director's bit-parallel hmeta). Reason
  (THEORY.md section 1): at odd D the hard holes are involutions and central elements (ODD_D_HOLES.md); a Frobenius
  group has neither. The same rule raised (4,11) from 24,360 to 27,554 and (5,11) from 297,648 to 299,222. Small k
  fails (nearly abelian: random-S word cover 1 % for k = 1, 6 % for k = 3, 97-99 % for k >= 11; r2/e11).
- Δ = 5 at D = 14: PSL(2,53) x Z83 with random S. The orbit form "3 1 2" (one random fixed generator + one orbit)
  stalls at Δ = 5 (cost 18 where random S solves in seconds).
- Δ = 6..10: SL/PSL(2,p) x Z_n with alpha-orbit S (haar_big0). At D = 13, SL with small n (as at D = 11) and also PSL
  with moderate n (40-75) solved; r1/c14's anatomy at (5,13): -I is missed by 20-46 % of random S, SL has 16-20 holes per
  random S against 22-27 for PSL.
- (10,13) is at the 20-billion cap (PSL(2,503) x Z157, the first S solved, λ = W/N = 31.8).
- Even D was again easy: (8,14) solved at mu 7.1 in 21 evaluations; odd D needed chained links at mu 7-9.

**Squad (64 Haiku cards in 4 rounds of 16; LOG.md).** The two ideas that moved small Δ came from wildcard cards:
odd-order groups (r1/c15) and voltage lifts (r2/e16); a prime-power field (PSL(2,49), r1/c16) and random S at Δ = 5
(r1/c08) were also card ideas. The mid cells (Δ = 6, 7) were raised 1-5 % by cards in every round. The director's
contributions: the cell plan and selection, the (8,13), (8,14), (9,13), (10,13) values, the Δ = 3 D = 14 lift, the
checkers for non-SL/PSL graphs (metacheck.py, metacheck2.py, tab2edges.py, meta2edges.py), hmeta and liftd, THEORY.md.

**What failed or was not tried.**
- Orbit S inside metacyclic groups (alpha = scaling): costs saturate (r2/e03, e14, director). Metacyclic groups at
  even D: no gain (r2/e06), except (4,14) where Z7001 x|_4532 Z35 (odd order) beat PSL(2,41) x Z7 by 1.6 %.
- Lifts at Δ = 4, 5: K4,4, PG(2,3), GQ(3,3), the biplane and random bases stayed below the Haar values (best PG(2,3) x
  Z4600 = 119,600 at (4,13)); THEORY.md Fact 2 caps K4,4 lifts. Non-abelian voltage groups on GP(10,3): cost 2 at 3,300.
- Near misses at cost 1-2 that did not close: (3,14) GP(10,3) x Z282 and Pappus x Z312; (3,13) Z33 x|_4 Z5 voltages;
  (4,13) Z3307 x|_265 Z29 and Z2297 x|_1862 Z41 (N ~ 94-96k); (6,13) SL(2,59) x Z103; (8,14) PSL(2,397) x Z181 (mu 12).
- The machine (4 cores) was the limit: the director's three big checks held 4-5 threads, so cards ran at 5-10 % of a
  core (r1/c01, c02, r2/e04, e13 found nothing for that reason). The (10,13) check was OOM-killed once after 58 min
  (a card's numpy checker plus a director search pushed the box over 15 GB) and was rerun.
- Not tried: (9,13) above mu 3 (one SL group solved in 5 evaluations; a push would gain ~3 % and need another
  two-hour check), (8,14) above mu 7.1.

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
