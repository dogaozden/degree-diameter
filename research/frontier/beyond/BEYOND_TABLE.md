# Beyond the 2013 table: first values for 55 new cells

Job new-cells-beyond (Opus director + Haiku squads, cloud session, 2026-10-26, branch claude/new-cells-beyond-etos3t).
The 2013 bipartite table (DS14v2, Table 4) stops at Δ = 16 and D = 10. This file gives a checked lower bound for every
cell in the next band: Δ = 17..20 at D = 3..10 (32 cells) and D = 11, 12 at Δ = 3..10 (16 cells), with an upper bound
and the comparison with the formula families. As far as we know (literature card r2/d10) no bipartite values have been
published for these cells, so every value here is a first value, not a record.

Extended 2026-11-01 by job beyond-d11 (branch claude/new-cells-d11-d12-beyond-8sas9r): seven more cells, D = 11 at
Δ = 11..14 and D = 12 at Δ = 11..13, and new values for (4..10, 11) and (4..10, 12); see the section "D = 11 at
Δ = 11..14 and D = 12 at Δ = 11..13" below.

Extended 2026-11-02 by job raise-d8b (branch claude/raise-d8-d7-beyond-table-8mozbm): the four D = 8 cells at
Δ = 17..20 raised with generator sets closed under an automorphism of order 5 or 7, and the four D = 7 cells updated to
the hexagon-with-hubs graphs of job conics-2, whose all-pairs checks are now complete; see the section "D = 8 at
Δ = 17..20 and D = 7 (job raise-d8b)" below.

## Summary

- **Optimal (Moore graphs), 9 cells:** (17|18|20, 3), (17|18|20, 4), (17|18|20, 6) — incidence graphs of PG(2,q),
  W(q), H(q) with q = Δ − 1 = 16, 17, 19.
- **Theorems of the lab, Δ = 19:** (19,3) 624 (fourth hat), (19,4) 10,982 (Theorem A), (19,6) 3,203,968 (Theorem D).
- **D = 5, new construction:** multi-doubled-matching lifts of W(q) (MDM.md): (18,5) 47,600 and, inside the old
  table, a record (13,5) 11,700 (was 11,486). (19,5) 52,428 is the k = 1 case (DM on W(16)); (20,5) 75,000 is a
  route-chart lift over F5 from squad round 1. (17,5) has only the floor 33,792 (the (16,5) graph).
- **D = 7:** level graphs (polygon covers) of H(13) and H(16) plus hub vertices on freed point-line pairs (job
  conics-2, typed whiskers), 5.7M–15.8M vertices, every one checked all-pairs (split into source ranges).
- **D = 8 .. 12:** Haar graphs of SL(2,p) × Z_n / PSL(2,p) × Z_n with automorphism-orbit generator sets (at D = 8,
  Δ = 17..20 orbits of order 5 or 7, job raise-d8b), up to
  billions of vertices, each checked by an independent low-memory BFS from both sides; the small cells (Δ = 3, 4) by
  exhaustive or annealed Haar searches.
- **D = 11 at Δ = 11..14, D = 12 at Δ = 11..13 (beyond-d11):** Haar graphs of SL(2,p) x Z_n (odd D) and
  PSL(2,p) x Z_n (even D) with alpha-orbit generator sets, 1.24 to 20.0 billion vertices; (12,12) and (13,12) sit at the
  job's 20-billion-vertex size limit. At odd D the hard elements are involutions and central elements (exact lemma and
  hole counts in research/frontier/beyond11/ODD_D_HOLES.md), which is why SL with small n is used there.
- Every value is at least the trivial floor from the neighbouring cells (n_b(Δ,D) ≥ n_b(Δ−1,D), n_b(Δ,D−1)).

## Upper bounds

M_b(Δ,D) = 2(1 + (Δ−1) + … + (Δ−1)^(D−1)) is the bipartite Moore bound. For D = 5, 7, 8, 9, 10, 11, 12 we use
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
| (17,7) | **5,693,959** | 15.91 | 35,791,388 | typed whiskers + hubs on the level graph of H(13): 7 levels (types HHDHHDD), 32,356 + 30,327 hub vertices, random hub graph of degree 10 (job conics-2, research/synthetic/conics2/README.md, Theorem 3.4 of D7_HEXAGON.md); was 5,631,276 (plain level graph) | apsp_mt all pairs on the coordinator's machine, VALID (research/coordinator_check/check_2026-10-29.txt); also 8 cloud source ranges VALID | 5,631,276 (polygon cover 7xH(13) (j=3)) |
| (17,8) | **43,463,280** | 7.59 | 572,662,300 | Haar graph PSL(2,41) x Z631, S = {e} + 2 fixed + 2 orbits of size 7 (alpha of order 7; raise-d8b squad r3/e01, chosen by a RANDORB screen, mu 41.2); earlier 43,298,640 (PSL(2,71) x Z121, k = 5, director); was 41,373,072 | haarcheck_gen VALID (checks/d17D8_psl_41_631_orb7-2-3_r3e01.gen.txt) | 2013-table D=8 pattern (no construction known): 67,575,312 (q=13, j=3); Haar size law at mu = 5: 2N = 3.78e+07 |
| (17,9) | **501,707,400** | 5.48 | 9,162,596,892 | Haar graph PSL(2,101) x Z487, S = {e} + 1 fixed + 5 orbits of size 3 | hcheckpsl VALID (runs/check_hcheckpsl_d17D9_psl_101_487_orb3_s2.txt) | Haar size law at mu = 5: 2N = 5.16e+08 |
| (17,10) | **7,022,052,336** | 4.79 | 146,601,550,364 | Haar graph PSL(2,313) x Z229, S = {e} + 1 fixed + 5 orbits of size 3 | hcheckpsl VALID (runs/check_hcheckpsl_d17D10_psl_313_229_orb3_s1.txt) | Haar size law at mu = 5: 2N = 7.19e+09 |
| (18,3) | **614** | 100.00 | 614 | PG(2,17) incidence graph (Moore graph) | apsp: checks/d18D3_n614_pg2_17.apsp.txt | 614 (PG(2,17) incidence graph (Moore)) |
| (18,4) | **10,440** | 100.00 | 10,440 | W(17) incidence graph (Moore graph) | apsp: checks/d18D4_n10440_W17.apsp.txt | 10,440 (W(17) incidence graph (Moore)) |
| (18,5) | **47,600** | 26.82 | 177,476 | multi-doubled-matching lift of W(13): 2 doubled matchings, Z2 x Z5 (18-regular) | apsp: checks/d18D5_n47600_W13_2dm_Z10.apsp.txt | 42,840 (polygon cover 9xW(13) (j=4)) |
| (18,6) | **3,017,196** | 100.00 | 3,017,196 | H(17) incidence graph (Moore graph) | classical; BFS from 96 vertices: ecc 6, Moore levels (checks/d18D6_n3017196_H17.sampled.txt) | 3,017,196 (H(17) incidence graph (Moore)) |
| (18,7) | **7,309,092** | 14.25 | 51,292,328 | typed whiskers + hubs on 9 levels of H(13) (HHDHDHDHD), 34,440 + 34,440 hubs, hub graph a Haar graph of PSL(2,41) of degree 9 with clusters (conics-2); was 7,240,212 | all-pairs check in 10 source ranges, all VALID (research/synthetic/conics2/d18D7/checks/d18D7_n7309092.check.txt) | 7,240,212 (polygon cover 9xH(13) (j=4)) |
| (18,8) | **64,792,896** | 7.43 | 871,969,674 | Haar graph PSL(2,97) x Z71, S = {e} + 3 fixed + 2 orbits of size 7 (alpha of order 7; raise-d8b squad r2/d06, mu 46.3); earlier 64,577,760 (PSL(2,79) x Z131, orbits of order 5, director) and 62,842,200; was 57,637,680 | haarcheck_gen VALID (checks/d18D8_psl_97_71_orb7-2-4_r2d06.gen.txt) | 2013-table D=8 pattern (no construction known): 108,603,180 (q=13, j=4); Haar size law at mu = 5: 2N = 5.61e+07 |
| (18,9) | **790,626,816** | 5.33 | 14,823,484,556 | Haar graph SL(2,127) x Z193, S = {e} + 2 fixed + 5 orbits of size 3 | hcheck5 VALID (runs/check_hcheck5_d18D9_sl_127_193_orb3_s2.txt) | Haar size law at mu = 5: 2N = 8.14e+08 |
| (18,10) | **11,787,972,672** | 4.68 | 251,999,237,550 | Haar graph PSL(2,223) x Z1063, S = {e} + 2 fixed + 5 orbits of size 3 | hcheckpsl VALID, ecc 10/10 (runs/check_hcheckpsl_d18D10_psl_223_1063_orb3_s1.txt) | Haar size law at mu = 5: 2N = 1.21e+10 |
| (19,3) | **624** | 90.96 | 686 | fourth hat R(17;2,3), POLISHED.md Thm 2.2 (19-regular) | apsp: checks/d19D3_n624_fourthhat_q17.apsp.txt | 624 (fourth hat, q=17 (POLISHED Thm 2.2)) |
| (19,4) | **10,982** | 88.92 | 12,350 | AS(17) + clones of two elliptic quadrics, POLISHED.md Cor. A1 (19-regular) | apsp: checks/d19D4_n10982_AS17_clones.apsp.txt | 10,982 (Thm B, q=17: 2q^2 Delta) |
| (19,5) | **52,428** | 23.58 | 222,296 | doubled-matching lift of W(16) over Z6 (DM_D5.md; = MDM with k = 1); nu, sigma annealed by squad r1/c05 (dmfast, routes allowed) | apsp: checks/d19D5_n52428_W16_dm_Z6.apsp.txt | 52,428 (doubled matching 6x W(16) (DM_D5, annealed)) |
| (19,6) | **3,203,968** | 80.07 | 4,001,438 | Theorem D of POLISHED.md, q = 17, m = 2 (doubling of H(17) with levels and exact whiskers; max degree 19) | theorem (paper + Lean for all odd q); builder checked all-pairs at q = 5, 7 (checks/thmD_builder_q5_q7.apsp.txt); q = 17 instance: BFS from 96 vertices, ecc 6 (checks/d19D6_n3203968_thmD_q17.sampled.txt) | 3,203,968 (Thm D, q=17, m=2) |
| (19,7) | **11,316,940** | 15.71 | 72,025,880 | typed whiskers + hubs on 5 levels of H(16) (HDHDH), 66,065 + 66,065 hubs, random hub graph of degree 14 (conics-2); was 11,184,810 | all-pairs check in 16 source ranges, all VALID (checks/d19D7_n11316940_ranges_complete.txt; the last 7 ranges were read from the finished check sessions by raise-d8b) | 11,184,810 (polygon cover 5xH(16) (j=2)) |
| (19,8) | **92,599,320** | 7.14 | 1,296,465,944 | Haar graph PSL(2,59) x Z451, S = {e} + 3 fixed + 3 orbits of size 5 (alpha of order 5; squad r2/d10 reached cost 5, the director finished it from that state, mu 38.5); earlier 92,166,360 (PSL(2,131) x Z41, r2/d07), 91,939,320 and 88,597,200; was 86,317,296 | haarcheck_gen VALID (checks/d19D8_psl_59_451_orb5-3-4_s3.gen.txt) | 22,369,620 (polygon cover n+2: 10x H(16)); 2013-table D=8 pattern (no construction known): 159,284,664 (q=13, j=5); Haar size law at mu = 5: 2N = 8.15e+07 |
| (19,9) | **1,218,394,320** | 5.22 | 23,336,387,096 | Haar graph SL(2,131) x Z271, S = {e} + 6 orbits of size 3 | hcheck5 VALID (runs/check_hcheck5_d19D9_sl_131_271_orb3_s2.txt) | Haar size law at mu = 5: 2N = 1.25e+09 |
| (19,10) | **19,233,722,496** | 4.58 | 420,054,967,832 | Haar graph SL(2,607) x Z43, S = {e} + 6 orbits of size 3 | hcheck5 VALID, ecc 10/10 (runs/check_hcheck5_d19D10_sl_607_43_orb3_s1.txt) | Haar size law at mu = 5: 2N = 1.96e+10 |
| (20,3) | **762** | 100.00 | 762 | PG(2,19) incidence graph (Moore graph) | apsp: checks/d20D3_n762_pg2_19.apsp.txt | 762 (PG(2,19) incidence graph (Moore)) |
| (20,4) | **14,480** | 100.00 | 14,480 | W(19) incidence graph (Moore graph) | apsp: checks/d20D4_n14480_W19.apsp.txt | 14,480 (W(19) incidence graph (Moore)) |
| (20,5) | **75,000** | 27.26 | 275,116 | route-chart lift over F5 (4 letters x 5 scalars, fibre F5^4): K3,3 + doubled matching over Z20 (m = 60), chart with 22 singular patterns (squad r1 c04); also 66,640 by the multi-doubled-matching lift of W(13), Z2 x Z7 (MDM.md) | apsp: checks/d20D5_n75000_routechart_F5_Z20.apsp.txt; checks/d20D5_n66640_W13_3dm_Z14.apsp.txt | 82,500 (route chart 4 letters x F5 IF a controller with m = 66 per side existed (not found; 2*m*q^4)) |
| (20,6) | **5,227,320** | 100.00 | 5,227,320 | H(19) incidence graph (Moore graph) | classical; BFS from 100 vertices: ecc 6, Moore levels (checks/d20D6_n5227320_H19.sampled.txt) | 5,227,320 (H(19) incidence graph (Moore)) |
| (20,7) | **15,795,219** | 15.90 | 99,319,076 | typed whiskers + hubs on 7 levels of H(16) (HHDHHDD), 70,163 + 66,322 hubs, random hub graph of degree 13 (conics-2); was 15,658,734 | all-pairs check in 24 source ranges, all VALID (checks/d20D7_n15795219_ranges_complete.txt; 15 ranges read from the finished check sessions by raise-d8b) | 15,658,734 (polygon cover 7xH(16) (j=3)) |
| (20,8) | **131,610,120** | 6.97 | 1,887,062,554 | Haar graph PSL(2,59) x Z641, S = 4 free orbits of size 5, no e (f = 0, alpha of order 5; search energy weights an uncovered alpha-fixed element 5 (haar_big0w ORBW=5); raise-d8b squad r4/f04, mu 39.0); earlier 130,252,080 (PSL(2,41) x Z1891) and 126,119,280; was 122,739,120 | haarcheck_gen VALID (checks/d20D8_psl_59_641_orb5-4-0_r4f04.gen.txt) | 30,171,960 (polygon cover n+2: 10x H(17)); 2013-table D=8 pattern (no construction known): 219,619,764 (q=13, j=6); Haar size law at mu = 5: 2N = 1.16e+08 |
| (20,9) | **1,823,175,864** | 5.08 | 35,854,188,636 | Haar graph PSL(2,163) x Z421, S = {e} + 1 fixed + 6 orbits of size 3 | hcheckpsl VALID (runs/check_hcheckpsl_d20D9_psl_163_421_orb3_s2.txt) | Haar size law at mu = 5: 2N = 1.88e+09 |
| (20,10) | **30,518,778,360** | 4.48 | 681,229,584,194 | Haar graph PSL(2,421) x Z409, S = {e} + 1 fixed + 6 orbits of size 3 | hcheckpsl VALID, ecc 10/10 (runs/check_hcheckpsl_d20D10_psl_421_409_orb3_s1.txt) | Haar size law at mu = 5: 2N = 3.12e+10 |
| (3,11) | **1,474** | 36.00 | 4,088 | metacyclic Haar graph Z67 x|_9 Z11, S = {e, 67, 336} (director sweep of all metacyclic groups of order 541-1,100, exhaustive pairs); earlier 1,080 (A5 x Z9, r3/e01) | apsp VALID, diameter exactly 11 (checks/d3D11_n1474_meta67_11_9.apsp.txt) | Haar size law at mu = 5: 2N = 908 |
| (4,11) | **24,360** | 13.75 | 177,140 | Haar graph PSL(2,29), S = {e} + 1 orbit of size 3 (squad r4/f13); was 19,152; mu = 8.46 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d4D11_psl_29_1_orb3-1-1_f13.gen.txt) | Haar size law at mu = 5: 2N = 2.29e+04 |
| (5,11) | **297,648** | 10.64 | 2,796,196 | Haar graph SL(2,53), S = {e} + 1 fixed + 1 orbit of size 3 (squad r3/e01); was 253,080; mu = 12.38 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d5D11_sl_53_1_orb3-1-2_e01.gen.txt) | Haar size law at mu = 5: 2N = 2.74e+05 |
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
| (4,12) | **68,544** | 12.90 | 531,434 | Haar graph SL(2,17) x Z7, S = {e} + 1 orbit of size 3 (squad r4/f14); was 50,160; mu = 14.71 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d4D12_sl_17_7_orb3-1-1_f14.gen.txt) | Haar size law at mu = 5: 2N = 6.1e+04 |
| (5,12) | **1,041,768** | 9.31 | 11,184,804 | Haar graph PSL(2,53) x Z7, S = {e} + 1 fixed + 1 orbit of size 3 (squad r3/e07); was 912,576; mu = 11.32 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d5D12_psl_53_7_orb3-1-2_e07.gen.txt) | Haar size law at mu = 5: 2N = 9.74e+05 |
| (6,12) | **9,366,240** | 7.67 | 122,070,306 | Haar graph PSL(2,79) x Z19, S = 2 free orbits of size 3 (squad r3/e08); was 9,303,840; mu = 10.24 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d6D12_psl_79_19_orb3-2-0_e08.gen.txt) | Haar size law at mu = 5: 2N = 8.91e+06 |
| (7,12) | **59,838,504** | 6.87 | 870,712,928 | Haar graph PSL(2,67) x Z199, S = {e} + 2 orbits of size 3 (squad r3/e09); was 56,297,592; mu = 14.34 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d7D12_psl_67_199_orb3-2-1_e09.gen.txt) | Haar size law at mu = 5: 2N = 5.6e+07 |
| (8,12) | **284,095,056** | 6.16 | 4,613,762,394 | Haar graph PSL(2,167) x Z61, S = {e} + 1 fixed + 2 orbits of size 3 (squad r4/f10); was 268,496,208; mu = 12.57 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d8D12_psl_167_61_orb3-2-2_f10.gen.txt) | Haar size law at mu = 5: 2N = 2.7e+08 |
| (9,12) | **1,105,785,120** | 5.63 | 19,634,136,204 | Haar graph PSL(2,241) x Z79, S = 3 free orbits of size 3 (squad r3/e11); was 1,055,973,600; mu = 10.75 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d9D12_psl_241_79_orb3-3-0_e11.gen.txt) | Haar size law at mu = 5: 2N = 1.06e+09 |
| (10,12) | **3,712,424,352** | 5.26 | 70,607,384,114 | Haar graph PSL(2,337) x Z97, S = {e} + 3 orbits of size 3 (squad r4/f12); was 3,500,976,768; mu = 10.20 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d10D12_psl_337_97_orb3-3-1_f12.gen.txt) | Haar size law at mu = 5: 2N = 3.58e+09 |
| (11,12) | **11,189,148,096** | 5.04 | 222,222,222,216 | Haar graph PSL(2,223) x Z1009, S = {e} + 1 fixed + 3 orbits of size 3 (director, 17 evals); earlier 10,966,037,544 and 10,474,157,232; mu = 13.26 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d11D12_psl_223_1009_orb3-3-2_s2.gen.txt) | Haar size law at mu = 5: 2N = 1.07e+10 |
| (12,12) | **19,980,294,768** | 3.18 | 627,685,675,338 | Haar graph PSL(2,503) x Z157, S = 4 free orbits of size 3; at the job's 20-billion-vertex cap (first S solved); mu = 0.00 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d12D12_psl_503_157_orb3-4-0_s1.gen.txt) | Haar size law at mu = 5: 2N = 2.88e+10 |
| (13,12) | **19,993,487,976** | 1.23 | 1,621,109,172,404 | Haar graph PSL(2,307) x Z691, S = {e} + 4 orbits of size 3; at the job's 20-billion-vertex cap (first S solved); mu = 0.00 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d13D12_psl_307_691_orb3-4-1_s1.gen.txt) | Haar size law at mu = 5: 2N = 7.14e+10 |
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

### D = 8 at Δ = 17..20 and D = 7 (job raise-d8b, 2026-11-01/02)

Job raise-d8b (Opus director + five Haiku squad rounds of 16 cards, cloud session, 4 cores shared by all searches,
branch claude/raise-d8-d7-beyond-table-8mozbm). Tools in research/frontier/raise_d8/ (big.sh, bigw.sh, grp.py,
save.sh, harvest.py, roundsum.py, haar_big0w.c); squad cards, logs and scoreboards in research/squads/raise_d8b/r1..r5;
round notes in research/squads/LOG.md.

**D = 8 values** (every one checked by haarcheck_gen, BFS from (e,A) and (e,B); solutions in research/frontier/sols/,
logs in checks/*.gen.txt):

| cell | before | now | gain | group, S |
|---|---:|---:|---:|---|
| (17,8) | 41,373,072 | **43,463,280** | +5.1 % | PSL(2,41) x Z631, e + 2 fixed + 2 orbits of 7 (mu 41.2) |
| (18,8) | 57,637,680 | **64,792,896** | +12.4 % | PSL(2,97) x Z71, e + 3 fixed + 2 orbits of 7 (mu 46.3) |
| (19,8) | 86,317,296 | **92,599,320** | +7.3 % | PSL(2,59) x Z451, e + 3 fixed + 3 orbits of 5 (mu 38.5) |
| (20,8) | 122,739,120 | **131,610,120** | +7.2 % | PSL(2,59) x Z641, 4 free orbits of 5, no e (mu 39.0) |

**What made the difference: the order of the automorphism.** The earlier values used S closed under an automorphism
alpha of order 3 (conjugation by an element of order 3 times z -> r z). With alpha of order 5 or 7 the uncovered set
comes in alpha-orbits of 5 or 7, and the search cost follows mu/k (the expected number of uncovered orbits): a fit over
74 finished runs of this job (squad card r4/f15) gives evaluations ~ exp(1.0 + 1.21 mu/k) (sigma 1.9), with nothing
solved beyond mu/k ~ 9 at the ~0.2 core per search available here. The first k = 5 run solved (18,8) at mu 29.6 in 97
evaluations, where k = 3 at mu 28 needed ~30 minutes. Limits found on the way:
- **Fixed letters must be few.** S = {e} + (f - 1) alpha-fixed letters + orbits; the fixed letters lie in the abelian
  centralizer of alpha (a torus), and three or more commuting letters make 6-cycles. "5 3 4" (f = 4) still worked on
  PSL with moderate n, but k = 7 with f = 5, 6 ((19,8), (20,8)) screened 5-20x worse than k = 5, as did "5 3 5" at (20,8).
- **With f = 0 the last holes are alpha-fixed elements** (r3/e13): z = 0 and in the torus of the alpha element, each
  missed with probability ~ e^(-lambda/k), so the expected number is (torus size) x e^(-lambda/5): ~1 for PSL(2,41)
  (torus 20), ~3 for PSL(2,109) (55), ~6 for PSL(2,229) (115). The fix that solved (20,8) at mu 39: weight an uncovered
  fixed element 5 in the search energy (ORBW, as in haar_sym and the lab's (15,8) record) and use a group with a small
  torus; research/frontier/raise_d8/haar_big0w.c adds ORBW to haar_big0 (for f = 0 a hole x of H(G, S s0^-1) is tested
  as x s0).
- **Which k wins depends on the group**, and a 16-sample RANDORB screen (median cost divided by k) predicted it: round 3's
  screen chose k = 7 at (17,8) and solved in 1,860 evaluations. k = 9 (alpha^3 of order 3), orbits of order 4, single
  orbits of 11 and k = 7 with many fixed letters all screened far worse.
- Large cyclic factors (n/p > ~40) and n = 1 with large p (PSL(2,509), 1.5 s per evaluation) were poor, as before.

**Negative results** (squad cards, numbers in the LOG): product groups in haar_sym; an alpha acting on one factor of
PSL(2,41) x SL(2,5) x Z11 to give the fixed letters a non-abelian centralizer (2,400 fixed elements, far worse); 2+2
multi-Haar lifts of K_{2,2} over SL(2,p) (no better than Haar graphs of equal order); cyclic and coset-union Haar graphs
(a counting bound caps them near 10^6 vertices); k = 3 near-miss finishing with larger K and other seeds; the doubling
n_b(Δ,D) >= 2 n(Δ-1,D-1), since the general table stops at degree 16 and 2 n(16,7) = 29,990,734 < 41.4M.

**D = 7.** The table now carries the hexagon-with-hubs graphs of job conics-2 (branch claude/conics-2-diameter-7-ic0oat,
research/synthetic/conics2/README.md): (17,7) 5,693,959 (on master since Oct 30), (18,7) 7,309,092, (19,7) 11,316,940
and (20,7) 15,795,219. When that job ended, (19,7) had 9 of 16 and (20,7) 9 of 24 source ranges of its all-pairs check
recorded; the other ranges had finished afterwards in their cloud sessions, and this job read the RESULT lines and the
edge-list sha256 from the 22 session transcripts: all VALID, full coverage (checks/d19D7_n11316940_ranges_complete.txt,
checks/d20D7_n15795219_ranges_complete.txt). Haar graphs are far below these values at D = 7 (size law ~2.9M at
(17,7)). Squad card r3/e16 tried extra hubs on the spare slots of the typed level graphs at q = 5: one to 200 extra hubs
always leave 170-220 level-0 vertices at distance 8, because level 0 (whose freed set sets the hub cap) has no spare
slots. Negative for the naive version.

**A lead for D = 8 (not pursued).** The 2013 table's (q+2, 8) values are exactly 3(q^6 - 1) (e.g. (13,8) = 5,314,680 =
3 x (11^6 - 1)), and q^6 - 1 is the number of nonzero singular vectors of the parabolic quadric Q(6,q) that carries the
split Cayley hexagon H(q). So the table's construction looks like a lift of H(q) whose vertices are singular vectors up
to sign (q - 1)/2 per point, times Z3 levels, joined by one matching. For q = 3 random voltages already work (squad
beyond r1/c10), so small cases do not reveal the structure. If found, it would give about 1.6-1.9x the current Haar
values at (17..20, 8) (REGULARITIES.md 2.1).

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
