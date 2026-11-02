# Beyond the 2013 table: first values for 59 new cells

Job new-cells-beyond (Opus director + Haiku squads, cloud session, 2026-10-26, branch claude/new-cells-beyond-etos3t).
The 2013 bipartite table (DS14v2, Table 4) stops at Δ = 16 and D = 10. This file gives a checked lower bound for every
cell in the next band: Δ = 17..20 at D = 3..10 (32 cells) and D = 11, 12 at Δ = 3..10 (16 cells), with an upper bound
and the comparison with the formula families. As far as we know (literature card r2/d10) no bipartite values have been
published for these cells, so every value here is a first value, not a record.

Extended 2026-11-01 by job beyond-d11 (branch claude/new-cells-d11-d12-beyond-8sas9r): seven more cells, D = 11 at
Δ = 11..14 and D = 12 at Δ = 11..13, and new values for (4..10, 11) and (4..10, 12); see the section "D = 11 at
Δ = 11..14 and D = 12 at Δ = 11..13" below.

Extended 2026-11-01 by job beyond-d11b (branch claude/beyond-d11-d12-new-cells-3t3djx): new cells (15,11), (16,11) and
(14,12) with Haar graphs of 28.7-30.0 billion vertices, (12,12) and (13,12) raised to ~30 billion, and (4..6, 11), (4,12),
(5,12) raised with Frobenius groups Z_p x| Z_k; see the section "D = 11 at Δ = 15, 16, D = 12 at Δ = 14, and raises".

Extended 2026-11-02 by job raise-d12 (branch claude/d12-frontier-cells-m24ikx): new cell (15,12) at 30.0 billion
vertices, and (8,12), (9,12), (10,12), (11,12) raised 4.0-6.6 % with orbits of the field automorphism of GF(128)
(order 7) and GF(243) (order 5); see the section "D = 12: field-automorphism orbits".

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
- **Beyond-d11b:** (15,11), (16,11), (14,12) at 28.7-30.0 billion vertices (SL(2,617) x Z61, PSL(2,449) x Z331,
  PSL(2,241) x Z2143), (12,12) and (13,12) raised to ~30 billion at the job's 30-billion cap; the small cells (4..6, 11),
  (4,12), (5,12) raised with odd-order Frobenius groups Z_p x| Z_k, which at Δ = 4 beat the size law by far
  (research/frontier/beyond11/FROBENIUS.md).
- **raise-d12:** (8,12), (9,12) on SL(2,128) x Z_n with S closed under the field automorphism x -> x^2 (order 7,
  fixed set SL(2,2)), (10,12), (11,12) on PSL(2,243) x Z_n with x -> x^3 (order 5, fixed set PSL(2,3)): +4.0-6.6 %;
  new cell (15,12) 29,999,670,624 (PSL(2,197) x Z3924) at the 30-billion cap. Squad rounds found no structure for
  (3..7,12), where no field group of the right size exists (research/squads/LOG.md, job raise-d12).
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
| (4,11) | **30,334** | 17.12 | 177,140 | Haar graph of the Frobenius group Z523 x\|_9 Z29 (odd order 15,167, trivial centre), plain random S = 4 elements (haar_gen3; job beyond-d11b squad r2/h01); was 24,360 (PSL(2,29)); also 29,470 (Z421 x\| Z35, r2/h02), 28,918 (Z761 x\| Z19, r1/g02); mu = 44.13 | build_haar2.py VALID and all-pairs apsp VALID (research/frontier/runs/cloudcheck/d4D11_meta_523_29_9_b2h01.check.txt) | Haar size law at mu = 5: 2N = 2.29e+04 |
| (5,11) | **311,426** | 11.14 | 2,796,196 | Haar graph of the Frobenius group Z5023 x\|_2886 Z31 (odd order 155,713, trivial centre), random S annealed with a save/resume chain (haar_gen3s; job beyond-d11b squad r5/k05); was 297,648 (SL(2,53)); also 310,718 (Z3613 x\| Z43, r4/j12), 310,498 (Z8171 x\| Z19, r2/h17); mu = 19.63 | build_haar2.py VALID and all-pairs apsp VALID (research/frontier/runs/cloudcheck/d5D11_meta_5023_31_2886_b5k05.check.txt) | Haar size law at mu = 5: 2N = 2.74e+05 |
| (6,11) | **2,122,518** | 8.69 | 24,414,056 | Haar graph of the Frobenius group Z20809 x\|_12972 Z51 (odd order 1,061,259, trivial centre), plain random S (haar_gen3s; job beyond-d11b squad r5/k07); was 2,094,960 (SL(2,29) x Z43); also 2,112,114 (Z20707 x\| Z51, r4/j06), 2,098,038 ((Z67 x\| Z3) x (Z307 x\| Z17), r3/i08); mu = 10.72 | build_haar2.py VALID (research/frontier/runs/cloudcheck/d6D11_meta_20809_51_12972_b5k07.check.txt) | Haar size law at mu = 5: 2N = 2e+06 |
| (7,11) | **11,012,976** | 7.59 | 145,118,816 | Haar graph SL(2,53) x Z37, S = {e} + 2 orbits of size 3 (squad r2/d09); was 10,648,176; mu = 10.43 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d7D11_sl_53_37_orb3-2-1_d09.gen.txt) | Haar size law at mu = 5: 2N = 1.05e+07 |
| (8,11) | **45,329,808** | 6.88 | 659,108,908 | Haar graph SL(2,283), S = {e} + 1 fixed + 2 orbits of size 3 (squad r3/e04); was 43,702,560; mu = 10.98 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d8D11_sl_283_1_orb3-2-2_e04.gen.txt) | Haar size law at mu = 5: 2N = 4.31e+07 |
| (9,11) | **155,250,816** | 6.33 | 2,454,267,020 | Haar graph SL(2,223) x Z7, S = 3 free orbits of size 3 (squad r2/d08); was 145,258,344; mu = 10.58 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d9D11_sl_223_7_orb3-3-0_d08.gen.txt) | Haar size law at mu = 5: 2N = 1.49e+08 |
| (10,11) | **460,691,568** | 5.87 | 7,845,264,896 | Haar graph SL(2,613), S = {e} + 3 orbits of size 3 (squad r2/d13); was 445,709,568; mu = 9.26 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d10D11_sl_613_1_orb3-3-1_d13.gen.txt) | Haar size law at mu = 5: 2N = 4.45e+08 |
| (11,11) | **1,241,299,248** | 5.59 | 22,222,222,216 | Haar graph SL(2,853), S = {e} + 1 fixed + 3 orbits of size 3 (director, 892 evals at mu 10.4); earlier 1,210,478,448 (SL(2,317) x Z19, squad r2/d01) and 1,170,162,000 (SL(2,251) x Z37); mu = 10.42 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d11D11_sl_853_1_orb3-3-2_s1.gen.txt) | Haar size law at mu = 5: 2N = 1.19e+09 |
| (12,11) | **2,976,066,240** | 5.22 | 57,062,334,116 | Haar graph SL(2,239) x Z109, S = 4 free orbits of size 3 (f = 0, haar_big0; squad r1/c04); earlier 2,874,207,072 (SL(2,263) x Z79, director); mu = 7.01 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d12D11_sl_239_109_orb3-4-0_c04.gen.txt) | Haar size law at mu = 5: 2N = 2.93e+09 |
| (13,11) | **6,781,213,392** | 5.02 | 135,092,431,028 | Haar graph SL(2,563) x Z19, S = {e} + 4 orbits of size 3 (director); earlier 6,508,747,920 (SL(2,229) x Z271); mu = 7.56 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d13D11_sl_563_19_orb3-4-1_s1.gen.txt) | Haar size law at mu = 5: 2N = 6.65e+09 |
| (14,11) | **14,381,398,080** | 4.81 | 298,693,399,000 | Haar graph SL(2,1009) x Z7, S = {e} + 1 fixed + 4 orbits of size 3 (director); mu = 6.87 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d14D11_sl_1009_7_orb3-4-2_s1.gen.txt) | Haar size law at mu = 5: 2N = 1.42e+10 |
| (15,11) | **28,655,908,512** | 4.60 | 623,010,026,096 | Haar graph SL(2,617) x Z61, S = 5 free orbits of size 3 (f = 0; director, 13 evals); new cell (job beyond-d11b); mu = 5.18 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d15D11_sl_617_61_orb3-5-0_s1.gen.txt) | Haar size law at mu = 5: 2N = 2.86e+10 |
| (16,11) | **29,961,590,400** | 2.42 | 1,235,679,408,476 | Haar graph PSL(2,449) x Z331, S = {e} + 5 orbits of size 3; at the job's 30-billion cap (first S solved); new cell (job beyond-d11b); mu = 0.00 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d16D11_psl_449_331_orb3-5-1_s1.gen.txt) | Haar size law at mu = 5: 2N = 5.51e+10 |
| (3,12) | **2,176** | 26.57 | 8,184 | metacyclic Haar graph Z68 x|_3 Z16, S = {e, 68, 205} (director sweep of metacyclic groups, exhaustive pairs; best of 7 hits at orders 979-1,088); earlier 1,860 (AGL(1,31), r3/e02) | apsp VALID, diameter exactly 12 (checks/d3D12_n2176_meta68_16_3.apsp.txt) | Haar size law at mu = 5: 2N = 1.61e+03 |
| (4,12) | **70,176** | 13.20 | 531,434 | Haar graph of the metacyclic group Z731 x\|_7 Z48 (731 = 17 x 43; order 35,088), random S annealed with save/resume chains (haar_gen3s; job beyond-d11b squad r5/k02); was 68,544 (SL(2,17) x Z7); also 70,038 (Frobenius Z1297 x\| Z27, r3/i10), 68,906 (Z263 x\| Z131, r2/h12); mu = 18.04 | build_haar2.py VALID and all-pairs apsp VALID (research/frontier/runs/cloudcheck/d4D12_meta_731_48_7_b5k02.check.txt) | Haar size law at mu = 5: 2N = 6.1e+04 |
| (5,12) | **1,058,342** | 9.46 | 11,184,804 | Haar graph of the Frobenius group Z8969 x\|_205 Z59 (order 529,171), random S finished with save/resume chains (haar_gen3t; job beyond-d11b squad r6/l03); was 1,041,768 (PSL(2,53) x Z7); also 1,056,886 (Z8663 x\| Z61, r5/k03), 1,050,906 (Z10303 x\| Z51, r4/j10); mu = 13.61 | build_haar2.py VALID (research/frontier/runs/cloudcheck/d5D12_meta_8969_59_205_b6l03.check.txt) | Haar size law at mu = 5: 2N = 9.74e+05 |
| (6,12) | **9,366,240** | 7.67 | 122,070,306 | Haar graph PSL(2,79) x Z19, S = 2 free orbits of size 3 (squad r3/e08); was 9,303,840; mu = 10.24 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d6D12_psl_79_19_orb3-2-0_e08.gen.txt) | Haar size law at mu = 5: 2N = 8.91e+06 |
| (7,12) | **59,838,504** | 6.87 | 870,712,928 | Haar graph PSL(2,67) x Z199, S = {e} + 2 orbits of size 3 (squad r3/e09); was 56,297,592; mu = 14.34 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d7D12_psl_67_199_orb3-2-1_e09.gen.txt) | Haar size law at mu = 5: 2N = 5.6e+07 |
| (8,12) | **297,777,408** | 6.45 | 4,613,762,394 | Haar graph SL(2,128) x Z71, S = {e} + one orbit of size 7 of alpha = (field automorphism x -> x^2 of GF(128), order 7) x (z -> 20 z), Fix(alpha) = SL(2,2) (director, haar_bigq, 3 of 420 random orbit samples had cost 0; job raise-d12); was 284,095,056 (PSL(2,167) x Z61, k = 3); mu = 27.79 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d8D12_sl_128_71_orb7-1-1_r2.gen.txt) | Haar size law at mu = 5: 2N = 2.7e+08 |
| (9,12) | **1,178,527,488** | 6.00 | 19,634,136,204 | Haar graph SL(2,128) x Z281, S = {e} + one alpha-fixed generator of order 3 + one orbit of size 7 of the field automorphism (director, haar_bigq, 1,444 evaluations; job raise-d12); was 1,105,785,120 (PSL(2,241) x Z79, k = 3); mu = 34.28 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d9D12_sl_128_281_orb7-1-2_s21.gen.txt) | Haar size law at mu = 5: 2N = 1.06e+09 |
| (10,12) | **3,888,487,944** | 5.51 | 70,607,384,114 | Haar graph PSL(2,243) x Z271, S = 2 free orbits of size 5 of alpha = (field automorphism x -> x^3 of GF(243), order 5) x (z -> r z), Fix(alpha) = PSL(2,3) (director, haar_bigq, 626 evaluations; job raise-d12); was 3,712,424,352 (PSL(2,337) x Z97, k = 3); mu = 25.28 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d10D12_psl_243_271_orb5-2-0_s11.gen.txt) | Haar size law at mu = 5: 2N = 3.58e+09 |
| (11,12) | **11,636,766,504** | 5.24 | 222,222,222,216 | Haar graph PSL(2,243) x Z811, S = {e} + 2 orbits of size 5 of the field automorphism x -> x^3 (times z -> r z), Fix(alpha) = PSL(2,3) (director, haar_bigq, 161 evaluations; job raise-d12); was 11,189,148,096 (PSL(2,223) x Z1009, k = 3); mu = 29.60 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d11D12_psl_243_811_orb5-2-1_s31.gen.txt) | Haar size law at mu = 5: 2N = 1.07e+10 |
| (12,12) | **29,996,171,040** | 4.78 | 627,685,675,338 | Haar graph PSL(2,241) x Z2143, S = 4 free orbits of size 3 (director, 45 evals, job beyond-d11b); was 19,980,294,768 (PSL(2,503) x Z157, 20-billion cap); mu = 12.25 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d12D12_psl_241_2143_orb3-4-0_s1.gen.txt) | Haar size law at mu = 5: 2N = 2.88e+10 |
| (13,12) | **29,997,644,040** | 1.85 | 1,621,109,172,404 | Haar graph PSL(2,181) x Z5059, S = {e} + 4 orbits of size 3; at the job's 30-billion cap (first S solved; job beyond-d11b); was 19,993,487,976 (PSL(2,307) x Z691, 20-billion cap); mu = 0.00 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d13D12_psl_181_5059_orb3-4-1_s1.gen.txt) | Haar size law at mu = 5: 2N = 7.14e+10 |
| (14,12) | **29,996,171,040** | 0.77 | 3,883,014,187,074 | Haar graph PSL(2,241) x Z2143, S = {e} + 1 fixed + 4 orbits of size 3; at the job's 30-billion cap (first S solved); new cell (job beyond-d11b); mu = 0.00 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d14D12_psl_241_2143_orb3-4-2_s1.gen.txt) | Haar size law at mu = 5: 2N = 1.65e+11 |
| (15,12) | **29,999,670,624** | 0.34 | 8,722,140,365,424 | Haar graph PSL(2,197) x Z3924, S = 5 free orbits of size 3 (conjugation alpha; f = 0); at the job's 30-billion cap (first S solved); new cell (job raise-d12); the floor from (13,12) is 29,997,644,040; mu = 0.00 | haarcheck_gen VALID (research/frontier/runs/cloudcheck/d15D12_psl_197_3924_orb3-5-0_s1.gen.txt) | Haar size law at mu = 5: 2N = 3.59e+11 |
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

### D = 11 at Δ = 15, 16, D = 12 at Δ = 14, and raises (job beyond-d11b, 2026-11-01)

Job beyond-d11b (Opus director + six Haiku squad rounds of 12-17 cards, cloud session, branch
claude/beyond-d11-d12-new-cells-3t3djx). Size limit for the job: about 30 billion vertices (N <= 1.5e10).

**The 30-billion cells (director).** haar_big0 with the beyond-d11 parameters; groups chosen just under the cap with p
small enough that haarcheck_gen's p^2 field tables stay in cache (p <= ~620), n prime = 1 mod 3.
- (16,11) PSL(2,449) x Z331, "3 5 1": lambda = W/N = 41.2, so even PSL (whose involutions are missed with probability
  ~exp(-lambda/2)) and n = 331 central elements (~exp(-lambda/5) each) are harmless; first S solved (37 s per evaluation
  at 4 threads, 7.7 GB). haarcheck_gen VALID, 5,281 s.
- (15,11) SL(2,617) x Z61, "3 5 0" (f = 0, 3 | Δ): the only odd-D cell here that is not cap-limited (mu = 14 at the cap);
  ODD_D_HOLES.md's rule (SL, small n) with p kept <= ~620 for the checker gives n = 61 and mu 5.2 at 28.66 billion; solved
  in 13 evaluations (132 s). A push to SL(2,571) x Z79 (29.4 billion, mu 9.3) was planned and dropped: the checks needed
  the machine.
- (14,12) PSL(2,241) x Z2143 "3 4 2" and (13,12) PSL(2,181) x Z5059 "3 4 1": lambda = 129 and 54, first S solved.
- (12,12) PSL(2,241) x Z2143 "3 4 0": mu 12.25 at the cap, solved in 45 evaluations (178 s); raises 19,980,294,768.
- Checks: haarcheck_gen from (e,A) and (e,B), one at a time (0.75 N bytes = 11.2 GB each, 4 threads), logs
  research/frontier/runs/cloudcheck/<stem>.gen.txt; all five VALID: (16,11) 5,281 s, (15,11) 4,663 s (both with squad
  cards running), (14,12) 2,859 s, (12,12) 2,406 s, (13,12) 2,576 s (idle machine). All five are above 20 billion vertices, so the coordinator's
  reference check needs the split runs: research/structured/tools/haarcheck_psl.c SOL A and SOL B for the four PSL
  graphs, and research/frontier/haarcheck_sl.c SOL A / SOL B for (15,11) (this job added the same A|B option to
  haarcheck_sl.c; tested on a small VALID and a D-1 INVALID case).

**Small cells: odd-order Frobenius groups (squads).** Round 1 card g02 tried odd-order metacyclic groups at (4,11) (the
(3,11) value Z67 x| Z11 is one) and g16 tried SL(2,p) x (centre-free odd Frobenius group); both beat (4,11) at once,
far above the size law. Rounds 2-6 followed the lead: Frobenius groups Z_p x|_r Z_k (p prime, k | p - 1, r of order k;
odd order and trivial centre for odd k) with random S raised (4,11) 24,360 -> 30,334, (5,11) 297,648 -> 311,426,
(6,11) 2,094,960 -> 2,122,518, (4,12) 68,544 -> 70,176 (a metacyclic Z731 x| Z48) and (5,12) 1,041,768 -> 1,058,342
(from round 4 on with a save/resume version of haar_gen3, haar_gen3s, and in round 6 a targeted finisher, haar_gen3t;
sources in research/squads/beyond11b/tools/). Card r2/h13 measured why: at Δ = 4 random S on Z761 x| Z19 leave 1.1x the
size-law mu
uncovered, SL(2,23) and SL(2,13) x Z7 4-5x, and the difference is middle-level collisions (short relations in small
SL(2,p)), not involutions. The gain shrinks with N: the new values sit at size-law mu 44 at (4,11), 20 at (5,11), 18 at (4,12), 14 at (5,12) and
11 at (6,11), against 8-15 for the SL/PSL values they replace.
k matters (k = 3 collapses, k = 7 is bad, k = 13-63 behave like random groups). Details, proofs (r2/h17) and the list
of what failed: research/frontier/beyond11/FROBENIUS.md. These graphs were checked by build_haar2.py (all) and the
all-pairs apsp (2N <= 311k); haarcheck_gen does not know metacyclic groups. Near the limit the annealer's cost-1/2
states are real local minima: an exhaustive scan of all 105,609 single-generator swaps of a cost-1 (4,12) state found no
cost 0 (r6/l01); solves came from many fresh lineages and a few resumed chains.

**What failed or was not reached.** Raises of (11..14, 11) and (11,12) were not attempted (each needs mu above where
odd-D searches stall, for gains of 1-3 %, and the machine was busy with the five ~11 GB checks). Frobenius groups at
(7,11) and (8,11) stopped at cost 2 and 8 (evaluation too slow for squad cards at N >= 5.5M). Cubic cells: no gain
(exhaustive Frobenius and product groups, lifts of cubic multigraphs to cost 2 at 2,184 vertices for (3,12)). Negatives
from round 1: Sz(8), F_{p^3} x| C_k, bipartite Cayley graphs of PGL(2,p), PSL(2,p^e) with a Frobenius automorphism,
agl1 products, voltage lifts of PG(2,3) (19,500 at (4,11)). Squad log: research/squads/LOG.md (job beyond-d11b).

### D = 12: field-automorphism orbits at Δ = 8..11, and (15,12) (job raise-d12, 2026-11-01/02)

Job raise-d12 (Opus director + Haiku squad rounds, cloud session, branch claude/d12-frontier-cells-m24ikx). Size limit:
30 billion vertices.

**The idea.** BEYOND_RANDOM.md: if S is closed under an automorphism alpha of odd order k, the uncovered elements come in
alpha-orbits, so a valid S appears with probability about exp(-mu/k - F) instead of exp(-mu), where F counts the
alpha-fixed elements (each missed with probability exp(-lambda/k)). The earlier D = 12 values used k = 3 (conjugation by
a matrix of order 3, whose fixed set is a torus of ~p/2 elements). The field automorphism x -> x^p of GF(p^e) has order e
and fixes only SL(2,p) or PSL(2,p): for SL(2,128) (e = 7) the fixed set is SL(2,2), 6 elements, and for PSL(2,243)
(e = 5) it is PSL(2,3), 12 elements. So these groups allow k = 7 and k = 5 with almost no fixed-point cost. The search
tool is research/frontier/raise-d12/haar_bigq.c: haar_big0 (bit-parallel, N/2 bytes) for SL/PSL(2,q) x Z_n with q a
prime power; its rows are cosets of the split torus x Z_n (cyclic when gcd(|T|, n) = 1), and AFROB=j selects the field
automorphism. It reproduces haar_big0's cost exactly on prime fields and haarcheck_gen's unreached count on GF(81).

**Results (director).**
- (8,12) **297,777,408** (+4.8 %): SL(2,128) x Z71, alpha = (x -> x^2) x (z -> 20 z), S = {e} + one 7-orbit
  ("7 1 1"). Size-law mu 27.8, so mu/7 = 4.0 and the fixed term ~ 5 exp(-lambda/7) = 0.55: plain random sampling of
  the orbit representative x gave cost 0 for 3 of 420 samples (0.22 s each). n = 71 is the only n with an order-7
  multiplier between the old value and mu ~ 100, so the method stops here at Δ = 8.
- (9,12) **1,178,527,488** (+6.6 %): SL(2,128) x Z281, S = {e} + one alpha-fixed generator of order 3 (from SL(2,2))
  + one 7-orbit ("7 1 2", FIXORD=3); mu 34.3. Solved by haar_bigq's annealer after 1,444 evaluations (random sampling:
  none in ~1,100 samples, minimum one clump). An involution as the fixed generator is much worse (median cost 357
  against 56): e t^-1 = t e^-1 wastes words.
- (10,12) **3,888,487,944** (+4.7 %): PSL(2,243) x Z271, alpha = (x -> x^3, order 5) x (z -> r z), S = two free
  5-orbits ("5 2 0"); mu 25.3. Solved after 626 evaluations (a second seed also reached 0); the last holes were
  alpha-fixed elements.
- (11,12) **11,636,766,504** (+4.0 %): PSL(2,243) x Z811, S = {e} + two 5-orbits ("5 2 1"); mu 29.6 (mu/5 = 5.9).
  Solved after 161 evaluations (494 s on 2 threads). Z821 (+5.3 %, mu/5 = 7.6) stalled at cost 10 (see runs/).
- (15,12) **29,999,670,624**, new cell: PSL(2,197) x Z3924 with 5 free conjugation 3-orbits (haar_big0); lambda = 291,
  so the first S solved (15 s). The group order was picked so that 2N lies between the floor 29,997,644,040 (the (13,12)
  graph, also a graph of max degree 15) and the cap 30,000,000,000. haarcheck_gen from (e,A) and (e,B), 4,120 s,
  11.3 GB.
- Checks: research/frontier/haarcheck_gen.c (independent group and field code, BFS from (e,A) and (e,B)), logs in
  research/frontier/runs/cloudcheck/<stem>.gen.txt; solutions in research/frontier/sols/. (8..10,12) are below
  20 billion vertices; the coordinator's haarcheck_psl / haarcheck_sl only handle prime fields, so the reference
  re-check of the GF(128) / GF(243) graphs needs haarcheck_gen (its header format "sl 128 poly x^7+x+1"). (15,12) is a prime-field PSL graph above 20 billion: haarcheck_psl SOL A and SOL B.

**Why it works and where it does not (squads, 27 cards in 2 rounds, research/squads/LOG.md).** Every card was
negative, and the negatives explain the shape of the method:
- The abelian-section wall (round 1 a05, a10, a14; round 2 b07, b08): the image of a word in an abelian quotient (or in
  an abelian normal subgroup on which alpha acts by a scalar) depends only on its signed letter counts, so an
  orbit-closed S reaches a bounded set of residues there. SL(2,8) x Z1063 leaves 82 % uncovered; SL(2,32) x (Z191 x| Z5)
  at (7,12) has 1,121 holes against 25 for a random S. b08's exact count (r2/b08/NOTE.md): one 3-orbit covers Z_n only
  for n <= 241, one 5-orbit up to 7,691; some failures (SL(2,8) x Z73 at (4,12), min cost 61 over all 12,262 orbits;
  SL(2,32) x Z941 at (7,12), min 395) are not explained by the count alone.
- Small cells have no field group of the right size: SL(2,32) (order 32,736) and PSL(2,243) (7.2 million) bracket
  (5..7,12), and products with a cyclic or dihedral factor hit the wall above. (6,12) SL(2,32) x Z151 (one 5-orbit,
  +5.6 %) and the affine group F_32768 x| C151 both floor at 3 clumps of 5 holes (cost 15) over ~10^5 samples.
- Other families measured and dropped: lifts of Moore-graph bases (Tutte 12-cage lifts stop at 1,386 vertices for
  (3,12): 65 walks per vertex-line pair, all geodesic plus apartment detours; W(3) and H(3) lifts at (4,12)), class-2
  groups with fixed-point-free automorphisms, wreath groups H^k with the shift (D7^5: always disconnected, proof), affine
  semilinear groups F_q x| C_k (54 groups exhaustively at Δ = 3; F_512 x| C73 at Δ = 4 has a structural floor of 22
  holes), inverse-closed S, order-5 conjugation orbits in PSL(2,p) (fixed torus of ~p/2 elements), unstructured
  cubic graphs (1,350 vertices).

**Who found what, and cost.** All five values of the job are the director's (haar_bigq written in the job, groups and
orbit structures chosen from the clump model of BEYOND_RANDOM.md; (15,12) with haar_big0). The 33 Haiku cards of three
rounds raised nothing; their value was negative knowledge: the abelian-section and parity walls, the Moore-base walk count,
disconnection proofs, and exhaustive scans that closed whole families for (3..7,12) (research/squads/LOG.md). Machine
time: searches 15 s ((15,12)), 82 s of sampling ((8,12)), 904 s ((9,12)), 1,435 s ((10,12)), 494 s ((11,12)); checks
172 s, 387 s, 1,079 s, 1,121 s and 4,120 s.

**Leads for other cells (not run; outside this job's D = 12 scope).** research/frontier/raise-d12/fieldfit.py lists, for
even D, the groups SL(2,32), SL(2,128), PSL(2,243) x Z_n (n with an order-k multiplier, gcd(n,|T|) = 1) and orbit
structures Δ = f + k m (f <= 2) with mu/k <= 5, where the (8..10,12) finds were solved (mu/k = 4.0, 4.9, 5.1); best
per cell in fieldfit_best.txt. Above the current values: (17,10) PSL(2,243) x Z541, "5 3 2", 7,762,627,224 (table
7,022,052,336, +10.5 %); (20,8) SL(2,32) x Z1951, "5 4 0", 127,735,872 (table 122,739,120, +4.1 %); (17,8) SL(2,32) x
Z641, "5 3 2", 41,967,552 (table 41,373,072, +1.4 %). Caution: the SL(2,32) x Z_n candidates have large n, and with one
orbit that failed at (7,12) (n = 941); with 3-4 orbits the word lattice is much larger, but test RANDORB first.

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
