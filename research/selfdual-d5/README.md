# selfdual-d5: self-dual (bipartite Cayley) Haar graphs in other diameter-5 cells

Job "selfdual-d5" (Opus cloud session, Oct 30 2026, from 20:35 UTC). Method from `../d75-raise/README.md` (the (7,5)
1,312 record): if S is a union of orbits of psi(x) = c^-1 beta(x)^-1 for an extension G^ = G u G t of G
(t^2 = c, t x t^-1 = beta(x)), then H(G,S) = Cay(G^, tS) is vertex-transitive and only X X = G (X = S^-1 S) has to
be checked. Work in progress; see the status section at the end.

**NEW (9,5): 2,934 vertices** (our value was 2,758, the Haar graph of C197 : C7; 2,790, 2,814 and 2,928 earlier in
this job): the Haar graph of G = C163 : C9 = <x, y | x^163 = y^9 = 1, y x y^-1 = x^58> = SmallGroup(1467,1) (y acts with
order 3), elements x^i y^j written (i,j), S = {(0,0), (4,0), (105,0), (143,4), (39,5), (119,8), (56,1), (117,7),
(106,2)}, (g,A) ~ (s g, B). 9-regular, bipartite, diameter 5. Self-dual for beta(x) = x^-1, beta(y) = y (psi fixes
(0,0), (4,0), (105,0) and swaps three pairs), so also a Cayley graph of C163 : C18 with T = S tau. Checks: apsp.c VALID
at D = 5, INVALID at D = 4 (`records/d9D5_n2934_haar_c163c9_apsp.txt`), independent Python checker VALID, GAP-free
rebuild from the formula identical to the saved edge list, Cayley build and the search's own build: same nauty
canonical form (`records/d9D5_n2934_haar_c163c9_cayley.txt`). Files: `records/d9D5_n2934_haar_c163c9.edges` (sha256
f5e6c338c0068e874e3e0f472ac4be620a4391f53488604bedfe8c7cb2c6af18), rebuild `records/build_d9D5_n2934_haar_c163c9.sh`,
search output `records/d9D5_n2934_haar_c163c9_search.out` (sdtabu K = 9, record 1, type (3,3), 300 s deep run on a
near miss of the metacyclic sweep).

Earlier in this job, **2,928 vertices**: the Haar graph of G = C61 : C24 = <x, y | x^61 = y^24 = 1, y x y^-1 = x^14> = SmallGroup(1464,1) (y acts with
order 6), elements x^i y^j written (i,j), S = {(0,0), (19,0), (42,12), (59,4), (35,20), (54,7), (30,5), (57,14),
(56,10)}, (g,A) ~ (s g, B). 9-regular, bipartite, diameter 5. Self-dual for beta(x) = x^-1, beta(y) = y^13, so also a
Cayley graph of G : <tau> (order 2,928) with T = S tau. Checks: apsp.c VALID at D = 5, INVALID at D = 4
(`records/d9D5_n2928_haar_c61c24_apsp.txt`), independent Python checker VALID, GAP-free rebuild from the formula identical
to the saved edge list, Cayley build and the search's own build: same nauty canonical form
(`records/d9D5_n2928_haar_c61c24_cayley.txt`). Files: `records/d9D5_n2928_haar_c61c24.edges` (sha256
b018047dc73e01113857ca8eb258da2d6ae3f7e693dd64f08466dead75ecd233), rebuild `records/build_d9D5_n2928_haar_c61c24.sh`,
search output `records/d9D5_n2928_haar_c61c24_search.out` (sdtabu K = 9 on the metacyclic list, record 6, type (3,3)).

Earlier in this job, **2,814 vertices**: the Haar graph of G = C67 : C21 = <x, y | x^67 = y^21 = 1, y x y^-1 = x^29> = SmallGroup(1407,2) = C7 x (C67 : C3), elements
x^i y^j written (i,j), S = {(0,0), (51,0), (4,0), (22,10), (10,11), (44,5), (3,16), (55,19), (25,2)}, (g,A) ~ (s g, B).
9-regular, bipartite, diameter 5. Self-dual for beta(x) = x^-1, beta(y) = y (psi fixes (0,0), (51,0), (4,0) and swaps
three pairs), so also the Cayley graph of G : <tau> = C67 : C42 with T = S tau (three involutions, three inverse pairs).
Checks: apsp.c RESULT VALID at D = 5 and INVALID at D = 4 (`records/d9D5_n2814_apsp.txt`), independent Python checker
VALID (`records/d9D5_n2814_check_independent.txt`), GAP-free rebuild from the formula identical to the saved edge
list, Cayley build (`records/build_metacyclic_cayley.py`) and the search's own build: same nauty canonical form. Files:
`records/d9D5_n2814_haar_c67c21.edges` (sha256 951655670d9d7bed30f3568c696814e397a010081bc26827268c58046d7e42d8),
rebuild `records/build_d9D5_n2814.sh`, search output `records/sg1407_2_tabu.out` (sdtabu K = 9, type (3,3)). A second
group of the same order also works: C469 : C3 = SmallGroup(1407,4) (`records/sg1407_4_tabu.out`, apsp VALID).

Earlier in this job, **2,790 vertices**: the Haar graph of
G = C31 : C45 = <x, y | x^31 = y^45 = 1, y x y^-1 = x^28> = SmallGroup(1395,1) (y acts with order 15), elements x^i y^j
written (i,j), S = {(0,0), (28,20), (18,25), (24,26), (22,19), (21,28), (3,17), (10,41), (4,4)}, (g,A) ~ (s g, B).
9-regular, bipartite, diameter 5. S is self-dual for beta(x) = x^-1, beta(y) = y (psi fixes (0,0) and swaps the four
pairs), so the graph is also the Cayley graph of C31 : C90 = G : <t> with T = S t (one involution, four inverse pairs).
Checks: apsp.c RESULT VALID at D = 5 and INVALID at D = 4 (`records/d9D5_n2790_apsp.txt`), independent Python checker
VALID (`records/d9D5_n2790_check_independent.txt`), GAP-free rebuild from the formula identical to the saved edge list,
the Cayley build and the search's own build have the same nauty canonical form. Files:
`records/d9D5_n2790_haar_c31c45.edges` (sha256 5d63f5bee169b51c1fbe38ab0ca7971c35460b7f73e8cf25884db9cc21b9b6b7),
rebuild `records/build_d9D5_n2790.sh`, search output `records/sg1395_1_tabu.out` (sdtabu K = 9, type (1,4), found in
the DEEP phase of record 1 within 27 s).

## Tools (src/)

| file | what it does | calibration |
|---|---|---|
| `export_sd.g` | GAP: SmallGroup(N,ID) as a multiplication table + inverses; `ALPHA 1` (identity) and `ALPHA 2` (each class of involutions of Aut(G)) with centralizer generators (split cosets, c = e); `EXT c` for every Aut(G)-class of pairs (beta, c), c <> e, beta(c) = c, beta^2 = conjugation by c, with the stabilizer (non-split cosets: needed when T has no involution, K even). | |
| `sdk.c` | valency K (env K): ALPHA records: S = e + (f-1) psi-fixed + m psi-2-orbits, f + 2m = K, f >= 1, f = K mod 2; EXT records (K even): S = {e, c^-1} + K/2 - 1 further 2-orbits. First free orbit (or fixed element when m = 0) up to the stabilizer. Fast rejection as in haar75 (move-to-front targets); every set with X X = G gets the full three-condition Haar check. Caps MAXEV, MAXEVF (types with f >= 4); `SAMPLE=1` draws random sets of each type instead. | K = 7 on SmallGroup(656,28): the same 9 sets as haar75 anti (the 1,312 record), all types 36 s (`logs/calib/K7_656_28.out`). K = 6 on SL(2,7) = SmallGroup(336,114): 38 sets, apsp VALID at D = 5 (672 vertices, below the table's 684) |
| `export_hat.g`, `brute.c`, `canon_cmp.py` | independent check: every inverse-closed T of size K in the coset of an index-2 subgroup of a group of order 2n, no normalisation, diameter by BFS; isomorphism classes (nauty-labelg) compared with sdk's | SL(2,7), K = 6: the 4 groups of order 672 containing it give 3,360 hits = 5 classes = sdk's 5 classes. C5 x (C13 : C4) = SmallGroup(260,2): sdk's 7 classes from non-split cosets (EXT) = the classes of the 18,720 brute hits on the two non-split groups 520_5, 520_6 (no involution in the coset); no brute class outside sdk's (`logs/calib/brute_vs_sdk.txt`) |
| `cover.py` | coverage table of a sweep log | |
| `run1.sh`, `sweep.sh` | drivers: one group (export + sdk, one line in `logs/K$K/sweep.txt`), a list in parallel | |
| `list_groups.g` | non-abelian SmallGroups of a range of orders with their numbers of involution classes and involutions | |

Check of every hit: research/lifts/coordinator_check/apsp.c (`src/apsp`), VALID at D = 5 and INVALID at D = 4.
| `sdtabu.c` | tabu search inside the same family (same records and types as sdk) for types too large to enumerate: replace one fixed element or one 2-orbit, NB random candidates per step, tabu tenure, restarts; energy \|G \ X X\|; `DEEP=thr,secs` gives extra time to types that get within thr | K = 7 on 656_28 (3,2): 3 of the 1,312 sets in 0.4 s; K = 6 SL(2,7): sets in 0.1-1 s; K = 9 on C197 : C7 = SmallGroup(1379,1) (the group of our 2,758 record): valid 9-sets of types (3,3) and (5,2) in 7-40 s (apsp VALID at D = 5, INVALID at D = 4); K = 8 on AGL(1,7) x C21 = 882_40: a (4,2) set in 0.3 s, many types at 1 |
| `run_tabu.sh`, `sweep_tabu.sh` | drivers for sdtabu (one line per group in `logs/K$K/tabu.txt`) | |
| `haar_edges.py` | edge list of H(G,S) from an export table and S | |
| `stop_driver.sh` | stop a sweep driver (running groups finish) | |

## Status (running log)

- 20:35 start. GAP 4.12 + full SmallGroups (gap-smallgrp-extra) installed in the container.
- (6,5): sdk K = 6 sweep of every non-abelian group of order 343-450 (no 384): first 343-352 (+ the rest of 343-360
  later), then 361-450 with <= 7 involutions first. Caps: MAXEV 1e8 for every type; types with >= 4 psi-fixed elements:
  2e7 (first 53 groups, lexicographic cut), then 3e6, from 21:20 UTC types larger than the cap are randomly sampled
  (SAMPLED) instead of cut. Closest: SmallGroup(352,50) = C11 x (order-32 group), type (6,0): |G \ X X| = 1, the
  whole type enumerated (`logs/K6/deep/352_50_f46.out`); 372_1 = C31 : C12, (2,2): 2. Squad round sd5-r1: 8 other
  families, nothing above 684 (`../squads/LOG.md`).
- (9,5): sdtabu K = 9 sweep of groups of order 1380-1460 (no 1408, 1440, 1456, 1458), odd order first, then by number of
  involutions; SECS = 2 per (record, type), DEEP = 10,25, types (1,4), (3,3), (5,2) ((7,1), (9,0) are hopeless on
  C197 : C7: best 362 and 1182). Hits: 1395 (groups 1, 2, 3, 5: C31 : C45, C9 x (C31 : C5), C5 x (C31 : C9),
  C3 x (C31 : C15)) -> 2,790; 1407 (2: C7 x (C67 : C3), 4: C469 : C3) -> 2,814; then the metacyclic list
  (`src/meta_group.g`, `src/run_meta.sh`: C_p : C_k with y acting with order d >= 3, p >= 31 prime, orders 1379-1800,
  `logs/meta9_list.txt`): C61 : C24 (d = 6) -> 2,928. After each hit the lists were cut to larger orders. Near misses
  (|G \ X X| = 2) at 1467 (C163 : C9), 1474 (C67 : C22), 1485 (SmallGroup(1485,4), (1485,5)); a probe of the metacyclic
  groups of order 1569-1635 stays at 10 or more, so the frontier of this family is around 1470-1500.
- (7,5): SmallGroup(660,16) (the previous job's near miss) with every type uncapped: no solution, best 2
  (`logs/K7/deep/660_16_all.out`).
