# selfdual-d5: self-dual (bipartite Cayley) Haar graphs in other diameter-5 cells

(Master holds the records, tools and this README; the search logs under logs/ are on branch claude/selfdual-d5-haar-sweep-w8uhtf.)

Job "selfdual-d5" (Opus cloud session, Oct 30-31 2026, 20:35-01:40 UTC). Method from `../d75-raise/README.md` (the
(7,5) 1,312 record): if S is a union of orbits of psi(x) = c^-1 beta(x)^-1 for an index-2 extension G^ = G u G t of
G (t^2 = c, t x t^-1 = beta(x)), then H(G,S) = Cay(G^, tS) is vertex-transitive and only X X = G (X = S^-1 S) has to
be checked. New here: valency K as a parameter, non-split extensions (c != e, needed when K is even and T has no
involution), and a tabu search inside the family for the cells where enumeration is out of reach.

## Result: (9,5) 3,036 (was 2,758)

**(9,5): 3,036 vertices**, the Haar graph of G = C69 : C22 = <x, y | x^69 = y^22 = 1, y x y^-1 = x^8>
= S3 x (C23 : C11) = SmallGroup(1518,2) (trivial center, 3 involutions). Elements x^i y^j written (i,j), product
(i,j)(a,b) = (i + 8^j a, j + b). S = {(0,0), (66,11), (56,11), (28,13), (22,9), (13,15), (64,7), (25,14), (8,8)},
(g,A) ~ (s g, B). 9-regular, bipartite, diameter 5. S is self-dual for the involutory automorphism beta(x) = x^22,
beta(y) = y (22 = 1 mod 3, -1 mod 23; type (3,3)), so the graph is also a Cayley graph of G : <tau> (order 3,036) with
T = S tau.
Checks: research/lifts/coordinator_check/apsp.c RESULT VALID at D = 5 and INVALID at D = 4
(`records/d9D5_n3036_haar_c69c22_apsp.txt`); independent Python checker (../beyond-haar-d5/records/check_independent.py)
VALID; GAP-free rebuild from the formula (`records/build_metacyclic_haar.py 69 22 8 ...`, BFS from every vertex)
identical to the saved edge list; the Cayley build (`records/build_metacyclic_cayley.py`) and the search's own build
have the same nauty canonical form (`records/d9D5_n3036_haar_c69c22_cayley.txt`). Edge list
`records/d9D5_n3036_haar_c69c22.edges`, sha256 05305fe907f354997948eb0a8b98061dd5ecc1492c837716a531c03f99051ea9;
rebuild: `bash records/build_d9D5_n3036_haar_c69c22.sh`. Found by a 300 s deep tabu run (sdtabu, record 2, type
(3,3), seed 11, STALL = 2000) on a near miss of the sweep of the groups of order 1468-1560 with a cyclic or
generalized quaternion Sylow 2-subgroup.

The steps of the job (each one checked the same way: apsp VALID at D = 5 and INVALID at D = 4, independent checker,
formula rebuild identical to the saved edge list, Cayley build isomorphic; rebuild script and search output next to
each edge list):

| vertices | group | presentation / formula | S (in those coordinates) | beta | found by | edge list (sha256 prefix) |
|---:|---|---|---|---|---|---|
| 2,790 | C31 : C45 = SmallGroup(1395,1) | y x y^-1 = x^28 | (0,0) (28,20) (18,25) (24,26) (22,19) (21,28) (3,17) (10,41) (4,4) | x -> x^-1, y -> y | sdtabu, type (1,4) | `d9D5_n2790_haar_c31c45.edges` (5d63f5bee169b51c) |
| 2,814 | C7 x (C67 : C3) = C67 : C21 = SmallGroup(1407,2) | y x y^-1 = x^29 | (0,0) (51,0) (4,0) (22,10) (10,11) (44,5) (3,16) (55,19) (25,2) | x -> x^-1, y -> y | sdtabu, (3,3) | `d9D5_n2814_haar_c67c21.edges` (951655670d9d7bed) |
| 2,928 | C61 : C24 = SmallGroup(1464,1) | y x y^-1 = x^14 | (0,0) (19,0) (42,12) (59,4) (35,20) (54,7) (30,5) (57,14) (56,10) | x -> x^-1, y -> y^13 | sdtabu (metacyclic list), (3,3) | `d9D5_n2928_haar_c61c24.edges` (b018047dc73e0111) |
| 2,934 | C163 : C9 = SmallGroup(1467,1) | y x y^-1 = x^58 | (0,0) (4,0) (105,0) (143,4) (39,5) (119,8) (56,1) (117,7) (106,2) | x -> x^-1, y -> y | 300 s deep run, (3,3) | `d9D5_n2934_haar_c163c9.edges` (f5e6c338c0068e87) |
| 2,970 | Heis(3) x (C11 : C5) = SmallGroup(1485,4) | `records/build_d9D5_n2970.py` | there | there | 300 s deep run, (3,3) | `d9D5_n2970_haar_heis3_f55.edges` (d51d229ebb737ce9) |
| 2,976 | C31 : (C3 x Q16) = SmallGroup(1488,11) | `records/build_d9D5_n2976.py`: x^i z^c a^k b^l, z x z^-1 = x^25, b x b^-1 = x^-1 | (0,0,0,0) (25,0,2,0) (18,0,6,0) (12,2,1,1) (10,1,7,1) (0,1,1,0) (0,2,5,0) (24,2,0,0) (11,1,0,0) | x -> x^-1, z -> z, a -> a^3, b -> b | 300 s deep run, (3,3) | `d9D5_n2976_haar_c31_c3q16.edges` (a124e06804fc9bd5) |
| 3,000 | (C5 x C5 x C5) : (C3 : C4) = SmallGroup(1500,113) | `records/build_d9D5_n3000.py`: v s^i u^j, v in F5^3, Rs = [[1,0,0],[0,2,3],[0,1,2]], Ru = [[3,0,0],[0,2,2],[0,1,3]] | (0,0,0,0,0) (4,0,0,1,2) (0,2,3,1,2) (3,0,0,2,2) (2,0,1,2,2) (3,2,1,2,1) (4,3,1,1,3) (0,0,2,2,1) (0,4,1,1,3) | on F5^3 (1,0,0) -> (1,0,0), (0,1,0) -> (0,2,1), (0,0,1) -> (0,2,3); s -> s^2, u -> u | 300 s deep run, (5,2) | `d9D5_n3000_haar_c5cube_dic3.edges` (afec2757d72b73a6) |
| 3,024 | C7 : (C3 x ((C3 x C3) : C8)) = SmallGroup(1512,783) | `records/build_d9D5_n3024.py`: x^i z^c w1^a w2^b u^k, M = [[2,2],[1,2]] | (0,0,0,0,0) (5,0,1,0,0) (2,0,0,2,2) (0,2,0,1,4) (0,1,2,1,4) (0,2,1,2,3) (0,1,0,1,7) (5,2,1,2,0) (3,1,1,1,0) | x -> x^-1, z -> z, w1 -> w1^2, w2 -> w2, u -> w1^2 w2 u^3 | sweep pass, (3,3) | `d9D5_n3024_haar_c7_c3xc3sqc8.edges` (150a0027094cd3bc) |
| **3,036** | C69 : C22 = S3 x (C23 : C11) = SmallGroup(1518,2) | y x y^-1 = x^8 | (0,0) (66,11) (56,11) (28,13) (22,9) (13,15) (64,7) (25,14) (8,8) | x -> x^22, y -> y | 300 s deep run, (3,3) | `d9D5_n3036_haar_c69c22.edges` (05305fe907f35499) |

Metacyclic ones: x^i y^j written (i,j), <x, y | x^m = y^k = 1, y x y^-1 = x^r>, product (i,j)(a,b) = (i + r^j a, j + b);
`records/build_metacyclic_haar.py m k r "S"` builds them, `records/build_metacyclic_cayley.py` the Cayley form,
`records/find_beta_meta.py` finds beta. Other groups with solutions at the same orders: 1395_2, 1395_3, 1395_5
(2,790), 1407_4 = C469 : C3 (2,814), 1488_21 (2,976); search outputs in `logs/K9/`.

## Tools (src/)

| file | what it does | calibration |
|---|---|---|
| `export_sd.g` | GAP: SmallGroup(N,ID) as a multiplication table + inverses; `ALPHA 1` (identity) and `ALPHA 2` (each class of involutions of Aut(G)) with centralizer generators (split cosets, c = e); `EXT c` for every Aut(G)-class of pairs (beta, c), c <> e, beta(c) = c, beta^2 = conjugation by c, with the stabilizer (non-split cosets: needed when T has no involution, K even). | |
| `sdk.c` | valency K (env K): ALPHA records: S = e + (f-1) psi-fixed + m psi-2-orbits, f + 2m = K, f >= 1, f = K mod 2; EXT records (K even): S = {e, c^-1} + K/2 - 1 further 2-orbits. First free orbit (or fixed element when m = 0) up to the stabilizer. Fast rejection as in haar75 (move-to-front targets); every set with X X = G gets the full three-condition Haar check. Caps MAXEV, MAXEVF (types with f >= 4); `SAMPLE=1` draws random sets of each type instead. | K = 7 on SmallGroup(656,28): the same 9 sets as haar75 anti (the 1,312 record), all types 36 s (`logs/calib/K7_656_28.out`). K = 6 on SL(2,7) = SmallGroup(336,114): 38 sets, apsp VALID at D = 5 (672 vertices, below the table's 684) |
| `export_hat.g`, `brute.c`, `canon_cmp.py` | independent check: every inverse-closed T of size K in the coset of an index-2 subgroup of a group of order 2n, no normalisation, diameter by BFS; isomorphism classes (nauty-labelg) compared with sdk's | SL(2,7), K = 6: the 4 groups of order 672 containing it give 3,360 hits = 5 classes = sdk's 5 classes. C5 x (C13 : C4) = SmallGroup(260,2): sdk's 7 classes from non-split cosets (EXT) = the classes of the 18,720 brute hits on the two non-split groups 520_5, 520_6 (no involution in the coset); no brute class outside sdk's (`logs/calib/brute_vs_sdk.txt`) |
| `cover.py` | coverage table of a sweep log | |
| `run1.sh`, `sweep.sh` | drivers: one group (export + sdk, one line in `logs/K$K/sweep.txt`), a list in parallel | |
| `list_groups.g` | non-abelian SmallGroups of a range of orders with their numbers of involution classes and involutions | |
| `sdtabu.c` | tabu search inside the same family (same records and types as sdk) for types too large to enumerate: replace one fixed element or one 2-orbit, NB random candidates per step, tabu tenure, restarts; energy \|G \ X X\|; `DEEP=thr,secs` gives extra time to types that get within thr | K = 7 on 656_28 (3,2): 3 of the 1,312 sets in 0.4 s; K = 6 SL(2,7): sets in 0.1-1 s; K = 9 on C197 : C7 = SmallGroup(1379,1) (the group of our 2,758 record): valid 9-sets of types (3,3) and (5,2) in 7-40 s (apsp VALID at D = 5, INVALID at D = 4); K = 8 on AGL(1,7) x C21 = 882_40: a (4,2) set in 0.3 s, many types at 1 |
| `run_tabu.sh`, `sweep_tabu.sh` | drivers for sdtabu (one line per group in `logs/K$K/tabu.txt`) | |
| `haar_edges.py` | edge list of H(G,S) from an export table and S | |
| `stop_driver.sh` | stop a sweep driver (running groups finish) | |
| `meta_group.g`, `meta_group2.g`, `run_meta.sh`, `run_meta2.sh`, `sweep_meta.sh`, `sweep_meta2.sh` | metacyclic C_p : C_k (prime p, action of order d) and C_m : C_k (y x y^-1 = x^r) as permutation groups for export_sd.g, and their sdtabu drivers (`logs/K9/meta.txt`, `meta2.txt`) | C197 : C7 and C69 : C22 re-found |
| `deep_tabu.sh`, `deep_loop.py` | 300 s sdtabu runs on single (group, record, type) near misses above the record order in `logs/K9/RECORD_N` | gave 5 of the 9 steps |
| `sweep_tabu2.sh`, `sweep_tabu3.sh`, `prune.py` | second/third sdtabu stream; cut a list to orders above the record | |
| `cover_tabu.py`, `k6_bands.py` | coverage summaries (`logs/K9/coverage.md`, the K = 6 table below) | |
| `canon_eq.py`, `make_meta_record.sh`, `meta_coords2.g` | nauty isomorphism test of edge lists; record files for a metacyclic hit; coordinates x^i y^j of a solution | |

Check of every hit: research/lifts/coordinator_check/apsp.c (`src/apsp`), VALID at D = 5 and INVALID at D = 4, plus the
independent builders and checkers listed with each record.


## How the (9,5) graphs were found

GAP export (`src/export_sd.g`, no non-split records for odd K) and `src/sdtabu` over every involution class of Aut(G)
and the types (1,4), (3,3), (5,2) (2 s each, 25 s more for a type that gets within 10), then 300 s deep runs with two
seeds on every near miss (best <= 3, later <= 4) above the current record order (`src/deep_loop.py`). Group lists,
each cut to orders above the current record after every hit: SmallGroups of order 1380-1460 (no 1408, 1440, 1456,
1458) by number of involutions; metacyclic C_p : C_k (p >= 31 prime, y acting with order d >= 3, `logs/meta9_list.txt`,
built by `src/meta_group.g`) of order 1379-1800; odd-order groups of order 1461-1700 that are not of that metacyclic
form (`logs/wl9_odd_1461_1700.txt`); groups of order 1468-1560 with a cyclic or generalized quaternion Sylow
2-subgroup, center <= 30, not nilpotent (`logs/wl9_inv1_1468_1560.txt`). Per order: `logs/K9/coverage.md` (groups
run, smallest |G \ X X| reached, groups with solutions); one line per group in `logs/K9/tabu.txt`, `logs/K9/meta.txt`,
deep runs in `logs/K9/deep/`. Tabu is a heuristic: a group without a solution here may still have one.
Calibration: on C197 : C7 (our old 2,758 group) sdtabu finds valid self-dual 9-sets in 7-40 s. A short parameter test
(`logs/K9/tune/`, one seed, 240 s on C163 : C9) found a solution only with STALL = 2000 (restart after 2,000 steps
without improvement instead of 300), so the deep runs use STALL = 2000 from 23:55.
Where it stands (03:00 UTC): hits at 1395, 1407, 1464, 1467, 1485, 1488, 1500, 1512 (783 and 782), 1518; misses of 2 at
1491, 1505, 1515, 1539 (deep runs with two seeds did not close them); the metacyclic groups of order 1569-1635 stay at
10 or more. Groups run: 235 SmallGroups, 56 metacyclic with prime kernel, 24 metacyclic with composite kernel
(`logs/K9/meta2.txt`, from 02:25: C_m : C_k, m squarefree odd composite, an action of order >= 2 on every prime of m and
>= 3 on one, `logs/wl9_metac.txt`; calibrated on C69 : C22), 56 deep runs.
Not reached: the rest of the 1513-1560 Sylow-2-cyclic/quaternion list (`logs/wl9_inv1_r5*.txt`, about 120 groups) and of
the composite list (about 45 groups, orders 1554-1700).

## (6,5): no graph above 684

`sdk` K = 6 over every non-abelian group of order 343-450 (no 384), exhaustive except for types larger than the caps
(MAXEV 1e8; types with >= 4 psi-fixed elements 2e7 lexicographic for the first 53 groups, then 3e6, from 21:20 UTC
1e7 random samples instead of a cut). Coverage (searched / non-abelian groups, smallest |G \ X X| among sets that
passed 25 targets), `src/k6_bands.py`, per order `logs/K6/coverage.md`:

| orders (vertices) | inv <= 1 | inv 3-7 | inv 8-31 | inv > 31 |
|---|---:|---:|---:|---:|
| 343-360 (686-720) | 23 / 61 (best 4) | 76 / 93 (best 1) | 39 / 94 (best 5) | 34 / 146 (best 20) |
| 361-400 (722-800) | 82 / 82 (best 2) | 108 / 108 (best 4) | 35 / 88 (best 4) | 72 / 174 (best 16) |
| 401-450 (802-900) | 119 / 155 (best 8) | 303 / 718 (best 8) | 0 / 637 | 0 / 1127 |

Order 343-360 was run first as a check (an earlier exhaustive search found no degree-6 Haar graph there at all) and
then paused for orders above 360. Closest: SmallGroup(352,50) = C11 x (order-32 group), type (6,0): 1 (that type
fully enumerated, `logs/K6/deep/352_50_f46.out`); 372_1 = C31 : C12, (2,2): 2 (enumerated); 375_2, 375_6, 378_41,
378_48: 4. C13 x the same order-32 group (416_51), types (4,1) and (6,0) fully: best 30. Squad round sd5-r1 (8 other
families: order-4 self-duality, self-dual tabu, plain tabu, bi-coset |H| = 2 and 3, 2+2 lifts, order-3/5 symmetric
sets, formula-only metacyclic Cayley graphs): nothing above 684, best 2 (plain tabu on SL(2,5) x C3 at 720); see
`../squads/LOG.md`. A valid 672-vertex graph (SL(2,7)) was used for calibration only.

## (7,5): nothing above 1,312

- SmallGroup(660,16), the previous job's near miss, every type uncapped (`logs/K7/deep/660_16_all.out`): best 2.
- The 600 groups of order 657-672 the previous sweep had not reached (mostly order 672 with more than 31 involutions,
  `logs/wl7_a_657_672.txt`) ran at low priority from 23:00 (MAXEVF 3e5, oversized types sampled): 28 groups done,
  best 6, no solution (`logs/K7/sweep.txt`, `logs/K7/coverage.md`). Not reached: the rest of that list, 673-700
  with 8+ involutions, 701-800 with 3+ involutions, order 729 (lists `logs/wl7_*.txt`).

## (8,5): nothing above 2,048

Self-dual tabu works at 882 (AGL(1,7) x C21, the old Haar record group: a (4,2) set in 0.3 s, many types at 1), but a
metacyclic probe at 1025 (C41 : C25, `logs/K8/meta.txt`) reached only 4 in 13 minutes; 1025 is 16% above 882, so the
probe was stopped. Not searched further.

## Next steps

- (9,5): the rest of the lists above (resume with `src/sweep_tabu.sh` / `src/sweep_meta2.sh` on the remaining lines
  and `src/deep_loop.py` with RECORD_N = 1518); the near miss 1539 (2) with more seeds; groups of order 1519-1600 with
  more involutions; the same tabu at K = 10, 11 (cells (10,5), (11,5)), where the self-dual family may also beat the
  table.
- (6,5): orders 401-450 with 8+ involutions (1,764 groups) and order 384; the sweep shows no group above 360 closer
  than 2.
- (7,5): the list above; `src/run1.sh` now skips the non-split export for odd K.
