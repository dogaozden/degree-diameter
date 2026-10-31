# selfdual-d5c: self-dual (bipartite Cayley) Haar search at (12..16, 5)

Job "selfdual-d5c" (Opus cloud session, Oct 31 2026, from 05:50 UTC). Goal: beat (12,5) 9,840, (13,5) 11,700,
(14,5) 17,568, (15,5) 20,736, (16,5) 33,792 (our values, from generalized-quadrangle constructions) with self-dual
Haar graphs, using only groups given by a formula. The sibling job selfdual-d5b does K = 9, 10, 11.
Method: `../selfdual-d5/README.md` and `../d75-raise/README.md`.

**Status: no record, and none of the five targets is within reach of this family.** The tool works (it rebuilds the
(9,5) 3,036 graph bit for bit and finds valid self-dual graphs at K = 12 up to 6,984 vertices and at K = 13 up to
10,040 vertices, all apsp VALID at D = 5, the ones also checked at D = 4 INVALID there), but above the targets the
best |G \ X X| is 18 at (13,5) (C245 : C24, order 5,880, after a 600 s deep run; 0 is needed), 57 at (12,5), 104 at
(14,5), 70 at (15,5), 440 at (16,5). At K = 13 the frontier of this family is near order 5,000-5,250 (solved at
5,020, best 5 at 5,240, 10 at 5,420, 12 at 5,490); (13,5) needs 5,851. The last section explains the gap with the
size law: every self-dual solution or record so far sits at mu = N e^(-W/N) <= 70, the targets need 122-682.

## Method and conventions

Self-dual family: G^ = G u G t (t x t^-1 = beta(x), t^2 = c), T in G t inverse-closed with |T| = K and t in T,
S = T t^-1 (so e in S). Then psi(S) = S for psi(x) = c^-1 beta(x)^-1, the Haar graph H(G,S) equals Cay(G^, T), and
it has diameter <= 5 iff X X = G (X = S^-1 S); every hit also gets the full three-condition Haar check.
Haar graph H(G,S): vertices (g,A), (g,B), g in G; (g,A) ~ (s g, B) for s in S; vertex numbers (g,A) = e(g),
(g,B) = |G| + e(g), with the element index e below.

Groups (all G = H x C_n3, element (h, l), index e = h*n3 + l; `src/fsd.c` and `src/build_fsd_haar.py` implement
them independently and give the same edge lists):
- `meta m k r n3`: H = C_m : C_k = <x, y | x^m = y^k = 1, y x y^-1 = x^r>, x^i y^j = (i,j), h = i*k + j,
  (i,j)(a,b) = (i + r^j a, j + b). Same convention as `../selfdual-d5/records/build_metacyclic_haar.py`; fsd rebuilds
  the (9,5) 3,036 edge list bit for bit (sha256 05305fe9...).
- `aff p f k n3`: H = F_q : C_k, q = p^f, F_q = F_p[x]/(x^f + poly[f-1] x^(f-1) + ... + poly[0]) with the first
  primitive polynomial in the order fsd searches (printed on its GROUP line; the builder takes it as an argument),
  omega = x, y acts by multiplication by omega^((q-1)/k); v = sum c_i x^i is coded as sum c_i p^i; (v,j) has
  h = v*k + j, (v,j)(w,b) = (v + omega^(e j) w, j + b), e = (q-1)/k.
- `psl p n3`, `sl p n3`: PSL(2,p) (matrix up to sign, the representative whose first nonzero entry of (a,b) is in
  1..(p-1)/2) and SL(2,p); h = 0 is the identity, then the matrices in lexicographic order of (a,b,c,d), written
  a.b.c.d.
Records (fsd generates them, no GAP): for every automorphism beta in a formula family (meta: x -> x^a,
y -> x^b y^c z^d, z -> z^w; aff: x -> (a,0), y -> y^c z^d, z -> z^w; psl/sl: conjugation by 1 or diag(1, nonsquare),
z -> z^w) with beta^2 inner, coset representatives mod Inn(G), merged under outer generators; every c0 with
beta^2 = conj(c0), beta(c0) = c0; then every G^-class of elements t' of the coset G t0 (orbits of
g -> h g beta(h)^-1 and g -> beta(g)). t' an involution: ALPHA record, types (f, m) = (psi-fixed elements of S,
psi-pairs), f + 2m = K; t' not an involution: EXT record (K even), S = {e, c'^-1} + K/2 - 1 pairs. EXT records with t'
central in G^ are skipped (on C37 : C81 at K = 12 they were the only EXT records that failed).
Search: tabu as `../selfdual-d5/src/sdtabu.c` with the FAST energy of sdtabu2 (d5b branch), STALL 2000.

## Tools (src/)

| file | what it does |
|---|---|
| `fsd.c` | groups by formula, records, tabu (env K, SECS, TYPES, REC, SEED, STOPFIRST, SHUFFLE, TBUDGET, DEEP, EDGES, CHECK, RECS, BENCH); `SIGMA=q` exhaustive search over S invariant under psi and an automorphism of order q |
| `build_fsd_haar.py` | independent builder from the formula (own group code), edge list + BFS eccentricities |
| `meta_list.py`, `all_list.py` | metacyclic groups of an order range (one r per subgroup <r>); all formula groups (meta, meta x C_n3, aff, psl, sl) |
| `run1.sh`, `sweep.sh`, `deep_pick.py`, `summ.sh`, `killfsd.sh`, `killsweep.sh` | drivers: one group (`logs/K$K/runs.txt`, `logs/K$K/out/`), a list over W workers, deep-run candidates, summaries, stop |

Checks: research/lifts/coordinator_check/apsp_mt.c (`src/apsp_mt`), VALID at D = 5 and INVALID at D = 4.

## Calibration (valid graphs below the targets; not records)

| K | group | order | vertices | found | check |
|---:|---|---:|---:|---|---|
| 9 | C197 : C7 (meta 197 7 36 1) | 1,379 | 2,758 | types (3,3), (5,2) in 8-13 s | as sdtabu |
| 9 | PSL(2,13) | 1,092 | 2,184 | 0.1-0.9 s per type | apsp VALID / INVALID at D = 4, builders agree |
| 9 | F_49 : C24 (aff 7 2 24 1, poly 3,1) | 1,176 | 2,352 | 0.3 s | apsp VALID, builders agree |
| 12 | C37 : C81 (meta 37 81 7 1) | 2,997 | 5,994 | 188 of 196 EXT records at once | apsp VALID |
| 12 | C97 : C36 (meta 97 36 6 1) | 3,492 | 6,984 | EXT record 91, after 5 min | apsp VALID / INVALID at D = 4, builders agree |
| 13 | C41 : C110 (meta 41 110 4 1) | 4,510 | 9,020 | type (1,6), 22 s | apsp VALID |
| 13 | C251 : C20 (meta 251 20 32 1) | 5,020 | 10,040 | type (3,5), 83 s | apsp VALID |

The two largest (6,984 and 10,040 vertices) are saved with edge lists, sha256 and a rebuild script in `records/`.
The K = 12 sets: C97 : C36, S = (0,0) (0,15) (53,10) (86,5) (14,2) (68,13) (53,32) (89,19) (26,15) (58,0) (31,16)
(65,35). The K = 13 sets: C41 : C110, S = (0,0) (21,104) (39,6) (9,92) (39,18) (23,8) (40,102) (12,37) (30,73) (9,93)
(20,17) (14,69) (15,41); C251 : C20, S = (0,0) (79,10) (4,10) (5,19) (160,11) (68,12) (154,8) (44,13) (124,17) (34,1)
(205,9) (29,7) (237,3).

## Ladder at K = 12 (best |G \ X X|; types f = 2 and EXT, 30 s per record and type, shuffled records)

| order | group | best | note |
|---:|---|---:|---|
| 3,420 | PSL(2,19) | 4 | 4 records |
| 3,492 | C97 : C36 | **0** | solved |
| 3,996 | C37 : C108 | 4 | 24 records |
| 4,520 | C113 : C40 | 33 | 21 types |
| 4,944 | C103 : C48 | 57 | 21 types (above the 4,921 needed) |

So at K = 12 the frontier of this family is near 3,500-4,000; (12,5) needs 4,921.

## Results above the targets (all: no valid graph)

Energy = |G \ X X| (0 = valid), lowest over the records and types run.

- (13,5), order >= 5,851 (the closest target): ladder (60 s per record and type): C61 : C96 (5,856) 20, C163 : C36
  (5,868) 22. Screen (`src/all_list.py 5851 5950`, filtered to k >= 10, m >= 13: `logs/wl13_c.txt`; types f = 1, 3,
  8 s per record and type, 240 s per group, one line per group in `logs/K13/runs.txt`, tag `_scr`; summary
  `python3 src/screen_summary.py 13 logs/wl13_c.txt`): all 143 metacyclic C_m : C_k, best 20 (C89 : C66, r = 2), then
  22 (C267 : C22 r = 2, C245 : C24 r = 68), and 7 more at 24-25; the 3 affine groups F_49 : C12 x C10, F_49 : C24 x C5,
  F_169 : C7 x C5: 27-36; PSL(2,11) x C9: 35; every 6th metacyclic x C_n3 (29): best 28. Groups with k <= 5 (screened
  before the filter) are far off (C1951 : C3 246, C1465 : C4 399). Deep runs (600 s on the best record and type of
  the 4 best groups, `src/deep.sh`): C89 : C66 23, C245 : C24 18, C267 : C22 24, C123 : C48 21.
  Frontier at K = 13 (same ladder settings): C251 : C20 (5,020) solved, C131 : C40 (5,240) 5, C271 : C20 (5,420) 10,
  C61 : C90 (5,490) 12.
- Squad round sd5c-r1 (`../squads/LOG.md`): eight other families and search methods at (13,5): non-split metacyclic
  50, F_p^2 : C_k with a diagonal action 35, metacyclic groups with even m or a large unmoved factor 36, Heis(3) x
  metacyclic 42, products of two metacyclic groups 44; clause-weighted tabu, annealing / late acceptance and targeted
  moves no better than the plain tabu (targeted moves worse). None beats plain metacyclic C_p : C_k.
- (12,5), order >= 4,921: C103 : C48 (4,944) 57 after 21 types; at 4,520 already 33.
- (14,5), order >= 8,785: C163 : C54 (8,802), 81 records, 20 types at 60 s: 104.
- (15,5), order >= 10,369: C433 : C24 (10,392), 9 types at 60 s: 70.
- (16,5), order >= 16,897: C353 : C48 (16,944), 400 records (capped), 20 types at 60 s: 440.
- sigma-invariant self-dual sets (`SIGMA=q`, S a union of <psi, sigma>-orbits, exhaustive): on C37 : C81 at K = 12,
  where plain self-dual sets solve at once, q = 3 gave best 182 (360,126 sets, all) and q = 2 best 34 (3e6 sets,
  capped). Extra symmetry costs more than the conditions it saves.

## Why the targets are out of reach for this family

A self-dual Haar graph has diameter <= 5 iff the W = 1 + K(K-1) + K(K-1)^3 non-backtracking words of length <= 4 in
X X cover G. If they were random, the expected number of misses would be mu = N e^(-W/N) (N = |G|; the size law of
`../frontier/SIZE_LAW.md`). Every solved point and record of the self-dual searches sits at mu <= 70:

| point | K | N | W/N | mu |
|---|---:|---:|---:|---:|
| (7,5) record, d75-raise | 7 | 656 | 2.37 | 61 |
| (9,5) record, selfdual-d5 | 9 | 1,518 | 3.08 | 70 |
| (10,5) d5b best | 10 | 2,054 | 3.59 | 57 |
| solved here, C97 : C36 | 12 | 3,492 | 4.61 | 35 |
| best 4 here, C37 : C108 | 12 | 3,996 | 4.03 | 71 |
| solved here, C251 : C20 | 13 | 5,020 | 4.51 | 55 |
| best 12 here, C61 : C90 | 13 | 5,490 | 4.12 | 89 |
| (12,5) target | 12 | 4,921 | 3.27 | 187 |
| (13,5) target | 13 | 5,851 | 3.87 | 122 |
| (14,5) target | 14 | 8,785 | 3.52 | 260 |
| (15,5) target | 15 | 10,369 | 3.99 | 192 |
| (16,5) target | 16 | 16,897 | 3.21 | 682 |

The targets need mu 2 to 10 times past that wall. At mu = 65 the predicted frontier is N = 3,927 (K = 12), 5,169 (13),
6,679 (14), 8,491 (15), 10,640 (16), against 4,921, 5,851, 8,785, 10,369, 16,897 needed. The GQ lifts that set the
targets (`../d10D7/DM_D5.md`: 6 (q+1)(q^2+1) vertices per side at degree q+3) are structured, not random-like, and a
Haar graph (a lift of the 2-vertex dipole) does not reproduce that structure.

## Not done, and next steps

- Not screened at (13,5): 145 of the 174 groups (C_m : C_k) x C_n3 of order 5,851-5,950 (the sampled 29 gave best 28,
  worse than the plain metacyclic groups), groups with k < 10 or m < 13 at those orders (the few screened were far
  off), and orders 5,951-6,300 (`logs/meta13_5851_6300.txt`; larger orders are harder). Resume with
  `K=13 TYPES=1,3 SECS=8 STOPFIRST=1 MAXSOL=1 TBUDGET=240 TAG=scr src/sweep.sh LIST W I` (done groups are skipped).
- The numbers say the self-dual Haar family stops about 10-60 % short of every target here, and neither the eight
  squad directions nor deep runs moved the plateau (18-25 at (13,5)). Beating the GQ lifts at these valencies needs
  a construction whose words are not random-like, for example lifts of a structured base graph, as the targets are.
- A self-dual K = 13 graph on 10,100-10,500 vertices (order 5,050-5,250) is probably within reach (5,240 got to 5),
  but it would not be a record.
