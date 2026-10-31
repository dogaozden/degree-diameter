# selfdual-d5c: self-dual (bipartite Cayley) Haar search at (12..16, 5)

Job "selfdual-d5c" (Opus cloud session, Oct 31 2026, from 05:50 UTC). Goal: beat (12,5) 9,840, (13,5) 11,700,
(14,5) 17,568, (15,5) 20,736, (16,5) 33,792 (our values, from generalized-quadrangle constructions) with self-dual
Haar graphs, using only groups given by a formula. The sibling job selfdual-d5b does K = 9, 10, 11.
Method: `../selfdual-d5/README.md` and `../d75-raise/README.md`.

**Status: no record.** Valid self-dual graphs below the targets (calibration, below); the searches above the targets
are summarized under "Results".

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
