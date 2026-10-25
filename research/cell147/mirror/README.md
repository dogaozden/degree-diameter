# Mirrored surgery: more freed points than a partial ovoid allows (job cell-14-7, third session, 2026-10-25)

## The base construction (cell-13-7 session, research/d13D7/REPORT.md)

(2r+1) copies of the split Cayley hexagon H(q), levels Z_{2r+1}, matchings (p, i) ~ (sigma(p), i+k), k = 1..r, for one
bijection sigma: points -> lines. Surgery at a point set R deletes every matching edge at (x, i) and (sigma(x), i) for
x in R and adds r line-side hubs per point (joined to (x, i) for all i) and r point-side hubs (joined to (sigma(x), i)):
+2r vertices per point. (14,7) = r = 2, q = 11: n = 1,771,560 + 4|R|. Master had |R| = 756 (1,774,584).

## The relaxed theorem

The proof in research/d13D7/REPORT.md §2 only uses:
- (N1) R is non-collinear (no two points of R on a hexagon line);
- (N2) sigma(R) is non-concurrent (no two of its lines meet);
- (L) sigma is a local duality at every x in R: sigma(Gamma_2(x)) = Gamma_2(sigma(x)), where Gamma_2(x) are the 132
  points collinear with x and Gamma_2(l) the 132 lines meeting l;
- (H) same-side hubs within distance 6 in the hub graph.

Case by case (levels i, i+k with the k-th matching; a point a = x in R, b at level i+k):
- b a point: (x,i) - (p', i) - (sigma(p'), i+k) - ... - b with p' in Gamma_2(x). p' is not in R by (N1), so its
  matching edge exists; by (L) the lines sigma(p') are all of Gamma_2(sigma(x)), and every point is within distance 3 of
  one of them (covering lemma). Length <= 2 + 1 + 3 = 6.
- b a line: (x,i) - hub - (x, i+k) - ... - b, length <= 2 + 5 = 7.
- b = sigma(x') a damaged line, a a line: (sigma(x'), i+k) - (l', i+k) - (sigma^-1(l'), i) - ... - a with l' in
  Gamma_2(sigma(x')); l' is not in sigma(R) by (N2), and the points sigma^-1(l') are all of Gamma_2(x') by (L), which
  cover every line within distance 3 (dual covering lemma). Length <= 6.
- a a line, b a point: a line m through b with m not in sigma(R) exists by (N2); length <= 5 + 1 + 1 = 7.
- everything else as in the base proof (undamaged matching edges, hubs through one copy: 2 + 5).

Pairwise opposite R is NOT needed. But (L) at two points x, y of R at distance 4 (midpoint m, the unique point
collinear with both) forces sigma(m) to be in Gamma_2(sigma(x)) and Gamma_2(sigma(y)), so sigma(x), sigma(y) are at
distance 4 with connecting line sigma(m); and conversely opposite points must go to opposite lines. So **the distance-4
graph of R must be mirrored exactly by sigma(R)** (midpoints to connecting lines; if a point is collinear with three or
more points of R, the lines must form the same "dual star"). The cell-13-7 session tried large structured R (stars of 11
points) and found the line side incoherent for q = 11 (no duality). Here we keep stars of size <= 2.

## Adding points to the 756 set

R756 (pairwise opposite; the W(E7) orbit, research/cell147/ovoid/) plus extra points X:
- X pairwise opposite, non-collinear with R756 (76,608 candidates; each is at distance 4 from 60-78 points of R756);
- lines L_x (one per x) pairwise opposite, not in the Hermitian spread S (the 1,332 lines in x0 + x4 = 0);
- sigma(R756) = f(R756) with f: R756 -> S a bijection onto 756 spread lines such that f(r) is at distance 4 from L_x
  exactly when r is at distance 4 from x, and opposite otherwise; spread lines concurrent with some L_x are not used.
Since R756 and S are pairwise opposite, and X and L pairwise opposite, every star has size <= 2 automatically. f exists
iff for every "type" t (the set of x at distance 4) the number of R756 points of type t is at most the number of usable
spread lines of type t. A random line not in S meets exactly 1 spread line, is at distance 4 from 121 and opposite to
1,210, so one extra point is always possible. Points of R756 whose type has too few spread lines can also be dropped
(each costs one point).

sigma: R' -> f(R'), each midpoint m(x, r) -> the connecting line of (L_x, f(r)), the rest of Gamma_2(a) onto the rest of
Gamma_2(sigma(a)) for every a in R', the remaining points onto the remaining lines. multi.c (DUALFILE mode) re-checks
(N1), (N2) and (L) before building.

## Results

| freed points | n at (14,7) | check |
|---|---|---|
| 756 (master) | 1,774,584 | coordinator |
| 757 (one extra point) | **1,774,588** | apsp_orb VALID (checks/d14D7_hex11_mirror757_n1774588.check.txt) |
| 765 (greedy, k = 9) | 1,774,620 | multi.c spot check (BFS from all damaged vertices and hubs) |
| 767 (annealing, k = 11) | **1,774,628** | apsp_orb VALID (checks/d14D7_hex11_mirror767_n1774628.check.txt) |
| 768 (squad r6 c3, k = 12) | **1,774,632** | apsp_orb VALID (checks/d14D7_hex11_mirror768_n1774632.check.txt) |

The same sigma and R' work for every r: (13,7) n = 1,062,936 + 2|R'|, (15,7) n = 2,480,184 + 6|R'|.

## Other cells (same construction, other q)

mirror_sa5.py / mirror_build2.py take the hexagon, base set and spread as arguments (any odd q); mirror_sa6.py /
mirror_build3.py compute point distances by BFS in the incidence graph instead of the bilinear form, which is needed in
characteristic 2 (q = 8). Base sets and spreads are the cell-13-7 session's (research/d13D7/q57, q8, q13).

| cell | q, copies | base set | spread | extra points F | n | master | check |
|---|---|---|---|---|---|---|---|
| (7,7) | 5, 3 | R72 | 126 lines | 9 | **23,598** | 23,580 | apsp_mt all-pairs VALID |
| (9,7) | 7, 3 | R288 (W(E7) orbit) | 344 lines | 7 | **118,238** | 118,224 | apsp_mt all-pairs VALID |
| (10,7) | 8, 3 | R217 | 513 lines | 12 | **225,152** | 225,128 | apsp_mt all-pairs VALID |
| (13,7) | 11, 3 | R756 | 1,332 lines | 12 (same sigma as (14,7)) | **1,064,472** | 1,064,448 | apsp_orb VALID |
| (15,7) | 11, 7 | R756 | 1,332 lines | 12 (same sigma) | 2,484,792 | 2,484,720 | see checks/ |
| (16,7) | 13, 5 | R792 | 2,198 lines | 21 | 4,025,592 | 4,025,508 | multi.c checks + spot check; full apsp_orb in checks/ when done |

At q = 13 there is more room than at q = 11: a random line is at distance 4 from 169 spread lines, the spread has 1,406
spare lines, and some extra points are at distance 4 from only 24, 40, 46 or 48 base points (257,298 candidates; at
q = 11 the minimum is 60). Restricting the candidates to c <= 40 or 48 (--cmax) the annealer reaches F = 21 in a few
minutes; warm restarts did not improve it.

## Files

- hexmod.py: H(q) from hexgen.c output (research/d13D7/hexgen.c), distances.
- mirror1.py: one extra point. mirrork.py: greedy k. mirror_sa2.py: annealing (cost = type deficit), mirror_sa3.py:
  annealing on k - deficit. inspect_state.py: type statistics of a state.
- mirror_sa5.py / mirror_build2.py: the same for any q (--hex, --rfile, --sfile; builder args HEXFILE SPREAD.npy).
- mirror_build.py STATE.npz SEED OUT: re-checks a configuration (non-collinear, pairwise opposite where needed, exact
  mirroring of every distance-4 pair) and writes sigma.txt and R.txt for multi.c.
- configs/: the configurations (X, L, dropped points) of the graphs above.
