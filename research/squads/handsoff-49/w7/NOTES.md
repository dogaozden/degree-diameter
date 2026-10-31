# w7 NOTES: bi-coset graphs (Haar graphs over cosets of a small subgroup H)

Start: 2026-10-31 21:42 UTC. Deadline: 23:42 UTC (2 hours). Last update: 22:00 UTC.

## Best so far (no valid graph yet; C = cost, 0 = diameter <= 9)
- BEST n >= 4972: **PSL(2,25), H = <x> of order 3 (non-central), n = 5200, C = 30 (exact minimum of this (G,H) over
  all S: composition {1,3} exhaustive, 6912 sets; {1,1,1,1} gives 10368).** Diameter 10, far pairs 39000.
  Edge list: best_psl25_h3_C30_n5200.edges (apsp: diameter 10, score48 far = 39000 = M*C/2 exactly).
  Rebuild: `python3 build_tabs.py "PSL2_5^2"`, then `./bicos tabs/PSL2_5^2.bin exh 6 1,3 100000 OUT.edges`
  (element 6 is an order-3 element; `bicos TABLE classes` lists the class reps).
- Next best: PSL(2,23), H involution, n = 6072: C = 90 (SA {2,2}); exh {1,1,2} gives 148.
- PSL(3,3), H involution, n = 5616: exh {1,1,2} C = 120 (diameter 10, verified).
- PSL(2,27), H order 3, n = 6552: exh {1,3} C = 176.  PSL(2,25), H involution, n = 7800: C = 312 (SA), 420 (exh {1,1,2}).
- S7 (n=5040), transposition H: SA C = 992.  Metacyclic groups with a non-central involution: 11 tried, all DISCONNECTED
  (C 5000-9000): <S^-1 S, H> is a proper subgroup, so the metacyclic family does not help here.

## Construction (derived, implemented in bicos.c)
G group (order N), H <= G of order h. Both sides = right cosets Hg (M = N/h each).
S = HSH is a union of double cosets with sum of k_D = 4 (k_D = |HsH|/h = number of right cosets in HsH).
Edge: Hg (side A) ~ Hk (side B) iff k g^-1 in S. Simple, 4-regular, bipartite, n = 2N/h.
G acts on the right and is transitive on each side, so two BFS (from A-root and B-root) give the diameter.
Cost C = aFar + bFarB + 2 bFarA (far = distance > 9 or unreachable); far pairs = M*C/2 (checked on 3 graphs).
Connected iff <S^-1 S, H> = G (walks from the root only reach H<S^-1 S>).

## Key facts
- Central H: the bi-coset graph is exactly the Haar graph of G/H (n = N). Only NON-central H is new.
  Central-involution metacyclic example reproduces the Haar floor (SA C = 4 at n = 4992).
- For h = 2: k-compositions {1,1,1,1} put S in C(t) and are disconnected (C ~ 10^4); only {1,1,2} and {2,2} matter.
- For h = 3: k in {1,3}; compositions {1,3} (one normaliser coset + one size-9 double coset) and {1,1,1,1}.
- Perfect groups (abelianization trivial) avoid the connectivity obstruction; PSL(2,q) is the good family here.

## Tools in w7/
- bicos.c / bicos: classes | info | exh | sa | elems. Table = groups.py format (int32 N, uint16 N*N).
  Fixed: exh now writes the edge list of the BEST S. An earlier version wrote the LAST S evaluated, so every exh edge file
  and the 'disconnected' PSL(3,3) {2,2} file from before the fix are invalid (their C values were right; the files were not).
- pgen.py (perm groups, PSL/PGL(2,q) incl. q = p^k), build_tabs.py, build_perm_prod.py (perm products, low memory).
- batch.py: screens all non-central involution (h=2) / order-3 (h=3) classes of a table; run_all.sh, run_h3.sh drivers.
- deep.sh: multi-seed SA. enum_meta.py / meta_noncentral_inv.txt: metacyclic lists.

## Results table (best C per (G,H); exh = exact over all S of that composition; n = 2N/h)
| group | H | n | best C | comp / mode |
|---|---|---|---|---|
| PSL(2,25) | order 3 | 5200 | **30** | {1,3} exh (6912 S), exact |
| PSL(3,3) | involution | 5616 | 120 | {1,1,2} exh |
| PSL(2,23) | involution | 6072 | 90 | {2,2} SA 20 s (exh {1,1,2}: 148) |
| PGL(2,19) | involution | 6840 | 148 | {2,2} SA 20 s (other classes 218-266) |
| PSL(2,27) | order 3 | 6552 | 176 | {1,3} exh |
| PSL(2,25) | involution | 7800 | 312 | {2,2} SA (exh {1,1,2}: 420) |
| A5 x PSL(2,7) | order 3 | 6720 | 370 | {1,3} exh (other order-3 class 12320) |
| PSL(2,8) x Z15 | order 3 | 5040 | 160 | {1,3} exh |
| PSigmaL(2,16) (= PSL(2,16):2, Frobenius) | order 3 | 5440 | 164 | {1,3} exh (18000 S) |
| S7 | transposition | 5040 | 992 | {2,2} SA 20 s |
| metacyclic, non-central involution (11 groups) | involution | ~5000 | 5000-9000 | disconnected |
| metacyclic, order 3 (in progress, results_meta_h3.tsv) | order 3 | 5040-5100 | ~10^4 so far | disconnected |

Verified: PSL(2,25) order-3 graph (best_psl25_h3_C30_n5200.edges): apsp diameter 10, score48 far pairs 39000 = M*C/2.
PSL(3,3) and PSL(2,23) graphs also have far pairs = M*C/2 (checked).
Abandoned: PSL(2,8)xZ10 and similar small-cyclic products (not run), PSU(3,3) (not built: needs GF(9) unitary group).

## Status / next
- No valid (cost 0) graph with n > 4970 found. Best: n = 5200, cost 30 (PSL(2,25), H of order 3), exhaustively optimal
  for that (G, H). Stored in w7/best_psl25_h3_C30_n5200.edges; scoreboard line appended.
- Next idea if continued: other perfect groups of order 7458..8000 with H of order 3 (none known besides PSL(2,25));
  search over automorphism-invariant S inside PSL(2,25) with H of order 3 (no gain: already exhaustive).
