# deep-49 tools

Build: `gcc -O3 -march=native -o hx hx.c` (same for bicos.c, capacity.c, apsp.c, score48.c, farlist.c).

- `hx TABLE AUT LIMIT [D] [XFROM XTO] [OUT]`: exact search for Haar graphs H(G,S), |S| = 4, diameter <= D (default 9),
  reduced by Aut(G) (x over Aut-orbit representatives, y over Stab(x)-orbit representatives, z over all). Cost =
  #(G \ (SS^-1)^4) + #(G \ (S^-1S)^4); prints `MIN c` (exact if c <= LIMIT) or `MIN >LIMIT`. `HIT0 x y z` lines give
  S = {0, x, y, z}. The stderr line 1 gives the number of x representatives, for splitting runs with XFROM XTO.
- `export_group.g` (GAP): `ExportGroup(G, file)`; `build_tab.py file prefix` writes prefix.tab / prefix.aut for hx.
  Run GAP as `gap -q --quitonbreak FILE.g < /dev/null` (an error otherwise waits forever in a break loop).
- `mkmeta.py m k r prefix`: table and automorphism generators of Z_m x|_r Z_k (element a + m*j).
- `haar_edges.py TABLE OUT s1 s2 s3 s4`: edge list of H(G,S) (A = g, B = N + g, edge g ~ N + g*s).
- `apsp EDGES d D`: the coordinator's independent all-pairs check (copy of research/lifts/coordinator_check/apsp.c).
- `score48 EDGES 4 9`: far-pair count of any edge list (from handsoff-49).
- `bicos p k h r`: bi-coset graphs of the Frobenius group Z_p x| Z_k with point stabiliser of order h (2 or 3).
- `capacity DMAX`: upper bound on |(SS^-1)^4| for metacyclic groups whose kernel action has order d.
- `fibre.py`, `fib2.py`, `meta.py`: fibre analysis of Haar sets in Z_p x| Z_k.
