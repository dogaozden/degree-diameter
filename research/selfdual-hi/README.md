# selfdual-hi: self-dual (bipartite Cayley) Haar graphs at diameters 7 and 8

Job "selfdual-hi" (Opus cloud session, Oct 31 2026). Method of `../selfdual-d5/README.md` and `../d75-raise/README.md`,
taken from D = 5 to D = 7 and 8 with formula-only groups (no GAP).

## The test at diameter D

H(G,S): vertices (g,A), (g,B); (g,A) ~ (s g, B). X = S^-1 S. If psi(S) = S for psi(x) = u0 beta(x)^-1 (beta in
Aut(G), u0 in G), then (g,A) -> (u0 beta(g), B), (h,B) -> (beta(h), A) is a side-swapping automorphism, and the graph
is vertex-transitive. So the diameter is <= D iff the ball of radius D-1 around (e,A) covers the side of parity D-1:

- D = 2k+1 (D = 7): X^k = G. Side B (Y^k = G) follows from the swap; a plain Haar graph needs both.
- D = 2k (D = 8): S X^(k-1) = G. This single condition already suffices for every Haar graph (X^k and Y^k follow
  from it), so at even D self-duality does not remove a condition; it makes S X^(k-1) psi-invariant, so the
  uncovered elements come in psi-orbits.

psi need not be an involution: S is a union of <psi>-orbits; psi has even order 2j and psi^2 is an order-j
automorphism-like map, so j > 1 combines self-duality with orbit-symmetric S (research/structured/STRUCTURE.md).

## Tools (src/)

| file | what it does | calibration |
|---|---|---|
| `sdhi.c` | groups Q1 x Q2 from formulas (SL/PSL/PGL(2,q), q = p^e <= 64; metacyclic C_m : C_k; Z_n); psi options per factor (involutions modulo inner automorphisms; ORDS for higher orders); types = partitions of K into orbit lengths; tabu inside the family (energy = uncovered vertices of the side of parity D-1 within distance D-1 of (e,A)), ENUM=1 exhaustive enumeration with fast rejection and normalisation by the automorphisms commuting with psi; every hit gets a full BFS from (e,A) and (e,B). Header comment has every option. | D = 5, K = 7 on C41 : C16 (the 1,312 group): the tabu finds valid self-dual sets in 1.8 s; ENUM gives the same 202,625,280 sets / 320 solutions as the first version. D = 7, K = 5: PGL(2,5) x Z11 (2,640 vertices) and SL(2,5) x Z10 have self-dual solutions; builder and apsp agree. |
| `build_sdhi.py` | independent builder from the printed formula (own field, matrix and metacyclic arithmetic), same vertex numbering as sdhi's EDGES; BFS from (e,A) and (e,B); compares edge lists | identical edge lists on the probe solutions |
| `meta_list.py` | metacyclic groups of an order range, one r per cyclic subgroup <r>, with involution counts | |
| `sweep.py` | parallel driver: one sdhi run per group, `summary.txt`, `SOLS.txt` | |

Checks of every hit: research/lifts/coordinator_check/apsp.c (`src/apsp`), VALID at D and INVALID at D-1.

## Status (running log)

- (5,7), K = 5: the record S (PGL(2,5) x Z13, 3,120) is not self-dual for any psi of that group (SDTEST: no
  b S a^-1 is psi-invariant). Exhaustive enumeration of the self-dual family of PGL(2,5) x Z13: no solution in the
  types finished so far (best 2 by tabu in type 1+1+1+1+1). Self-dual solutions exist at 2,640 (PGL(2,5) x Z11) and
  2,400 (SL(2,5) x Z10): probe of orders 1,150-1,560 running to locate the frontier. Metacyclic groups at order
  1,564 are far off (180-300 uncovered).
