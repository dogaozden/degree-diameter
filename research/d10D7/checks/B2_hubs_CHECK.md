# The B2 hub construction: (10,7) 224,828, (9,7) 117,760, (7,7) 23,500 (all apsp VALID)

cell-10-7 job (Opus), 2026-10-24. Base: X(M) over the split Cayley hexagon H(q) (exp2 construction,
research/squads/exp2/hexd7/README.md: 3 levels, one extra edge (p,i) ~ (M(p), i+1) per point, diameter 7 for any
bijection M). Hubs: freeing a pair (p, l = M(p)) deletes the 3 extra edges of p and adds z ~ (p,0),(p,1),(p,2) and
z' ~ (l,0),(l,1),(l,2), +2 vertices; it is valid iff (p,0) reaches every point of level 1 and (l,0) every line of
level -1 within 6.

**B2 condition (new).** If M maps the q(q+1) points at distance 2 from p onto the q(q+1) lines at distance 2 from l,
then (p,0) -> (L,0) -> (u,0) -> (M(u),1) followed by <= 3 hexagon steps reaches EVERY point of level 1, because every
point lies within distance 3 of some line at distance 2 from l (if d(x,l) = 5 take the second line of the geodesic,
if d(x,l) <= 3 a line through x or through its foot meeting l). Dually (l,0) -> (y,0) -> (L,0) -> (M^-1(L),-1) and
<= 3 steps reach every line of level -1. No other condition on M, and p, l need not be incident. Freed points must
not lie at distance 2 from each other (their own extra edges are gone), and for the B2 sets of different pairs to
be disjoint the freed points are taken pairwise opposite, and the freed lines too. Same-side hubs are joined by a
random bipartite hub graph (degree <= q-1); hubs reach everything in 7.

Construction (`d7hex b2 HEXBIN Kmax seed OUT.sol hubdeg restarts`): greedy maximal sets of pairwise opposite points and
lines (best of `restarts` runs), paired at random, M(p_k) = l_k, a random bijection B2(p_k) -> B2(l_k) for each k,
the rest of M random, hub graph = union of hubdeg random perfect matchings. It reports the exact freed-source cost
(BFS from every freed point and line), which is 0 in all three cases.

| cell | table | previous best | B2 graph | K | file |
|---|---|---|---|---|---|
| (10,7) | 224,694 | 224,718 (ours, this session) | **224,828** | 67 | research/frontier/sols/d10D7_hex8_B2K67_n224828.sol |
| (9,7) | 117,648 | 117,690 (exp2-squad) | **117,760** | 56 | research/frontier/sols/d9D7_hex7_B2K56_n117760.sol |
| (7,7) | 23,436 | 23,488 (exp2-squad) | **23,500** | 32 | research/frontier/sols/d7D7_hex5_B2K32_n23500.sol |

Commands: `./d7hex b2 hex/hex_q8.bin 1000 1 b2_q8_s1.sol 6 40`, `./d7hex b2 hex/hex_q7.bin 1000 1 b2_q7_s1.sol 5 40`,
`./d7hex b2 hex/hex_q5.bin 1000 2 b2_q5.sol 4 20` (hex/hex_q*.bin from hexgen2.c).

Rebuild and check (from research/d10D7): `./d7hex edges hex/hex_qQ.bin SOL g.edges && ./apsp g.edges Δ 7`.

apsp outputs (all pairs, no symmetry assumed), 2026-10-24 23:3x UTC:
- (10,7): n=224828 edges=1124073 degree min=9 max=10 bipartite=yes diameter=7, RESULT VALID d=10 D=7 n=224828;
  edge list sha256 dd70fb1ecdb6aca537a2fd4e3c5c8644d707addf5727cd5334994e1a2f71de5c
- (9,7): n=117760 edges=529864 degree min=8 max=9 bipartite=yes diameter=7, RESULT VALID d=9 D=7 n=117760;
  sha256 32f6f25834c4926ccddcd9ccdd6b5d0516fb43b8368662926e6a1cdaff8277fd
- (7,7): n=23500 edges=82250 degree min=7 max=7 bipartite=yes diameter=7, RESULT VALID d=7 D=7 n=23500;
  sha256 eeec3bde83fda7e955cfa78be06218e125d96a4a48d1f092b1d9709d2feeb8c1

K is limited by the size of the greedy pairwise-opposite point and line sets (about 67 at q = 8). Larger partial
ovoids/spreads, or freed points at distance 4 with an isometric choice of lines, would give more.
