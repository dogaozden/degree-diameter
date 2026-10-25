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

## (11,7) 404,222: H(9) with M a duality, 2,821 freed pairs

H(9) is self-dual. With M = phi (the duality from research/d10D7/dual/dualfind.c), M(B2(p)) = B2(phi(p)) holds for
EVERY point p, and midpoints map to midlines automatically. So any set of pairwise non-collinear points can be freed
together with the lines phi(p). Pairs at distance 4 share a B2 point, which is consistent because M = phi; their
hubs are within 2 + 4 = 6. A greedy random maximal non-collinear set has 2,821 points (Hoffman bound 6,643).
The hub graph is the union of 8 random perfect matchings (degree 8 = q - 1).
    ./d7hex b2dual hex/hex_q9.bin dual/x9_dual_K28.sol 1 b2dual_q9_s1.sol 8 0   (M from the duality solution)
    file research/frontier/sols/d11D7_hex9_B2dualK2821_n404222.sol
apsp (all pairs), 2026-10-24 23:3x UTC: n=404222 edges=2223221 degree min=11 max=11 bipartite=yes diameter=7,
RESULT VALID d=11 D=7 n=404222. Edge list sha256 767516bed8341d61b52f3398bc5f7d1428c67cdc3aeca816d74228b9594994bb.
(The 5-level version with the same 2,821 points, 675,584 vertices for (12,7), has diameter 8: with 4K = 11,284 hubs
of hub-graph degree 7 some same-side hub pairs end up more than 6 apart. Being redone with fewer pairs.)

## Larger sets from squad round 4: (10,7) 224,962, (9,7) 118,224, (7,7) 23,580

The sets came from squad round 4 (research/squads/d10D7-r4/; each set checked with tools/setcheck) and the
Hermitian-type spread. Lines are no constraint: the H(q)-lines inside a hyperplane whose section of Q(6,q) is elliptic
form a spread of q^3+1 pairwise opposite lines (research/d10D7/sets/hspread.py builds it for q = 8; the squad found
spreads for q = 7, 5 by search). Pairwise opposite points (partial ovoids; H(q) has no ovoid unless q = 3^h) set K.
| cell | points (source) | lines | K | n | solution |
|---|---|---|---|---|---|
| (10,7) | 134 (c1, local search; sets/P8_c1_134.txt) | 513 (spread, sets/L8_spread513.txt) | 134 | **224,962** | d10D7_hex8_B2K134_n224962.sol |
| (9,7) | 288 (c5; sets/P7_c5_288.txt) | 344 (c5 spread; sets/L7_c5_344.txt) | 288 | **118,224** | d9D7_hex7_B2K288_n118224.sol |
| (7,7) | 72 (c6; sets/P5_c6_72.txt) | 126 (c6 spread; sets/L5_c6_126.txt) | 72 | **23,580** | d7D7_hex5_B2K72_n23580.sol |
Build: `B2PTS=sets/P8_c1_134.txt B2LINES=sets/L8_spread513.txt ./d7hex b2 hex/hex_q8.bin 1000 3 OUT.sol 6 1`
(q = 7: hub degree 5; q = 5: hub degree 4). apsp (all pairs), 2026-10-24 ~23:5x UTC:
- (10,7): n=224962 edges=1124676 degree min=9 max=10 bipartite=yes diameter=7, RESULT VALID d=10 D=7; sha256 a8d2e3efe3dc9ad0fd65a679eebd509598d6c87cb34c129a0105c84c41e9a70a
- (9,7): n=118224 edges=531720 degree min=8 max=9 bipartite=yes diameter=7, RESULT VALID d=9 D=7; sha256 f08d8d789bf37dec2d5fc0ae82850d5be17b7ca2c5b8d817187b25d4d6a2cf3b
- (7,7): n=23580 edges=82530 degree min=7 max=7 bipartite=yes diameter=7, RESULT VALID d=7 D=7; sha256 946de08a99434031f515d5deaf1acbf2d8dd45b2536554eee14c80686a7c043e

## (11,7) 406,402: the duality M with 3,911 freed pairs

Same construction as 404,222 with a larger set of pairwise non-collinear points of H(9): 3,911 from squad card r4/c4
(min-degree greedy + k-fixed tabu search; research/d10D7/sets/P9_c4_noncollinear.txt, setcheck VALID).
    B2PTS=sets/P9_c4_noncollinear.txt ./d7hex b2dual hex/hex_q9.bin dual/x9_dual_K28.sol 1 OUT.sol 8 0
    file research/frontier/sols/d11D7_hex9_B2dualK3911_n406402.sol
apsp (all pairs), 2026-10-24 23:4x UTC: n=406402 edges=2235211 degree min=11 max=11 bipartite=yes diameter=7,
RESULT VALID d=11 D=7 n=406402. Edge list sha256 f0d850ede1cdb0425619e2b543be1b0085b3e4b6bbe2b21646e9530a61302010.

## (10,7) 225,128: 217 freed pairs (squad round 5, card c4)

Same construction as 224,962, but with a larger set of pairwise opposite points of H(8): 217 points
(research/d10D7/sets/P8_r5c4_217.txt, sha256 afdff00e5b38fd5fa47acec8dfc96d5030443c5b0de099c4fee3056c7f6026b6,
setcheck VALID). Card r5/c4 took the orbits of the order-3 subgroup of the norm-1 torus (order 513) of W(5,8) and ran a
tabu search on the orbit graph, which gave 31 orbits (93 points). A k-fixed tabu search started from that set then
grew it to 217. The 513-line spread is unchanged. n = 6·37,449 + 2·217 = 225,128.
    B2PTS=sets/P8_r5c4_217.txt B2LINES=sets/L8_spread513.txt ./d7hex b2 hex/hex_q8.bin 1000 3 OUT.sol 6 1
    file research/frontier/sols/d10D7_hex8_B2K217_n225128.sol (sha256 5b8448d0242bb376da25433dd44810c6fda0d2aeefd0609169f9686eae932935)
d7hex's own hub test reported "same-side hub violations 2212". That test is conservative: it counts only hub-graph
paths and ignores routes through the main graph. The all-pairs check below is what counts.
apsp (all pairs), 2026-10-25 00:1x UTC: n=225128 edges=1125423 degree min=9 max=10 bipartite=yes diameter=7,
RESULT VALID d=10 D=7 n=225128. Edge list sha256 ea850090549331d2396141cab45d7be422782623193f77e56cfe67a5d4107a07
(`./d7hex edges hex/hex_q8.bin SOL g.edges` on the saved solution gives the same hash).

## (11,7) 407,134: the duality M with 4,277 freed pairs (squad round 5, card c6)

Same construction as 406,402, but with 4,277 pairwise non-collinear points of H(9) (research/d10D7/sets/P9_r5c6_4277.txt,
sha256 7c8243ead6054f0ba9a5cf94f5a6b63a7f18c82c0ac841ecf72ee32ba218f4d5, setcheck VALID). Card r5/c6 used an element
g of SL(3,9) of order 91, acting on H(9) as (v, a, w) -> (gv, a, g^-T w). It has 730 orbits of size 91, and a tabu
search found 47 pairwise compatible orbits: 47·91 = 4,277. n = 6·66,430 + 2·4,277 = 407,134.
    B2PTS=sets/P9_r5c6_4277.txt ./d7hex b2dual hex/hex_q9.bin dual/x9_dual_K28.sol 1 OUT.sol 8 0
    file research/frontier/sols/d11D7_hex9_B2dualK4277_n407134.sol (sha256 abe318b79b5fcc43417894fced2de0204ab53ba2f42ba7baeaee789dec8dd124)
apsp (all pairs), 2026-10-25 00:1x UTC: n=407134 edges=2239237 degree min=11 max=11 bipartite=yes diameter=7,
RESULT VALID d=11 D=7 n=407134. Edge list sha256 92a0f3059f15a39b1f9d710fe83dc608cf77abea8bbb452e2547ef510384af6f
(`./d7hex edges hex/hex_q9.bin SOL g.edges` on the saved solution gives the same hash).
