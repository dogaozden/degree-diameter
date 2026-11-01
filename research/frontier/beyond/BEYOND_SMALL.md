# Beyond the table at small diameter: the eleven cells of job beyond-small

Job beyond-small (Opus director + three Haiku squad rounds, cloud session, 2026-11-01, branch
claude/beyond-small-cells-fwb6si). Brief: the cells beyond the 2013 table that the coordinator does not yet hold at small
diameter, D = 3 and 4 at Δ = 17, 18, 20, D = 5 at Δ = 17, and D = 6 at Δ = 17..20.

## Summary

| cell | value | % of Moore | upper bound | construction | check |
|---|---:|---:|---:|---|---|
| (17,3) | **546** | 100 | 546 | PG(2,16) incidence graph (Moore) | apsp (moore/check_d17D3_pg16.apsp.txt) |
| (18,3) | **614** | 100 | 614 | PG(2,17) (Moore) | apsp (moore/check_d18D3_pg17.apsp.txt) |
| (20,3) | **762** | 100 | 762 | PG(2,19) (Moore) | apsp (moore/check_d20D3_pg19.apsp.txt) |
| (17,4) | **8,738** | 100 | 8,738 | W(16) (Moore) | apsp (moore/check_d17D4_w16.apsp.txt) |
| (18,4) | **10,440** | 100 | 10,440 | W(17) (Moore) | apsp (moore/check_d18D4_w17.apsp.txt) |
| (20,4) | **14,480** | 100 | 14,480 | W(19) (Moore) | apsp (moore/check_d20D4_w19.apsp.txt) |
| (17,5) | **35,728** | 25.6 | 139,804 | **new**: the (16,5) route-chart graph + 1,936 hubs in 88 Z22-orbits (below) | apsp (research/squads/beyond-small/graphs/d17D5_n35728.check.txt) |
| (17,6) | **2,236,962** | 100 | 2,236,962 | H(16) (Moore) | exact, orbit BFS (hex6/check_d17D6_H16.auto.txt) |
| (18,6) | **3,017,196** | 100 | 3,017,196 | H(17) (Moore) | exact, orbit BFS (hex6/check_d18D6_H17.auto.txt) |
| (19,6) | **3,203,968** | 80.1 | 4,001,438 | Theorem D, q = 17, m = 2 (lab theorem, Lean) | exact, orbit BFS (thmd19/check_d19D6_thmD_q17.auto.txt) |
| (20,6) | **5,227,320** | 100 | 5,227,320 | H(19) (Moore) | exact, orbit BFS (hex6/check_d20D6_H19.auto.txt) |

Why these cells were open for us. Nine of them are Moore cells: Δ − 1 = 16, 17, 19 is a prime power, so the
projective plane, the symplectic quadrangle W(q) and the split Cayley hexagon H(q) of order Δ − 1 give the bipartite
Moore bound exactly (optimal; nothing to construct). The earlier job (new-cells-beyond) had them with all-pairs checks at
D = 3, 4 but only sampled BFS at D = 6, and none of them was in the coordinator's records. (19,6) is the lab's Theorem D
at q = 17 (also only sampled before). (17,5) was the one real gap: our formula families need Δ = q+1+(even) (MDM) or
Δ = letters × field size (route charts), and 17 is neither; the previous job left only the floor 33,792.

## (17,5): hubs on the (16,5) route-chart graph

**Base.** G = the (16,5) graph of research/theorems/graphs/build_d16D5_n33792.py: K3,3 with a doubled perfect matching
lifted by Z22 (66 + 66 controller vertices), fibre F4^4, lift edge ((a_i,g),x) ~ ((b_j,g+v),A_c x + λ b_c), λ ∈ F4;
33,792 vertices, 16-regular, diameter 5. Every vertex has one spare degree.

**Proposition (hubs).** Let G be bipartite with sides A, B and diameter 5. Add new vertices ("hubs"); a hub on side A
is joined to a set N ⊆ B, a hub on side B to a set N ⊆ A, every old vertex lying in at most one N. If
(1) every vertex of the hub's own side is within distance 3 of N, and
(2) any two hubs on the same side have x ∈ N(h), x' ∈ N(h') with d_G(x, x') ≤ 2,
then the new graph has diameter ≤ 5. *Proof.* Old pairs keep their distance. A hub h on side A reaches A within 4 by
(1), and B within 5 because B–B distances in G are ≤ 4 (bipartite, diameter 5). Two A-hubs are within 4 by (2). An A-hub
reaches every A-vertex within 4, so it reaches every B-hub (which has an A-neighbour) within 5. ∎
So the two sides are independent: the best A-packing and the best B-packing combine freely. With |N| ≤ 16 the hubs
have a spare degree, and with old degree 16 + 1 the maximum degree is 17. At most 16,896/16 = 1,056 hubs per side fit
(35,904 vertices in all).

**Hubs from fibre lines (squad r1/c03).** A set N of 4 affine fibre lines {(v, y + λc) : λ ∈ F4} in 4 controller
vertices covers a whole side within distance 3 for many choices of (v, c), and for fixed fibres and directions the
cover does not depend on the offsets y (director's test: 3,080 of 3,080 random parallel replacements still cover).
Random 17-sets need 18 sets to cover (r1/c01), lines need 4.

**Z22 orbits (squad r2/d06).** g → g+1 on the controller coordinate is an automorphism of G (the group of G has order
66: Z22 × the fibre scalars F4*, r3/e07 with bliss). If N satisfies (1) so do its 22 translates; they are disjoint iff the
keys (j, y) of N's vertices are distinct, and the orbit satisfies (2) internally iff N is compatible with N+u for all
u ≠ 0. Packing orbits instead of single hubs multiplies every good choice by 22 (768 keys per side: at most 48 orbits of
16 per side).

**Searching orbit packings.** Adaptive growth (r3/e02 growb.c, and e01 on side A): a new orbit base is a joint greedy
choice of 4 lines with unused keys that covers the side and meets the distance-2 set of every existing hub; it saturates
(32 A-orbits, 37 B-orbits). Escaping the saturation was the director's step: a destroy-and-repair loop around growb (drop
2–5 random orbits, regrow for 60 s, keep the result if it has at least as many orbits; side A runs on the side-swapped
graph, vertex v ↦ v ± 16,896), an annealer over orbit packings (r3/e03 anneal3.c, moves insert/delete/replace/line-swap
with conflicts as a soft penalty), and region destroys (r4/f07: drop every orbit whose keys meet a random affine set of
keys, then regrow). Side A went 27 → 32 → 36 → 38 → 42 orbits, side B 21 → 37 → 39 → 41 → 44.

**Best graph: 35,728 = 33,792 + 1,936 hubs, in 43 Z22-orbits on side A and 45 on side B (22·88 = 1,936).** Files in
research/squads/beyond-small/graphs/: d17D5_n35728_orbit_bases.txt (orbit bases, global ids; bases with ids ≥ 16,896
are A-hub orbits), d17D5_n35728_orbits.edges.gz, d17D5_n35728.check.txt (apsp.c RESULT VALID d=17 D=5 and the sha256),
and the builder build_d17D5_hubs.py, which rebuilds G from research/theorems/graphs/build_d16D5_n33792.py, expands the
orbits, checks conditions (1) and (2) of the proposition directly, and writes the edge list.
Rebuild: `python3 research/squads/beyond-small/graphs/build_d17D5_hubs.py OUT.edges --orbits
research/squads/beyond-small/graphs/d17D5_n35728_orbit_bases.txt && apsp OUT.edges 17 5`.
Independent checks: apsp.c for every recorded value; bfs_all.c (plain BFS from every vertex) on the final 35,728 graph and on 35,618
(max eccentricity 5, distance histograms sum to n²: graphs/d17D5_n35728.bfs_all.txt, d17D5_n35618.bfs_all.txt).

Steps on the way (all apsp VALID, director-checked): 33,794 (2 SA hubs, r1/c16), 33,814 (one Z22 orbit, r1/c02), 33,849
(57 line hubs, r1/c03), 33,983 (191 hubs, director's hubpack clique packing), 34,290 / 34,401 (adaptive growth and
annealing of single hubs, r2/d01, r2/d15), 34,848 (48 orbits, r2/d06; apsp and bfs_all), 34,863 / 34,885 / 34,980
(director's combinations of the best A- and B-packings), 35,310 (e01 + e02), 35,420 / 35,442 / 35,486 / 35,618 / 35,640
(director's destroy-and-repair loops, with e03's 38 A-orbits), 35,684 (42 A + f07's 44 B), 35,706 (42 A + f08's 45 B),
35,728 (f03's 43 A + f08's 45 B). Round 5 (12 cards, four destroy styles and annealing, 45–50 min each) found no 44th A-orbit
or 46th B-orbit: the packings sit on a plateau of equal-count moves.
The method's cap is 48 orbits per side (35,904); 35,728 is 25.6 % of the Moore bound 139,804 (the (16,5) graph is 31.2 %
of its own bound).

## (17,5): what failed and why

- Route charts with a degree-17 alphabet. A 5th translation vector on one letter (17 = 5+4+4+4) keeps every walk of the
  16-regular chart and adds some, so a bigger controller might work: at Z23 (35,328 vertices) the exact far-pair count
  drops from 106k to 47k but not to 0, and an extra vector cannot repair a singular pattern that uses the extended letter
  once (r1/c07). Haar and multi-orbit controllers with the extra vector: 70k–300k far pairs (r1/c04–c06). Cutting three
  F5 letters to 4 scalars (r1/c08): boxes instead of affine spaces, 3.9M uncovered. A plain fifth letter had failed before.
- Lifts of W(13) with 3 extra degrees (8 sheets). Director's argument: with flags carrying 4ν in Z8, a doubled matching
  (1, 5) and a plain matching (2), the class-2 pairs need ν(geod σ(p)→u) = ν(geod p→σ(u)) for almost all pairs; the
  4-term sums of these conditions are base cycles, which forces ν to be a coboundary and kills the opposite-pair
  condition, unless σ is a polarity and ν σ-invariant. Card r1/c09 tested W(8) (which has a polarity): σ-invariant ν cut
  the far pairs from 174k to 2,432 but not to 0. Z2 × Z4 fails on the diagonal outright; D4 and Q8 fail because every
  element squares into {1, z}.
- Lifts of W(16) (17-regular, diameter 4): any cover has girth 8, so (p, 0) and (p, δ) are at distance ≥ 6 (r1/c14).
- Haar graphs: best 20,200 (AGL(1,101), r1/c15); self-dual and orbit-closed S stall at cost 125–374 (r1/c10, c11, r2/d14).
- Quotients of generalized hexagons: free Z7 on H(4) gives diameter 6 (r1/c12).
- Deleting a 1-factor from the (18,5) MDM graph: 43–50M far pairs (r1/c16).
- Hub variants: connectors without a common root are at distance 6 (r2/d10); 3-line hubs have pair density 0.82
  (r2/d12); 17-neighbour hubs raise compatibility from 0.937 to 0.957 but not the packing (r2/d04, r3/e06).
- Director's projective-plane scaffold (research/squads/beyond-small/director/slab*.c, scaffold.c, scafopt.c). Hubs hang
  on connectors (copies of the 13 lines of PG(2,3), 12 hubs each), connectors on roots (its 13 points), and one matching
  joins the connectors of the two sides; two hubs then always meet through a root, so condition (2) is free and the new
  vertices include 104 connectors and 26 roots (35,170 in all). Each fibre is cut into "slabs" (2-planes) and
  "hyperplanes" (4 slabs): a slab at a fibre covers ~11 whole fibres at distance 2 and a hyperplane dominates 4 whole
  fibres of the other side (exact counts, slabA.c), and covers depend only on (fibre, direction). With a fibre-level
  design (slabC/slabD + local search) hubs and roots have no far pairs, but each connector still misses about 120 old
  vertices in 2–3 fibres (exact count 12,182 after a 7-minute exact-cost search). Superseded by the orbit packings.

## D = 6: exact checks by verified automorphisms

All-pairs BFS of 2–5M-vertex graphs takes hours here, so research/frontier/beyond/hex6/apsp_auto.c checks the exact
diameter from one vertex per orbit of a group generated by permutations that it verifies itself (a bijection of the
vertex set that maps every edge to an edge is an automorphism; eccentricity is constant on orbits). It agrees with
apsp.c on H(4) and on the Theorem D graphs at q = 5 and 7, and rejects D − 1.
- H(q) (hexgen2.c of research/d10D7, points of X0X4 + X1X5 + X2X6 = X3² with Tits' six line equations): hexauto.c writes
  the edge list and the torus elements diag(a, b, (ab)⁻¹, 1, a⁻¹, b⁻¹, ab), which preserve the quadric and Tits'
  equations (λ0λ1λ2 = 1), for (a,b) = (ω,1), (1,ω). Orbit representatives: 10,026 (q = 16), 11,832 (q = 17),
  16,230 (q = 19). Results: H(16), H(17) and H(19) VALID with diameter exactly 6 (H(19): 5,227,320 vertices, 41 min on 2 threads under load).
- Theorem D at q = 17 (thmd19/thmd_auto.c, the r1/c08 builder of the previous job plus automorphisms): exactly the torus
  elements with a = 1 preserve the level function (the plane X0 + cX4 = 0, the Hermitian spread, L_v and the exact
  whisker set), so they lift to automorphisms of the doubled graph; one generator of order 16, 200,486 orbit
  representatives. Result: VALID, diameter exactly 6 (83 CPU-minutes on 3 threads).
Rebuild: `cd research/frontier/beyond/hex6 && gcc -O3 -o hexgen2 hexgen2.c && gcc -O3 -o hexauto hexauto.c && gcc -O3
-pthread -o apsp_auto apsp_auto.c && ./hexgen2 q && ./hexauto q && ./apsp_auto hex_q{q}.edges hex_q{q}.aut q+1 6 T`;
Theorem D: `cd ../thmd19 && gcc -O3 -o thmd_auto thmd_auto.c && ./thmd_auto ../hex6/hex/hex_q17.bin 0 1 E.edges E.aut &&
../hex6/apsp_auto E.edges E.aut 19 6 T`. Edge-list sha256 values are in the check files.

## D = 3, 4: self-contained builders

research/frontier/beyond/moore/build_moore_d34.py (`pg q` or `w q`, q prime or 16): the three projective planes
rebuild byte-identically to the previous job's edge lists (sha256 94c96d39…, ab6a42c6…, e20c61f7…); the three W(q)
graphs differ from the stored ones only in labelling. All six: apsp.c VALID.
