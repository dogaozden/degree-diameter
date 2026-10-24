# exp2-solo: the D = 7 cells (7,7), (9,7), (11,7), one Opus session alone

Opus, cloud container (4 cores, 15 GB), 2026-10-24, start 16:56:02 UTC. No subagents and no squads (this arm measures
Opus alone). Branch `claude/exp2-solo-haar-d7-jroi1u`.

## 1. Result

| cell | table | best Haar graph, VALID by build_haar2.py | / table | table construction rebuilt, VALID by apsp.c |
|---|---|---|---|---|
| (7,7) | 23,436 | **20,160** (PSL(2,3) × SL(2,5) × Z7, orbit k = 3) | 0.860 | 23,436 = 1.000 (not a raise) |
| (9,7) | 117,648 | **82,992** (SL(2,13) × Z19, orbit k = 3, f = 0) | 0.705 | 117,648 = 1.000 (not a raise) |
| (11,7) | 398,580 | **266,448** (SL(2,13) × Z61, orbit k = 3) | 0.668 | 398,580 = 1.000 (not a raise) |

**No cell beaten.** The Haar files (haar_gen3 format) are in `research/frontier/sols/`:
`d7D7_prod_psl_3_sl_5_7_orb3_s1.txt`, `d9D7_sl_13_19_orb3f0_s1.txt`, `d11D7_sl_13_61_orb3_s1.txt` (plus the lower rung
`d7D7_sl_8_19_orb3_s1.txt`). Logs with the build_haar2.py verdicts and edge-list sha256 are in `solo_runs/`.

The rebuilt table graphs are not Haar graphs, so they have no haar_gen3 file. `hexd7/threecopy.py q OUT` writes the
edge list (deterministic) and `research/lifts/coordinator_check/apsp.c` checks it (all-pairs BFS, no symmetry assumed).

## 2. What the table values are

All three table values are exactly three copies of a generalized hexagon:

- (7,7) = 23,436 = 3 · 7,812, and 7,812 is the incidence graph of H(5) (the (6,6) Moore graph);
- (9,7) = 117,648 = 3 · 39,216 (H(7));
- (11,7) = 398,580 = 3 · 132,860 (H(9)).

The rest of the D = 7 column has the same pattern: Δ = q + 1 + k and (2k+1) · |H(q)|. (10,7) = 3 · H(8), (12,7) = 5 · H(9),
(13,7) = 3 · H(11), (14,7) = 5 · H(11), (15,7) = 7 · H(11), (16,7) = 5 · H(13). Only (6,7) and (8,7) are something else
(lifts, and we hold both).

**The construction (k = 1), as I rebuilt it.** Let Γ be a bipartite graph of diameter D0 (D0 even) with max degree d,
sides "points" and "lines", and let φ be any bijection from points to lines (for example a perfect matching of Γ).
Take three copies Γ × Z3 and add the cross edges (p, c) ~ (φ(p), c+1). The result is bipartite, has max degree d + 1
and diameter at most D0 + 1. Proof (in Γ, point–line distances are ≤ D0 − 1 and same-side distances ≤ D0):

- own copy: within D0.
- copy c+1 from a point p: step to (φ(p), c+1), then everything in that copy within D0. Total ≤ D0 + 1.
- copy c−1 from a point p: a point (z, c−1) has its cross neighbour (φ(z), c) in p's copy, at distance ≤ D0 − 1 from
  p. Total ≤ D0. A line (Z, c−1) has its cross neighbour (φ⁻¹(Z), c+1); go (p,c) → (φ(p), c+1) → φ⁻¹(Z) (≤ D0 − 1)
  → (Z, c−1). Total ≤ D0 + 1.
- lines are symmetric (their cross edges go to copy c−1).

With Γ = H(q) (D0 = 6, d = q + 1) this gives 6 · (q⁶−1)/(q−1) vertices, max degree q + 2 and diameter 7: the table
values. I built H(q) from Tits' description in Q(6,q) (points X0X4 + X1X5 + X2X6 = X3²; lines with p12 = p34,
p54 = p32, p20 = p35, p65 = p30, p01 = p36, p46 = p31) in `hexd7/hexagon.py`. It checks the Moore ball sizes, which
identify a generalized hexagon. Then `threecopy.py` adds a perfect matching found by augmenting paths. apsp.c verdicts:

| q | n | max degree | diameter | apsp.c | edge-list sha256 |
|---|---|---|---|---|---|
| 5 | 23,436 | 7 | 7 | RESULT VALID d=7 D=7 | 31b376c8af4e0e2b3276b47363eb6064e2d896cbf553f36f8958c33519881fd1 |
| 7 | 117,648 | 9 | 7 | RESULT VALID d=9 D=7 | cae40238f8dcb6c6e7606a6be739ba18f8772742cf0cbafa1a54c94b9fe472ec |
| 9 | 398,580 | 11 | 7 | RESULT VALID d=11 D=7 | 2e8ee60e9b274f40a765a43dd494b70356c4957dbe19ec8b852a32db5b4f4a12 |

Run times: H(5) 4 s to build, 0.4 s to check; H(7) about 1 min and 1 min; H(9) about 4 min and 7 min (one core).

So the table graphs are reproduced exactly, not raised. With k extra edges and copies over Z_(2k+1) (cross edges with
voltages 1..k) the same proof gives b(Δ + k, D + 1) ≥ (2k+1) · b(Δ, D) for even D. That is the source of the whole
D = 7 column. Applied to our own D = 6 records ((7,6) 9,592, (11,6) 148,944, (13,6) 388,972, (15,6) 870,440), it
gives nothing above the table.

## 3. Haar search (the required format)

Tool: `research/structured/haar_sym.c` (ORBIT mode, k = 3; copied onto this branch from
claude/structured-search-orbit-w5dd4f), job queue `tools/orbq.sh`, each solution checked by build_haar2.py. SL-type
groups (odd D), every prime of n ≡ 1 mod 3. Δ = 7: S = {e} ∪ 2 orbits (f = 1); Δ = 9: 3 free orbits (f = 0);
Δ = 11: {e, t} ∪ 3 orbits (f = 2). μ = N e^(−W/N).

(RUNG TABLE: filled in at the end)

Observations:

- At D = 7 the low rungs fall in seconds. μ ≈ 25–39 solved in 0.4–13 s. The walls appear at μ ≈ 38–48: runs stall at
  cost 6–12 (two to four uncovered α-orbits).
- (7,7) has a small orbit space. With m = 2 orbits there are only about (N/3)² ≈ 10⁷ symmetric S. On SL(2,7) × Z31
  (μ 48.2) the search made 5.7·10⁷ evaluations (several passes over the space) and stayed at cost 6, so very
  probably no α-symmetric solution exists there. Groups with a large cyclic factor (SL(2,4) × Z169: best 42) are
  hopeless. Above N = 10,080 only a few group orders exist below the table (10,140; 10,248; 10,416; …).
- At the table orders μ is 99, 361 and 755, above the first-moment ceiling for any random-like or orbit-symmetric S
  (SIZE_LAW.md, STRUCTURE.md). The Haar route cannot reach these cells, and these runs agree.

## 4. Attempts to beat the hexagon construction (all negative)

1. **Two extra vertices by a local gadget.** Delete q+1 edges (a_j, b_j) of the 3-copy H(5) graph, add x ~ all a_j,
   w ~ all b_j, x ~ w: degrees stay ≤ 7 and n = 23,438. `hexd7/violations.c` counts ordered pairs at distance > 7.
   Deleting one edge already breaks 626–752 ordered pairs for a cross edge, about 1,250 for an ordinary hexagon
   edge, and 230 for the hexagon copy of a matching edge. The matching edge is cheap because of the 6-cycle
   p, φ(p), p, … through the three copies. With the gadget the best of a short local search over which matching
   edges to delete was 1,100 broken pairs (start 1,186, `hexd7/gadget.py`). The broken pairs are mostly between
   third parties, which the gadget cannot shorten. Dropped.
2. **More copies (lifts of Γ + doubled matching by a group K, |K| ≥ 4).** Impossible for Γ = H(q). In Γ + M' (girth 12
   apart from the digons), the walks of length ≤ 6 between two vertices at distance 4 are the geodesic, its M → M'
   substitutions, and one digon detour (length 6). If the geodesic contains no matching edge, they realize at most 3
   voltages (g, g ± δ for cyclic K, and for Z2² a 3-colouring condition that fails because the contracted graph has
   degree 2q). Every vertex has M-free geodesics of length 4, so the lift has diameter > 7. For a bijection φ not
   inside Γ, Z4 fails differently: the antipodal copy c+2 needs two cross steps, which leave only ~2q⁴ ≪ q⁵ points in
   reach. Three copies is the maximum for this base.
3. **Why 2k+1 copies is the limit of every copy design.** Take any number r of copies of Moore graphs of diameter 6
   (of any orders), each vertex with k spare edges, and use only the two mechanisms that cover a whole copy at once:
   F (v has a cross neighbour in the target copy) and L (the target has a cross neighbour in v's copy).
   - Same-colour pairs (v in copy i, t in copy j) need F or L. So for every pair {i, j}, either every colour-0
     vertex of i has a neighbour in j, or every colour-0 vertex of j has one in i. That is a tournament T0 on the
     copies, and likewise T1 for colour 1.
   - A colour-0 vertex spends one spare edge per out-arc of T0. A colour-1 vertex spends one per out-arc of T1, and an
     edge serves an in-arc only when it is one of those same edges. So each copy has degree ≤ 2k in T0.
   - A tournament needs degree r − 1, so r ≤ 2k + 1. Mixing hexagons of different q does not help: (11,7) from
     2·H(9) + 2·H(8) would have 415,516 vertices, but an H(9) copy (k = 1) admits only 3 copies in all.
   The other routes (through a neighbour's cross edge) cover only radius-4 balls of about q⁴ out of q⁵ vertices per
   copy, so they cannot replace F or L for a whole copy.
4. **Other bases.** The construction needs a base of diameter ≤ 6 and degree Δ − 1, and the Moore bound makes H(q) the
   largest. A base of diameter 5 gives only 3 copies (copies c ± 2 are out of reach), e.g. 3 · 1,152 at Δ = 7. A
   generalized quadrangle allows 5 copies at D = 7 (checked by hand, same first/last-step argument), but 5 · |GQ(q,q)|
   ~ 10q³ ≪ 6q⁵. Subgraphs of H(q') for larger q' fail: deleting a vertex of a girth-12 graph puts two of its
   neighbours at distance ≥ 10. A Z3-lift of our (7,6) Haar graph (9,592 vertices) would have 28,776 vertices, but
   the pairs at distance 6 have ~11 geodesics for 3 voltages, so μ ≈ 125 even with a perfect base. Haar graphs cannot
   carry the 3-copy trick either: it needs a (Δ−1, 6) Haar graph near the Moore bound.

**What would be needed.** A diameter-7 graph whose radius-6 balls cover with multiplicity ~5 and no misses, as the
hexagon construction does, but with more than 3·|H(q)| vertices. None of the structured families tried here
(orbit-symmetric Haar graphs, lifts of hexagons, local gadgets) does this.

## 5. Budget and time

(filled in at the end)
