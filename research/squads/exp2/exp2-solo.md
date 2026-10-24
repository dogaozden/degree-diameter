# exp2-solo: the D = 7 cells (7,7), (9,7), (11,7), one Opus session alone

Opus, cloud container (4 cores, 15 GB), 2026-10-24, start 16:56:02 UTC. No subagents and no squads (this arm measures
Opus alone). Branch `claude/exp2-solo-haar-d7-jroi1u`.

## 1. Result

| cell | table | **new graph** (apsp.c VALID) | / table | best Haar graph (build_haar2.py VALID) | / table |
|---|---|---|---|---|---|
| (7,7) | 23,436 | **23,438** | 1.00009 | 20,160 (PSL(2,3) × SL(2,5) × Z7, orbit k = 3) | 0.860 |
| (9,7) | 117,648 | **117,650** | 1.00002 | 82,992 (SL(2,13) × Z19, orbit k = 3, f = 0) | 0.705 |
| (11,7) | 398,580 | (q = 9 run in progress) | | 266,640 (SL(2,11) × Z101, orbit k = 5) | 0.669 |

**Two cells beaten, by 2 vertices each** (the third is running). The new graphs are not Haar graphs. They are 3 copies of
the generalized hexagon H(q) (the table's own construction), with one point "unhooked" in all three copies and a
2-vertex gadget added, and a bijection φ chosen by local search (§2). Files in `graphs/`:

- `d7D7_hex5_plus2.phi`, `d9D7_hex7_plus2.phi`: the bijection φ (one line index per point).
- `*.edges.gz`: the edge lists (apsp.c format: n, then one "a b" per line).
- `*.apsp.txt`: the apsp.c verdicts and the sha256 of the uncompressed edge lists.

To rebuild: `python3 hexd7/plus2.py q OUT.edges 1 graphs/<file>.phi`, then `apsp OUT.edges q+2 7`
(`research/lifts/coordinator_check/apsp.c`: all-pairs BFS, no symmetry assumed).

| cell | n | max degree | diameter | apsp.c | edge-list sha256 |
|---|---|---|---|---|---|
| (7,7) | 23,438 | 7 | 7 | RESULT VALID d=7 D=7 n=23438 | debe7e451970a59f790c0e08830bb2232355c071dd7f9a9074e9c4515bdc049e |
| (9,7) | 117,650 | 9 | 7 | RESULT VALID d=9 D=7 n=117650 | 94303a1b4845c9112504d773c89fe751b136b6efef320d04242c70c46f555385 |

The Haar files (haar_gen3 format, the brief's format) are in `research/frontier/sols/`:
`d7D7_prod_psl_3_sl_5_7_orb3_s1.txt`, `d9D7_sl_13_19_orb3f0_s1.txt`, `d11D7_sl_11_101_orb5_s1.txt` (plus lower rungs
`d7D7_sl_8_19_orb3_s1.txt`, `d11D7_sl_13_61_orb3_s1.txt`). Each is VALID by build_haar2.py and by
check_haar_indep.py. Logs with the build_haar2.py verdicts and edge-list sha256 are in `solo_runs/`.

## 2. The new graphs: 3 copies of H(q), one point unhooked, plus 2

**Base (the table's construction, §3).** Γ is the incidence graph of H(q): points and lines, (q⁶−1)/(q−1) of each,
degree q+1, diameter 6. Take copies (v, c), c ∈ Z3, and cross edges (y, c) ~ (φ(y), c+1) for every point y, with φ
any bijection points → lines. This has max degree q+2 and diameter 7 for every φ.

**Change.**
- Pick a point p and let L0 = φ(p).
- Delete the three cross edges (p, c) ~ (L0, c+1).
- Add two vertices: x ~ (p, 0), (p, 1), (p, 2); w ~ (L0, 0), (L0, 1), (L0, 2); and x ~ w.

The copies of p and L0 lose one edge and gain one, x and w have degree 4, so the max degree stays q + 2, and
n = 6(q⁶−1)/(q−1) + 2.

**Why only two vertices need checking.**
- *Pairs avoiding p and L0.* The 3-copy proof (§3) reaches every target with the source's own cross edge ("first
  step") and the target's own cross edge ("last step"). So a pair that involves no copy of p or L0 keeps its routes.
  This was measured: deleting one cross edge breaks only pairs that contain one of its two endpoints.
- *x and w.* x is adjacent to (p, c) in every copy, so it reaches each copy within 1 + 6. Likewise w, and x ~ w.
- *The rest.* The construction is Z3-symmetric, so it suffices to check a = (p, 0) and b = (L0, 1).

**Checking a and b.** The gadget covers most of what they lost:
- From a, copy 2 is reached by last steps (points) and through x → (p, 2) (lines, ≤ 2 + 5).
- In copy 1, a reaches the lines and the points within distance 4 of p through x → (p, 1).
- From b, copy 2 is reached by last steps (lines) and through w → (L0, 2) (points).
- In copy 0, b reaches the points and the lines within distance 4 of L0 through w → (L0, 0).
- What remains:
  - (A*) every point of copy 1 opposite p (distance 6, q⁵ of them) must be within 6 of a;
  - (B*) every line of copy 0 opposite L0 must be within 6 of b.
- These depend on φ. A sufficient form:
  - (A) every point opposite p lies on a line φ(y) with y ≠ p within distance 4 of p (route a → (y,0) → (φ(y),1) →
    point);
  - (B) every line opposite L0 contains a point φ⁻¹(M) with M ≠ L0 within distance 4 of L0.
- Each asks for a cover of q⁵ targets by about 780 (q = 5) or 2,800 (q = 7) choices, with q⁴ = 625 or 2,401 as the
  fractional optimum.

**Finding φ.** `hexd7/plus2.py` builds φ from greedy covers for (A) and (B) on disjoint domains, then fills the rest
at random. The greedy covers were slightly too big (843 and 835 for 780 slots at q = 5), so they are truncated.
`hexd7/plus2ls.c` then counts the vertices beyond distance 7 from a and from b by BFS (exact, all routes). It runs a
local search that swaps the images of two points: targeted swaps create a route a → y → φ(y) → t for an unreached
point t, or b → M → φ⁻¹(M) → t for an unreached line t, and the rest are random.

| q | start (vertices missed from a, b) | swaps to 0 | time |
|---|---|---|---|
| 5 | 9 + 6 | 32 | 0.2 s |
| 7 | 165 + 191 | 1,261 | 14 s |

The final graphs were then checked from scratch by apsp.c (all pairs, no symmetry or theory assumed): VALID.

**Remarks.**
- Several points can be unhooked, each with its own gadget, for +2 per point, as long as the conditions for
  different points can be met together and the gadget vertices stay within 6 of each other. Not pursued for time
  (it only moves the ratio by 2/n per point).
- The same idea should work for every prime power q (so for all the (2k+1)·H(q) cells of the D = 7 column with
  k = 1). I checked only q = 5 and 7 (and q = 9 below).
- A first, failed attempt (§5.1) used a non-symmetric gadget on edges inside one copy, with φ fixed. The working
  version unhooks the same point in all three copies and adapts φ to it.

## 3. What the table values are

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
As the proof says, φ does not matter. With q = 5, two random perfect matchings and two random bijections points →
lines (not edges of Γ) all gave RESULT VALID d=7 D=7 n=23436.

So the table graphs are reproduced exactly, not raised. With k extra edges and copies over Z_(2k+1) (cross edges with
voltages 1..k) the same proof gives b(Δ + k, D + 1) ≥ (2k+1) · b(Δ, D) for even D. `hexd7/kcopy.py` checks it:
3, 5 and 7 copies of H(3) (n = 2,184, 3,640, 5,096 at Δ = 5, 6, 7) and 5 copies of H(5) (n = 39,060 at Δ = 8) are all
RESULT VALID with D = 7 by apsp.c. With k = 1, 2, 3 this accounts for the whole D = 7 column except (6,7) and (8,7).
Applied to our own D = 6 records ((7,6) 9,592, (11,6) 148,944, (13,6) 388,972, (15,6) 870,440), it
gives nothing above the table.

## 4. Haar search (the required format)

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
- k = 5 orbits (S = {e} ∪ two α-orbits of size 5) work at D = 7 for Δ = 11. SL(2,11) × Z101 at μ 32 fell in 1 s
  (7,169 evaluations).

**A new trick for odd D that did not pay here: transpose-closed S** (`research/structured/haar_tsym.c`, `TSYM=1`).
- At odd D the cost has two conditions, (S⁻¹S)³ = G and (SS⁻¹)³ = G. If an anti-automorphism τ maps S onto itself,
  then (SS⁻¹)³ = τ((S⁻¹S)³), and the two conditions are one. That halves the number of independent ways to fail.
- On SL(2,q) × Zn, τ(A, z) = (Aᵀ, z) fixes every S whose matrices are symmetric. τ commutes with α when α is
  conjugation by a rotation (gᵀg = I) of order 3, which exists for q ≡ ±1 mod 12. For Δ = 11 the fixed part is
  {t, t⁻¹}, with t a rotation (τ(t) = t⁻¹).
- Implemented and checked: all sampled costs are even, so the two conditions coincide.
- But it loses badly. Symmetric matrices are R·diag·Rᵀ, with R in the same rotation torus as α. The orbits then
  share commuting structure, and 10–30 % of the words of length 4 coincide.
  - On SL(2,11) × Z103 at (11,7), random symmetric S have median cost 1,600, against 266 for ordinary orbits.
  - A Python check on SL(2,11) × Z7 shows the same effect: |(S⁻¹S)²| has median 1,245 against 1,405.
- The variant that avoids symmetric matrices pairs two orbits instead, φ(O_x) = O_y⁻¹ with φ = conjugation by an
  element of order 4 that commutes with α. It needs a torus with elements of order 3 and 4 and an even number of
  orbits. It also halves the degrees of freedom, which these cells cannot afford: they already sit near the
  orbit-space ceiling. No group of the right order fits (7,7), (9,7) or (11,7).
- For larger odd-D cells (bigger orbit spaces) the pairing variant might still be worth a test.

## 5. Earlier attempts to beat the hexagon construction (negative)

1. **Two extra vertices by a local gadget, φ fixed** (superseded by §2). Delete q+1 edges (a_j, b_j) of the 3-copy H(5) graph, add x ~ all a_j,
   w ~ all b_j, x ~ w: degrees stay ≤ 7 and n = 23,438. `hexd7/violations.c` counts ordered pairs at distance > 7.
   Deleting one edge already breaks 626–752 ordered pairs for a cross edge, about 1,250 for an ordinary hexagon
   edge, and 230 for the hexagon copy of a matching edge. The matching edge is cheap because of the 6-cycle
   p, φ(p), p, … through the three copies. With the gadget the best of a short local search over which matching
   edges to delete was 1,100 broken pairs (start 1,186, `hexd7/gadget.py`). The broken pairs are mostly between
   third parties, which the gadget cannot shorten. Dropped. What fixed it (§2): delete cross edges instead (their loss
   breaks only pairs with an endpoint), unhook the same point in all three copies, and choose φ to fit.
2. **More copies (lifts of Γ + doubled matching by a group K, |K| ≥ 4).** In Γ + M' (M ⊂ Γ a perfect matching, M' its
   parallel copy; girth 12 apart from the digons), the walks of length ≤ 6 between two vertices at distance 4 are:
   the geodesic, its M → M' substitutions, and one digon detour (length 6).
   - With one voltage δ on every digon this fails. If the geodesic contains no matching edge, only g and g ± δ
     occur, i.e. 3 voltages, and every vertex has matching-free paths of length 4.
   - General voltages turn this into a colouring condition on the matching. For Z4, every matching-free path of
     length 4 must see both an odd and an even δ among the matching edges at its five vertices. On top come much
     harder conditions for the q+1 geodesics of each pair at distance 6. I did not settle this case.
   - For a bijection φ not inside Γ, with voltage 1 on the cross edges, Z4 fails: the antipodal copy c+2 needs two
     cross steps, which leave only ~2q⁴ ≪ q⁵ points in reach.
   A random voltage assignment over Z4 would leave about N·e^(−3.58) ≈ 440 misses per source, so only a very special
   structure could work.
3. **Why 2k+1 copies is the limit of every copy design.** Take any number r of copies of Moore graphs of diameter 6
   (of any orders), each vertex with k spare edges, and use only the two mechanisms that cover a whole copy at once:
   F (v has a cross neighbour in the target copy) and L (the target has a cross neighbour in v's copy).
   - Same-colour pairs (v in copy i, t in copy j) need F or L. So for every pair {i, j}, either every colour-0
     vertex of i has a neighbour in j, or every colour-0 vertex of j has one in i. That is a tournament T0 on the
     copies, and likewise T1 for colour 1.
   - A colour-0 vertex spends one spare edge per out-arc of T0, so out-degrees in T0 are ≤ k. An in-arc j → i of T0
     lands |colour-0 side of j| edges on the colour-1 side of i, whose capacity k·|side of i| is shared with T1. For
     copies of equal size this gives in-degree ≤ k, so each copy has degree ≤ 2k in T0.
   - A tournament needs degree r − 1, so r ≤ 2k + 1 for equal copies. Mixing hexagons of different q does not help.
     (11,7) from 2·H(9) + 2·H(8) would have 415,516 vertices, but an H(9) side (66,430 vertices, k = 1) can absorb only
     one H(8) side (37,449), so an H(9) copy still has degree ≤ 2 and r ≤ 3. With two H(9) copies, their free sides
     can serve only one further copy: 2·132,860 + 74,898 = 340,618 < 398,580. Small copies with many spare edges add
     too few vertices to matter.
   The other routes (through a neighbour's cross edge) cover only radius-4 balls of about q⁴ out of q⁵ vertices per
   copy, so they cannot replace F or L for a whole copy.
4. **Other bases.** The construction needs a base of diameter ≤ 6 and degree Δ − 1, and the Moore bound makes H(q) the
   largest. A base of diameter 5 gives only 3 copies (copies c ± 2 are out of reach), e.g. 3 · 1,152 at Δ = 7. A
   generalized quadrangle allows 5 copies at D = 7 (checked by hand, same first/last-step argument), but 5 · |GQ(q,q)|
   ~ 10q³ ≪ 6q⁵. Subgraphs of H(q') for larger q' fail: deleting a vertex of a girth-12 graph puts two of its
   neighbours at distance ≥ 10. A Z3-lift of our (7,6) Haar graph (9,592 vertices) would have 28,776 vertices, but
   the pairs at distance 6 have ~11 geodesics for 3 voltages, so μ ≈ 125 even with a perfect base. Haar graphs cannot
   carry the 3-copy trick either: it needs a (Δ−1, 6) Haar graph near the Moore bound.

**What these show.** Copy designs and lifts are capped at 3·|H(q)|, and so is anything symmetric under the copy
group. The +2 of §2 comes from breaking the symmetry locally (one point) and spending the freedom in φ there.

## 6. Budget and time

(filled in at the end)
