# exp2-solo: the D = 7 cells (7,7), (9,7), (11,7), one Opus session alone

Opus, cloud container (4 cores, 15 GB), 2026-10-24, start 16:56:02 UTC. No subagents and no squads (this arm measures
Opus alone). Branch `claude/exp2-solo-haar-d7-jroi1u`.

## 0. Summary (plain English)

- **What the cells are.** All three table values are 3 copies of a generalized hexagon H(q) (q = 5, 7, 9) joined by
  one extra edge per vertex. I rebuilt that construction and proved it works for any way of choosing the extra
  edges (§3).
- **What worked: a +2 construction.** Detach one point p from its extra edges in all three copies, add two new
  vertices that take over those edge slots, and choose the extra edges near p by exact covers of the hexagon (§2).
  - The graph keeps max degree q + 2 and diameter 7, with 2 more vertices than the table.
  - Repeating it for several points adds 2 per point; with 12 points at q = 5 this gave 23,460.
  - All graphs were checked by the all-pairs BFS checker apsp.c.
- **What did not work.**
  - Orbit-symmetric Haar graphs (the required format) reached only 0.86, 0.71 and 0.67 of the table. These cells sit
    above the first-moment ceiling for random-like S.
  - Also: more than 3 copies, lifts of the hexagon, local gadgets with the extra edges fixed, and a new
    transpose-symmetry trick for odd D (§4, §5).
- **Format note.** The new graphs are not Haar graphs, so they are not in haar_gen3 format. They come as edge lists plus
  the bijection φ that generates them, and they are verified by apsp.c instead of build_haar2.py.

## 1. Result

| cell | table | **new graph** (apsp.c VALID) | / table | best Haar graph (build_haar2.py VALID) | / table |
|---|---|---|---|---|---|
| (7,7) | 23,436 | **23,460** | 1.00102 | 20,160 (PSL(2,3) × SL(2,5) × Z7, orbit k = 3) | 0.860 |
| (9,7) | 117,648 | **117,656** | 1.00007 | 82,992 (SL(2,13) × Z19, orbit k = 3, f = 0) | 0.705 |
| (11,7) | 398,580 | **398,582** | 1.000005 | 266,640 (SL(2,11) × Z101, orbit k = 5) | 0.669 |

**All three cells beaten**: (7,7) by 24 vertices, (9,7) by 8, (11,7) by 2.
- The new graphs are not Haar graphs. They are 3 copies of the generalized hexagon H(q) (the table's own
  construction), with m points "unhooked" in all three copies and a 2-vertex gadget per point (§2).
- The bijection φ that links the copies is either explicit (exact covers, §2) or found by local search.

Files in `graphs/`:
- `*.phi`: the bijection φ (one line index per point).
- `*.edges.gz`: the edge lists (apsp.c format: n, then one "a b" per line).
- `*.apsp.txt`: the apsp.c verdicts and the sha256 of the uncompressed edge lists.

To rebuild:
- m = 1 graphs: `python3 hexd7/plus2.py q OUT.edges 1 graphs/<file>.phi`. For q = 9 add `NOGREEDY=1`, otherwise the
  unused greedy cover takes very long.
- m = 4 and 12: `python3 hexd7/plus2.py 5 X.edges` writes X.edges.hfile. Then
  `PHIIN=graphs/d7D7_hex5_plus24.phi plusm X.edges.hfile 12 0 1 OUT.edges` (plusm.c, gadget layout fixed by m).
  This reproduces the edge list byte for byte.
- Then run `apsp OUT.edges q+2 7` (`research/lifts/coordinator_check/apsp.c`: all-pairs BFS, no symmetry assumed).

| cell | n | max degree | diameter | apsp.c | edge-list sha256 |
|---|---|---|---|---|---|
| (7,7), m = 1 | 23,438 | 7 | 7 | RESULT VALID d=7 D=7 n=23438 | debe7e451970a59f790c0e08830bb2232355c071dd7f9a9074e9c4515bdc049e |
| (7,7), m = 1, explicit φ | 23,438 | 7 | 7 | RESULT VALID d=7 D=7 n=23438 | add6ae4a772245fe769826ad801a27c1d719177e75dcf8ab395428a97c74ffbd |
| (7,7), m = 4 | 23,444 | 7 | 7 | RESULT VALID d=7 D=7 n=23444 | 17b756eb35a7d77dd27760c4f601c92b221cc99b6b6c6ce9154fc34e86a828f9 |
| (7,7), m = 12 | 23,460 | 7 | 7 | RESULT VALID d=7 D=7 n=23460 | 2ee0fb8fa2e3258e855e595b8769426fbe8947fc26912e02fb9540d0198eb44a |
| (9,7), m = 1 | 117,650 | 9 | 7 | RESULT VALID d=9 D=7 n=117650 | 94303a1b4845c9112504d773c89fe751b136b6efef320d04242c70c46f555385 |
| (9,7), m = 1, explicit φ | 117,650 | 9 | 7 | RESULT VALID d=9 D=7 n=117650 | 3478bfc0d278f713e7313c71612ba446f74c055339007bc21488ab7837da3cc3 |
| (9,7), m = 4 | 117,656 | 9 | 7 | RESULT VALID d=9 D=7 n=117656 | 4b4eeee82eb417f0ac0b2a9f7e58e9036234e51a2e2c95c159edec14ddcbbf27 |
| (11,7), m = 1, explicit φ | 398,582 | 11 | 7 | RESULT VALID d=11 D=7 n=398582 | 72f859aa243d587ed381cb1519918878f5f0c086872646545bec1d34c8b8ce13 |

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

**An explicit φ (no search needed).** The hexagon has exact covers for (A) and (B).
- Let L1 ≠ L0 be a second line through p. C_A = {lines M : d(p, M) = 5, d(L1, M) = 4} partitions the points opposite
  p, q⁴ lines with q points each.
  - Why: assign to an opposite point z the first line of its unique geodesic to L1 (d(z, L1) = 5). For another
    opposite point z' on that line, the same line starts its geodesic to L1, so the assignment is consistent.
  - Every such M has d(L0, M) = 6, since a path of length 4 from M to L0 would close a cycle of length ≤ 10 through p.
    So C_A avoids B4(L0).
- Dually, let p1 ≠ p be a point of L0. C_B = {points y : d(L0, y) = 5, d(p1, y) = 4} meets every line opposite L0
  exactly once, and C_B avoids B4(p).
- Since q⁴ < |B4| − 1 = (q⁵−1)/(q−1) − 1, φ can map B4(p) − {p} onto C_A plus fillers, and C_B plus fillers onto
  B4(L0) − {L0}, on disjoint domains. Then (A) and (B) hold exactly.
- `hexd7/greedyphi.c` with `EXACT=1` builds this φ and checks exactness and disjointness: 0 violations for q = 3, 5,
  7, 9 (|C_A| = |C_B| = 81, 625, 2,401, 6,561).
- With it the BFS score from a and b is 0 before any search (plus2ls.c: "start score 0") for q = 5, 7, 9. For q = 3
  the graph (n = 2,186, Δ = 5) is RESULT VALID by apsp.c.
- So, for every q for which H(q) exists (all prime powers; built and checked here for odd q), there is a bipartite
  graph of max degree q + 2 and diameter 7 on 6(q⁶−1)/(q−1) + 2 vertices. By the proof, that is 2 more than every
  table entry of the form 3·|H(q)| at D = 7, i.e. (7,7), (9,7), (10,7), (11,7) and (13,7). (7,7), (9,7) and (11,7)
  were built from the explicit φ and checked by apsp.c (q = 5, 7, 9); (10,7) needs q = 8, which hexagon.py does not
  build (even q).

**Finding φ by search (how the first graphs were made).** `hexd7/plus2.py` builds φ from greedy covers for (A) and
(B) on disjoint domains, then fills the rest at random. The greedy covers were slightly too big (843 and 835 for
780 slots at q = 5), so they are truncated.
`hexd7/plus2ls.c` then counts the vertices beyond distance 7 from a and from b by BFS (exact, all routes). It runs a
local search that swaps the images of two points: targeted swaps create a route a → y → φ(y) → t for an unreached
point t, or b → M → φ⁻¹(M) → t for an unreached line t, and the rest are random.

| q | start (vertices missed from a, b) | swaps to 0 | time |
|---|---|---|---|
| 5 | 9 + 6 | 32 | 0.2 s |
| 7 | 165 + 191 | 1,261 | 14 s |

The final graphs were then checked from scratch by apsp.c (all pairs, no symmetry or theory assumed): VALID.

**Several points (`hexd7/plusm.c`).** Unhook m points p_i, each with its own gadget x_i, w_i, for n = 6P + 2m.
- The gadget points are p_1 and points collinear with it (pairwise distance ≤ 4); the gadget lines are a line L* and
  lines meeting it. Then the gadget vertices are within 6 of each other.
- φ starts random (φ(p_i) = L_i). The score is the number of vertices beyond distance 7 from the 4m sources a_i, b_i,
  x_i, w_i, computed by bit-parallel BFS (64 sources per pass). The moves are the same targeted swaps.
- q = 5, m = 4: 23,444 (90 s). m = 12: 23,460 (37,929 moves, 36 s). q = 7, m = 4: 117,656 (26,481 moves, 209 s).
  All RESULT VALID by apsp.c.
- Files: `graphs/d7D7_hex5_plus8.*` and `graphs/d7D7_hex5_plus24.*` (edges.gz, phi, apsp.txt). The m = 12 edge list
  is written by plusm.c directly; rebuild it from the .phi with the same gadget choice.

**Remarks.**
- For more points the conditions of different gadgets compete for the same images of φ. The clustered layout went to
  m = 12 at q = 5 in seconds; m = 16 stalled at score 2 and m = 30 at about 1,200 (stopped).
  - Exact covers for each gadget, plus a sparse network of extra edges between the gadget vertices (they have three
    spare slots), should allow far-apart gadgets. Not tried; it adds only 2/n per point.
- **A route to many more vertices when H(q) is self-dual (q = 3^e, e.g. (11,7) with q = 9; not built).**
  - Let φ be a duality δ: an incidence-preserving bijection points → lines.
  - For a point z opposite p, the line δ⁻¹(z) is within distance 5 of p. Its point y closest to p is within 4 of p,
    and z ∈ δ(y). So (A) holds for every point p at once, and dually (B) for every line, as long as the projection
    points y are not themselves unhooked.
  - So a large set U of points could be unhooked: no two at distance 4, plus gadget-to-gadget distances ≤ 6. The
    gadget vertices have three spare edges each, so they could be wired into their own diameter-6 network (e.g. a
    copy of the incidence graph of H(3)).
  - That might give hundreds of extra vertices at (11,7) and (13,7) (q = 11 is not 3^e, so not (13,7) by this route).
    It needs an explicit duality of H(9).
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

Every run (generated by `rungs.py` from `solo_runs/*.log`; "best cost" 0 = solved, otherwise the run was stopped):

| cell | group | N | 2N | mu | k,m,f | Fix | best cost | evals | s | build_haar2 |
|---|---|---|---|---|---|---|---|---|---|---|
| (7,7) | sl 8 x Z_19 | 9576 | 19152 | 27.7 | 3,2,1 | 8 | 0 | 4.5e+03 | 0 | VALID |
| (7,7) | prod psl 3 sl 5 x Z_7 | 10080 | 20160 | 39.0 | 3,2,1 | 17 | 0 | 3.9e+04 | 0 | VALID |
| (7,7) | sl 4 x Z_169 | 10140 | 20280 | 40.6 | 3,2,1 | 2 | 42 | 2.2e+07 | 221 |  |
| (7,7) | psl 7 x Z_61 | 10248 | 20496 | 43.5 | 3,2,1 | 2 | 6 | 4.9e+07 | 361 |  |
| (7,7) | sl 7 x Z_31 | 10416 | 20832 | 48.2 | 3,2,1 | 5 | 6 | 9.7e+07 | 716 |  |
| (7,7) | sl 7 x Z_31 | 10416 | 20832 | 48.2 | 3,2,1 | 5 | 6 | 2.8e+06 | 21 |  |
| (9,7) | sl 11 x Z_31 | 40920 | 81840 | 27.1 | 3,3,0 | 11 | 0 | 2.9e+03 | 0 | VALID |
| (9,7) | sl 13 x Z_19 | 41496 | 82992 | 30.4 | 3,3,0 | 11 | 0 | 7.0e+04 | 2 | VALID |
| (9,7) | prod psl 3 sl 8 x Z_7 | 42336 | 84672 | 35.8 | 3,3,0 | 26 | 6 | 1.6e+07 | 1500 |  |
| (9,7) | prod psl 3 sl 8 x Z_7 | 42336 | 84672 | 35.8 | 3,3,0 | 26 | 8 | 8.5e+06 | 783 |  |
| (9,7) | sl 7 x Z_127 | 42672 | 85344 | 38.1 | 3,3,0 | 5 | 12 | 7.5e+06 | 232 |  |
| (9,7) | sl 7 x Z_127 | 42672 | 85344 | 38.1 | 3,3,0 | 5 | 12 | 3.1e+07 | 1200 |  |
| (9,7) | prod sl 4 sl 9 | 43200 | 86400 | 42.0 | 3,3,0 | 53 | 12 | 7.3e+06 | 1200 |  |
| (9,7) | sl 9 x Z_61 | 43920 | 87840 | 47.9 | 3,3,0 | 17 | 10 | 4.6e+06 | 156 |  |
| (11,7) | sl 19 x Z_19 | 129960 | 259920 | 25.2 | 3,3,2 | 17 | 0 | 8.1e+03 | 1 | VALID |
| (11,7) | sl 13 x Z_61 | 133224 | 266448 | 31.8 | 3,3,2 | 11 | 0 | 1.1e+05 | 13 | VALID |
| (11,7) | sl 11 x Z_101 | 133320 | 266640 | 32.0 | 5,2,1 | 9 | 0 | 7.2e+03 | 1 | VALID |
| (11,7) | sl 11 x Z_103 | 135960 | 271920 | 38.4 | 3,3,2 | 11 | 6 | 8.2e+06 | 1200 |  |
| (11,7) | sl 9 x Z_191 | 137520 | 275040 | 42.6 | 5,2,1 | 9 | 10 | 8.9e+06 | 1898 |  |
| (11,7) | sl 9 x Z_191 | 137520 | 275040 | 42.6 | 5,2,1 | 9 | 2 | 1.0e+07 | 1800 |  |
| (11,7) | sl 27 x Z_7 | 137592 | 275184 | 42.8 | 3,3,2 | 53 | 4 | 5.7e+06 | 1200 |  |
| (11,7) | sl 5 x Z_1151 | 138120 | 276240 | 44.3 | 5,2,1 | 9 | 252 | 2.0e+05 | 350 |  |
| (11,7) | sl 9 x Z_193 | 138960 | 277920 | 46.8 | 3,3,2 | 17 | 50 | 4.7e+06 | 892 |  |

Observations:

- At D = 7 the low rungs fall in seconds. μ ≈ 25–39 solved in 0.4–13 s. The walls appear at μ ≈ 36–48: runs stall at
  cost 2–12 (fixed points, or one to four uncovered α-orbits). The Haar searches were stopped at 18:15 once the
  hexagon construction (§2) had beaten two cells.
- (7,7) has a small orbit space. With m = 2 orbits there are only about (N/3)² ≈ 10⁷ symmetric S. On SL(2,7) × Z31
  (μ 48.2) the search made 9.7·10⁷ evaluations (several passes over the space) and stayed at cost 6, so very
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

1. **Two extra vertices by a local gadget, φ fixed** (superseded by §2). Delete q+1 edges (a_j, b_j) of the 3-copy
   H(5) graph, add x ~ all a_j, w ~ all b_j, x ~ w: degrees stay ≤ 7 and n = 23,438. `hexd7/violations.c` counts ordered pairs at distance > 7.
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
   This caps the number of copies when every vertex keeps F or L, i.e. for a φ that is not designed around particular
   vertices. With a φ designed for one vertex, the cross edges of the points within distance 4 of it can cover a whole
   copy (q⁴ well-chosen lines through q⁵ points). That is how §2 adds vertices; it does not add a copy.
4. **Other bases.** The construction needs a base of diameter ≤ 6 and degree Δ − 1, and the Moore bound makes H(q) the
   largest. A base of diameter 5 gives only 3 copies (copies c ± 2 are out of reach), e.g. 3 · 1,152 at Δ = 7. A
   generalized quadrangle allows 5 copies at D = 7 (checked by hand, same first/last-step argument), but 5 · |GQ(q,q)|
   ~ 10q³ ≪ 6q⁵. Subgraphs of H(q') for larger q' fail: deleting a vertex of a girth-12 graph puts two of its
   neighbours at distance ≥ 10. A Z3-lift of our (7,6) Haar graph (9,592 vertices) would have 28,776 vertices, but
   the pairs at distance 6 have ~11 geodesics for 3 voltages, so μ ≈ 125 even with a perfect base. Haar graphs cannot
   carry the 3-copy trick either: it needs a (Δ−1, 6) Haar graph near the Moore bound.

**What these show.** Copy designs in which every vertex reaches the other copies by its own or the target's cross edge
are capped at 3·|H(q)|, and so are lifts of the hexagon (with uniform voltages). The +2 of §2 gets past the cap
differently. One point gives up its cross edges; a φ designed around that point (exact covers) plus a 2-vertex gadget
make up for it.

## 6. Budget and time

(filled in at the end)
