# Problem 4, diameter 6 (d6-opus) — REPORT

Status: in progress (last update 2026-10-20 01:30). All five open D = 6 cells beat the table value (Section 3);
(7,6) passed verify_record.py; the (15,6), (16,6) full BFS checks are running (diamp.c, ~1.5 h each).

## 1. Table values (diameter 6)

Source: Combinatorics Wiki, "The Degree Diameter Problem for Bipartite Graphs", table "as of January 2012"
(downloaded 2026-10-19). Open cells are those with Delta-1 not a prime power.

| Delta | q used | table value | Moore bound M_b(Delta,6) | table construction |
|---|---|---|---|---|
| 7  | 5  | 8 992   | 18 662    | Delorme–Farhi duplication |
| 11 | 9  | 142 464 | 222 222   | Delorme–Farhi duplication |
| 13 | 11 | 374 452 | 542 906   | Delorme–Farhi duplication |
| 15 | 13 | 842 048 | 1 158 390 | Delorme–Farhi duplication |
| 16 | 13 | 884 062 | 1 627 232 | Delorme–Farhi duplication |

**Where the table values come from.** Delorme [D85, Sec. 8(b)]: H(q) has q^3+1 pairwise opposite elements
(Thas [T80]; the Hermitian spread). Take A2 = one of them, A1 = A2's neighbours plus the q^3+1 elements, A0 = A1 plus
its neighbours, and "dédoubler" A0, then A1, then A2. His worked example is exactly 7812+912+2(132)+4 = 8992.
In general (checked against all four Delta = q+2 cells):

  table(q+2, 6) = 2(q+1)(q^4+q^2+1) + q^4 + 4q^3 + q^2 + 4q + 10      (q = 5, 9, 11, 13 give 8992, 142464, 374452, 842048).

Delta = 16 is the same with tripling instead of doubling on H(13): 804468 + 2(|A0|-|A1|) + 8(|A1|-1) + 26 = 884062.

## 2. The construction: Delorme's levels plus whiskers

**Level lifts** (a reformulation of [D85, Sec. 7]). G bipartite, levels lev: V -> {-1,0,1,2,...} with
|lev(x)-lev(y)| <= 1 on edges. A vertex of level k gets b^(k+1) versions (strings of length k+1 over b letters);
a level -1 vertex keeps one version (the empty string). (x,a) ~ (y,c) iff x ~ y and one of a, c is a prefix of the other.

- *Degree.* deg(x,a) = deg(x) + (b-1)·#{neighbours of higher level}.
- *Walk lifting.* If W is a walk x = x_0, ..., x_m = y in G with minimum level mu, and a, c agree on their first mu+1
  letters, then (x,a) and (y,c) are joined by a walk of length m (take the prefixes of a padded with zeros up to the
  minimum point, the prefixes of c after it).
- *Diameter lemma.* Let A0 = {lev >= 0}, L = {lev = -1}. If diam G <= D and every two x, y in the same component of
  G[A0] (x = y allowed) have some z in L with d(x,z) + d(z,y) <= D, then the lift has diameter <= D.
  (Pairs with an end in L, or ends in different components of G[A0], use a shortest path, which meets L.)
- Bipartite: the lift of a bipartite graph is bipartite.

**Theorem D.** Let H be a generalized hexagon of order (q,q), q >= 2, S a set of q^3+1 pairwise opposite lines
(for H(q): the Hermitian spread, the H(q)-lines in an elliptic hyperplane section [T80]), v in S, V the lines other
than v meeting v, and C the lines opposite v that are not in S. Let W ⊆ C be a set of lines, no two of which share a
point off the lines of S. Put lev(v) = 2; points of v: 1; V: 0; S - v: 1; points of S - v: 0; W: 0; all else -1.
With b = 2 the lift is a bipartite graph of maximum degree q+2, diameter 6 and order

  2(q+1)(q^4+q^2+1) + q^4 + 4q^3 + q^2 + 4q + 10 + |W|            (|W| = 0 is Delorme's graph).

With b = 3 (tripling) it has maximum degree q+3 and order 2(q+1)(q^4+q^2+1) + G_3 + 2|W|, where G_3 is Delorme's
tripling gain 2(|A0|-|A1|) + 8(|A1|-1) + 26 = 2q^4 + 10q^3 + 2q^2 + 10q + 34 (= 79 594 at q = 13).

*Proof.*
1. *Counting.* A line has q(q+1), q^3(q+1), q^5 lines at distance 2, 4, 6. The balls of radius 2 around the lines of S
   are disjoint (lines of S are pairwise opposite) and have (q^3+1)(q^2+q+1) = N lines in total, so every line not
   in S meets exactly one line of S, in one point. In particular every line of C contains exactly one point of S
   (on a line of S - v) and q points off S, and all its points are at distance 5 from v.
2. *Levels differ by <= 1 on edges, and every vertex has at most one neighbour of higher level.* v: none higher.
   A point u of v: only v. A V-line: only its point on v (its other q points are off S, level -1). s in S - v: its
   points have level 0, none higher. A point p of s: only s (its other lines are in W, or are L-lines). A whisker: its
   S-point has level 0, its other points -1. An L-line: its unique S-point (level 0) is its only A0-neighbour: points
   off S have level -1, and it cannot pass through a point of v (those lines are v and V). A point r off S: its A0
   lines are the lines of V ∪ W through it; two V-lines through r would close a cycle of length <= 6 through v, a
   V-line and a whisker through r would put the whisker at distance <= 4 from v (but whiskers are opposite v), and
   two whiskers through r are excluded. So degrees are deg + (b-1) <= q+b.
3. *Diameter.* The components of G[A0] are C_v = {v, points of v, V} (a tree of radius 2) and, for s in S - v,
   C_s = {s, points of s, whiskers at them}. Every point p of s has an L-line m_p: the unique line through p at
   distance 4 from v (it is neither s, nor in V, nor in C). With r = a point off S on a whisker or V-line, the
   pairs inside one component and their z in L are: (s,s): m_p, 2+2. (s,p): m_p, 1+2. (s,w): r on w, 1+3.
   (p,p'): m_p', 1+3. (p,w'): r on w', 1+4. (w,w'): r on w, 1+5 (a point and a line are at odd distance <= 5).
   (v,v): r, 3+3. (v,u): r on a V-line at u, 2+3. (v,m): r on m, 1+3. (u,u'): r on a V-line at u', 2+4.
   (u,m'): r on m', 1+4. (m,m'): r on m, 1+5. All sums are <= 6 (<= 5 for pairs on opposite sides, as parity
   requires). The diameter lemma gives diameter <= 6; two original points opposite in H have no common neighbour,
   so the diameter is exactly 6. QED

**Partial whiskers when b >= 3 (used for Delta = 16).** The diameter part of the proof never uses the degree
condition, so the b-fold lift has diameter <= 6 for *any* W ⊆ C, overlaps allowed. Give a whisker w a multiplicity
m in {1, ..., b-1}: keep versions w^0, ..., w^(m-1) and identify w^m, ..., w^(b-1) with w^(m-1) (so w^(m-1) is
also joined to p^m, ..., p^(b-1) of its spread point p). The identification is a surjective graph homomorphism from
the full lift, so distances do not grow and the graph stays bipartite; w^(m-1) has degree q+1+b-m <= q+b, and a
free point gains m per whisker through it. So the condition becomes: **a multiset W ⊆ C covering every free point
at most b-1 times**, and the order is 2(q+1)(q^4+q^2+1) + G_b + sum of multiplicities. For b = 3 this is a
2-packing, which can be much larger than twice a packing: at q = 9, 10 265 vs 2 x 4081 = 8162 (annealing, 150 s);
at q = 5, checked by diamp.c on several mixed examples (e.g. 11 557 vertices, degree 8, diameter 6).

**Which lines can be whiskers.** C has q^5 - q^3 lines; every point off S at distance 5 from v ("free point") is on
exactly q lines of C (all its lines except the one toward v). So W is a packing of the q^5 - q^3 free points by lines of C:
- |W| <= q^4 - q^2 (each whisker uses q free points);
- a greedy (maximal) W has |W| >= (q^5-q^3)/(q^2-q+1) > q^3 + q^2 - q - 3, since a line of C conflicts with at most
  q(q-1) others ((q^5-q^3) = (q^2-q+1)(q^3+q^2-q-2) - (q-2)). Hence, **for every prime power q, n_b(q+2,6) >= table + q^3 + q^2 - q - 2
  and n_b(q+3,6) >= Delorme's tripling value + 2(q^3 + q^2 - q - 2).**

**Novelty.** The table values at D = 6 for Delta = 7, 11, 13, 15, 16 are exactly Delorme's 1985 nested duplication
(we rebuilt 8992 edge for edge from his description and it checks). The level-lift reformulation, the observation that
Delorme's construction leaves every free point's spare degree unused, and whiskers are, to our knowledge, new. The
Combinatorics Wiki bipartite table has not changed these cells since 2012; a quick literature search found no later
bipartite D = 6 constructions (compound graphs of Gómez, Pelayo, Balbuena et al. are for the general, non-bipartite
problem).

## 3. Results

| Delta | q | table | ours | over table | perfect-W value | file / how to rebuild | checked |
|---|---|---|---|---|---|---|---|
| 7 | 5 | 8 992 | **9 592** | +600 | 9 592 (reached) | graphs/h5_whisk600_n9592.json | **verify_record.py VALID**; diam.c, diamp.c OK |
| 11 | 9 | 142 464 | **146 545** | +4 081 | 148 944 | `./hexgen 9; ./d6lift 9 2 0 1 out.txt graphs/h9_whisk4081_W.txt` | diam.c OK (max degree 11, diameter <= 6) |
| 13 | 11 | 374 452 | **382 650** | +8 198 | 388 972 | `./hexgen 11; ./d6lift 11 2 0 1 out.txt graphs/h11_whisk8198_W.txt` | diamp.c OK (max degree 13, bipartite, diameter <= 6) |
| 15 | 13 | 842 048 | **856 521** | +14 473 | 870 440 | `./hexgen 13; ./d6lift 13 2 0 1 out.txt graphs/h13_whisk14473_W.txt` | diamp.c OK (max degree 15, bipartite, diameter <= 6) |
| 16 | 13 | 884 062 | **913 008** (b = 3) | +28 946 | 940 846 | `./d6lift 13 3 0 1 out.txt graphs/h13_whisk14473_W.txt` | queued |

"Perfect-W value" = Theorem D with |W| = q^4 - q^2 (b = 3: 2|W| more). Delorme's own graph is rebuilt exactly
(graphs/h5_delorme_n8992.json, 8992, diameter 6), which confirms the reading of [D85].

The q = 9 graph (146 545 vertices) is too large for verify_record.py's Python BFS (days); it was checked with the
bit-parallel C BFS from every vertex (diam.c). The rebuild is deterministic (seed 1 picks the elliptic hyperplane;
graphs/h9_S_seed1.txt lists the spread, first line = v).

**Structure of perfect whisker sets (q = 5).** Every perfect W found leaves exactly q^2 spread lines (besides v)
without whiskers and puts a whisker at every point of the others. The q^2 blocks of the Hermitian unital through v
(block = the q+1 spread lines at distance 3 from a point) carry an affine plane AG(2,q) (the inversive plane derived
at v: three blocks are collinear iff no block avoiding v meets all three). Taking B = the q^2 spread lines on one
affine line of q blocks, the perfect W exists and is found instantly (SAT, CaDiCaL, 0.0 s; annealing 8 s); random
choices of q blocks give at most 570. A perfect W would give n_b(q+2,6) >= 2(q+1)(q^4+q^2+1) + 2q^4 + 4q^3 + 4q + 10 in general.
More structure at q = 5: the q+1 whiskers at an A-line s are exactly the projections of s onto a line t_s opposite s
(the lines through the points of s at distance 4 from t_s); there are q such t_s (with s they form a regulus), all
opposite v, meeting q-1 A-lines and one B-line. **But at q = 7 no perfect W was found**: annealing reaches 1608 of
2352 (68%), min-conflict search with B = affine line stalls at 2105 overcovered points, and CaDiCaL did not finish in
15 min. So perfection may be special to q = 5; we do not conjecture it in general.

## 4. How this answers Problem 4 at diameter 6, and the earlier attempt

- [AL20]'s construction adds a few vertices ("hats") to a Moore graph and rewires. At D = 6 the analogue that works
  is Delorme's nested duplication plus whiskers: the extra vertices are versions of hexagon elements, attached by the
  prefix rule. The research/gh6 and research/d3d6 attempts (point/line copies, stand-ins, hat pairs) stopped at
  8820–8890 on H(5) because they only used copies whose neighbours are originals ("level 0"); each copy then costs
  q+1 spare degrees, so they are capped near 2N/(q+1) and need near-perfect distance-2 ovoids/spreads of H(5), which
  searches never found (505 of 651). Delorme's level-1/level-2 vertices (copies of copies around the Hermitian
  spread) are about twice as efficient per spare degree, and whiskers then use the spare degree of points that
  Delorme leaves idle.
- The Feit–Higman obstruction to an AS(q)-like hexagon is not needed: the level lift works directly on H(q).

## 5. What blocks the rest

- **Perfect whisker sets.** Only q = 5 reaches |W| = q^4 - q^2. At q = 7 (a test case; (9,6) is a Moore cell) the
  best found is 1632 of 2352 (69%; ILS and annealing agree), at q = 9 4081 of 6480 (63%). An upper bound below
  q^4 - q^2 is open (the LP is perfect; the conflict graph's cliques are just the point stars).
- **Verification size.** The Delta = 13, 15, 16 graphs have 0.38–0.94 million vertices; verify_record.py cannot run
  on them. diamp.c (multi-threaded, 256 sources per pass) checks q = 9 in 13 CPU-seconds, so the big ones take
  minutes to tens of minutes; an independent re-check needs another C-speed checker.
- **Level 2 is the ceiling.** A level-k vertex is at distance >= k+1 from L, and the diameter lemma (x = y) needs
  distance <= 3, so levels are <= 2 at D = 6. We did not search level patterns other than Delorme's + whiskers.

## 6. Diameter case list (also in the proof) (component C_s = s, its points p_i, whiskers w at p_i; C_v = v, points u, V-lines m)

Parity: for x, y on opposite sides the bound needed is 5. r denotes a free point on a whisker or V-line.
- (s,s): z at distance <= 3. (s,p): z = an L-line at p (1+2) or r on a whisker at p (2+3). (s,w): r on w (1+3).
- (p,p'): L-line at p' (1+3) or r on a whisker at p' (2+4). (p,w'): r on w' (1+4). (w,w'): r on w (1+5).
- (v,v): r (3+3). (v,u): r on a V-line at u (2+3). (v,m): r on m (1+3). (u,u'): r on m' at u' (2+4).
  (u,m'): r on m' (1+4). (m,m'): r on m (1+5).

## 7. Files
- hexq.py, delorme_q5.py, lift.py, whiskers_q5.py, whisk_ils.py, whisk_greedy.py: Python version for q = 5.
- hexgen.c: H(q) for q = p, p^2 (builds lines from Tits' equations, checks counts). hex/hex_q{q}.bin.
- d6lift.c: Hermitian spread, Delorme levels, whisker annealing, lift output. diam.c: bit-parallel diameter check.

## References
- [D85] C. Delorme, Grands graphes de degré et diamètre donnés, European J. Combin. 6 (1985) 291–302, Sec. 7–8.
- [T80] J. A. Thas, Polar spaces, generalized hexagons and perfect codes, J. Combin. Theory Ser. A 29 (1980) 87–93.
