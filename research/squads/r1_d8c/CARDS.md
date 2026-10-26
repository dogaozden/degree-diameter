# Round 1 cards (own-d8-compound, 2026-10-26)

Every card: read research/squads/r1_d8c/CONTEXT.md first. Folder research/squads/r1_d8c/cN/. Score = largest m with
exact COST 0 at Delta = q+3 (unless the card says otherwise). Time box about 25 minutes.

## c1 Pair-sheet permutation lift (literal count hypothesis)
Sheets at element e (point or line, any level): two plain sheets A, B, plus one sheet per pair in a fixed pairing of
the q+1 neighbours of e (q odd: (q+1)/2 pairs). Hexagon edge (p, L): A->A, B->B; the pair at p containing L <-> the pair
at L containing p; the other (q-1)/2 pairs at p <-> the other pairs at L by a rule (try: (a) order pairs by the index
of their smaller member and match in order; (b) a fixed random bijection per flag; (c) your own). Then 5 levels with
two matchings p -> phi(p) at levels +1, +2 (try phi random and phi = identity-index map), with sheet maps A->A, B->B,
pairs->pairs by index. Build the explicit graph (k = 2 + (q+1)/2 sheets per element per level, m = 5k copies' worth
of vertices) and check with gcheck D=8 (sources: one level suffices if the construction is level-invariant; say so).
q = 3 (k = 4) then q = 5 (k = 5). Report the cost and, if not 0, which (source, target) classes fail.

## c2 Flags as vertices (odd q: per level = flags + 2 copies of points + 2 copies of lines)
Vertex count fits 5*(#flags + 4N) for odd q. Invent adjacency rules on V = Z5 x (F u P1 u P2 u L1 u L2) with max
degree q+3, bipartite, using the geometry (flag (p,L) adjacent to p and/or L in some copies, plus level matchings), and
test diameter 8 with gcheck at q = 3 (|F| = 1456, N = 364). Enumerate a small family of rules systematically (at
least 20 rules), report the best cost and the rule. Even a rule that reaches diameter 8 at q = 3 with this vertex
count is a strong lead (then test q = 5).

## c3 The one-matching test bed (Delta = q+2)
Table (13,8) = 15*|I(H(11))| with ONE extra matching. If the construction scales down: m = 6 at q = 5 (Delta = 7),
m = 9 at q = 7. One random matching with random Z_m voltages fails already at m = 5 (q = 5, cost 1,178). Find ANY
valid design at q = 5 with one matching (degree 7) and m = 5 or 6 copies (lift by Z_m or D_n with glift; any
voltages on hexagon edges allowed). Suggested: SAT with pysat on a reduced model (voltages invariant under a
symmetry you construct, e.g. a cyclic subgroup of G2(5) acting semiregularly), or a targeted repair search
(pick an uncovered (source, target, sheet), re-voltage one edge of a short walk to cover it). Report the best m and
the structure of the voltages you found (are hexagon voltages a coboundary? which values occur?).

## c4 Multiplicative coordinate voltages (a geometric cover of I)
For each line L fix two of its points e_L, f_L with fixed representative vectors; for p on L write the normalized
vector of p as alpha e_L + beta f_L and give the flag (p, L) the voltage log_g(alpha/beta) in Z_{q-1} (g a primitive
root; p = e_L or f_L get the special values 0 or a chosen constant) or its image in a quotient Z_d, d | q-1.
First measure the cover alone: for 200 random pairs of opposite points (and of opposite lines), how many distinct
voltages do the q+1 geodesics carry (bundle diversity), against random voltages. Then use these hexagon voltages in
lifts Z_5 x Z_d (levels +1, +2 on two random matchings, glift with "Z 5d" and voltage = level + 5*sheet via CRT or
direct) at q = 5 (d = 2, 4) and q = 7 (d = 2, 3, 6). Score: largest valid m.

## c5 A duality as the matching (q = 3^e), aiming at q = 9
For q = 3^e, H(q) has dualities delta (points <-> lines preserving incidence). Build delta for q = 3 and q = 9 with
the lab's research/d10D7/dual/dualfind.c (on master: `git show origin/master:research/d10D7/dual/dualfind.c >
dualfind.c`; it needs hex/hex_q9.bin from hexgen2). Use the matchings p -> delta(p) and p -> delta^-1(p) (or delta
twice with levels +1, +2), with voltages in Z_m chosen by a geometric rule (coordinates, distance to a fixed
element, ...). With a duality every route is geometric, so a rule can be checked by thought. Screen at q = 3 (random
already reaches 16+ there, so look for structure that scales), then test q = 9 with glift sampled sources
(r:200:1) at m = 36 (36*132,860 = 4,782,960 > table 4,650,100 at (12,8)). Report the best sampled q = 9 cost.

## c6 Bundle-rainbow hexagon voltages by SAT (q = 3)
Find hexagon voltages in Z_k (k = 4, then 5, 6) on I(H(3)) such that for EVERY pair of opposite elements (points and
lines) the q+1 = 4 geodesics carry 4 distinct voltages (abelian sums with sign by direction point->line +,
line->point -). Encode with pysat (one-hot voltage per flag, pairwise-distinct constraints on geodesic sums via
auxiliary variables, or a CEGAR loop that adds violated bundles). Fix a spanning tree to 0 (gauge). If found, inspect
the structure (is it invariant under a subgroup? a coordinate formula?) and test it in a lift Z_5 x Z_k (two random
matchings, levels +1, +2) with glift at q = 3.

## c7 Twisted Z_10 lemma: 10 levels for free, times k sheets
The Z_10 lemma: zero hexagon voltages, two arbitrary matchings with voltages 1 and 4 in Z_10 give diameter 8. Lift
further by K = Z_k (group Z_10 x Z_k = Z_10k when gcd = 1, or D_n) with K-voltages on hexagon edges and matchings.
Try structured K-voltages: (a) at each vertex the q+1 edges carry each value of a set {+a, -a} pairs (pair idea), (b)
coordinates, (c) annealing restricted to K-part with exact cost. q = 3 (k = 2: m = 20, k = 3: m = 30) and q = 5
(k = 2, 3: m = 20, 30). Report the best and which pairs fail.

## c8 Typed copies: identity hops between H-type and D-type copies plus one arbitrary matching
Copies have a type: in an H-copy points are black, in a D-copy lines are black. Type-preserving hops join an element
e of an H-copy to the SAME element e of a D-copy (bipartite since types swap); type-changing hops join point p to line
sigma(p) between copies of the same type. Give every element one type-preserving hop and one type-changing hop.
With type-preserving hops, routes p ~> u -> u' ~> w are geometric (u on the q+1 geodesics between p and w). Choose
the copy offsets of hops from a geometric rule (e.g. a "pencil coordinate" c(u) = [b(a,u) : b(a',u)] in PG(1,q) for two
fixed vectors a, a', mapped to Z_n) and test with glift (group D_n: H-copies = rotations, D-copies = reflections, or
your own encoding) or gcheck at q = 4, 5. Score: largest m.

## c9 The untwisted bound, made concrete: pencil-rainbow colourings (one matching first)
Opus derived: with zero hexagon voltages and ONE matching sigma with voltages e(p) in Z_m, a point p reaches the
copies {0, e(p)} u {-e(sigma^-1(l)) : l through p} (all full: every line of those copies within distance 7). Colour
each line l by c(l) = -e(sigma^-1(l)). If the lines through every point carry q+1 distinct colours from Z_m \ {0}
(m = q+3, palette of q+2 colours) and e(p) = the colour missing at p, then every point reaches all of Z_m: m = q + 3
copies at Delta = q+2. Counting forces every colour class to have N/(q+2) lines, so this needs (q+2) | N(q): true for
q = 5 (7 | 3906, classes of 558). Build it at q = 5: (1) a colouring of the 3906 lines of H(5) with 7 colours such that
concurrent lines get different colours and every class has 558 lines (pysat: one-hot per line, at-most-one per colour
per pencil; cardinality via pysat.card or repair afterwards; or look for a symmetric solution: an automorphism of
order 7 or 21 of H(5) acting on the lines); (2) e(p) := the missing colour at p; (3) sigma maps the points with
e(p) = c bijectively to the lines with colour -c... check the sign convention with the definitions above; (4) check
with glift (group Z 8, one matching, Delta 7) all sources. Random one-matching lifts fail already at m = 5, so m = 8 is
a real structured result. Then: (5) two matchings (Delta = q+3 = 8): palettes A1, A2 with A_t = -A_t, e.g. Z_14 with
A1 = {7, +-1, +-2, +-3}, A2 = {7, +-4, +-5, +-6}: m = 14; push to 15-17 using the other walk families.

## c10 Hermitian spread voltages
H(q) has a Hermitian spread S: q^3+1 pairwise opposite lines; every line not in S meets exactly one line of S; every
point is on a line of S or at distance 3 from exactly one. (Lemma 1.2(b) of research/theorems/D7_HEXAGON.md on branch
claude/d7-hexagon-theorems-4w1prt: the lines of H(q) inside a hyperplane meeting Q(6,q) in an elliptic Q-(5,q).)
Construct S for q = 5 (find a hyperplane whose section is elliptic: e.g. test random hyperplanes, count lines
inside = q^3+1). Define structured hexagon voltages from S (e.g. a flag's voltage depends on whether its line is in S,
meets S, and on the position of its point relative to the spread line), and matchings from S (e.g. points of a spread
line matched among themselves by a rule). Test lifts at q = 5 with glift. Score: largest m.

## c11 Lifting the D7 graph: what fails, exactly
Take the D7 level graph G7 (5 levels, doubled random phi, cross distance <= 7) and lift it by Z_k (k = 2, 3, 4, 5)
with Z_k voltages on the hexagon edges ONLY (matchings 0). Anneal the hexagon voltages with exact cost at q = 5
(glift with group Z_5k: voltage = 5*h on hexagon flags... careful with CRT; or Z_5 x Z_k as Z_{5k} with k coprime
to 5: hexagon voltage 5h, matchings 1 and 2*... use the CRT map). Report the best m and a breakdown of uncovered
targets by (level difference, hexagon distance). The question: are the near targets (distance 1, 3) the obstacle?

## c12 Hub surgery at D = 8 (the "improve" step)
Theorem 3.4 of research/theorems/D7_HEXAGON.md (branch claude/d7-hexagon-theorems-4w1prt): free some matching edges
and attach hub vertices. Do it at D = 8 on a design that is valid with slack: the Z_10 lemma graph (zero hexagon
voltages, matchings with shifts 1, 4) at q = 3 and q = 5. Find the largest set of matching edges whose deletion keeps
diameter <= 8, attach new vertices (each joined to freed slots, degree <= q+3) keeping diameter 8 (gcheck all), and
report vertices gained as a fraction of 10*|I|. This measures what surgery can add to a DGQ-size graph.

## c13 Additive projective-parameter voltages with GEOMETRIC base points (q prime)
For a line L choose two base points e_L, f_L by a geometric rule (not the storage order): e.g. e_L = the point of L
nearest to a fixed point a (unique unless L is opposite... handle ties by a second reference), f_L = the point nearest
to a second fixed element b. For p on L write p = e_L + t f_L (normalized), t in GF(q) u {inf}, and give flag (p, L)
the voltage t (additive group Z_q for prime q; inf -> a chosen value). Note: a voltage that depends only on p (or
only on L) is a coboundary and useless; this one depends on the flag. The lab tried t with base points in storage
order, taken mod m != q ("random-like"); here K = Z_q exactly and the frame is geometric. Combine with Z5 levels
(+1, +2 on two matchings) in Z_{5q}: at q = 7, k = 7 gives m = 35 > 30 (table). Screen q = 3 (Z_15) exact, then
q = 7 sampled (glift r:200:1), report the best m and bundle diversity of the cover.

## c14 Wildcard A
Find an approach none of the other cards uses (c1 pair sheets, c2 flag vertices, c3 one matching, c4 multiplicative
voltages, c5 duality, c6 SAT bundle-rainbow, c7 twisted Z10, c8 typed identity hops, c9 pencil-rainbow untwisted, c10
Hermitian spread, c11 lifting D7, c12 hub surgery, c13 field-additive, c15/c16 wildcards). Ideas: non-regular graphs
(vertices of degree < q+3 allowed: max degree counts), other bases (dual hexagon, H(q) minus a structure plus
gadgets), products with small graphs of diameter 2. Score at q = 5 (Delta = 8): largest vertex count with diameter 8
divided by |I(H(5))| = 7,812, compared with 25.

## c15 Wildcard B: invert the problem
Instead of guessing the construction, measure it: for the table graph, each (point, target line, copy) needs a walk
of length <= 7. Write a tool that, for a given base with matchings and a CANDIDATE voltage rule, lists for random
(p, y) pairs the guaranteed walk families and the distinct voltages they produce; then search the space of "rules"
(formulas in a few parameters: affine maps of coordinates, pencil coordinates, discrete logs) for the rule that
maximises the minimum number of distinct voltages over sampled pairs. Report the best rule and test it with glift at
q = 5 (m = 25) and q = 7 (m = 30, sampled).

## c16 Wildcard C: q = 4 and q = 8 (even q)
Even q gives k = q/2 + 2 (q = 4: k = 4, m = 20; q = 8: k = 6, m = 30 = table (11,8)). In characteristic 2 the
quadric's polar form is alternating and H(q) has extra structure (the Artin-Schreier map x -> x^2 + x is 2-to-1 onto
the trace-0 elements: q/2 values!). Look for a construction where sheets correspond to orbits of x -> x + 1 on GF(q)
or to Tr = 0 elements, on H(4) (Delta 7, m = 20; random lifts first to calibrate). Score: largest m at q = 4.
