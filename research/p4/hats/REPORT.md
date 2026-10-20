# Hats in generalized polygons (Problem 4 of Araujo-Pardo and López)

Agent hats-opus, night of 2026-10-19/20. Last update 00:50 (v2; saved by the main session from the agent's message).
Code, logs, graphs: research/p4/hats/.

## Short version
- AL's "hat" is a case of Delorme's **doubling** (dédoublement; Europ. J. Combin. 6 (1985) 291-302, Sec. 7). A hat point
  is the copy of a point X on a line ℓ that is itself copied; it is joined to the copy M of ℓ instead of to ℓ.
- Lemma 2: in a generalized n-gon, Delorme's diameter condition holds exactly when every component of the doubled set
  is a tree of diameter at most n−2. So D = 3 allows only single vertices and flags (hence AL's patch edges); D = 4
  allows stars; D = 6 allows radius-2 trees. This is the general hat lemma.
- Delorme's own table values at D = 4 (346, 1734, 3064, 4946) and D = 6 (8992, 142464, 374452, 842048) are such
  doublings. AL do not cite this paper.
- **D = 6, new.** Delorme's hexagon graph plus an exact set of q²(q²−1) "whiskers" (extra doubled lines) gives order
  2(q+1)(q⁴+q²+1) + 2q⁴+4q³+4q+10. Exact whisker sets exist for q = 2, 3, 5, 7, 11 (and q = 13 is running). This
  beats the table at
  - (7,6): **9592** vs 8992 (graphs/hex_q5_delorme_whisk600_n9592.json, **verify_record VALID**);
  - (13,6): **388972** vs 374452 (q = 11; C checkers only, see Section 5).
  At the q²(q²−1) maximum every vertex outside the doubled set sees exactly one doubled vertex, so this is the most
  this family can give.
- **D = 4.** No new value. In the natural family (an ovoid of Q(4,q) plus lines meeting only on the ovoid) the optimum
  at q = 5 is exactly 359, the current (7,4) value (proved by ILP). A general star-forest ILP at q = 5 also found 359
  (bound 60 not closed). At q = 9 the best found gives 1778 < 1782 (Theorem A).

## 1. Doubling, levels, and the hat lemma
**Doubling.** G a graph, A ⊆ V(G). G^A has vertex set V(G) ∪ A′; edges: all edges of G, a′b′ for each edge ab inside A,
a′w for each edge aw with w ∉ A. **Levels** (Delorme): A0 ⊇ A1 ⊇ … ; a vertex of level k (in A_k∖A_{k+1}) gets 2^{k+1}
versions indexed by binary strings of length k+1, a vertex outside A0 one version (empty string); versions x^a, y^b
are adjacent iff xy is an edge and one of a, b is a prefix of the other. Single doubling = only A0.

**Theorem 1** (Delorme 1985, Sec. 7, stated without proof; our proof). Let G be bipartite with diameter ≤ D, D ≥ 2,
maximum degree Δ. Suppose (a) for each i ≥ 0, N(A_{i+1}) ⊆ A_i and each vertex of A_i∖A_{i+1} has at most one
neighbour in A_{i+1}; (b) each vertex outside A0 has at most one neighbour in A0; (c) for all x, y in one component of
G[A0] (x = y allowed) some z ∉ A0 has d(x,z)+d(z,y) ≤ D. Then the levelled graph is bipartite, has maximum degree
≤ Δ+1, diameter ≤ D, and order |V| + |A0| + 2|A1| + 4|A2| + ….

*Proof.* Degrees: a version of x of level k is adjacent, for each neighbour y, to one version of y if lev(y) ≤ k, and to
2^{lev(y)−k} versions if lev(y) > k. By (a), (b), x has at most one neighbour of higher level, and it has level k+1; so
the degree goes up by at most 1. Sheets: for each binary sequence σ, the versions whose strings are prefixes of σ (one
per vertex) induce a copy of G. Two versions lie in a common sheet iff one string is a prefix of the other; then their
distance is ≤ D. Otherwise x^a and y^b have strings that first differ at some position, so x, y ∈ A0. A walk from x to
y through z ∉ A0 runs in sheet σ ⊇ a up to z (z has one version, in every sheet) and in sheet σ′ ⊇ b afterwards. If
x, y are in different components of G[A0], a shortest x–y path leaves A0; otherwise use (c). Bipartite: versions keep
the side of the vertex. Order: telescoping sum. ∎

**Lemma 2** (generalized polygons). G the incidence graph of a generalized n-gon of order (s,t), s, t ≥ 1. Then (c)
with D = n holds iff every component of G[A0] is a tree of diameter ≤ n−2.

*Proof.* Only if: a component with a path P of n−1 edges (it has one if its diameter is ≥ n−1 or it has a cycle, as
cycles have length ≥ 2n): P is the unique shortest path between its ends x, y (a second walk of length ≤ n−1 would
close a cycle shorter than 2n), so d(x,y) = n−1; by parity any z with d(x,z)+d(z,y) ≤ n lies on a shortest x–y path,
i.e. on P ⊆ A0. If: B a tree of diameter ≤ n−2, x, y ∈ B, P the tree path, |P| = d. Tree leaves have degree ≥ 2 in G,
so some vertex of B has a neighbour outside A0; let k be the least B-distance from P to such a vertex u, z ∉ A0 a
neighbour of u: d(x,z)+d(z,y) ≤ d+2k+2. If k ≥ 1, all vertices within k−1 of P have all neighbours in B, so from x and
from y (from x along two neighbours if x = y) one walks k steps away from P; this gives a path of length d+2k in B, so
d+2k ≤ n−2. ∎
Random tests agree (test_lemma2.py: 9/9 trials on Q(4,3), 9/9 on H(2), including sets that violate it).

**Counting bound.** Single level at Δ = q+2 in a (q+1)-regular bipartite graph with N vertices per side:
q|A0| + 2c ≤ 2N (c = number of components); equality iff every outside vertex sees exactly one vertex of A0.

## 2. Diameter 3: AL = doubling + patches
In PG(2,q) two doubled points span a line that is outside (sees two) or doubled (a 2-edge path); so a pure doubling at
Δ = q+2 adds at most a point and a line: 2(q²+q+2). AL double A0 = {ℓ, A, X_s, AX_s : s ∈ {0,1,a}} with ℓX_s and A·AX_s
parallel (M0~H_s, Q0~K_s) and X_s·AX_s crossed (H_s~AX_s, X_s~K_s). al_as_doubling.py (q = 5): maximum degree q+2 and 18
pairs at distance > 3, namely (H_s,X_t), (K_s,AX_t) (s ≠ t), (H_s,Q), (K_s,M), as Lemma 2 predicts. AL's core = this
+ 6 edges (H_1K_0, H_0K_1, H_aℓ, AK_a, X_aM, Q·AX_a) − 1 edge (X_a·AX_a). Our fourth hat: 32 broken pairs; the +2 core
adds 10 edges (including the rotation) and removes 4.

## 3. Diameter 4
**Delorme's graphs** = W(3,q), spread Σ, A0 = Σ ∪ (points of one v ∈ Σ), A1 = {v}: gain q²+q+4 (dually: ovoid O of
Q(4,q), all lines through one o ∈ O).
**Ovoid family.** A0 = O ∪ M, M lines of Q(4,q) whose non-ovoid points are pairwise disjoint (stars centred at ovoid
points). Order 2(q+1)(q²+1)+q²+1+|M|.
*Proposition.* If o ∈ O lies on k ≥ 2 lines of M then |M| ≤ k + (q+1−k)q ≤ q²−q+2; otherwise M is a partial spread.
*Proof.* A line of M not through o has exactly one point collinear with o; it is a non-ovoid point on one of the q+1−k
lines through o not in M, and distinct lines use distinct points. ∎
q = 5: with two lines through o forced, the optimum over all 15 pairs at one ovoid point is 21; the largest partial
spread of Q(4,5) is 18 (both ILP, proved optimal); the stabiliser of the elliptic quadric is transitive on it. So
**max |M| = 21, order 359** (= current (7,4) value; graphs/opart_q5_two_n359.json VALID). Delorme's 346 is k = q+1.
Beating Theorem A needs |M| ≥ q²−2q−2 = 61, 97, 141 (q = 9, 11, 13); found 56 at q = 9 (ILS, 10 min) → 1778.
**General star forests at q = 5** (delorme_ilp.py, all doubled sets incl. level 2): 359 found, bound 60 after 50 min
(not closed). Upper bound for any single-level doubling of a GQ(q,q) at Δ = q+2: gain < 2q²+2q.

## 4. Diameter 6
**Delorme's graphs.** H(q), S a Hermitian spread (q³+1 pairwise opposite lines; the lines of H(q) in a hyperplane
X0 + cX4 = 0, −c a non-square), v ∈ S. A2 = {v}, A1 = {v} ∪ points(v) ∪ (S∖v), A0 = A1 ∪ (lines through points of v)
∪ (points of S-lines). Gain q⁴+4q³+q²+4q+10 = exactly the table values at Δ = 7, 11, 13, 15.

**Theorem 3 (whiskers).** Let W be lines, each opposite v, not in S (so each meets exactly one S-line, at a point of an
S-line ≠ v), such that every point off S at distance 5 from v ("free" point) lies on at most one line of W. Adding W at
level 0 keeps (a), (b), (c) (components: v's radius-2 ball, and each S-line with its points and whiskers, radius 2).
So n_b(q+2,6) ≥ 2(q+1)(q⁴+q²+1) + q⁴+4q³+q²+4q+10 + |W|. There are q³(q²−1) free points, so |W| ≤ q²(q²−1); at
equality the level-0 doubling is perfect (every outside vertex sees exactly one A0 vertex).
(p4-d6-opus found whiskers independently: 9355, 9480 at q = 5.)

**Exact whiskers.** S carries the Hermitian unital (block of an off-S point p = the q+1 S-lines met by lines through p;
2-(q³+1, q+1, 1) design, checked). Exact solutions (ILP) have this shape: q blocks through v stay empty, every other
S-line has exactly one whisker at each point. At q = 3, exactly 12 of 84 triples of blocks through v work: those no
other block meets in all three (an AG(2,3)). The working q-sets look like a Baer subpencil at v containing the tangent
(conjecture). Symmetric reduction: solutions exist that are invariant under K ⋊ ⟨τ⟩, |K| = q² (unipotent elements of
G2(q) fixing v, S, E; K_S = {x1(a) x2(b) x3(s) x4(cb) x5(−2a/c)} in our root coordinates), τ = diag(1,g,1/g,1,1,1/g,g),
g primitive. Then the exact cover has only q+1 point orbits with q−1 choices each, and solves in seconds.

| q | Δ | Delorme | + exact whiskers | whiskers | table | check |
|---|---|---|---|---|---|---|
| 2 | 4 | 196 | 208 | 12 | Moore | VALID |
| 3 | 5 | 948 | 1020 | 72 | Moore | VALID |
| 5 | 7 | 8992 | **9592** | 600 | 8992 | VALID (verify_record) |
| 7 | 9 | 41076 | 45428 | 2352 | Moore | C checker |
| 11 | 13 | 374452 | **388972** | 14520 | 374452 | two C checkers (diam.c; research-lab bigcheck VALID, exact diameter 6) |
| 13 | 15 | 842048 | 870440 if exact | 28392 | 842048 | running |
| 9 | 11 | 142464 | 148944 if exact | 6480 | 142464 | needs GF(9); code ready (hexbig_gf.py) |

Conjecture: exact whisker sets exist for every odd q.

## 5. Verification
- verify_record VALID: 9592 (7,6); 359, 346 (7,4); 98 (5,4); 208, 196, 162 (4,6); 1020, 948, 868 (5,6).
- Large graphs (q ≥ 7): Python checkers are far too slow. C checks: research/p4/d6/diam.c (bit-parallel, compiled as
  hats/diam) and the agent's separate tools/check_big.c (simple graph, BFS 2-colouring, max degree, bit-parallel
  diameter; agrees on 9592 and correctly fails D = 5); plus the main session's independently written
  research-lab/verify/bigcheck (q = 11: VALID, exact diameter 6). Each graph is rebuilt from a small whisker JSON
  (whiskers_big_q{q}.json) by hexbig.py; the fast H(q) builder matches gh_build's H(5) line set exactly.

## 6. Novelty
- Doubling with levels on GQs and hexagons: Delorme 1985. Theorem 1 is his; the proof is ours. Lemma 2 and the
  AL = doubling + patches reading: not seen elsewhere.
- Whiskers: found in parallel by p4-d6-opus; exact whisker sets, the unital structure, the symmetric reduction and the
  q = 7, 11 results are from this folder. To our knowledge 9592 and 388972 beat the current table values (8992,
  374452 are Delorme 1985).
- D = 4: no new value; the proposition and the q = 5 optimum are small new facts.

## 7. Next
q = 13 (running), q = 9 (GF(9) version), and a proof of exact whiskers for all q.
