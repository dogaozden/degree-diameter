# Hats in generalized polygons (Problem 4 of Araujo-Pardo and López)

Agent hats-opus, night of 2026-10-19. Last update 23:45 (saved by the main session from the agent's message; the
harness blocks subagents from writing report files). Code, logs and graphs: research/p4/hats/.

## Short version
- AL's "hat" is a case of Delorme's doubling (dédoublement), Europ. J. Combin. 6 (1985) 291-302, Sec. 7. A hat point is
  the copy of a point X on a line ℓ that is itself copied; the hat is joined to the copy M of ℓ instead of to ℓ.
- Delorme's doubling keeps the diameter if his condition (c) holds. Lemma 2 below: in a generalized n-gon, (c) holds
  exactly when every component of the doubled set is a tree of diameter at most n−2.
- D = 3: only single vertices and flags may be doubled. AL's hats break this, and AL's extra edges are exactly patches
  for the broken pairs (Section 2). That is why D = 3 needs a hand-made gadget.
- D = 4 and 6: no patches are needed. Stars (D = 4) and radius-2 trees (D = 6) can be doubled freely. This is the
  general form of the hat, and Delorme used it in 1985: his table values 346, 1734, 3064, 4946 (D = 4) and 8992,
  142464, 374452, 842048 (D = 6) are such doublings. AL do not cite this paper.
- D = 6, new: Delorme's (7,6) graph plus 600 "whiskers" gives **9592 at (Δ,D) = (7,6)**, against the table value 8992
  (graphs/hex_q5_delorme_whisk600_n9592.json). The whisker set is an exact cover found by ILP in 14 s under an ansatz
  read off the exact solutions at q = 2, 3. Every vertex outside the doubled set then sees exactly one doubled vertex,
  so this is the most this family can give.
- D = 4: no new value. In the natural family (an ovoid of Q(4,q) plus lines meeting only on the ovoid) the optimum at
  q = 5 is exactly 359, the current (7,4) value (ILP, proved).

## 1. Delorme's doubling and the hat lemma
**Doubling.** G a graph, A ⊆ V(G). G^A has vertices V(G) ∪ A′ (A′ a copy of A). Edges: all edges of G; a′b′ for each
edge ab with a, b ∈ A; a′w for each edge aw with a ∈ A, w ∉ A. Delorme also nests levels A0 ⊇ A1 ⊇ …, with gain
|A0| + 2|A1| + 4|A2| + …; we use his level statement as given and check every such graph by computer.

**Lemma 1** (Delorme 1985, Sec. 7, stated there without proof). Let G have diameter ≤ D (D ≥ 2) and maximum degree Δ.
Suppose (b) each vertex outside A has at most one neighbour in A; (c) for all x, y in one component of G[A] (x = y
allowed) some z ∉ A has d(x,z) + d(z,y) ≤ D. Then G^A has maximum degree ≤ Δ+1, diameter ≤ D, order |V(G)| + |A|, and
is bipartite if G is.

*Proof.* a and a′ both have degree deg_G(a); w ∉ A gains at most one edge. Put a′ on a's side. V(G) induces G, and
(V(G)∖A) ∪ A′ induces a second copy of G, so two vertices in a common "sheet" are at distance ≤ D. Only pairs x ∈ A,
y′ ∈ A′ share no sheet. Any x–y walk in G through some z ∉ A runs in the first sheet up to z and in the second after it,
so d(x,y′) ≤ d(x,z) + d(z,y). If x, y lie in different components of G[A], a shortest x–y path leaves A, so
d(x,y′) ≤ D; otherwise use (c). ∎

**Lemma 2** (generalized polygons). G the incidence graph of a generalized n-gon of order (s,t), s, t ≥ 1. Then (c)
with D = n holds iff every component of G[A] is a tree of diameter ≤ n−2.

*Proof.* Only if: suppose a component contains a path P with n−1 edges from x to y (true if it has diameter ≥ n−1 or
a cycle, as cycles have length ≥ 2n). A second x–y walk of length ≤ n−1 would close a cycle shorter than 2n, so P is
the unique shortest path and d(x,y) = n−1. By parity any z with d(x,z) + d(z,y) ≤ n has sum n−1, so z lies on P ⊆ A.
If: let B be a tree of diameter ≤ n−2, x, y ∈ B, P their tree path of length d. Tree leaves have G-degree ≥ 2, so some
vertex of B has a neighbour outside A. Let k be the least B-distance from P to such a vertex u, and z ∉ A a neighbour
of u; then d(x,z) + d(z,y) ≤ d + 2k + 2. If k ≥ 1, every vertex within distance k−1 of P has all neighbours in B, so
from x (and from y; or along two neighbours of x if x = y) one can walk k steps away from P. That gives a path of
length d + 2k in B, so d + 2k ≤ n−2. ∎

So at Δ = q+2, in a generalized n-gon of order (q,q), the doubled set must have components with at most one edge
(n = 3), stars (n = 4), radius-2 trees (n = 6), and each vertex outside it must see at most one doubled vertex.
**This is the general hat lemma.** Random tests agree with it in every trial (test_lemma2.py: 9/9 on Q(4,3), 9/9 on
H(2), including sets that break it).

**Counting bound.** With one level at Δ = q+2, outside vertices see ≤ 1 doubled vertex and a ∈ A has q+1−deg_A(a)
outside neighbours, so q|A| + 2c(A) ≤ 2N (N vertices per side, c = number of components). Equality means every outside
vertex sees exactly one doubled vertex.

## 2. Diameter 3: AL = doubling + patches
In PG(2,q) two doubled points span a line that is outside (sees two) or doubled (a 2-edge path). So a pure doubling at
Δ = q+2 adds at most one point and one line: order 2(q²+q+2).

AL double A0 = {ℓ, A, X_s, AX_s : s ∈ {0,1,a}} (A ∉ ℓ, X_s ∈ ℓ, AX_s = line AX_s), with ℓX_s and A·AX_s parallel
(M0~H_s, Q0~K_s) and X_s·AX_s crossed (H_s~AX_s, X_s~K_s). al_as_doubling.py (q = 5): this has maximum degree q+2 and
18 pairs at distance > 3: (H_s, X_t), (K_s, AX_t) for s ≠ t, (H_s, Q), (K_s, M), exactly those Lemma 2 predicts. AL's
core is this doubling plus 6 edges (H_1K_0, H_0K_1, H_aℓ, AK_a, X_aM, Q·AX_a) minus one (X_a·AX_a). Our fourth hat:
32 broken pairs; the +2 core adds 10 edges (with the rotation) and removes 4.

## 3. Diameter 4
**Delorme's graphs.** In W(3,q) take a spread Σ (lines pairwise at distance 4), A0 = Σ ∪ (points of one v ∈ Σ),
A1 = {v}. Gain q²+q+4, order 2(q+1)(q²+1)+q²+q+4 = the old table values. Dually in Q(4,q): an ovoid O, all q+1 lines
through one o ∈ O, level 2 at o.

**Ovoid family.** A0 = O ∪ M, M a set of lines of Q(4,q) whose non-ovoid points are disjoint (lines may share ovoid
points; ovoid points are star centres). Order 2(q+1)(q²+1) + (q²+1) + |M|.

*Proposition.* If an ovoid point o is on k ≥ 2 lines of M, then |M| ≤ k + (q+1−k)q. Otherwise M is a partial spread.
*Proof.* A line of M not through o has one ovoid point (not collinear with o) and exactly one point collinear with o;
that point is a non-ovoid point on one of the q+1−k lines through o not in M, and different lines of M use different
points. ∎
So |M| ≤ max(q²−q+2, largest partial spread); exact q²+1 would need a spread, impossible for q odd. Delorme's choice is
k = q+1.

q = 5 (ILP, opart2.py, pspread_q5.py): with two lines of M through o forced, the optimum over all 15 pairs at one
ovoid point is 21; with k ≤ 1, the largest partial spread of Q(4,5) is 18. The stabiliser of O is transitive on O, so
**max |M| = 21 and the family's best is 359**, equal to the current (7,4) value (graphs/opart_q5_two_n359.json, VALID).
Beating Theorem A (2q²(q+2)) needs |M| ≥ q²−2q−2: 61, 97, 141 at q = 9, 11, 13 (bounds 74, 112, 158). Earlier partial
spread searches found 52, 72, 92. Search at q = 9 is next. A general star-forest ILP at q = 5 (all doubled sets, with
level 2) is running.

## 4. Diameter 6
**Delorme's graphs.** H(q), S a Hermitian spread (q³+1 pairwise opposite lines), v ∈ S. A2 = {v}, A1 = (points of v)
∪ (S∖v), A0 = A1 ∪ (lines through points of v) ∪ (points of S-lines). Gain q⁴+4q³+q²+4q+10; this equals the table
value at Δ = 7, 11, 13, 15 (8992, 142464, 374452, 842048).

**Whiskers** (also found independently by p4-d6-opus: 9355, 9480, then 9592). Extra level-0 lines, each through a point
of an S-line other than v and opposite v, no two sharing a free point (off S, at distance 5 from v). Free points:
q³(q²−1); so at most q²(q²−1) whiskers, and then the counting bound is tight.

**Exact whiskers** (hex_small.py, whisk_ansatz.py, all graphs VALID by verify_record unless noted):
| q | Δ | Delorme | + whiskers | whiskers | table |
|---|---|---|---|---|---|
| 2 | 4 | 196 | 208 | 12 = max | Moore |
| 3 | 5 | 948 | 1020 | 72 = max | Moore |
| 5 | 7 | 8992 | **9592** | 600 = max | 8992 |

Structure: the S-lines carry the Hermitian unital (block of an off-S point p = the q+1 S-lines met by lines through p;
a 2-(q³+1,q+1,1) design, checked q = 2, 3). In every exact solution the empty S-lines are q blocks through v, and every
other S-line has exactly one whisker at each point. At q = 3 exactly 12 of the 84 triples of blocks through v work,
namely those no other block meets in all three. At q = 5 we took 5 blocks through v met by every other block in ≤ 2 of
them, and the exact cover was found at once. In PG(2,q²) terms this looks like a Baer subpencil at v containing the
tangent (conjecture). If it holds for all q: n_b(q+2,6) ≥ 2(q+1)(q⁴+q²+1) + 2q⁴+4q³+4q+10, which would beat the
table at Δ = 11, 13, 15 by q²(q²−1).

## 5. Novelty
- Doubling with levels and its use on GQs and hexagons: Delorme 1985. Lemma 1 is his (we add a proof). Lemma 2 and the
  AL = doubling + patches reading: we have not seen them.
- 9592 at (7,6): new as far as we know (table 8992 is Delorme 1985). Whiskers were found in parallel by p4-d6-opus; the
  exact-whisker ansatz and unital structure are from this folder.
- D = 4: no new value. The proposition and the q = 5 optimum are new but small.

## 6. Next
q = 5 general star-forest ILP; q = 9 ovoid family search; a proof or explicit form of exact whiskers for all q.
