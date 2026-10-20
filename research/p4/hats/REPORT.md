# Hats in generalized polygons (Problem 4 of Araujo-Pardo and López)

Agent hats-opus, night of 2026-10-19/20. Last update 01:45 (v3; saved by the main session from the agent's message).
Code, logs, graphs: research/p4/hats/.

## Short version
- AL's "hat" is a case of Delorme's **doubling** (dédoublement; Europ. J. Combin. 6 (1985) 291-302, Sec. 7). A hat point
  is the copy of a point X on a line ℓ that is itself copied, joined to the copy M of ℓ instead of to ℓ.
- **Lemma 2:** in a generalized n-gon, Delorme's diameter condition holds iff every component of the doubled set is a
  tree of diameter ≤ n−2. So D = 3 allows only single vertices and flags (hence AL's patch edges), D = 4 allows stars,
  D = 6 allows radius-2 trees. This is the general hat lemma.
- Delorme's own table values at D = 4 (346, 1734, 3064, 4946) and at D = 6 (8992, 142464, 374452, 842048 for
  Δ = q+2; 884062 for Δ = 16 with 3-ary levels) are such doublings. AL do not cite this paper.
- **D = 6, new theorem (Theorem 4).** For every odd prime power q, Delorme's hexagon doubling extends by an exact set
  of q²(q²−1) "whiskers", given by an explicit formula. So n_b(q+2,6) ≥ 2(q+1)(q⁴+q²+1) + 2q⁴+4q³+4q+10 and
  n_b(q+3,6) ≥ 2(q+1)(q⁴+q²+1) + 4q⁴+10q³+10q+34. At the q²(q²−1) maximum every vertex outside the doubled set sees
  exactly one doubled vertex, so this is the most the family gives.
- Table cells (D = 6), each beaten:

  | (Δ,6) | q | table (= Delorme) | new | gain | check |
  |---|---|---|---|---|---|
  | (7,6) | 5 | 8992 | **9592** | 600 | verify_record VALID |
  | (11,6) | 9 | 142464 | **148944** | 6480 | 2 C checkers + main session's bigcheck |
  | (13,6) | 11 | 374452 | **388972** | 14520 | 2 C checkers + bigcheck |
  | (15,6) | 13 | 842048 | **870440** | 28392 | bigcheck VALID (main session); agents' checks running |
  | (16,6) | 13 (3-ary) | 884062 | **940846** | 56784 | C checks running |

- **D = 4.** No new value. In the natural family (an ovoid of Q(4,q) plus lines meeting only on the ovoid) the optimum
  at q = 5 is exactly 359, the current (7,4) value (proved by ILP). At q = 9 the best found gives 1778 < 1782 (Theorem A).

## 1. Doubling with levels, and the hat lemma
**Doubling.** G a graph, A ⊆ V(G): G^A has V(G) ∪ A′; edges: all of G, a′b′ for edges ab inside A, a′w for edges aw
with w ∉ A. **Levels** (Delorme): A0 ⊇ A1 ⊇ …; a vertex of level k (in A_k∖A_{k+1}) gets m^{k+1} versions, strings of
length k+1 over an m-letter alphabet; a vertex outside A0 has one version (empty string); versions x^a, y^b are
adjacent iff xy ∈ E(G) and one string is a prefix of the other. m = 2 is Delorme's doubling, m = 3 his tripling.

**Theorem 1** (Delorme 1985, Sec. 7, stated without proof; our proof). G bipartite, diameter ≤ D (D ≥ 2), maximum
degree Δ. Suppose (a) for i ≥ 0, N(A_{i+1}) ⊆ A_i and each vertex of A_i∖A_{i+1} has ≤ 1 neighbour in A_{i+1}; (b) each
vertex outside A0 has ≤ 1 neighbour in A0; (c) for all x, y in one component of G[A0] (x = y allowed) some z ∉ A0 has
d(x,z)+d(z,y) ≤ D. Then the levelled graph is bipartite, has maximum degree ≤ Δ+m−1, diameter ≤ D, and order
|V| + (m−1)(|A0| + m|A1| + m²|A2| + …).

*Proof.* A version of x of level k sees one version of each neighbour of level ≤ k and m^{j−k} versions of a neighbour
of level j > k; by (a),(b) x has at most one neighbour of higher level, of level k+1, so the degree rises by ≤ m−1.
Sheets: for each infinite string σ, the versions whose strings are prefixes of σ induce a copy of G. Two versions share
a sheet iff one string is a prefix of the other; then they are at distance ≤ D. Otherwise both underlying vertices are
in A0; a walk from x to y through some z ∉ A0 (one version, in every sheet) runs in a sheet of x^a up to z and in a
sheet of y^b after it. If x, y lie in different components of G[A0], a shortest path leaves A0; otherwise use (c).
Versions keep the side, so the graph is bipartite. The order is a telescoping sum. ∎

**Lemma 2.** G the incidence graph of a generalized n-gon of order (s,t), s, t ≥ 1. Then (c) with D = n holds iff
every component of G[A0] is a tree of diameter ≤ n−2.

*Proof.* Only if: a component containing a path P with n−1 edges (it has one if its diameter is ≥ n−1 or it has a
cycle, as cycles have length ≥ 2n): P is the unique shortest path between its ends (another walk of length ≤ n−1 would
close a cycle shorter than 2n), so d(x,y) = n−1, and by parity any z with d(x,z)+d(z,y) ≤ n lies on P ⊆ A0. If: B a
tree of diameter ≤ n−2, x, y ∈ B, P their tree path, |P| = d. Leaves of B have G-degree ≥ 2, so some vertex of B has
a neighbour outside A0; let k be the least B-distance from P to such a vertex u, z ∉ A0 adjacent to u:
d(x,z)+d(z,y) ≤ d+2k+2. If k ≥ 1, all vertices within k−1 of P have all neighbours in B, so from x and from y (along
two neighbours if x = y) one walks k steps away from P, giving a path of length d+2k in B; so d+2k ≤ n−2. ∎
Random tests agree (test_lemma2.py: 9/9 on Q(4,3), 9/9 on H(2), including violating sets).

**Counting bound.** One level at Δ = q+2 in a (q+1)-regular bipartite graph with N vertices per side:
q|A0| + 2c(A0) ≤ 2N; equality iff each outside vertex sees exactly one vertex of A0.

## 2. Diameter 3: AL = doubling + patches
In PG(2,q), two doubled points span a line that is outside (sees two) or doubled (a 2-edge path); so a pure doubling at
Δ = q+2 adds at most a point and a line: 2(q²+q+2). AL double A0 = {ℓ, A, X_s, AX_s : s ∈ {0,1,a}} with ℓX_s and A·AX_s
parallel (M0~H_s, Q0~K_s) and X_s·AX_s crossed (H_s~AX_s, X_s~K_s). al_as_doubling.py (q = 5): maximum degree q+2 and 18
pairs at distance > 3, namely (H_s,X_t), (K_s,AX_t) (s ≠ t), (H_s,Q), (K_s,M), as Lemma 2 predicts. AL's core = this
doubling + 6 edges (H_1K_0, H_0K_1, H_aℓ, AK_a, X_aM, Q·AX_a) − 1 edge (X_a·AX_a). Our fourth hat: 32 broken pairs; the
+2 core adds 10 edges (including the rotation) and removes 4.

## 3. Diameter 4
Delorme's graphs = W(3,q), spread Σ, A0 = Σ ∪ points(v) (v ∈ Σ), A1 = {v}: gain q²+q+4 (dually an ovoid O of Q(4,q)
and all lines through one o ∈ O).
**Ovoid family.** A0 = O ∪ M with M lines of Q(4,q) whose non-ovoid points are pairwise disjoint; order
2(q+1)(q²+1)+q²+1+|M|.
*Proposition.* If o ∈ O lies on k ≥ 2 lines of M then |M| ≤ k + (q+1−k)q ≤ q²−q+2; otherwise M is a partial spread.
(A line of M not through o has exactly one point collinear with o, a non-ovoid point on one of the q+1−k lines through o
outside M; distinct lines use distinct points.)
q = 5 (ILP, proved): two lines through o forced → optimum 21 over all 15 pairs at one ovoid point; largest partial
spread of Q(4,5) is 18; the stabiliser of the elliptic quadric is transitive on it. So max |M| = 21 and the family's
best is **359** (graphs/opart_q5_two_n359.json, VALID) = the current (7,4) value. A general star-forest ILP at q = 5
(all doubled sets, with level 2) also found 359 (bound 60 not closed in 50 min). Beating Theorem A needs
|M| ≥ q²−2q−2 = 61, 97, 141 (q = 9, 11, 13); ILS reached 56 at q = 9 (1778 < 1782). Any single-level doubling of a
GQ(q,q) at Δ = q+2 has gain < 2q²+2q, so it can beat Theorem A by at most about 4q.

## 4. Diameter 6
**Delorme's graphs.** Model: Q(x) = x0x4+x1x5+x2x6−x3² on PG(6,q), H(q) via Tits' equations (as
research/gh6/gh_build.py). v = ⟨e1,e6⟩; Π: L(x) := x0 + c x4 = 0 with −c a non-square; S = H(q)-lines in Π (a
Hermitian spread: q³+1 pairwise opposite lines). A2 = {v}, A1 = {v} ∪ points(v) ∪ (S∖v), A0 = A1 ∪ (lines through
points of v) ∪ (points of S-lines). Gain q⁴+4q³+q²+4q+10 (m = 2), equal to the table at Δ = 7, 11, 13, 15; with m = 3
at q = 13 it gives the table's 884062 at Δ = 16.

**Theorem 3 (whiskers).** Call a point free if it is off Π and at distance 5 from v; there are q³(q²−1). Let W be lines,
each opposite v and not in S, with no free point on two of them. Adding W at level 0 keeps (a), (b), (c) (components:
v's radius-2 ball; each S-line with its points and its whiskers). So
n_b(q+m,6) ≥ 2(q+1)(q⁴+q²+1) + (m−1)(|A0| + |W| + m|A1| + m²). |W| ≤ q²(q²−1), with equality iff every free point is
on exactly one line of W ("exact").
(p4-d6-opus found whiskers independently by search: 9355, 9480 at q = 5.)

**Theorem 4 (exact whiskers for every odd q).** Let ν(x) = (x2x3 − x4x5)/(c x2² + x5²). For z = (α,β) ≠ 0 let
Π_z: x0 + c x4 + α x2 + β x5 = 0 and S_z its H(q)-lines. Choose c0, c1 with G(a,b) = (c0a + c1b)(a² + cb²) − b³ ≠ 0 on
GF(q)²∖0, and put F(z) = G(z)/(α² + cβ²). Then W = {m ∈ S_z∖{v} : z ≠ 0, ν(m ∩ Π) = F(z)} is exact.

*Proof.*
1. Π_z has pole (c, β, 0, 0, 1, 0, α) with Q = c, like Π, so Π_z ∩ Q is elliptic (Witt index 2) and contains no
   totally singular plane. For y ∈ Π_z ∩ Q the H(q)-lines through y are the lines through y of the totally singular
   plane π_y ⊄ Π_z, so exactly one of them lies in Π_z: S_z is a spread of Π_z ∩ Q, contains v, and its lines are
   pairwise opposite (a line meeting two of them would lie in Π_z). S ∩ S_z = {v}, since on an S-line ≠ v the map
   x ↦ (x2:x5) is bijective (Π ∩ Q ∩ {x2 = x5 = 0} = v, as c x4² + x3² is anisotropic).
2. The points of the planes π_w, w ∈ v, satisfy x2 = x5 = 0 (direct from the equations), and the off-Π points of Q with
   x2 = x5 = 0 number q²(q+1), the number of points at distance 3 from v. So a free point p has (p2,p5) ≠ 0. Normalise
   L(p) = 1. Then p ∈ Π_z iff z lies on the affine line A_p: αp2 + βp5 = −1 (q values), and for each such z exactly
   one S_z-line passes through p; these q lines are distinct (a line in Π_z ∩ Π_z′ through p would have (x2:x5)
   constant, so would meet v).
3. Closed-form identity (proof/verify_closed.py, verify_closed2.py; polynomial identities with integer coefficients, so
   valid in every odd characteristic): for z ∈ A_p the Π-point X(z) of that line satisfies
   ν(X(z)) + β³/(α²+cβ²) = an affine function of z on A_p whose slope per step (p5, −p2) is −p2³/(c p2² + p5²).
   (Chart p5 ≠ 0: the function is −(p2³p5 s + p2² − p2p3p5 + p4p5²)/(p5(cp2²+p5²)) at z = (s p5, −1/p5 − s p2); chart
   p5 = 0: (p2 s + p3)/(c p2) at z = (−1/p2, s). All denominators are nonzero at free points.)
4. Hence the line of S_z through p is in W iff that affine function equals c0α + c1β. The difference is affine on A_p
   with slope −p2³/(cp2²+p5²) − (c0p5 − c1p2), which vanishes iff G(p5, −p2) = 0. G has no zeros, so the difference
   has exactly one root: p is on exactly one line of W. ∎

Such c0, c1 exist for every odd q: (c0 ≠ 0, c1) is bad iff c0α + c1 = 1/(α²+c) for some α, a union of q lines each with
q−1 points with c0 ≠ 0; the lines for α = 0 and α = 1 meet at c0 = −1/(c(1+c)) ≠ 0, so the union misses a point.
Computation agrees: exact iff G has no zero, for q = 3, 5, 7 (2, 6, 14 pairs) (whisk_cubic.py).

**How it was found.** Exact solutions by ILP at q = 2, 3, then an ansatz (q blocks of the Hermitian unital through v
stay empty, one whisker per point elsewhere), then invariance under a group of order q²(q−1) (q+1 point orbits, solves in
seconds for q = 5, 7, 9, 11, 13), then the observation that the whiskers split into pieces of the q²−1 spreads S_z, then
the class function F.

## 5. Verification
- verify_record VALID: 9592 (7,6); 359, 346 (7,4); 98 (5,4); 208, 196, 162 (4,6); 1020, 948, 868 (5,6).
- Large graphs: independent C checkers — research/p4/d6/diam.c (compiled as hats/diam), hats/tools/check_big.c (simple
  graph, BFS 2-colouring, max degree, own bit-parallel diameter; agrees on 9592 and fails it at D = 5), and the main
  session's research-lab/verify/bigcheck (written without seeing the agents' code; exact diameter by BFS from every
  vertex): VALID on 148944, 388972, 870440. q = 9: the built H(9) is the degree-10 diameter-6 Moore graph. Graphs are
  rebuilt from whisker JSONs (whiskers_big_q{q}.json) by hexbig.py / hexbig_gf.py ... build [--load] [--arity=3]; the
  fast H(q) builder matches gh_build's H(5) exactly. Python verify_record is too slow above ~10^4 vertices.

## 6. Novelty
- Doubling with levels on GQs and hexagons: Delorme 1985 (Theorem 1 is his; the proof is ours). Lemma 2, the AL =
  doubling + patches reading, Theorem 4 and the exact whisker construction: not seen elsewhere. Whiskers as such were
  found in parallel by p4-d6-opus.
- To our knowledge the five D = 6 values above beat the current table (all table entries there are Delorme 1985).
- D = 4: no new value; the proposition and the q = 5 optimum are small new facts.

## 7. Files
lift.py, opart*.py, pspread_q5.py, delorme_ilp.py, opart_ils.py (D = 4); hex_small.py, whisk_ansatz.py, whisk_sym*.py,
hexbig.py, hexbig_gf.py, build_hex_whisk.py, whisk_cubic.py, whisk_spread2.py, whisk_kappa.py, whisk_formula.py,
whisk_phi.py (D = 6); proof/identity*.py, proof/verify_closed*.py (symbolic); test_lemma2.py; al_as_doubling.py;
tools/check_big.c; g2_gens.py, g2_roots.py, ks_params.py (G2 root elements).
