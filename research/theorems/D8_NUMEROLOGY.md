# The unexplained D = 8 numbers (job thm-d8table, 2026-10-24 and 2026-10-25)

Branches `claude/d8-numerology-ocg3xq` (first session, Oct 24) and `claude/d8-table-numerology-mi6but` (resumed
session, Oct 25; it carries the first session's commits). Every script and its saved output is in
`research/theorems/d8/` (named per item). "Table" is the DS14v2 bipartite table (research/frontier/TABLE.md).
|GH(q)| = 2(q^6−1)/(q−1) is the order of the incidence graph of the split Cayley hexagon H(q) (built with
research/evenq/hexq.py, cached for q = 2, 3, 4, 5, 7, 8, 9, 11). The green D = 8 cells are credited on the wiki to
Delorme, Gómez and Quisquater (DGQ), "On large bipartite graphs", submitted, never found (research/lifts LITERATURE.md
on branch claude/voltage-lifts-search-6lfotq). A lift of H(q) "with j matchings and M copies" means: add j perfect
matchings from points to lines ("hops", degree q+1+j) and take an M-fold voltage lift; it has M·|GH(q)| vertices.

## Short answer

1. **The construction behind the numbers was not found** (two sessions, three squad rounds, 24 Haiku strategies).
2. **Which cells are still unexplained and unbeaten.** Since the first session our group searches beat (11,8) (by 0.5%),
   (13,8) and (15,8) (README). The four DGQ cells still standing are (10,8), (12,8), (14,8), (16,8): M·|GH(q)| with
   Δ = q+3 and **M = 5(q+5)/2 for q = 7, 9, 11, 13** (all odd q).
3. **The numbers, exactly** (§2.1, `numerology.py`): (Δ,8) = M·|GH(q)|, Δ = q+3, M = 5·⌊(q+5)/2⌋ = 5(⌊Δ/2⌋ + 1) for
   q = 7, 8, 9, 11, 13, and (13,8) = 15·|GH(11)| with Δ = q+2. For odd q this is |V(X)| + |E(X)| where X is DGQ's own
   diameter-7 graph at the same degree (the Z_5 polygon cover). Because DGQ entered their best value in every cell,
   the table also caps what their construction gives at other (q, j); for one matching M = q + 4 fits every cap,
   while the REGULARITIES formula 3⌊(q−1)/2⌋ breaks the cap at q = 13 (unless it needs q ≡ 3 mod 4).
4. **What is special about DGQ's numbers is their growth, not their size (new, §2.2–2.3).** At small q, plain
   optimization passes DGQ's formula: 25 copies at q = 3 and 22 at q = 4 (formula 20 at both), all checked by an
   all-pairs BFS; at q = 5 and q = 7 it reaches 20 (formulas 25 and 30), and at q = 9 random symmetric lifts give 16
   (formula 35). The number of short walks
   between a point and a line is about 250–310 for every DGQ cell, nearly independent of q, and generic lifts get one
   copy per 13–20 walks, while DGQ's M = 5(q+5)/2 grows linearly and uses one copy per 7–8.6 walks. So DGQ's
   construction must use walk families whose size grows with q (lines through a point, points on a line, the q+1
   geodesics between opposite elements), in a coordinated way.
5. **Proved:**
   - (§1.1) The zero-voltage "n+2 cover" with j constant-voltage matchings has diameter ≤ n+2 whenever a
     sum/difference set covers Z_M. The largest M is 4, 10, 16, 26, 38 for j = 1, ..., 5 (REGULARITIES had j = 2).
   - (§1.2) A list of "guaranteed walks" present in every lift of H(q) plus matchings, and a count showing that a
     regular zero-holonomy labelling covered by those walks alone has at most q + 4 copies (one matching). With two
     matchings the same method gives 1 + 2(q+1)(q+4)/(q−3), which stays above DGQ's values up to q = 17.
   - (§1.3) A spectral lemma: H(q) admits no "nearly rainbow" equitable labelling missing fewer than √q classes.
     It kills the tight designs, including one whose arithmetic picks out exactly q = 11 and M = 15, the (13,8) cell.
   - (§1.4, new) An exact count of the two-hop walks that a "polygon cover × Z_K" lift (the reading
     5·⌊(q+5)/2⌋ = |Z_5| · K of the numerology) can use for its Z_5-class 0: on average 12–16 per point–line pair at
     distance 3 for any matchings that are not close to dualities, so for large q such a lift needs near-dual
     matchings. In the table range the multi-hop walks still add tens per pair, so the reading is not excluded; at
     q = 3 it gives K = 5 (25 copies, more than DGQ's formula) after annealing.
   - (§1.5, new) With one matching, zero holonomy and regular labels, the tight value q + 4 cannot be certified by
     guaranteed walks for any q ≥ 11 (Theorem 2), so the bound of §1.2 drops to q + 3 there; for q = 7, 8, 9 the
     same holds when each point and line misses exactly one residue (Theorem 1). Both are spectral inequalities on the
     incidence matrix of H(q). So DGQ's (13,8) = (q+4)·|GH(11)| needs walks or holonomy beyond §1.2, or labels
     that repeat around a point or a line.
6. **No table cell beaten.**

---

## 1. Proved

### 1.1 The n+2 cover with j matchings (`sumdiff.py` → `sumdiff_out.txt`, `sumdiff_check.py` → `sumdiff_check_out.txt`)

*Statement.* Let B be a bipartite graph with equal colour classes A (points), A' (lines) and diameter at most n,
n even. Take j perfect matchings s_1, …, s_j from A to A', and lift B ∪ s_1 ∪ … ∪ s_j by Z_M with voltage 0 on B and
t_k on s_k (a point p in copy g is joined to s_k(p) in copy g + t_k). Put

  S(T) = {0} ∪ {±t_k} ∪ {t_k − t_l : k ≠ l} ∪ {t_k + t_l : k ≤ l}.

If S(T) = Z_M, the lift has diameter at most n + 2, whatever the matchings are.

*Proof.* In B, a point and a line are at distance ≤ n − 1 and two elements of the same colour at distance ≤ n.
From a point x in copy 0 to a line y in copy g (an odd walk of length ≤ n+1 is needed): g = 0 by a geodesic;
g = t_k by x → s_k(x) then a geodesic (line to line, ≤ n); g = −t_k by x → b → s_k^{-1}(b) for any line b ∋ x
then a geodesic (point to line, ≤ n − 1); g = t_k − t_l by x → s_k(x) → s_l^{-1}(s_k(x)) then a geodesic
(≤ n − 1); g = t_k + t_l by x → s_k(x), a geodesic from the line s_k(x) to the point s_l^{-1}(y) (≤ n − 1), then the
hop to y. Each walk has length ≤ n + 1. A line to a point is the reverse walk with voltage negated, so it needs
−S(T) = Z_M, which holds. Two points (even walk of length ≤ n + 2) and two lines are covered by the same walks with
one more step, and additionally by −(t_k + t_l) (x ⇝ s_k(a), the hop back to a, a step to the line s_l(y) ∋ a,
the hop back to y). ∎

*Largest M* (exhaustive over T, `sumdiff_out.txt`):

| j | counting bound 1 + 2j + j(j−1) + j(j+1)/2 | largest M | T (up to units) |
|---|---|---|---|
| 1 | 4 | 4 | {1} |
| 2 | 10 | 10 | {1, 4} |
| 3 | 19 | 16 | {1, 4, 7}, {1, 4, 10} |
| 4 | 31 | 26 | {1, 5, 8, 12} |
| 5 | 46 | 38 | {1, 12, 24, 30, 33} |

Each case was checked with liftdiam on H(3) and two random matchings: diameter ≤ 8 (`sumdiff_check_out.txt`).
**No table cell is beaten**: the multiplier is a constant, while DGQ's grows with q; with our D = 6 records as base
it is also below the table everywhere (e.g. 10·148,944 at (13,8) against 5,314,680).

### 1.2 Guaranteed walks in a lift of H(q) plus matchings

Let H = H(q) (or any bipartite graph with point–line distances ≤ 5, line–line and point–point ≤ 6), s_1, …, s_j
bijections points → lines, Γ an abelian group, and lift with voltage φ on the H-edges and t_k(p) on the hop at p.
Write l_k(L) = t_k(s_k^{-1}(L)). For a point x and a line y the following walks of length ≤ 7 always exist:

| walk | voltage when φ = 0 |
|---|---|
| geodesic x ⇝ y | 0 |
| x → s_k(x) ⇝ y | t_k(x) |
| x → b → s_k^{-1}(b) ⇝ y, any line b ∋ x | −l_k(b) |
| x ⇝ s_k^{-1}(y) → y | l_k(y) |
| x ⇝ s_k(a) → a → y, any point a ∈ y | −t_k(a) |
| x → s_k(x) ⇝ s_m^{-1}(y) → y | t_k(x) + l_m(y) |
| x → s_k(x) → s_m^{-1}(s_k x) ⇝ y (k ≠ m) | t_k(x) − l_m(s_k x) |
| x ⇝ s_m(s_k^{-1} y) → s_k^{-1}(y) → y (k ≠ m) | l_k(y) − t_m(s_k^{-1} y) |

That is 2q + 6 walks for j = 1 and 4q + 17 for j = 2 (more when s_k(x) is opposite y or x is opposite s_k^{-1}(y),
because those pairs have q + 1 geodesics). Two points or two lines have many more (at least (q+1)^2), so point–line
pairs are the binding case. All other walks ("conditional" walks) exist or not depending on where the matchings put
things. The unreached targets that liftdiam finds in random lifts (`unreached_profile.py`) are where this table
predicts: point–line pairs at H-distance 5 (zero holonomy) and at H-distance 3 or 5 (random holonomy).

**Counting consequence (zero holonomy, one matching).** Call a labelling *regular* if the lines through any point
carry pairwise different labels and so do the points on any line. If the guaranteed walks alone cover Z_M for every
point–line pair of a regular labelling, then M ≤ q + 4 (q ≥ 3).

*Proof.* Lines with the same label are pairwise non-concurrent, so a label sits on at most P/(q+1) lines (P = number
of points); the same holds for points. A label g is missed at a point x by the x-side terms {t(x)} ∪ −l(lines on x)
unless t(x) = g or a line on x has label −g, so at least P − n_g − (q+1)n_{−g} points miss it (n_v = number of points,
equivalently of lines, with label v); the same holds for lines. If a point x and a line y both miss g, the only walk
left is t(x) + l(y) = g; this forces all such points to share one label and all such lines to share one label, so
either every point or every line covers g, or n_g + (q+1)n_{−g} ≥ qP/(q+1). Summing over the M − 1 nonzero g, with
Σ_g (n_g + (q+1)n_{−g}) = (q+2)P, gives (M − 1)·q/(q+1) ≤ q + 2. ∎

Non-regular labellings are not covered by this count (constant labels give the n+2 cover with M = 4).

**Counting consequence (zero holonomy, two matchings)** (`j2bound.py` → `j2bound_out.txt`). If both labellings
t_1, t_2 are regular and the guaranteed walks alone cover Z_M for every point–line pair, then
M ≤ 1 + 2(q+1)(q+4)/(q−3) (q ≥ 4).

*Proof.* For g ≠ 0 let A_g be the points x with g ∉ X(x), where X(x) = {t_1(x), t_2(x), t_1(x) − l_2(s_1 x),
t_2(x) − l_1(s_2 x)} ∪ {−l_k(b) : b ∋ x, k = 1, 2} (the walks that depend on x only), and B_g the lines y with
g ∉ Y(y), defined in the same way. As above, |A_g| ≥ P − α_g with α_g = Σ_k (n^k_g + (q+1)n^k_{−g}) + c_g, where n^k_v
is the number of points with t_k = v (≤ P/(q+1) by regularity) and c_g counts the points with t_1(x) − l_2(s_1 x) = g
plus those with t_2(x) − l_1(s_2 x) = g; likewise |B_g| ≥ P − β_g with d_g in place of c_g. For x ∈ A_g and y ∈ B_g
only the four walks t_k(x) + l_m(y) are left, so the 2-sets S_x = {g − t_1(x), g − t_2(x)} and T_y = {l_1(y), l_2(y)}
must meet. Suppose both A_g and B_g are non-empty and fix T_0 = {a, b}. Every S_x contains a or b. If every S_x
contains a (or every S_x contains b), each x ∈ A_g has t_1(x) or t_2(x) equal to g − a, so |A_g| ≤ 2P/(q+1).
Otherwise some S_1 contains a but not b and some S_2 contains b but not a; every T_y meets both, so l_1(y) lies in the
set S_1 ∪ S_2 of at most 4 values and |B_g| ≤ 4P/(q+1). In every case max(α_g, β_g) ≥ P − 4P/(q+1). Summing
max(α_g, β_g) ≤ Σ_k (n^k_g + (q+1)n^k_{−g}) + c_g + d_g over the M − 1 nonzero g gives
(M − 1)(q − 3)/(q + 1) ≤ 2(q + 4). ∎

The bound is 45, 44, 44, 46, 48 at q = 7, 8, 9, 11, 13, above DGQ's 30, 30, 35, 40, 45; DGQ's formula passes it only
from q = 19 on. So, unlike the one-matching case, counting does not show that DGQ needs holonomy or conditional walks
anywhere in the table range. (An earlier draft called a heuristic version "2q + 15" and suggested it did; that was
wrong.)

### 1.3 A spectral obstruction (`spectrum_check.py` → `spectrum_check_out.txt`)

The incidence matrix of H(q) has singular values q + 1, √(3q), √q and 0 (checked numerically for q = 2, 3).

*Lemma.* Split the points of H(q) into classes P_1, …, P_m and the lines into L_1, …, L_m so that every point of P_i
lies on exactly A_ij ∈ {0, 1} lines of L_j and every line of L_j contains exactly A_ij points of P_i, where every row
and every column of A has exactly r zeros, 0 < r < m/2. Then r ≥ √q.

*Proof.* Double counting gives |P_i| = |L_j| whenever A_ij = 1, and the class graph is connected (r < m/2: any two rows share a column of ones), so all classes have
the same size and the partition is equitable with quotient [[0, A], [A^T, 0]]; its eigenvalues ± (singular values of
A) are eigenvalues of the incidence graph. A = J − X with X a 0/1 matrix with r ones in each row and column, a sum of
r permutation matrices, so on the vectors orthogonal to the all-ones vector A acts as −X with norm ≤ r. If r < √q
these singular values must all be 0, so X is a constant matrix there, impossible for a 0/1 matrix with 0 < r < m ones
per row. ∎

*Use.* Push the counting of §1.2 to equality (M = q + 4, one matching): each point then sees every nonzero label on
its lines except two, each line sees every label on its points except two, and the conditions force the excluded
labels to come from a permutation e of the nonzero residues with e(e(d)) = −d − e(d), i.e. a partition of the nonzero
residues mod q+4 into zero-sum triples (and elements of order 3). If the excluded labels depend only on the label
("equitable form"), the label classes have equal size, so (q+3) divides P. Among the prime powers up to 13,
(q+3) | P holds only for q = 4 and q = 11, and the triple partition exists only for q = 11 (mod 15:
{1,2,12}, {3,4,8}, {6,11,13}, {7,9,14}, plus 5 and 10). **So the tight design singles out exactly the (13,8) cell,
with M = 15 = q + 4.** But here r = 2 < √11, so by the lemma it does not exist. The M = q + 3 design (r = 1) dies the
same way. Guaranteed walks alone cannot produce DGQ's numbers in any equitable form; the coincidence at q = 11 remains
unexplained.

---

### 1.4 Class-0 walks in a "polygon cover × Z_K" lift (`class0.py` → `class0_out.txt`)

REGULARITIES §2.1 suggested reading M = 5·⌊(q+5)/2⌋ as Z_5 × Z_K: the Z_5 polygon cover (diameter 7, flags carry 0,
hop s_k carries k) lifted once more by Z_K, K = ⌊(q+5)/2⌋. Here is what such a lift must do.

*Setting.* Y is a lift of H(q) + s_1 + s_2 by Z_5 × B (B any group) whose Z_5-coordinate is the polygon cover. Take a
point x and a line y with d(x,y) = 3. To reach the |B| copies (y, (0, b)) within 7 steps, Y needs |B| base walks of
length ≤ 7 from x to y with Z_5-voltage 0 and different B-voltages. Since the hop voltages are ±1, ±2, a reduced
base walk has Z_5-voltage 0 only if it is (a) the geodesic, (b) a *cancelling* walk with exactly two hops, of the same
matching in opposite directions: x ⇝ u → s_k(u) ⇝ s_k(w) → w ⇝ y, or the same with lines (x ⇝ b → s_k^{-1}(b) ⇝ ...),
or (c) a walk with three or more hops (e.g. voltages 1 + 2 + 2). Every H(q)-segment of such a walk has length ≤ 5 and
is a geodesic (girth 12). So |B| ≤ 1 + c_2(x,y) + c_3(x,y) for every such pair, with c_2, c_3 the numbers of walks
of types (b) and (c).

*Identity.* Summed over the P·q²(q+1) pairs at distance 3,

  Σ c_2 = Σ_k Σ_{u ≠ w} ( [d(s_k u, s_k w) = 2] g_2(d(u,w)) + [d(s_k u, s_k w) = 4] g_4(d(u,w)) ) + (the same for lines),

with g_2(2) = 3q² − q, g_2(4) = 3q − 1, g_2(6) = 2(q+1), g_4(2) = q, g_4(4) = 1, g_4(6) = 0 (count the pairs (x, y) at
distance 3 with d(x,u) + d(s_k u, s_k w) + d(w,y) ≤ 5; for instance, when d(s_k u, s_k w) = 4 the walk is forced to
start at x = u and end on a line y through w). `class0.py` checks the identity against a direct enumeration of all
walks at q = 3 (two seeds, and one duality) and q = 4.

*Consequence.* A bijection s_k sends a pair of points at distance d to lines at distance 2 or 4. If it does so at the
rate of a random bijection, the average of c_2 over the pairs is

  4(q+1)(3q³ + 4q² + 2q − 1)/(q⁴ + q³ + q² + q + 1) = 16.1, 15.4, 14.1, 13.7, 13.4, 13.2 at q = 3, 4, 7, 9, 11, 13

(→ 12; measured 16.1 and 15.4 at q = 3, 4; the smallest per-pair value was 4 at q = 3). Only the term
g_2(2) = 3q² − q grows with q, so c_2 can grow with q only if s_k maps a positive fraction of the collinear pairs of
points to concurrent lines, i.e. s_k is close to a duality, which exists only for q = 3^h (at q = 3, replacing one of
the two random matchings by a duality raises the average of c_2 to 30 and the per-pair minimum from 4 to 22).

The walks of type (c) are not negligible in the table range. `class0_nbw.py` counts all non-backtracking walks of
length ≤ 7 from (x, 0) to (y, 0) in the Z_5 cover itself (an upper bound for K at each pair): for random matchings the
mean over pairs at distance 3 is 45, 35, 30, 24 at q = 3, 4, 5, 7 and the minimum 23, 14, 12, 3 (q ≥ 4 sampled). Each
three-hop pattern contributes O(1/q), but there are many patterns. So counting alone does not exclude K = 6–9 for
q ≤ 13; it shows that the class-0 walks are few (tens per pair, against K ≈ q/2) and must be coordinated, and that
K cannot exceed about 13 for large q without near-dual matchings.

*The other classes.* With zero holonomy, the guaranteed walks of §1.2 reach the Z_5-classes +1 and +2 only through
τ_1(x), λ_1(y) and the two composites (class +1: four values) and τ_2(x), λ_2(y), τ_1(x) + λ_1(y) (class +2: three
values). So a polygon cover × Z_K certified by guaranteed walks has K ≤ 3; DGQ's K = 6–9 needs flag holonomy (the
q+1 geodesics between opposite elements then give rich families t_k(x) + G(s_k x, y)) or walks that depend on the
matchings, in three of the five classes (0, +1, +2); only the classes −1 and −2 have rich guaranteed families
(the q+1 lines through x and the q+1 points on y).

*Experiments.* At q = 3 the reading works beyond DGQ's value: annealing (qanneal2.c) the Z_K parts of a polygon
cover × Z_K lift with random matchings gives K = 5, a valid lift with 25 copies (18,200 vertices,
`calib/q3_polycover_Z5xZ5_M25.txt`, checked by apsp), while K = 6 and 7 stay at 298 and 2,224 unreached pairs; with
these matchings the smallest c_2 is 4, so K = 6 would need multi-hop walks at the worst pairs. Squad card c2 kept
random hop labels and designed only the flag voltages; that fails already at K = 3 for q = 4 and 5. At q = 4 the
annealed polygon cover × Z_4 reaches DGQ's value exactly (20 copies, 54,600 vertices,
`calib/q4_polycover_Z5xZ4_M20.txt`, checked by apsp); Z_5 × Z_5 at q = 4 (25 copies) stayed at 3,194 unreached pairs after 13 minutes.

### 1.5 No tight one-matching design: q ≥ 11 in general, q ≥ 7 for one-miss labels (`tight_j1.py` → `tight_j1_out.txt`, `tight_j1_robust.py` → `tight_j1_robust_out.txt`)

§1.2 shows that one hop matching, zero holonomy and regular labels give M ≤ q + 4 if only guaranteed walks are used,
and §1.3 kills the tight case M = q + 4 when the label classes are equitable. DGQ's (13,8) value is exactly
(q + 4)·|GH(q)| at q = 11, so the non-equitable case matters. Theorem 1 closes it for q ≥ 7 under one natural
assumption; Theorem 2 drops the assumption for q ≥ 11.

*Setting.* M = q + 4; labels t on points, l on lines, same distribution (n_c points and n_c lines with label c;
automatic, since l(y) = t(s^{-1}(y))),
regular (distinct on the lines through a point and on the points of a line), every point–line pair covered by
{0, t(x), l(y), t(x) + l(y)} ∪ X(x) ∪ Y(y) with X(x) = {t(x)} ∪ −l(N(x)), Y(y) = {l(y)} ∪ −t(N(y)). *One-miss*: X(x)
consists of q + 2 distinct nonzero residues for every point (so it misses exactly one nonzero residue e(x)), and Y(y)
likewise misses exactly one f(y).

*Theorem 1.* For q ≥ 7 there is no such design.

*Proof.* (i) Structure. The lines through x carry exactly the labels Z_M* \ {−e(x), −t(x)}, once each; the points on
y carry Z_M* \ {−f(y), −l(y)}. Counting flags with line label d gives (q+1)n_d = P − a_{−d} − n_{−d}, where
a_g = #{x : e(x) = g}; the line side gives the same with b_g = #{y : f(y) = g}, so a_g = b_g. If a_g > 0, take x with
e(x) = g and y with f(y) = g: the only walk left for the residue g is t(x) + l(y), so t is constant (= α_g) on
P_g = {x : e(x) = g}. Hence a_g ≤ n_{α_g} ≤ P/(q+1).
(ii) Two identities. Let N be the point–line incidence matrix, u_d, w_c the indicators of the lines with label d and of
the points with label c, π_g and λ_g those of P_g and L_g = {y : f(y) = g}. By (i),
N u_d = 1 − π_{−d} − w_{−d} and N^T w_c = 1 − λ_{−c} − u_{−c}. Applying N^T to the first and using the second,

  (N^T N − I) u_d = q·1 + λ_d − μ,   μ = N^T π_{−d}.

μ is a 0/1 vector with (q+1)a_{−d} ones (the points of P_{−d} all have label α_{−d}, so no line meets two of them).
(iii) Spectrum. N^T N has eigenvalues (q+1)², 3q, q, 0 with the constants as the first eigenspace. Writing u_d in
eigencomponents, N u_d minus its mean has squared norm 3q‖u_1‖² + q‖u_2‖² = 3q‖z_1‖²/(3q−1)² + q‖z_2‖²/(q−1)²,
where z = λ_d − μ minus its mean. So

  s(P − s)/P ≤ q/(q−1)² · (√(a_d(P − a_d)/P) + √(|μ|(P − |μ|)/P))² ≤ q/(q−1)² · (√(P/(q+1)) + √(P/4))²,

where s = a_{−d} + n_{−d} is the number of zeros of N u_d (the left side is the variance of the 0/1 vector N u_d).
(iv) Choice of d. Σ_d s_d = Σ a + Σ n = 2P over the q + 3 nonzero d, so some d has s ≥ 2P/(q+3); also
s ≤ 2P/(q+1) ≤ P/2 by (i). So the left side is at least 2P(q+1)/(q+3)². For q ≥ 7 this exceeds the right side
(`tight_j1_out.txt`: 0.160 P against 0.142 P at q = 7, 0.122 P against 0.068 P at q = 11). ∎

*Theorem 2 (no one-miss assumption).* For q ≥ 11 no regular labelling with M = q + 4 has every point–line pair
covered by guaranteed walks. With §1.2: for q ≥ 11, one matching, zero holonomy, regular labels and guaranteed walks
give at most q + 3 copies.

*Proof.* Same setting without one-miss. For g ≠ 0 let A_g (B_g) be the points (lines) whose own set X(x) (Y(y))
misses g. Let κ_d be the points labelled −d that lie on a line labelled d, and ρ_d the lines labelled d that contain a
point labelled −d (the "coincidences": X(x) or Y(y) repeats a residue); k_d = |κ_d|, r_d = |ρ_d|.
(a) Counting. |A_g| = P − n_g − (q+1)n_{−g} + k_{−g} and |B_g| = P − n_g − (q+1)n_{−g} + r_g. If A_g and B_g are both
non-empty, then as in (i) t is constant on A_g, l is constant on B_g, and |A_g|, |B_g| ≤ P/(q+1). Call g of type A if
A_g is empty and of type B if B_g is empty but A_g is not; there are c_A and c_B of them. For type A, |B_g| = r_g − k_{−g};
for type B, |A_g| = k_{−g} − r_g. Summing |A_g| over the q + 3 nonzero g (the sum is P + (q+2)n_0 + Σ k) against these
bounds gives Σ_{g not of type B} k_{−g} + Σ_{g of type B} r_g ≤ S := (2 − c_A − c_B)P/(q+1) − (q+2)n_0, and the line side
gives the same with A and B (and k, r) exchanged. So c_A + c_B ≤ 2, and there are O(P/q) coincidences.
(b) Identity. Keeping the coincidences, (ii) becomes N u_d = 1 − π_{−d} − w_{−d} + κ_d and
N^T w_{−d} = 1 − λ_d − u_d + ρ_d (now π_g, λ_g are the indicators of A_g, B_g, and κ_d, ρ_d are also indicator vectors),
so (N^T N − I)u_d = q·1 + z_d with z_d = λ_d − μ_d − ρ_d + ν_d, μ_d = N^T π_{−d}, ν_d = N^T κ_d.
(c) One label. Call d good if d is not of type A and −d is not of type B. Then λ_d has b ≤ P/(q+1) ones, μ_d is 0/1
with A = (q+1)|A_{−d}| ones (or is 0), ν_d is 0/1 with K = (q+1)k_d ones (the points of κ_d all have label −d), and
λ_d, ρ_d are disjoint. Expanding the square of this signed sum of 0/1 vectors and dropping the negative cross terms,
‖z_d − mean‖² ≤ x − x²/P + 2b + 2K + 2⟨λ_d, ν_d⟩ + 2⟨ρ_d, μ_d⟩ ≤ P/4 + 2P/(q+1) + 4K + 2r_d (x = A + r_d − b − K).
By (iii), s_d(P − s_d)/P ≤ q/(q−1)²·‖z_d − mean‖², where s_d = P − (q+1)n_d is the number of zeros of N u_d; and
s_d ≤ 2P/(q+1), so the left side is at least s_d(q−1)/(q+1). Hence for every good d

  s_d ≤ (q+1)q/(q−1)³ · (P/4 + 2P/(q+1) + 4(q+1)k_d + 2r_d).

(d) All labels. Σ_{d≠0} s_d = 2P + (q+1)n_0. A d that is not good has s_d ≤ P/(q+1) (if −d is of type B) or
s_d ≤ 2P/(q+1), so the good d carry at least 2P − (c_B + 2c_A)P/(q+1), while by (a) Σ_good k_d ≤ S and Σ_good r_d ≤ S.
Summing (c):

  2P − (c_B + 2c_A)P/(q+1) ≤ (q+1)q/(q−1)³ · ((q+3)(P/4 + 2P/(q+1)) + (4q+6)S).

In the worst case (c_A = c_B = n_0 = 0) the right side is at most (0.33 + 15.4/(q−1))P, which is 1.87P at q = 11 and
decreases with q, against 2P on the left. `tight_j1_robust_out.txt` checks every case (c_A, c_B) for every q up to
10^5, and checks the identities of (a)–(c) exactly on random regular labellings of H(3) and H(4). ∎

At q = 7, 8, 9 the right side is 3.5P, 2.86P, 2.43P, so there the general case is open (the one-miss case is closed
by Theorem 1).

*Consequence.* DGQ's (13,8) graph, if it is a lift of H(11) plus one matching with 15 copies, either uses walks that
exist only for special matchings, or holonomy, or labels that repeat around a point or a line. Optimization meets or passes q + 4 at small q (q = 2: 10 copies, q = 3: 7, lanneal);
at q = 4, exact-cost annealing of 8 = q + 4 copies (C_7-symmetric, qanneal3/qanneal4) stops at 88 and 12 unreached pairs (one source per orbit) in two runs of 10 and 20 minutes (`eq/j1_q4_M8_runs.txt`).

## 2. Conjectured, with strong evidence

### 2.1 The six cells and what the table allows elsewhere (`numerology_out.txt`)

| cell | value | as M·|GH(q)| | Δ − q − 1 |
|---|---|---|---|
| (10,8) | 1,176,480 | 30·|GH(7)| | 2 |
| (11,8) | 2,246,940 | 30·|GH(8)| | 2 |
| (12,8) | 4,650,100 | 35·|GH(9)| | 2 |
| (13,8) | 5,314,680 | 15·|GH(11)| | 1 |
| (14,8) | 14,172,480 | 40·|GH(11)| | 2 |
| (15,8) | 14,172,480 | (copy of (14,8)) | |
| (16,8) | 36,201,060 | 45·|GH(13)| | 2 |

Closed forms for the five j = 2 cells: M = 5·⌊(q+5)/2⌋ = 5(⌊(q+1)/2⌋ + 2) = 5(⌊Δ/2⌋ + 1). For odd q, M·|GH(q)| =
10·|GH(q)| + 5·#flags.

Since DGQ entered their best value in each cell, M_max(q, j) = ⌊table(q+1+j, 8)/|GH(q)|⌋ caps their multiplier:

| q \ j | 1 | 2 | 3 |
|---|---|---|---|
| 7 | 11 | 30 | 57 |
| 8 | 15 | 30 | 62 |
| 9 | 16 | 35 | 40 |
| 11 | 15 | 40 | 40 |
| 13 | 17 | 45 | – |

For one matching, M = q + 4 fits every cap (and equals it at q = 7, 11, 13); 3⌊(q−1)/2⌋ gives 18 > 17 at q = 13, so
that formula holds only if the j = 1 construction needs q ≡ 3 mod 4. For three matchings the caps (40 at q = 9, 11)
show DGQ had no j = 3 version keeping the factor ⌊(q+5)/2⌋.

### 2.2 The construction is far from random

Largest tested M with 0 unreached pairs (liftdiam, all sources unless "sampled"), next tested M in brackets:

| model (H(q) + j matchings, voltages in Z_M) | q = 3 | q = 4 | q = 5 | q = 7 | DGQ |
|---|---|---|---|---|---|
| j = 2, random hop labels (models.py free) | 14 (18: 1 of 2 seeds) | 12 (16: 30) | 10 (12: 2) | | 20, 20, 25, 30 |
| j = 2, plus random H-voltages (holo) | 14 (18: 1 of 2) | 12 (16: 10) | 10 (12: 2) | 12 sampled (14: 1, 16: 37, sampled 1 in 13 sources) | |
| j = 2, Z_5 × Z_k, polygon-cover Z_5 part, random Z_k (f5kh) | 15 (20: 12) | 10 (15: 10) | 10 (15: 178) | | |
| j = 2, random Z_M, 300 label seeds (squad d5) | 20 (21: none of 300) | | | | |
| j = 2, parallel hops (2-factor of the incidence graph) | 10 (14: 6) | | | | |
| j = 2, annealing on the exact diameter (lanneal2, finished by squad c3 on Oct 25) | | 20 (21: 36) | | | |
| j = 1, random (models_j1 free/holo) | 4 (5: 4–10) | 4 (5: 10–16) | 4 (5: squad c6) | (9: ≈2.2M, sampled; squad d8) | q+4: 7, 8, 9, 11 |
| j = 1, annealing on the exact diameter (lanneal) | 7 (8: 16) | (7, 8: run in progress) | | | |

At q = 3 random structures still reach DGQ's value (20); from q = 5 on the gap opens and grows with q. DGQ's
construction is structured and valid for all q in the table range.

**Optimization in the resumed session (2026-10-25)** reaches or passes DGQ's formula at small q, so the formula is
not an optimum there (all files in `d8/calib/` and `d8/eq/`, each checked by liftdiam and by apsp.c on the expanded
graph, `calib/checks.txt`, `eq/*_check.txt`):

| q | DGQ formula | best found | how |
|---|---|---|---|
| 3 | 20 | **22** (16,016 vertices) | squad c6: one duality + one random matching, flag and hop voltages annealed |
| 3 | 20 | **25** (18,200) | Z_5 polygon cover × Z_5 (DGQ's reading with K = 5 instead of 4), Z_5-parts fixed, Z_5 × Z_5 voltages annealed (qanneal2) |
| 4 | 20 | 20 (54,600) | squad c3: tann2 on the exact cost, resumed from the 212-unreached file |
| 4 | 20 | 20 (54,600) | Z_5 polygon cover × Z_4 (DGQ's reading exactly), Z_4 parts annealed (qanneal2) |
| 4 | 20 | **22** (60,060) | C_7-equivariant lift (eqlift.py), quotient voltages annealed (qanneal2.c) |
| 5 | 25 | 14 (109,368) | squad c4: tann3 (tann2 without multi-edges) |
| 5 | 25 | 20 (156,240) | C_31-equivariant lift + qanneal2; 22 stopped at 30 unreached orbits, 25 at about 45 (focus sources) |
| 7 | 30 | 20 (784,320; apsp check running) | C_43-equivariant lift (C_43 from G_2(7), order q² − q + 1); qanneal4 took it from 380 to 6 unreached orbit pairs in 40 min, then to 0 in 45 s with all 912 sources in focus |
| 9 | 35 | 16 (2,125,760) | C_91-equivariant lift (Singer power), random voltages, no annealing; 18, 20, 22 copies leave 50, 252, 1,164 unreached pairs from one source per orbit (`eq/q9_frontier.sh` → `eq/q9_frontier_out.txt`; checked by liftdiam only, files not kept) |

The symmetric lifts use a cyclic group C of collineations acting semiregularly on points and lines (a Singer-type
element of SL(3,q) ⊂ G_2(q), order q² + q + 1 or a divisor, or an element of order q² − q + 1 found as a random product
of the G_2(q) generators of `g2gens.py`); the hops are C-equivariant and go to lines at distance 5. The lift is then a
C × Z_M lift of a quotient base with 2|P|/|C| vertices, so an exact evaluation costs |C| times less. With random
voltages the symmetric lifts are no better than random ones in total (q = 7, M = 16: 380 unreached pairs against
about 480 sampled for a random lift); their advantage is that annealing is fast. Flag voltages matter in this model
(q = 7, |C| = 43, M = 18: 64 unreached orbits with random flag voltages, 4,486 with flag voltage 0).

### 2.3 Walk budget (`walkbudget.py` → `walkbudget_out.txt`)

Expected number of reduced walks of length ≤ 7 from a point to a line in H(q) plus j random hop matchings
(first-order count: hop endpoints treated as uniform; q+1 geodesics between opposite elements counted separately):

| cell | q, j | one hop | two hops | three hops | total W | DGQ M | W / M |
|---|---|---|---|---|---|---|---|
| (10,8) | 7, 2 | 107 | 97 | 47 | 252 | 30 | 8.4 |
| (11,8) | 8, 2 | 121 | 96 | 40 | 258 | 30 | 8.6 |
| (12,8) | 9, 2 | 136 | 94 | 35 | 266 | 35 | 7.6 |
| (14,8) | 11, 2 | 164 | 93 | 28 | 286 | 40 | 7.1 |
| (16,8) | 13, 2 | 192 | 91 | 24 | 308 | 45 | 6.8 |
| (13,8) | 11, 1 | 82 | 23 | 4 | 110 | 15 | 7.3 |

W is nearly constant in q: the one-hop walks grow like 14q but the multi-hop walks shrink. A lift with random voltages
needs W/M ≈ ln(number of point-line pairs × M) ≈ 20–23 (q = 7: M ≈ 12, as observed); annealing gets to about 13 at
q = 4. DGQ's M grows like 2.5q and uses one copy per 7–8.6 walks, so their construction must exploit the families
that grow with q: the 2(q+1) labels on the lines through x and on the points of y (§1.2), and the q+1 geodesics
between opposite elements (with holonomy). The guaranteed-walk budget of §1.2 (about 2q + 15 copies for regular
labellings) and the class-0 count of §1.4 say that neither family alone, used in the obvious way, is enough.

---

## 3. Weak patterns

- **V + E.** For odd q the j = 2 value is exactly |V(X)| + |E(X)| for X = the Z_5 polygon cover of H(q) (DGQ's own
  diameter-7 graph at the same degree, 5·|GH(q)| vertices): 5|GH|(1 + (q+3)/2). For q = 8 it is |V(X)|(1 + ⌊Δ/2⌋).
  In all five cells the factor ⌊Δ/2⌋ + 1 is the number of ±-classes of Z_Δ, and also 2 + (out-degree of an Eulerian
  orientation of the incidence graph, after removing a 1-factor when q is even). Where the table uses the same q at
  D = 7 and D = 8 the ratio is exactly 7, 8, 9 = 1 + Δ/2 (Δ = 12, 14, 16). But (13,8)/(13,7) = 5, not 7, so the j = 1
  cell does not follow the pattern. An operation "diameter D → D+1 with |V| + |E| vertices at the same degree" applied
  to H(q) itself would give (q+1, 7) graphs at half the Moore bound (196,080 at (8,7), where the table has 40,586), so
  if it exists it must use something the polygon cover has and H(q) lacks. Four candidates failed (§4).
- **Pairs.** ⌊(q+1)/2⌋ = (⌊(q+5)/2⌋ − 2) is the number of values of a 2-to-1 quadratic map on GF(q) (x² for odd q,
  x² + x for even q) and the largest number of disjoint pairs among the q+1 lines through a point.
- **Pairs, refined (2026-10-25).** K − 1 = ⌊(q+3)/2⌋ (K = ⌊(q+5)/2⌋) is exactly the number of values of x ↦ x² (odd q) or
  x ↦ x² + x (even q) on PG(1,q) = GF(q) ∪ {∞}. The q+1 geodesics between two opposite elements are indexed by the
  q+1 lines through one of them, a PG(1,q). So one reading is a Z_K-holonomy under which the q+1 geodesics between
  opposite elements carry exactly K − 1 values, two-to-one like a quadratic map. Squad card c2 annealed flag voltages
  towards "≥ K − 1 distinct geodesic voltages for every opposite pair" and got nowhere near it (q = 4, K = 4: 13.8%
  of opposite pairs still short; q = 5, K = 5: 36%), and no natural such holonomy is known.
- **A tempting design for the "+2" fails (2026-10-25).** In a polygon cover × Z_K lift with zero holonomy, the Z_5-class
  −1 is reached by guaranteed walks (§1.2): the labels −λ_1(b) of the q+1 lines b through x, the labels −τ_1(a) of
  the q+1 points a on y, two composite walks τ_1(x) − λ_2(s_1 x) and λ_1(y) − τ_2(s_1^{-1} y), and one cross term. If
  the labels of matching 1 come from "two-to-one" colourings with r = ⌊(q+1)/2⌋ colours C (every point sees every
  colour on exactly two of its lines, every line on exactly two of its points), both neighbourhood families give
  exactly −C, and the two composites would add the missing two values if both were constant, which would make
  K = r + 2 = ⌊(q+5)/2⌋, DGQ's factor. But both composites constant means τ_2 = τ_1 − m_2 and λ_2 = λ_1 − m_1, and
  τ_2, λ_2 must have the same distribution, so C would be invariant under the shift m_1 − m_2 ≠ 0: impossible in
  Z_K for |C| < K. With one composite constant this design covers class −1 for K = r + 1 only. The shape
  "⌊(q+1)/2⌋ + 2" stays unexplained.
- (q+3) | P only for q ∈ {4, 11} among prime powers ≤ 13 (§1.3).
- (6,7) = |GH(5)| + 4·5³ − 2 and (8,7) = |GH(7)| + 4·7³ − 2 (Δ = q+1): a DGQ D = 7 construction adding 4q³ − 2
  vertices to H(q) at the same degree. Not reproduced.
- (4,8) = 2,184 = 3·|GH(3)| = 2·|PSL(2,13)| (a Loz cell): almost certainly a coincidence (a Z_3-lift of H(3) alone has
  diameter ≥ 11).

## 4. Dead ends (tested and dropped)

| idea | test | result |
|---|---|---|
| random voltage lifts, 12 variants (free, holo, polygon-cover, parallel 1-/2-factors, tripled flags, doubled hops, Z_5 × Z_k) | models.py, models5k.py, models_j1.py | §2.2: far below DGQ for q ≥ 5 |
| zero-holonomy designs using only guaranteed walks | gwanneal.c (annealing on the guaranteed-walk cost) | j = 1 stuck at M = q + 1 at q = 3. Weak evidence: for j = 2 the same annealer does not find the known M = 10 constant-label solution (cost 43) |
| line digraph of an Eulerian orientation (diameter +1 for digraphs) | linegraph_test.py, ulg_gh.py | for the Z_5 cover of H(3) and for H(3), H(5) the undirected line digraph of a random Eulerian orientation has diameter 10 |
| "V + E" candidate: that line digraph plus two tail copies of every element, × Z_5 (exactly DGQ's vertex count for odd q, max degree q+3) | ve_test.py | q = 3: diameter 11 |
| colour-voltage lift: properly (q+3)-edge-colour the Z_5 polygon cover and lift it by Z_K with voltage = colour (K = ⌊Δ/2⌋+1 gives DGQ's count) | colourlift_test.py | q = 3, K = 4: 26–44 unreached; q = 5, K = 5: 248,798 unreached, random-like |
| Delorme doubling of H(q) with the diameter relaxed to 8 | degree conditions (L0), (L1) | the doubled set stays of size O(q^4): lower-order gains only |
| Z_5 polygon cover of a diameter-7 base | count | the base would need 86% of the D = 7 Moore bound at q = 7 |
| star products with a degree-2 factor | count | at most 5 copies |
| G_2(q)-equivariant covers of the incidence graph | characters of the parabolics | none (the determinant characters disagree on the Borel); G_2(9) × Z_5 cannot act transitively on a side |
| a hop matching sending the lines through each point onto the points of one line | squad d7 | this is a duality, so it exists only for q = 3^h; at q = 3 it gives no gain |
| squad rounds r1-d8 and r2-d8 (16 strategies) | liftdiam, q = 3, 5, 7 | §4.1: none beats random |
| Z_5 polygon cover × Z_K with designed flag voltages and random hop labels (the REGULARITIES reading of the numerology) | squad c2, q = 4, 5; §1.4 | K = 3 already fails (q = 5: 192 unreached designed, 196 random). With annealed hop labels the reading works at q = 3 up to K = 5 (§1.4), so it is the labels, not the reading, that fail here |
| the same with the two hop matchings equal (each point joined twice to one line, Z_5 voltages 1 and 2: "digons" give class-0 walks at distance ≤ 3) | doubled.py, q = 4 | worse than independent matchings: K = 3: 28 unreached against 4; K = 4: 1,140 against 364 |
| quotient by the negation of the voltage group (a doubled hop with voltages ±φ, flags 0 or N/2; |GH|(⌊N/2⌋+1) vertices, which fits ⌊Δ/2⌋+1) | one-line proof | useless: the mirror of a walk has the negated voltage, so the quotient has diameter ≤ D exactly when the lift does, and the lift has about twice as many vertices |
| two dualities as hops (q = 3) | squad c6 | worst of three variants at M ≥ 22 (6 unreached at M = 22, where duality + random and random + random reach 0) |
| near-duality hop matchings (annealed so that collinear points go to concurrent lines) | squad c1, q = 4, 5; `nearfrac.py` | annealing gets 15.5% (q = 4) and 8.0% (q = 5) of collinear pairs onto concurrent lines (random: 1.5%, 0.8%), and 38% / 50% onto opposite lines (random 75% / 80%); far from a duality, and lifts on them are no better than on random matchings (q = 5: M = 12 for both, M = 14 fails for both) |
| exact SAT for guaranteed-walk label designs | squad c7 (pysat) | only tiny cases solve: j = 2, q = 2 up to M = 7; q = 3 times out; all solutions non-regular |
| symmetric random lifts (C-equivariant, §2.2) | eqlift.py | same total of unreached pairs as random lifts; useful only because annealing them is fast |
| squad round r3-d8 (8 strategies) | §4.2 | calibration only; no structure found |

### 4.1 Squad rounds (research/squads/r1-d8, r2-d8, LOG.md)

Round 1 (q = 5 unless noted): hyperplane-pencil labels (c1), square-class/quadratic holonomy (c2), annealing of Z_k
labels (c3: 76,002 unreached at M = 20 and 478,608 at M = 25, random starts about 78k and 500k), torus-invariant
labels (c4: no torus-equivariant hop matching exists at q = 5; with its 2-torsion, sampled 11,628 at M = 20), colour-class voltages in Z_M (c5: best, 2 unreached at M = 14), one-matching
designs (c6), apartment-projection labels (c7), non-abelian/permutation voltages (c8). Lessons: potential-type labels
(distances, projections, pencils) are locally constant and make one-hop walks to a near target collapse onto few
voltages; square-class holonomy lowers geodesic variety; non-abelian groups do not help. Card c1 found a bug in
liftdiam (a lift disconnected before level D was reported as 0 unreached); fixed, and every zero here was rechecked.

Round 2: V + E operations (d1: random level, diameter 9 at q = 3), "two states + out-arcs" bases (d2: base diameter
8–9, far off), colour voltages with the Z_5 part (d3: 188 unreached at M = 15, q = 5, random level), targeted
one-matching annealing at q = 4 (d4: 598 unreached at M = 8 = q + 4, from 3,912 for a random start; still falling), anti-homomorphic hop matchings (d5: no exact one; no gain), literature
(d6: the DGQ paper is cited nowhere it could reach; no diameter-8 hexagon construction and no "diameter + 1, order
× (1 + Δ/2)" operation found; nearest unread item: Bond and Delorme, "New large bipartite graphs with given degree and
diameter", Ars Combin. 25-C (1988) 123–132; notes in research/squads/r2-d8/d6/notes.md), duality hops (d7: no gain), GF(q)*/±1 labels for the (13,8) cell (d8: random level at q = 7, 9 copies).

### 4.2 Squad round r3-d8 (2026-10-25; research/squads/r3-d8, cards.md, scoreboard.jsonl)

c1 near-duality hops (8–16% of collinear pairs to concurrent lines, no gain in lifts); c2 holonomy design for the polygon cover × Z_K (fails at K = 3, above);
c3 exact-cost annealing at q = 4 (M = 20 valid; 21: 36 unreached); c4 the same at q = 5 (M = 14 valid; 16: 6
unreached); c5 statistics of optimized lifts against random ones (largest |z| = 3.6, hop-2 labels slightly more often
distinct around a point; suggestive only); c6 duality hops at q = 3 (M = 22 valid with one duality and one random
matching); c7 SAT designs (tiny cases only); c8 C_7-equivariant lift at q = 4 (M = 16 with random voltages, the seed of
eqlift.py). Every valid file was rechecked here with liftdiam and with apsp.c (`calib/checks.txt`).

## 5. Where to go next

- The cheapest way forward is the DGQ preprint itself (the authors or their institutions may have it). That is
  Doğa's call; this session contacted nobody.
- Done on 2026-10-25: exact-cost annealing at q = 3, 4, 5 (§2.2) and a SAT search for guaranteed-walk designs (only
  q = 2 solves). The open question is no longer "can anything reach DGQ's values" (at q ≤ 4 optimization passes
  them) but "what scales like 2.5q": a design for the families of §2.3 that keeps working as q grows.
- Concrete next tests: (a) symmetric lifts at q = 7 beyond 20 copies (the C_43 run reached 20 in about 45 minutes;
  22 and 24 need longer runs or larger groups), to see whether optimization alone approaches 30 there; (b) for q = 9 (self-dual H(9), the (12,8) cell) a duality as one hop
  matching gives many more class-0 walks (§1.4: at q = 3 the per-pair minimum of cancelling walks goes from 4 to 15–22).
  At q = 3 this did not help the annealer (polygon cover × Z_6 failed with and without a duality: 500 and 298
  unreached), so class 0 is not what limits small q; whether it limits q = 9 is open, and a duality would not explain
  q = 7, 11, 13 anyway.
- A construction reaching 5(⌊Δ/2⌋ + 1)·|GH(q)| for all q would also give values at q = 16, 17, 19 outside the table.
  (13,8) and (15,8) now hold 6,999,552 and 18,128,880 (group searches), so a j = 3 version would need at least 53
  copies of GH(9) or 52 of GH(11) to matter there.
- Theory: close §1.5 for q = 7, 8, 9 without the one-miss assumption (Theorem 2 needs q ≥ 11; summing the inequality
  over all labels instead of bounding each one separately should gain a constant), and look for a spectral version
  of the j = 2 count of §1.2; the
  combinatorial bound 1 + 2(q+1)(q+4)/(q−3) is far above DGQ's values, and the j = 2 case is not tight, so the §1.5
  argument does not carry over directly.

## Scripts and outputs (research/theorems/d8/)

| script | output | what |
|---|---|---|
| liftdiam.c | — | exact diameter of a Z_M1 × Z_M2 voltage lift, bitset BFS from every base vertex |
| gh.py, dumpgh.py | — | H(q) loader (research/evenq/hexq.py) and text dump |
| numerology.py | numerology_out.txt | the cells, closed forms, M_max(q, j) |
| sumdiff.py, sumdiff_check.py | sumdiff_out.txt, sumdiff_check_out.txt | §1.1 |
| spectrum_check.py | spectrum_check_out.txt | §1.3 |
| models.py, models5k.py, models_j1.py, cover_test.py | (printed, §2.2) | random lift models |
| unreached_profile.py | — | where a lift fails |
| gwanneal.c, lanneal.c, lanneal2.c | — | annealing on the guaranteed-walk cost / on the exact diameter |
| linegraph_test.py, ulg_gh.py, ve_test.py, colourlift_test.py | (printed, §4) | the V + E candidates |
| walkbudget.py | walkbudget_out.txt | §2.3 walk budget |
| class0.py | class0_out.txt | §1.4 identity and per-pair counts |
| g2gens.py | g2gens_out.txt | short-root elements of G_2(q) in the hexq model (with the SL(3,q) blocks they give collineations beyond SL(3,q)) |
| eqlift.py | eq/*.txt | C-equivariant lifts (Singer of SL(3,q), or an element of a given order from random G_2 products) |
| qanneal.c, qanneal2.c | eq/*.txt | annealing of the Z_M part of a quotient base on the exact cost (qanneal2: moves at failing pairs) |
| doubled.py | (printed, §4) | polygon cover with equal hop matchings |
| calib/ | calib/checks.txt | squad r3-d8's valid lifts (q = 3, 4, 5), rechecked with liftdiam and apsp.c |
| class0_nbw.py | class0_nbw_out.txt | exact number of non-backtracking class-0 walks per pair in a Z_5 cover |
| nearfrac.py | nearfrac_out.txt | how close a hop matching is to a duality (squad c1's matchings vs random) |
| qanneal3.c | eq/*.txt, calib/*.txt | qanneal2 plus equivariant hop swaps, one or two matchings, and moves that keep b mod 5 (polygon cover × Z_K) |
| j2bound.py | j2bound_out.txt | §1.2, the two-matching count |
| tight_j1.py | tight_j1_out.txt | §1.5 Theorem 1 (one-miss labels, q ≥ 7) |
| tight_j1_robust.py | tight_j1_robust_out.txt | §1.5 Theorem 2 (all regular labels, q ≥ 11): the final inequality in every case, and exact checks of the identities on random regular labellings of H(3), H(4) |
| qanneal4.c | eq/*.txt | qanneal3 plus repair moves (walks of depth 3 from the source and 4 from the target, matching C-part, one edge's Z-part fixed) |
| reseed.py | — | copy the Z_M voltages of a solved quotient base into a base with larger M (as a starting point) |
| expand_lift.py | — | expand a liftdiam base into a plain edge list for apsp.c |
| eq/q9_frontier.sh | eq/q9_frontier_out.txt | q = 9, C_91-equivariant random lifts at M = 16, 18, 20, 22 |
| — | eq/j1_q4_M8_runs.txt | q = 4, one matching, M = 8 = q + 4: the two annealing runs (§1.5) |
