# The unexplained D = 8 numbers (job thm-d8table, 2026-10-24)

Branch `claude/d8-numerology-ocg3xq`. Every script and its saved output is in `research/theorems/d8/` (named per
item). "Table" is the DS14v2 bipartite table (research/frontier/TABLE.md). |GH(q)| = 2(q^6−1)/(q−1) is the order of
the incidence graph of the split Cayley hexagon H(q) (built with research/evenq/hexq.py, cached for q = 2, 3, 4, 5, 7,
8, 9, 11). The green D = 8 cells are credited on the wiki to Delorme, Gómez and Quisquater (DGQ), "On large bipartite
graphs", submitted, never found (research/lifts LITERATURE.md on branch claude/voltage-lifts-search-6lfotq). A lift of
H(q) "with j matchings and M copies" means: add j perfect matchings from points to lines ("hops", degree q+1+j) and
take an M-fold voltage lift; it has M·|GH(q)| vertices.

## Short answer

1. **The construction behind the numbers was not found.** The evidence says it is a structured lift of H(q) with
   two extra matchings (one for the (13,8) cell) whose structure neither I nor two squad rounds could reproduce.
   Random and optimized lifts fall far short once q ≥ 5 (§2.2).
2. **The numbers, exactly** (§2.1, `numerology.py`): (Δ,8) = M·|GH(q)|, Δ = q+3, M = 5·⌊(q+5)/2⌋ = 5(⌊Δ/2⌋ + 1) for
   q = 7, 8, 9, 11, 13, and (13,8) = 15·|GH(11)| with Δ = q+2. For odd q this is |V(X)| + |E(X)| where X is DGQ's own
   diameter-7 graph at the same degree (the Z_5 polygon cover). Because DGQ entered their best value in every cell,
   the table also caps what their construction gives at other (q, j); for one matching M = q + 4 fits every cap,
   while the REGULARITIES formula 3⌊(q−1)/2⌋ breaks the cap at q = 13 (unless it needs q ≡ 3 mod 4).
3. **Proved (new, small):**
   - (§1.1) The zero-voltage "n+2 cover" with j constant-voltage matchings has diameter ≤ n+2 whenever a
     sum/difference set covers Z_M. The largest M is 4, 10, 16, 26, 38 for j = 1, ..., 5 (REGULARITIES had j = 2).
   - (§1.2) A list of "guaranteed walks" present in every lift of H(q) plus matchings, and a count showing that a
     regular zero-holonomy labelling covered by those walks alone has at most q + 4 copies (one matching).
   - (§1.3) A spectral lemma: H(q) admits no "nearly rainbow" equitable labelling missing fewer than √q classes.
     It kills the tight designs, including one whose arithmetic picks out exactly q = 11 and M = 15, the (13,8) cell.
4. **No table cell beaten.** Two squad rounds (16 Haiku strategies, §4.1) found nothing better than random lifts.

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

Non-regular labellings are not covered by this count (constant labels give the n+2 cover with M = 4). The same
heuristic count for two matchings gives roughly 2q + 15 (29 at q = 7, 41 at q = 13), a little below DGQ's
2.5q + 12.5. This suggests, but does not prove, that DGQ's construction uses holonomy on H(q) or walks that exist only
because of where the matchings are placed.

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
| j = 2, annealing on the exact diameter (lanneal2) | | (20: run in progress) | | | |
| j = 1, random (models_j1 free/holo) | 4 (5: 4–10) | 4 (5: 10–16) | 4 (5: squad c6) | (9: ≈2.2M, sampled; squad d8) | q+4: 7, 8, 9, 11 |
| j = 1, annealing on the exact diameter (lanneal) | 7 (8: 16) | (7, 8: run in progress) | | | |

At q = 3 random structures still reach DGQ's value (20); from q = 5 on the gap opens and grows with q. DGQ's
construction is structured and valid for all q in the table range.

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
(d6: the Comellas–Gómez 1995 paper on compounding generalized hexagons for general graphs, arXiv math/9411218,
and the Quisquater thesis reference; nothing on bipartite D = 8; final report pending), duality hops (d7: no gain), GF(q)*/±1 labels for the (13,8) cell (d8: random level at q = 7, 9 copies).

## 5. Where to go next

- The cheapest way forward is the DGQ preprint itself (the authors or their institutions may have it). That is
  Doğa's call; this session contacted nobody.
- Tests that would sharpen §2: an exact search (SAT/ILP) for zero-holonomy labellings covered by guaranteed walks at
  q = 3 and 4, to see whether M = 20 is reachable that way; annealing at q = 5 with exact cost to see whether 25
  copies are reachable by optimization at all.
- A construction reaching 5(⌊Δ/2⌋ + 1)·|GH(q)| for all q would also give values at q = 16, 17, 19 outside the table,
  and if it extends to j = 3 it would beat (13,8) and (15,8).

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
