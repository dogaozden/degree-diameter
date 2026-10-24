# The unexplained D = 8 numbers (job thm-d8table, 2026-10-24)

Branch `claude/d8-numerology-ocg3xq`. Every script and its saved output is in `research/theorems/d8/` (named per
item). "Table" is the DS14v2 bipartite table (research/frontier/TABLE.md). |GH(q)| = 2(q^6−1)/(q−1) is the order of
the incidence graph of the split Cayley hexagon H(q) (built with research/evenq/hexq.py, cached for q = 2, 3, 4, 5, 7,
8, 9, 11). The green D = 8 cells are credited on the wiki to Delorme, Gómez and Quisquater (DGQ), "On large bipartite
graphs", submitted, never found (research/lifts LITERATURE.md on branch claude/voltage-lifts-search-6lfotq).

## Short answer

1. **The construction behind the numbers was not found.** I can say a lot about what it is not, and the evidence
   points to a structured lift of H(q) plus extra edges whose structure we could not reproduce (§2).
2. **The numbers, exactly** (`numerology.py`): (Δ,8) = M·|GH(q)| with Δ = q+3 and M = 5·⌊(q+5)/2⌋ =
   5(⌊(q+1)/2⌋ + 2) for q = 7, 8, 9, 11, 13 (M = 30, 30, 35, 40, 45), and (13,8) = 15·|GH(11)| with Δ = q+2. For odd q
   this is 10·|GH(q)| + 5·(number of flags of H(q)). The table also bounds what the DGQ construction can give in the
   other cells (§2.2). The REGULARITIES formula (2j+1)(⌊(q−1)/2⌋ + 3(j−1)) predicts 18 copies at (q, j) = (13, 1),
   which would have put 14,480,424 at (15,8); the table has 14,172,480, so for j = 1 that formula fails at q = 13
   (unless the j = 1 construction needs q ≡ 3 mod 4). M = q + 4 fits all the j = 1 constraints.
3. **Proved (new, small):** the zero-voltage "n+2 cover" works with j constant-voltage matchings exactly when a
   sum/difference set covers Z_M; the largest M is 4, 10, 16, 26, 38 for j = 1, ..., 5 (§1.1; REGULARITIES had j = 2).
   A list of "guaranteed walks" that exist in every lift of H(q) plus matchings (§1.2), and a spectral obstruction
   showing that the tight designs built only from those walks cannot exist (§1.3).
4. **Random and optimized lifts fall far short** (§2.3): random voltage lifts of H(q) + 2 matchings reach about 18,
   14, 12 copies at q = 3, 4, 5 (DGQ: 20, 20, 25); with one extra matching random lifts reach only 4 copies.
   Annealing on the exact diameter reaches q + 4 copies for one matching at q = 3, but not at q = 4 within an hour.
5. **No table cell beaten.** A squad round (8 Haiku strategies, §4) found nothing better than random at q = 5
   except colour-class voltages (14 copies against 12).

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

*Largest M* (exhaustive over T, `sumdiff_out.txt`): j = 1: M = 4 (T = {1}); j = 2: 10 ({1,4}); j = 3: 16 ({1,4,7},
{1,4,10}); j = 4: 26 ({1,5,8,12}); j = 5: 38 ({1,12,24,30,33}). Checked with liftdiam on H(3) and two random
matchings per case: all have diameter ≤ 8 (`sumdiff_check_out.txt`). With B = H(q) this gives 16·|GH(q)| at Δ = q+4
and so on. **No table cell is beaten** (the multiplier is a constant; DGQ's grows with q). With B = our D = 6 records
it is also below the table in every cell (e.g. 10·148,944 at (13,8) against 5,314,680).

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
because those pairs have q + 1 geodesics). Two points or two lines have many more (at least (q+1)^2), so the
point–line pairs are the binding case. Everything else (the "conditional" walks) depends on where the matchings put
things. Unreached targets found by liftdiam in random lifts (`unreached_profile.py`) are exactly where this table
predicts: point–line pairs at H-distance 5 (zero holonomy) and 3 or 5 (random holonomy).

**Counting consequence (zero holonomy, guaranteed walks only, one matching).** Call a labelling *regular* if the
lines through any point carry pairwise different labels and so do the points on any line. If the guaranteed walks
alone cover Z_M for every point–line pair of a regular labelling, then M ≤ q + 4 (q ≥ 3). Proof: lines with the same
label are pairwise non-concurrent, so every label occurs on at most P/(q+1) lines (P = number of points). A label g
is missed at x by the x-side terms {t(x)} ∪ −l(lines on x) unless t(x) = g or a line on x has label −g; so the
number of points missing g on that side is at least P − n_g − (q+1)n_{−g} (n_v = number of points, equivalently
lines, with label v), and the same for lines. If both a point x and a line y miss g, the only remaining walk is
t(x) + l(y) = g, which forces all such x to share one label and all such y to share one label; so either every point
or every line covers g, or n_g + (q+1)n_{−g} ≥ qP/(q+1). Summing over the M − 1 nonzero g (Σ_g (n_g + (q+1)n_{−g}) =
(q+2)P) gives (M − 1)·q/(q+1) ≤ q + 2. For labellings that are not regular (the extreme being constant labels, the
n+2 cover with M = 4) the count does not apply as stated. The same heuristic count for two matchings gives roughly
2q + 15 (about 29 at q = 7, 41 at q = 13), a little below DGQ's 2.5q + 12.5; this suggests, but does not prove, that
DGQ's construction uses holonomy on H(q) or walks that exist only because of where the matchings are placed.

### 1.3 A spectral obstruction to the tight designs (`spectrum_check.py` → `spectrum_check_out.txt`)

The incidence matrix of H(q) has singular values q + 1, √(3q), √q and 0 (checked for q = 2, 3).

*Lemma.* Suppose the points and the lines of H(q) are each split into m classes so that every point of class i lies
on A_ij ∈ {0, 1} lines of class j and every line of class j contains A_ij points of class i (an equitable partition
of the incidence graph), with exactly r zeros in each row and column of A. If r < √q, this is impossible.

*Proof.* The singular values of the quotient matrix A are singular values of the incidence matrix. A = J − X with X
a 0/1 matrix with r ones in every row and column, so X is a sum of r permutation matrices and every singular value of
A on the vectors orthogonal to the all-ones vector is at most r < √q. They must therefore all be 0, so X is constant
on that space, which is impossible for a 0/1 matrix with r ones per row unless r = 0 or r = m. ∎

*Use.* The tight one-matching design with M = q + 4 has each point seeing all nonzero labels on its lines except
two, and each line seeing all point labels except two (r = 2). Working out the conditions shows it needs (q+3) | P
and a partition of the nonzero residues mod q+4 into zero-sum triples (plus elements of order 3). Among the prime
powers up to 13 this singles out **exactly q = 11, the (13,8) cell, with M = 15**: an arithmetic coincidence with
the DGQ value. But r = 2 < √11, so by the lemma the design does not exist. The M = q + 3 design (each point sees all
labels but one, r = 1) needs (q+2) | P (q ∈ {5, 19, …}) and also dies by the lemma when it is equitable on both
sides. So the guaranteed walks can never do the job alone; any construction near DGQ's numbers needs walks whose
existence depends on the placement of the matchings or holonomy on H(q).

---

## 2. Conjectured, with strong evidence

### 2.1 The six cells are M·|GH(q)| with a lift-like structure

`numerology_out.txt`. The five cells with Δ = q+3 have M = 5·⌊(q+5)/2⌋ = 5(⌊(q+1)/2⌋ + 2); (13,8) has M = 15 with
Δ = q+2. For odd q, M·|GH(q)| = 10·|GH(q)| + 5·#flags; for q = 8 it is 10·|GH(q)| + 5·(#flags − #points). Note
⌊(q+1)/2⌋ is the number of values of a 2-to-1 quadratic map on GF(q) (x² for odd q, x² + x for even q), and the
largest number of disjoint pairs among the q+1 lines through a point. I could not turn either reading into a
construction.

### 2.2 What the table allows at other (q, j)

`numerology_out.txt` part (3): M_max(q, j) = ⌊table(q+1+j, 8)/|GH(q)|⌋ bounds the DGQ multiplier at (q, j), since
DGQ entered their best value. For j = 1: M ≤ 11, 15, 16, 15, 17 at q = 7, 8, 9, 11, 13. So M_1 = q + 4 fits every
cell (and equals the bound at q = 7, 11, 13), while 3⌊(q−1)/2⌋ fails at q = 13 (18 > 17) unless q ≡ 3 mod 4 is
required. For j = 3: M ≤ 40 at q = 9 and q = 11, i.e. at most 5 per Z_7-copy: DGQ had no j = 3 version of the
j = 2 construction that kept the factor ⌊(q+5)/2⌋.

### 2.3 The construction is far from random

| model (H(q) + j matchings, voltages in Z_M) | q = 3 | q = 4 | q = 5 | DGQ formula |
|---|---|---|---|---|
| j = 2, random bijections, random hop labels (models.py free) | 14 ok, 18 (1 of 2 seeds) | 12 ok, 16 fails | 12 fails (2) | 20, 20, 25 |
| j = 2, plus random H-voltages (holo) | 14 ok, 18 (1 of 2) | 12 ok, 16 fails (10) | 12 fails (2) | |
| j = 2, Z_5 × Z_k, polygon-cover Z_5 part, random Z_k (models5k f5kh) | 15 ok, 20 fails (12) | 10 ok, 15 fails (10) | 10 ok, 15 fails (178) | |
| j = 2, parallel hops (2-factor of the incidence graph, par2) | 10 ok, 14 fails (6) | | | |
| j = 1, random (models_j1 free/holo) | 4 ok, 5 fails (4–10) | 4 ok, 5 fails (10–16) | 4 ok, 5 fails (c6) | q+4: 7, 8, 9 |
| j = 1, annealing on the exact diameter (lanneal) | 7 ok, 8 fails (16 left) | PENDING | | |

(Entries: tested M with 0 unreached pairs over all sources ("ok") and the next tested M, with its number of
unreached pairs in brackets; liftdiam, one or two seeds.) At q = 7 random reaches about 13 (REGULARITIES estimate)
against DGQ's 30. The gap grows with q, so DGQ used a structure valid for all q.

---

## 3. Weak patterns

- **V + E.** For odd q the j = 2 value is exactly |V(X)| + |E(X)|, where X is DGQ's own diameter-7 graph at the same
  degree, the Z_5 polygon cover of H(q) (5·|GH(q)| vertices, degree q + 3): 5|GH|(1 + (q+3)/2) = 5|GH|(q+5)/2. For
  q = 8 it is |V(X)|(1 + ⌊Δ/2⌋). Equivalently N/5 = 2·|GH(q)| + (number of arcs of an Eulerian orientation of the
  incidence graph, after removing a 1-factor when q is even): two extra "states" per element plus one per out-arc.
  Where the table uses the same q at D = 7 and D = 8 the ratio is exactly 7, 8, 9 = 1 + Δ/2 at Δ = 12, 14, 16. But
  (13,8)/(13,7) = 5, not 1 + ⌊13/2⌋ = 7, so the j = 1 cell does not follow the pattern. A degree-preserving operation
  "diameter D → D + 1 with |V| + |E| vertices" cannot exist in general (applied to H(q) itself it would give (q+1, 7)
  graphs at half the Moore bound); the line-digraph test above fails.

- (6,7) = |GH(5)| + 4·5³ − 2 and (8,7) = |GH(7)| + 4·7³ − 2 (Δ = q+1): a DGQ D = 7 construction that adds 4q³ − 2
  vertices to H(q) at the same degree. Not reproduced.
- (4,8) = 2,184 = 3·|GH(3)| = 2·|PSL(2,13)| (a Loz cell): almost certainly a coincidence (a Z_3-lift of H(3) alone
  has diameter ≥ 11).
- (q+3) | P holds exactly for q ∈ {4, 11} among prime powers ≤ 13 (§1.3).

## 4. Dead ends (tested and dropped)

| idea | test | result |
|---|---|---|
| random voltage lifts, 12 variants (free, holo, polygon-cover, parallel 1-/2-factors, tripled flags, doubled hops, Z_5 × Z_k) | models.py, models5k.py, models_j1.py | §2.3: far below DGQ for q ≥ 4 |
| zero-holonomy designs using only guaranteed walks | gwanneal.c (annealing on the guaranteed-walk cost) | j = 1 stuck at M = q + 1 at q = 3. Weak evidence: for j = 2 the same annealer does not even find the known M = 10 constant-label solution at q = 3 (cost 43), so the landscape is rugged |
| line digraph of an Eulerian orientation (diameter +1 for digraphs) | linegraph_test.py, ulg_gh.py | for the Z_5 cover of H(3) (|E| = 10,920 vertices, degree 6) and for H(3), H(5) themselves the undirected line digraph of a random Eulerian orientation has diameter 10, not 8 |
| Delorme doubling of H(q) with diameter relaxed to 8 | §2 of the analysis | the degree conditions keep A_0 of size O(q^4): gains lower-order terms only |
| Z_5 polygon cover of a diameter-7 base | count | the base would need 86% of the D = 7 Moore bound at q = 7 |
| star products with a degree-2 factor | count | at most 5 copies (C_5) |
| G_2(q)-equivariant covers of the incidence graph | characters of the parabolics | none (the two determinant characters disagree on the Borel); G_2(9) × Z_5 cannot act transitively on a side |
| squad round r1-d8 (research/squads/r1-d8/): hyperplane-pencil labels (c1), square-class/quadratic holonomy (c2), annealing of Z_k labels (c3), torus-invariant labels (c4), colour-class voltages in Z_M (c5), j = 1 designs (c6), apartment-projection labels (c7), non-abelian / permutation voltages (c8) | liftdiam at q = 5 | best: c5 colour voltages, 2 unreached at M = 14; all others at or below random (§4.1) |

### 4.1 Squad round r1-d8

See `research/squads/r1-d8/scoreboard.jsonl` and research/squads/LOG.md. Lessons: potential-type labels (distances,
projections, hyperplane pencils) are locally constant and make the one-hop walks to a near target collapse onto few
voltages (c7, c1); square-class holonomy lowers geodesic variety (c2); non-abelian groups do not help random labels
(c8). Card c1 found a bug in liftdiam (a lift that is disconnected before level D was reported as 0 unreached); it is
fixed and every zero in this note was rechecked.

## Scripts and outputs (research/theorems/d8/)

| script | output | what |
|---|---|---|
| liftdiam.c | — | exact diameter of a Z_M1 × Z_M2 voltage lift, bitset BFS from every base vertex |
| gh.py, dumpgh.py | — | H(q) loader (research/evenq/hexq.py) and text dump |
| numerology.py | numerology_out.txt | the cells, closed forms, M_max(q, j) |
| sumdiff.py, sumdiff_check.py | sumdiff_out.txt, sumdiff_check_out.txt | §1.1 |
| spectrum_check.py | spectrum_check_out.txt | §1.3 |
| models.py, models5k.py, models_j1.py, cover_test.py | (printed) | random lift models, §2.3 |
| unreached_profile.py | — | where a lift fails |
| gwanneal.c | — | annealing on the guaranteed-walk cost |
| lanneal.c, lanneal2.c | — | annealing on the exact diameter (all sources / focus set) |
