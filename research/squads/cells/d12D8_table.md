# (12,8): the table value 4,650,100 is not a graph of diameter 8 (job own-12-8, 2026-10-26)

Opus session, branch `claude/own-12-8-cell-ig5jhd`. Tools and logs: `research/d12D8/omega/` (the verdict) and
`research/d12D8/duallift/` (one new attempt to beat the value). This re-examines the Oct 25 finding of job cell-12-8
(branch `claude/cell-12-8-search-qhi11t`, `research/squads/cells/d12D8.md` and `research/d12D8/r2/OMEGA_D9.md` there),
from scratch: an independent hexagon, both possible readings of the thesis figures, exact diameters, and every D = 8
value of the thesis.

## Verdict

1. **The (12,8) value 4,650,100 is |ΩH₉|**, Gómez's construction in his thesis (§2.9.3, pp. 43–46). The count and the
   degree match: 30 copies of the H(9) incidence graph (132,860 vertices each) plus 664,300 vertices of degree 12;
   12-regular, bipartite, 27,900,600 edges.
2. **ΩH₉ has diameter 9, not 8.** Exact diameter 9 in both readings of the figures (BFS from one vertex of every orbit
   of an explicit automorphism group, each automorphism checked edge by edge on the 27.9M edges). With all blocks of
   one type the diameter is 10. Witness pairs at distance 9 are in `research/d12D8/omega/witness_pairs.txt`.
3. **No reading of §2.9.3 gives diameter 8** (Theorems 1 and 2 below): a "copy of K₁" is joined only to vertices
   carrying its own label t, so it sees at most two vertices of the hexagon (point t and line t). For q ≥ 7 that alone
   forces a vertex at distance ≥ 9.
4. **The same holds for every D = 8 value of the thesis**: ΩH₅ (8,8) 195,300, ΩH₇ (10,8) 1,176,480, ΩH₈ (11,8)
   2,246,940, ΩH₉ (12,8) 4,650,100, ΩH₁₁ (14,8) 14,172,480 (also the (15,8) entry), ΩH₁₃ (16,8) 36,201,060. A BFS
   from a K₁-vertex reaches eccentricity 9 in each (§4).
5. **Nothing valid above 4,650,100.** The best valid (12,8) graph we know is still the Haar graph on PSL(2,67) × Z₁₃,
   3,909,048 vertices (job cell-12-8, round 2). I am sure the cell will not fall to the methods we have: §5 gives the
   numbers for each family.

My reading differs from the Oct 25 session in one place (§1.3): which colour class the "inner" and "outer" dots of
Figs 2.21a/b are. The Oct 25 proof covers their reading only. Theorem 2 covers the other one, and the computations cover
both.

## 1. The construction, as the thesis defines it

### 1.1 Source

J. Gómez Martí, *Diámetro y vulnerabilidad en redes de interconexión*, tesis doctoral, ETS de Ingenieros de
Telecomunicación, Universitat Politècnica de Catalunya, Barcelona 1986 (scanned PDF on F. Comellas' site:
`web.mat.upc.edu/francesc.comellas/delta-d/papers/Gomez1986-PhD-red.pdf`, 161 pages; PDF page = thesis page + 6).

- §2.9.3 (bipartite compound graphs ΩB₁): thesis p. 43 (bottom) to p. 45. Fig. 2.21a on p. 44, Fig. 2.21b on p. 45.
- The value list on p. 46: ΩH₅: N(8,8) ≥ 195,300; ΩH₇: N(10,8) ≥ 1,176,480; ΩH₈: N(11,8) ≥ 2,246,940;
  **ΩH₉: N(12,8) ≥ 4,650,100**; ΩH₁₁: N(14,8) ≥ 14,172,480; ΩH₁₁d: N(15,8) ≥ 14,978,080; ΩH₁₃: N(16,8) ≥ 36,201,060.
- The labelling conventions it relies on: §2.8.1 (p. 27, eq. (2.18), Fig. 2.6) and §2.8.9 (pp. 39–41, Fig. 2.18).

Text of §2.9.3 (my translation):

> p. 43: In this construction, which gives bipartite graphs, we also take, as in §§2.8.4 and 2.8.9, copies of K₁
> (isolated vertices). But the interconnection structure differs from the earlier ones: the resulting diameter is
> bounded not by D₀ + D₁ + 1 = D₁ + 1 but by D₁ + 2.
> p. 44: Take first 5 copies of a bipartite graph B₁ with even diameter D₁, and 10 sets of N₁ vertices each. Every 10
> vertices (one from each set) are joined to the copies of B₁ as Figure 2.21a shows, so that their degree is two. Now
> we raise this degree to 4 by joining these vertices to 5 copies of B₁ as in Figure 2.21b. The bipartite graph so
> built has N = 10·N₁/2 + 10N₁ = 15N₁ vertices, degree Δ = max{4, Δ₁+2} and diameter D ≤ D₁ + 2. In general, if
> Δ₁ + 2 = 2α + β, α ≥ 2, β ∈ {0,1}, we take 5α copies of B₁ so that, using either of the two structures above, the
> degree of the vertices corresponding to the copies of K₁ rises to 2α.
> p. 45: We obtain a bipartite graph, ΩB₁, with N = 10·N₁/2 + 5αN₁ = 5(α+1)N₁, Δ = Δ₁ + 2 and D ≤ D₁ + 2.

No proof of D ≤ D₁ + 2 is given; §2.8.2 (p. 30) says the proofs in this part are omitted as "long but without
difficulty". "10 sets of N₁ vertices" is a slip for N₁/2 (the count on the same page uses N₁/2).

### 1.2 Labels: a copy of K₁ is joined to its own label

§2.8.1 (p. 27) writes the vertices of B₁ as (t, j), t ∈ {0, …, N₁/2 − 1}, j ∈ {0, 1} the colour class, and joins
copies by rules that keep the label ((2.18): (t,1,j,k,s) ~ (s,0,j,k,t), …). Fig. 2.6 draws class j = 0 above the
dashed line and class 1 below it. §2.8.9 (p. 39), which §2.9.3 cites, defines the copies of K₁ as (t, i),
t ∈ {0, …, n₁ − 1}, n₁ = N₁/2, and Fig. 2.18 (p. 41) joins vertex (t,1,j,k,h) of copy (B₁,k,h) to (t, i): **the
copy of K₁ with label t is joined to vertices with label t, and all copies of B₁ carry the same labels.** So in
§2.9.3 the 10 sets are {(t,k)} and {(t,k̄)}, k ∈ Z₅, t ∈ {0, …, N₁/2 − 1}, and (t,k) is joined to point (t,0) or line
(t,1) of the copies the figure says. The labels pair the N₁/2 points with the N₁/2 lines (point (t,0) with line
(t,1)); the thesis does not say how, so below σ is an arbitrary bijection, point t ↦ line σ(t).

### 1.3 The figures, and the one place my reading differs

Both figures show copies B₁⁰ … B₁⁴ at the corners of a pentagon, each with a dashed line (the two colour classes), an
"outer" dot on the circle side and an "inner" dot on the star side. In Fig. 2.21a the K₁-vertex k lies on the star
edge between copies k−1 and k+1, and k̄ on the circle arc between copies k+2 and k+3. In Fig. 2.21b, k lies on the arc
between copies k+3 and k+4, and k̄ on the star edge between copies k−1 and k+1. Each dot carries two edges, so every
copy vertex gets 2 new edges and every K₁-vertex 2 per block, 2α in all. This agrees with the Oct 25 session.

The figures do not say which colour class the inner and outer dots are. Two consistent readings:

- **Reading 1 (the thesis's own drawing convention).** In Figs 2.6 and 2.18 the dot above the dashed line is class
  j = 0. In both 2.21a and 2.21b the outer dot of the top copy is above the dashed line, so outer = class 0 = point t
  and inner = class 1 = line σ(t), in both figures. Then (t,k) is joined to **line σ(t) in the (a)-blocks and to point
  t in the (b)-blocks**; (t,k̄) to point t in (a)-blocks and line σ(t) in (b)-blocks. It is bipartite because the
  (b)-copies are coloured the other way round.
- **Reading 2 (the Oct 25 session, `mk_omega.py`).** (t,k) is always on point t and (t,k̄) always on line t; the
  inner dot of 2.21a and the outer dot of 2.21b are the same class.

So the Oct 25 premise "a new vertex is adjacent only to copies of one vertex t of B₁" holds in reading 2 but not in
reading 1, where a K₁-vertex meets a point in some copies and a line in others. Their argument is correct for reading
2. Reading 1 needs the counting argument of Theorem 2. Their sentence "no wiring of the copies with the thesis's
degrees and counts gives 8" claims more than they proved: relabelled copies are not covered by it (§5.1 measures them).

Which blocks are (a) and which (b) is also open ("using either of the two structures"). Mixing both types makes every
two K₁-vertices share a copy (checked by hand from the patterns); with one type only the diameter is 10 (computed at
q = 5 and q = 9).

Both readings: 5(α+1)N₁ vertices, Δ₁ + 2 on copy vertices, 2α on K₁-vertices, bipartite. For q = 9: Δ₁ = 10, α = 6,
N₁ = 2(9⁶−1)/8 = 132,860, N = 35·132,860 = **4,650,100**, all degrees 12.

## 2. Why the bound fails

**Theorem 1 (one label).** Let B₁ be bipartite of even diameter D₁. Take copies of B₁ and add new vertices, each
joined only to copies of a single vertex of B₁ (its label). If a new vertex x with label t misses copy j, and
d_{B₁}(t, v) = D₁, then the copy of v in copy j is at distance ≥ D₁ + 3 from x.

*Proof.* Map every copy vertex to its label in B₁ and every path to the sequence of labels. Copy edges map to edges of
B₁. A pass through a new vertex (copy vertex, new vertex, copy vertex) maps to "stay at the same label" (both ends have
that new vertex's label), and costs 2 edges. A path from x to v in copy j starts with an edge to a copy of t, passes at
least one new vertex (only new vertices join different copies, and x misses copy j), and its label sequence is a walk
from t to v in B₁, of length ≥ D₁. So it has ≥ 1 + 2 + D₁ edges. ∎

In reading 2 (and in reading 1 with all blocks of one type) every K₁-vertex is such an x and every vertex of a
generalized hexagon has an opposite vertex, so ΩH_q has diameter ≥ D₁ + 3 = 9.

**Theorem 2 (two labels).** In ΩH_q with q ≥ 7, under any assignment in which every K₁-vertex (t,·) is joined only
to point t and line σ(t) (any bijection σ, any mix of blocks, any choice of colour convention per copy, copies keeping
their labels), some pair is at distance ≥ 9.

*Proof.* If x = (t,k) meets one label only, use Theorem 1. Otherwise x meets line σ(t) in some copies and point t in
others. Take a copy j that x misses (in reading 1: one of the three (a)-copies of a block that x misses), and in it a
vertex w of the colour of x's neighbours, so at odd distance from x. Say w is a line (if it is a point, swap the roles of
t and σ(t) below; the count is the same) and choose w opposite σ(t) (distance 6; there are q⁵ such lines). A path from x
to w of length ≤ 8 has length ≤ 7. Project it to labels as before. Now a pass through a new
vertex y (label s) either stays at the same label or **switches** between point s and line σ(s) (when y meets s in
one copy and σ(s) in the other). Each pass costs 2, at least one is needed, so the projected walk has ≤ 4 edges of
B₁ in total. It starts at σ(t) (first copy where x meets σ(t)) with an even number of switches, or at t with an odd
number. The reachable lines w:
- start σ(t), no switch: w within distance 4 of σ(t), never opposite;
- start σ(t), 2 switches (≥ 2 passes, ≤ 2 edges): ≤ Σ_{e₁+e₂+e₃≤2} s_{e₁}s_{e₂}s_{e₃} = 601 lines (q = 9);
- start t, 1 switch: t → (e₁ edges) → u, switch to σ-partner u′, → (e₂ edges) → w with e₁ + e₂ even, ≤ 4:
  ≤ Σ s_{e₁}s_{e₂} = 39,161 lines (q = 9);
- start t, 3 switches (no edges left): w = σ(t), not opposite.
Here s₀ = 1, s_i = (q+1)q^{i−1} is the size of the sphere of radius i in the incidence graph (walks that turn back
reach no more than the shorter terms). In general the bound is A + B + 1 with
A = 1 + 2q(q+1) + (q+1)² + 2q³(q+1) + 3q²(q+1)² and B = 1 + 3(q+1) + 3q(q+1) + 3(q+1)²; it is below q⁵ for q ≥ 7
(15,459 < 16,807 at q = 7; 25,482 < 32,768 at q = 8; 39,763 < 59,049 at q = 9). So at least q⁵ − A − B − 1 lines of copy
j (19,286 at q = 9) are at distance ≥ 9 from x. ∎

For q = 3 and 5 the counting is not enough, but the computations below (all pairs, both readings, several σ) give 9.

## 3. The exact diameter of ΩH₉

All from scratch in `research/d12D8/omega/` (no file of the Oct 25 session was used):

- **H(q)**: `hexq6.c`, the Q(6,q) model with Tits' equations (the form in research/theorems/D7_HEXAGON.md §1.1),
  q = 3, 4, 5, 7, 8, 9, 11, 13. Each incidence graph passes `apsp_mt` (all pairs, no symmetry): bipartite,
  (q+1)-regular, diameter 6, on 2(q⁶−1)/(q−1) vertices. A bipartite graph that is (q+1)-regular, has diameter 6 and
  has that many vertices meets the bipartite Moore bound, so its girth is 12 and it is a generalized hexagon of order
  (q,q). Log: `hex_checks.txt`.
- **ΩH_q**: `omega.c` (edge list, both readings, any block types, any σ), `omega_bfs.c` (the same graph without an edge
  file, for the 14M and 36M cases).
- **Automorphisms**: `haut.py` builds g ∈ SL(3,9) ≤ G₂(9) acting as (u | x₃ | w) ↦ (Au | x₃ | A^{−T}w) (a Singer
  cycle of order 91 and a transvection) and checks that each maps every line of H(9) to a line. `omgens.py` lifts them
  to ΩH₉ together with the Z₅ rotation (copy 5B+c → 5B+c+1, (t,k) → (t,k+1)) and swaps of two blocks of the same type.
  For reading 1 the pairing σ is chosen equivariant under the Singer cycle (it acts semiregularly: 730 orbits of 91
  points and of 91 lines), so the Singer cycle stays an automorphism; the transvection is dropped.
- **`apsp_auto.c`** (new, apsp_mt.c plus symmetry): checks simple / degree / bipartite / connected, checks that every
  generator is a bijection mapping every edge to an edge, takes one vertex per orbit of the generated group (union-find)
  and runs the same 64-source bit-parallel BFS from them. Eccentricity is constant on orbits, so the largest one is the
  diameter. It prints a witness pair.

| graph (q = 9) | generators (all checked on 27,900,600 edges) | orbits | diameter | time (4 threads) |
|---|---|---:|---:|---:|
| reading 2, blocks aaabbb | rotation, 4 block swaps, Singer, transvection | 18 | **9** | 18 s |
| reading 1, σ Singer-equivariant, aaabbb | rotation, 4 block swaps, Singer | 4,380 | **9** | 39 s |
| reading 2, blocks aaaaaa | rotation, 5 block swaps, Singer, transvection | 12 | 10 | 20 s |

Logs: `check_om9_r2.txt`, `check_om9_r1s.txt`. Witness pairs (also re-checked with the plain one-source BFS
`bfs1.c`, which shares no code with apsp_auto):

| graph | source | target | d | what |
|---|---:|---:|---:|---|
| reading 2, aaabbb | 3,986,710 | 0 | 9 | K₁-vertex (t = 91, k = 0), on point 91 → point 0 of copy 0; d_{H(9)}(91, 0) = 6 |
| reading 1, aaabbb | 92 | 3,985,825 | 9 | point 92 of copy 0 → K₁-vertex (t = 2, k̄ = 0) |

Distance counts from the reading-2 source: 1, 12, 124, 1,148, 10,350, 93,150, 838,350, 1,167,858, 1,476,225 and
**1,062,882 at distance 9** (= 18 missed copies × 59,049 opposite points, as Theorem 1 says). Reading 1 with a random σ
(not symmetric, so only single BFS): eccentricity 9 from four K₁-vertices, 651,177–652,815 vertices at distance 9.

At q = 5 (ΩH₅, 195,300 vertices; all exact with apsp_auto): reading 2 abab 9; reading 1 abab with Singer σ 9 and with
a random σ 9 (23,436 orbits); reading 1 aabb 9; aaaa 10 in both readings. At q = 3 (14,560): 9 in both readings
(apsp_auto and plain apsp_mt agree).

## 4. The other D = 8 values of the thesis

`omega_bfs` (reading 2; blocks split between the two types), BFS from the first K₁-vertex; every vertex degree checked.
Log: `thesis_values_bfs.txt`.

| thesis | cell | vertices | copies × N₁ + K₁-vertices | degrees | eccentricity | at distance 9 |
|---|---|---:|---|---|---:|---:|
| ΩH₅ | (8,8) | 195,300 | 20 × 7,812 + 39,060 | 8 | 9 | 37,500 |
| ΩH₇ | (10,8) | 1,176,480 | 25 × 39,216 + 196,080 | 10 | 9 | 252,105 |
| ΩH₈ | (11,8) | 2,246,940 | 25 × 74,898 + 374,490 | 10–11 (β = 1) | 9 | 491,520 |
| ΩH₉ | (12,8) | 4,650,100 | 30 × 132,860 + 664,300 | 12 | 9 | 1,062,882 |
| ΩH₁₁ | (14,8), (15,8) | 14,172,480 | 35 × 354,312 + 1,771,560 | 14 | 9 | 3,382,071 |
| ΩH₁₃ | (16,8) | 36,201,060 | 40 × 804,468 + 4,022,340 | 16 | 9 | 8,911,032 |

In every case the far vertices are the points opposite t in the copies the K₁-vertex misses (count = missed copies ×
q⁵). ΩH₁₁d (N(15,8) ≥ 14,978,080) is a variant the thesis does not define in this section; the (15,8) table entry is
14,172,480 = ΩH₁₁. ΩH₅ never entered the table.

## 5. Beating 4,650,100 anyway: what was tried and why the cell will not fall

### 5.1 Repairing ΩH₉ (relabelled copies)

- Relabelling copies by automorphisms or dualities of H(9) changes nothing: transported labels keep their distances, so
  Theorem 1's projection argument goes through unchanged.
- **Random relabelling** (each copy by its own random class-preserving permutation, `twist.py`): far vertices drop
  from 1,062,882 to **22,158** per K₁-vertex (three sources: 22,158 / 22,249 / 22,185) and 3,851 / 3,427 per copy
  vertex. That is still ~10¹⁰ far pairs, far beyond local repair.
- Why (rough count): a copy vertex u and a K₁-vertex g of the other colour that misses u's copy must be joined by a
  path of length ≤ 7, i.e. u → ≤ a steps → hub → another copy → ≤ b steps → g's vertex → g with a + b ≤ 4 (both even).
  Those endpoints cover roughly a quarter of the points of each copy, so g (12 neighbours) is missed with probability
  around 0.74¹² ≈ 3 % for random-like labels. For labels that keep distances, it is missed with certainty for the opposite labels.
- So with copies that keep labels, D = D₁ + 2 forces **every hub to meet every copy**, i.e. ≤ 12 copies:
  (12 + 2)·N₁ = 1,860,040 vertices at q = 9.

### 5.2 Hexagon level graphs (D7_HEXAGON.md) at D = 8

- Theorem A joins two levels with one transition in ≤ 7 steps. With 2 transitions there is 1 step to spare, and with
  dualities as transitions a two-transition route always works: the projected walk is a geodesic of length ≤ 6 and the
  two jumps can sit at vertices of the needed types along it (I checked the four type orders). Three transitions leave
  ≤ 5 projected steps, and 89 % of same-class pairs are opposite (distance 6), so they fail.
- So the levels must form a 2r-regular graph of diameter 2: at most the (2r, 2) degree–diameter record many levels.
  At (12,8): q = 9, r = 2 gives ≤ 15 levels, **1,992,900**. Without a duality (q ≠ 3^h) transitions must alternate
  H/D types, the level graph is bipartite of diameter 2, i.e. K_{2r,2r}: q = 8, r = 3 gives 12 levels, 898,776.
  Surgery and hubs added 3–5 % at D = 7. All far below 3.9M.

### 5.3 A new attempt: duality-hop lifts (levels with per-vertex voltages)

L copies of H(9) (hexagon edges inside a level) and two hop edges per point x: (x, j) ~ (δx, j + t₁(x)) and
(δx, j + t₂(x)), δ a duality of H(9) (from research/d10D7/dual/dualfind.c, converted to my labels by coordinates and
re-checked: all 664,300 incidences preserved, `conv_dual.py`). 12-regular, bipartite, a Z_L-cover, L·132,860
vertices; L = 35 would be 4,650,100. Unlike the level graphs of §5.2 the target level depends on the vertex, and
unlike the random lifts of round 1 every route lands on exactly the right label. `duallift.c` (64 sources, BFS to depth
8):

| L | vertices | pairs at distance > 8 (64 sources) |
|---:|---:|---:|
| 10 | 1,328,600 | 0 |
| 12 | 1,594,320 | 3 |
| 15 | 1,992,900 | 144 |
| 20 | 2,657,200 | 5,507 |
| 30 | 3,985,800 | 224,077 |
| 35 | 4,650,100 | 611,403 |

Every far pair is a point–line pair at hexagon distance 5 (`duallift diag`). Their distance in the lift is odd, so ≤ 7;
a two-jump route then has only 5 projected steps, i.e. the **unique** geodesic, and all routes together give only
~190 level values (voltage sums and differences along it). Random voltages need ~L·ln(#pairs) ≈ 30L of them, hence the
limit L ≈ 10–12. Reaching L = 36 would need every one of ~4·10⁹ point–line pairs to see all 35 nonzero levels among its
~190 values. No voltage structure I can see does that.

### 5.4 The other families (numbers from earlier jobs, re-derived where noted)

- **Haar graphs**: the first-moment ceiling at (12,8) is 2N_h = 4,529,596 < 4,650,100 (SIZE_LAW), and orbit search
  stops near 3.9–4.1M (job cell-12-8 round 2: best 3,909,048; +3–4 % per 10× compute).
- **Lifts of H(q) + hop matchings** (cell-12-8 round 1): stall at group order 15–17 (2.0–2.3M); W(11) lifts 2,049,600.
- **Route-chart lifts** (the (16,5) idea, c letters × F_q, Δ = cq = 12): with one walk per pair, as in the (16,5)
  graph, the fibre is F_q⁷ (opposite pairs are joined by walks of length 7), so the c-regular bipartite controller needs
  diameter ≤ 8 (with walks of exactly length 7 and 8 between all pairs) on ≥ 4,650,100/q⁷ vertices: 284 for 3 × F₄
  (the (3,8) table value is 256), 2,128 for 4 × F₃ (table 2,184, predicted Haar 1,936, plus a universal chart in
  dimension 7), 36,330 for 6 × F₂ (our (6,8) record is 30,576). Out of reach.
- The D = 8 cells the size law flagged as "above the random ceiling" were exactly the ΩH_q entries. No valid D = 8
  construction above the ceiling is known to us.

## 6. For the coordinator

- (12,8): the table entry 4,650,100 is not a valid (12,8) graph. The largest valid (12,8) graph we know is ours,
  3,909,048 (`research/frontier/sols/d12D8_psl_67_13_orb3f0_w3_s2.txt`, branch claude/cell-12-8-search-qhi11t,
  build_haar2 VALID).
- The same defect removes the green D = 8 entries (10,8), (11,8), (14,8), (15,8), (16,8). Haar searches there were
  ruled out only because of these values; SIZE_LAW predicts Haar graphs of ≈ 1.03M, 10.4M and 26.0M at (10,8), (14,8),
  (16,8). These are new cells for the lab.
- Re-check of the witness: `cd research/d12D8/omega && cc -O2 -o hexq6 hexq6.c && ./hexq6 9 hex_q9.txt &&
  cc -O2 -o omega omega.c && ./omega hex_q9.txt aaabbb 2 om9_r2.txt && cc -O2 -o bfs1 bfs1.c &&
  ./bfs1 om9_r2.txt 3986710 0` → `d(3986710, 0) = 9` (any BFS tool works on om9_r2.txt; ~1 min, 2 GB).
- Exact diameter: `python3 haut.py hex_q9.txt haut_q9.npy singer trans && python3 omgens.py hex_q9.txt aaabbb 2
  haut_q9.npy g9_r2.bin && cc -O2 -pthread -o apsp_auto apsp_auto.c && ./apsp_auto om9_r2.txt g9_r2.bin 12 8 4`.
  Reading 1: `python3 sigma.py hex_q9.txt singer sig_q9_singer.txt haut_q9.npy`, then `./omega hex_q9.txt aaabbb 1
  om9_r1s.txt sig_q9_singer.txt`, `python3 omgens.py hex_q9.txt aaabbb 1 haut_q9.npy g9_r1s.bin sig_q9_singer.txt`,
  `./apsp_auto om9_r1s.txt g9_r1s.bin 12 8 4`.
