No record: I found no construction that beats the table, and I could not reconstruct Delorme's 5⌊(q+5)/2⌋ construction. What is here are proved limits on the designs we (and the earlier sessions) have tried. They say what Delorme's graphs cannot look like, and they point to where the next search should go.

# D = 8 from the split Cayley hexagon: theory notes

Theory agent for bigcheck-dist/d8, 2026-10-25. Builds on research/projects/bigcheck-dist/d8/NOTES.md (the lead) and on the cell-10-8 session (branch claude/cell-10-8-search-t6pwvg: research/squads/cells/d10D8.md §2, §3b; squad log rounds d10D8-r1, r2). Scripts are in this folder. All runs used ≤ 1 thread.

## 0. Summary

1. **The always-present routes** (§2). The cell-10-8 list of 4q+17 point-to-line walks of length ≤ 7 is complete. These are the walks that exist for every pair, whatever the matchings are (§2 has the proof).
2. **Intact copies have a hard ceiling** (§3, Theorem 1). Suppose the hexagon voltages are a coboundary, so the lift contains m untouched copies of H(q). Then the voltages that every point, or every line, reaches through always-present routes number at most **2q+9** when Δ = q+3. For Δ = q+2 the ceiling is q+3, and equality forces (q+2) | 21. Delorme's counts exceed 2q+9 for every q: 20 > 15, 25 > 19, 30 > 23 (q = 3, 5, 7), and the gap grows like q/2. The rest has to come from walks that depend on the pair: the U_s H U_t "mixed" walks, bundles (the q+1 geodesics between opposite elements, which only help if the hexagon voltages are nonzero), or walks specific to his matchings.
3. **Mixed walks are very constrained** (§4). If a voltage is missed by some point and by some line, all the points that miss it share one of ≤ 2 jump labels (Lemma 2). For Δ = q+2 this gives m ≤ q+4 when no label class is larger than N/(q+1). The fully tight version of q+4 is impossible for q ≥ 5 (Theorem 3, by an equitable-partition eigenvalue argument). The table's (13,8) = 15·|H(11)| is exactly q+4.
4. **No "levels × sheets"** (§5, Lemma 4). Suppose the voltage group maps onto Z_r, with the hexagon edges going to 0 and each matching to a nonzero constant. Then an incident pair p ∈ y has at most 5 always-present routes in the kernel coset (at most 9 if 2a_1 ≡ 2a_2 ≡ 0). So "5 levels × k sheets" with k ≥ 6 cannot be proved through always-present routes. Delorme's 5·k is not a T_5 or C_5 level structure carrying k sheets in this sense.
5. **Symmetry facts, computed at q = 3, 5** (§7). SL(3,q) has 4 orbits on points but 2 on lines, so it carries no equivariant matching. Every SL(3,q)-invariant flag voltage is a coboundary: every bundle has identical signed orbit counts. Useful hexagon voltages must therefore break SL(3,q).
6. **"Free" copies** (§8). The cell-10-8 Z10 lemma gives 10 copies for arbitrary matchings. Annealing over all pairs of copy permutations found 10 again and nothing for 11, 12 or 13.
7. **Other uses of the two extra degrees** (§6): tripled flags, rewiring a perfect matching across copies, and loops (the BDF ∗-product with C_m). Their always-present route counts are given. Loops need an even number of copies, so they cannot give 35 or 45.

## 1. Setting

H = incidence graph of H(q): N = (q+1)(q⁴+q²+1) points and N lines, girth 12, point–line distance ≤ 5, same-type distance ≤ 6. Opposite elements (distance 6) are joined by exactly q+1 geodesics, which I call a **bundle**; any two closer elements are joined by a unique geodesic. The base B is H plus two perfect matchings σ_1, σ_2 from points to lines (Δ = q+3), or one matching (Δ = q+2). A lift over a group A (|A| = m copies) puts a voltage ν on each hexagon edge and a voltage g on each jump edge (read point → line). The lift has m·|H(q)| vertices.

*Intact copies* means that ν is a coboundary. After a gauge change ν = 0, and the lift contains m copies of H(q) as induced subgraphs. With ν = 0, write:
- f_t(p) = g(p → σ_t(p)) for the label of a point's jump;
- h_t(y) = f_t(σ_t⁻¹(y)) for the label of the jump that arrives at line y.

Both are labels of the same jump edges, read from the two ends. Additive notation is used below, but nothing needs A to be abelian.

Point→line pairs are the binding case. A line→point walk is a reversed point→line walk, so its value set is the inverse. Same-type pairs have strictly more always-present routes: jumps at any point within distance 2 of either end, as in the cell-10-8 notes §2.

## 2. The always-present point→line routes (length ≤ 7)

U_t: up-jump p → σ_t(p). D_t: down-jump l → σ_t⁻¹(l). H: a hexagon geodesic between arbitrary ends. h: one hexagon step to a chosen neighbour.

| route | walk | value (ν = 0) | count |
|---|---|---|---|
| H | p ⇝ y | 0 | 1 |
| U_t H | p → σ_t(p) ⇝ y (line–line ≤ 6) | f_t(p) | 1 each (q+1 if σ_t(p) is opposite y) |
| H U_t | p ⇝ σ_t⁻¹(y) → y (point–point ≤ 6) | h_t(y) | 1 each (q+1 if opposite) |
| h D_t H | p → l → σ_t⁻¹(l) ⇝ y, l ∋ p | −h_t(l) | q+1 each |
| H D_t h | p ⇝ σ_t(x) → x → y, x ∈ y | −f_t(x) | q+1 each |
| U_s H U_t | p → σ_s(p) ⇝ σ_t⁻¹(y) → y | f_s(p) + h_t(y) | 4 |
| U_s D_t H (s ≠ t) | p → σ_s(p) → σ_t⁻¹σ_s(p) ⇝ y | f_s(p) − f_t(σ_t⁻¹σ_s p) | 2 |
| H D_s U_t (s ≠ t) | p ⇝ σ_s(z) → z → y, z = σ_t⁻¹(y) | h_t(y) − f_s(z) | 2 |

That is 4q+17 walks, plus the bundle multiplicities.

*Completeness.* A route that works for every pair, with arbitrary σ's, must contain a hexagon segment between ends it does not control. Such a segment has length 5 (point–line) or 6 (same type), so the other segments and the jumps share a budget of at most 2.
- **One jump.** The free segments (a, b) are (0, 6) or (6, 0) when the jump starts at a point, and (1, 5) or (5, 1) when it starts at a line. The splits (2, 4), (4, 2) and (3, 3) need a specific σ.
- **Two jumps.** The budget left is 0, so the three hexagon segments are (0, 5, 0), (0, 0, 5) or (5, 0, 0) in the parity-allowed forms U H U, U D H and H D U.
- **Three or more jumps.** These leave at most 4 for hexagon steps, which is too little.

## 3. Intact copies: the universal ceiling

For a point p, E(p) is the set of values of its routes H, U_t H, h D_t H and U_s D_t H; these depend only on p. For a line y, L(y) is the set of values of H U_t, H D_t h and H D_s U_t; these depend only on y. M(p, y) is the set of (at most 4) values of U_s H U_t. Under always-present routes the lift has diameter ≤ 8 exactly when E(p) ∪ L(y) ∪ M(p, y) = A for every pair. Put X* = ∩_p E(p) and Y* = ∩_y L(y).

**Theorem 1.** With intact copies and Δ = q+3, |X* ∪ Y*| ≤ 2q + 9. With Δ = q+2 (one matching), |X* ∪ Y*| ≤ q + 3, and equality forces every non-zero value to label exactly N/(q+2) jump edges, so (q+2) | N, i.e. (q+2) | 21: q ∈ {5, 19}.

*Proof.* For c ∈ A write m(c) for the number of jump edges labelled c and n(c) = m(−c). Take c ≠ 0 in X*.
- A point p reaches c in one of three ways: its own label (at most m(c) points); a line through p whose arriving label is −c (at most (q+1)n(c) points, since each such edge has one line with q+1 points); or a U D H value (d^P(c) points, where Σ_c d^P(c) ≤ 2N).
- So N ≤ m(c) + (q+1)n(c) + d^P(c).
- Likewise, for c ∈ Y*: N ≤ m(c) + (q+1)n(c) + d^L(c).

Summing over the non-zero c in X* ∪ Y*, and using Σ m = Σ n = 2N:

(|X* ∪ Y*| − 1)·N ≤ 2N + 2(q+1)N + 2N + 2N.

0 lies in X* through H, which gives the first bound.

With one matching there are no d terms, and Σ m = Σ n = N. Each c needs m(c) + (q+1)m(−c) ≥ N. The left sides sum to (q+2)N over all c ≠ 0, so |X* ∪ Y*| − 1 ≤ q + 2. Equality makes every inequality tight. Comparing c with −c then gives m(c) = m(−c) = N/(q+2), and N ≡ −21 mod (q+2). ∎

The lead's Proposition (Δ = q+2, q+3 copies, q = 5) is exactly this equality case.

| q | 3 | 5 | 7 | 8 | 9 | 11 | 13 |
|---|---|---|---|---|---|---|---|
| ceiling 2q+9 (Δ = q+3) | 15 | 19 | 23 | 25 | 27 | 31 | 35 |
| Delorme 5⌊(q+5)/2⌋ | 20 | 25 | 30 | 30 | 35 | 40 | 45 |

## 4. Values outside X* ∪ Y* (the mixed walks)

**Lemma 2.** Let c ∉ X* ∪ Y*. Let P_c⁻ be the set of points p with c ∉ E(p), and L_c⁻ the set of lines y with c ∉ L(y); both are non-empty. Then every pair in P_c⁻ × L_c⁻ has c ∈ M(p, y). Fixing y_0 ∈ L_c⁻:
- for Δ = q+3, every p ∈ P_c⁻ has f_1(p) or f_2(p) in the two-element set c − {h_1(y_0), h_2(y_0)};
- for Δ = q+2, f is constant on P_c⁻, and h is constant on L_c⁻ with sum c.

In words, the points that miss a non-universal value all lie in at most 2 jump-label classes.

**Corollary (Δ = q+2).** If no label class has more than N/(q+1) points, then m ≤ q + 4. If m = q + 4, at least q+1 of the q+3 non-zero values are non-universal.

*Proof.* For every c ≠ 0:

N ≤ min(N, (q+1)n(c)) + m(c) + [c non-universal]·m(a_c),

where a_c is the constant label on P_c⁻. Summing gives (m−1) ≤ q + 2 + (m−1)/(q+1). ∎

**Theorem 3.** For q ≥ 5 there is no intact Δ = q+2 design with m = q+4 in which every inequality above is tight, i.e. one with label classes of size N/(q+3) and every non-zero value non-universal.

*Proof.* Tightness forces the following.
- Each point with label a misses exactly one value φ(a), and each line with label b misses exactly ψ(b).
- The lines through a point of label a carry the labels A* ∖ {−a, −φ(a)}, one each. The points on a line of label b carry the labels A* ∖ {−b, −ψ(b)}, one each.
- Counting edges shows that the label classes form an **equitable partition** of the incidence graph with quotient B = J − P − Π, where P (a ↦ −a) and Π (a ↦ −φ(a)) are permutation matrices.
- Then B Bᵀ = (m−5)J + 2I + ρ + ρᵀ with ρ = PΠᵀ. Its eigenvalues on 1^⊥ are 2 + 2Re(ω) ∈ [0, 4], over the eigenvalues ω of the permutation ρ.
- These must be eigenvalues of N Nᵀ, i.e. lie in {0, q, 3q}. For q ≥ 5 they would all have to be 0, which makes trace(ρ) = 3 − m < 0. That is impossible for a permutation matrix. ∎

`exact_q2.py 7 8 9` enumerates the functional equation φ(a) = a + φ⁻¹(−a) that these conditions impose. It finds 4 solutions at m = 7 (q = 3) and none at m = 8 or 9; none of the solutions has an admissible spectrum.

So an intact construction of the table's (13,8) = 15·|H(11)| would have to sit in the narrow band between "classes ≤ N/(q+1)" and "fully tight". I think it more likely that Delorme uses hexagon voltages, or routes specific to his matchings. For Δ = q+3, Delorme needs ⌊q/2⌋ + 4 or more non-universal values (5 to 10 for q = 3..13), each confined to two label classes, with only 4 mixed values per pair. I have no proof that this is impossible.

## 5. Levels cannot carry sheets

**Lemma 4.** Let φ: A → Z_r be a homomorphism with φ(ν) = 0 on hexagon edges and φ = a_t ≢ 0 on the jumps of σ_t. Then for every incident pair p ∈ y, the always-present routes with φ-value 0 are:
- H (here just the edge p y);
- the U_s H U_t with a_s + a_t ≡ 0;
- the U_s D_t H and H D_s U_t with a_s ≡ a_t.

That is at most 5 routes, or 9 if 2a_1 ≡ 2a_2 ≡ 0. Hence |ker φ| ≤ 5 (resp. 9) for a proof through always-present routes.

The bundles (U_t H, H U_t) and the q+1-families (h D H, H D h) all sit at levels ±a_t ≠ 0. For T_5 (shifts 1, 2) the level-0 class of an incident pair contains only the edge. For H ∗ C_5 (shifts ±1) it contains 3 routes.

Small q does not contradict this. The cell-10-8 squad found 45 = 5·9 copies at q = 2 and ≥ 25 at q = 3, but there the walks that are not always present are plentiful. For q ≥ 7, only about O(1) such walks exist per pair (cell-10-8 notes §3).

## 6. Other ways to spend the two extra degrees

**Tripled flags (design P).** Take a perfect matching F of flags and give each F-flag three parallel edges with voltages {0, a, b}; the copies stay intact.
- A walk can detour w → F(w) → w with any of 6 differences.
- For a point–line pair at distance 5 the always-present walks are:
  - the geodesic plus one detour at each of its 6 vertices (36 walks);
  - the q² apartment-complement walks;
  - q-families through y's points and p's lines, as in §3.
- The universal argument of §3 caps the families at about 2(q+1).
- A value carried only by detours must have its carriers meeting every 5-path. In a girth-12, (q+1)-regular graph that takes about half of the vertices, so detours add at most about 12 universal values.
- Ceiling about 2q + 15: no better than the matchings.

**Rewired matching (design R, "compounding").** Remove F from every copy and give each F-flag three parallels with no zero among them. The universal ceiling rises to 3(q+1). But every geodesic that uses an F-flag now picks up an uncontrolled sum, and since every vertex lies on an F-flag, this cannot be avoided. It would only be useful with an F whose geodesic behaviour is understood.

**Loops** (BDF ∗-product H ∗ C_m, lead notes §4b). Bipartiteness needs m even, so loops cannot give 35·|H(9)| or 45·|H(13)|.

## 7. Symmetry facts (computed)

**Orbits of SL(3,q) ⊂ G_2(q)** (`orb_sl3.py`), with X → gX, Y → g^{−T}Y and x3 fixed:

| q | point orbits | line orbits | flag orbits |
|---|---|---|---|
| 3 | 13, 13, 104, 234 | 52, 312 | 5 |
| 5 | 31, 31, 744, 3100 | 186, 3720 | 5 |

In general the point orbits are q²+q+1, q²+q+1, (q²+q+1)(q²−1) and q²(q³−1), and the line orbits are (q+1)(q²+q+1) and q(q²−1)(q²+q+1). The sizes differ between points and lines, so there is no SL(3,q)-equivariant matching.

**Invariant hexagon voltages are trivial** (`bundles.py`). For every bundle of opposite points or lines, all q+1 geodesics have the same signed count of flags in each of the 5 SL(3,q)-orbits (q = 3 and 5, all orbit representatives). An SL(3,q)-invariant flag voltage therefore gives every apartment voltage 0: it is a coboundary. Any hexagon voltage that splits bundles must break SL(3,q).

## 8. Copies for free

The cell-10-8 lemma: H(q) plus two arbitrary matchings, lifted over Z10 with jump voltages 1 and 4, has diameter 8. More generally, a design that is uniform over copies is a pair of copy permutations (π_1, π_2), and the always-present routes from copy u reach:
- point→line: u, π_t(u), π_t⁻¹(u), π_tπ_s(u), π_t⁻¹π_s(u) and π_tπ_s⁻¹(u) (s ≠ t in the last two);
- line→point: the reversed words.

This is at most 13 copies. `freecopies.py 10 11 12 13` (annealing, 40 restarts × 20,000 steps) finds a pair for n = 10 and none for 11, 12 or 13. A Cayley pair on a group of order 13 would need ab ≠ ba, which is impossible in Z13.

## 9. What Delorme's graphs must look like, and what to try next

These constraints hold for any proof through always-present routes:
- either the copies are not intact (the hexagon voltages are not a coboundary and are not SL(3,q)-invariant), or about q/2 of the voltages are carried by mixed walks under the rigid structure of Lemma 2;
- there is no level quotient carrying the sheets (Lemma 4);
- the growth of 5/2 per unit of q, against the universal 2, has to come from pair-dependent families. The only ones of size about q are the bundles (q+1 geodesics between opposite elements), which need hexagon voltages.

A numerology hint: k − 1 = ⌊(q+3)/2⌋ is exactly the number of values a degree-2 map PG(1,q) → PG(1,q) with rational branch point(s) takes. That is (q+3)/2 for odd q (x ↦ x², with 0 and ∞ fixed) and (q+2)/2 for even q (x ↦ x² + x). The geodesics of a bundle are parametrised by PG(1,q), the lines through one end. "Bundle voltage = a quadratic function of the geodesic, plus one more sheet" would explain ⌊(q+5)/2⌋ for both parities, but I have not found such a voltage.

Suggested searches:
1. **Quotient search for intact designs.** If the jump labels are constant on the classes of an equitable partition of H (for example the orbits of a subgroup of G_2(q)), and σ_t maps classes to classes, then the whole always-present check reduces to the quotient matrix. Candidates can be enumerated and checked by hand or by bcd. Filter quotients first by the spectrum {±(q+1), ±√(3q), ±√q, 0}.
2. **Hexagon voltages that break SL(3,q).** Look for voltages invariant under a torus or a Borel subgroup that split every bundle into about (q+1)/2 classes. Score them by the minimum number of distinct bundle values over opposite pairs; this is cheap to compute from orbit representatives, as in bundles.py.

## 10. Files and commands (this folder)

- `geo.py`: loads /tmp/bcdt/hex/hex_q{q}.bin (prime q); point lookup by coordinates; the action of 7×7 matrices (`sl3(g)`) on points and lines; orbits.
- `orb_sl3.py q`: SL(3,q) orbits on points, lines and flags. Writes $SCRATCH/sl3_q{q}.npz. Run for q = 3 and 5: output as in §7.
- `bundles.py q`: signed flag-orbit counts of the q+1 geodesics of every bundle from each orbit representative. Output for q = 3 and 5: "flag orbits 5 distinct bundle types (up to translation) 2". The two types are one for points and one for lines, and all differences inside a bundle are zero.
- `freecopies.py 10 11 12 13`: "10 FOUND …", "11 none", "12 none", "13 none".
- `exact_q2.py 7 8 9`: "m 7 … 4 solutions, 0 admissible", "m 8 … 0", "m 9 … 0".

Commands used (each under `timeout 1800 nice -n 10`): `SCRATCH=<dir> python3 orb_sl3.py 3` (also 5); `SCRATCH=<dir> python3 bundles.py 3` (also 5); `python3 freecopies.py 10 11 12 13`; `python3 exact_q2.py 7 8 9`. bcd was not needed, since no candidate graph was built.

Dead ends, briefly:
- SL(3,q)-equivariant matchings (orbit sizes differ).
- SL(3,q)-invariant hexagon voltages (coboundaries).
- Level × sheet lifts of T_5 or H ∗ C_5 (Lemma 4).
- Duality-based jumps, which give extra always-present routes only for q = 3^h: of the target cells that is only q = 9. Not built.
- Doubling with levels applied to H ∗ C⃗_4: condition (c) fails for pairs inside one copy.
- Projection colourings of the points by hyperplane pencils (x0 : x4), which are rainbow on every line that misses the axis {x0 = x4 = 0}: these give about 2q + 3 copies, below Delorme.
- Searching the web: the Delorme papers are not readable from here. zbMATH returned 403, and a 2026 arXiv paper (2608.27253) only describes his diameter-3 and diameter-5 polarity and Kronecker constructions.
